#include <ctype.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

/*
 *
 *	PARSER SECTION
 *
 */

/*
 *	Debug mode = 1 prints the data of the solving into the console.
 */

#define DEBUG_MODE 0

/*
 *  Choose separator mode, one blank allows better performance, several blanks better flexibility.
 *  Choosing one blank on ill-formatted file will result in undefined behavior.
 *  If both are active, several will take precedence.
 */

#define ONE_BLANK 0
#define SEVERAL_BLANKS 1

#if !(ONE_BLANK || SEVERAL_BLANKS)
# error please choose separator mode
#endif

__attribute__((always_inline)) inline void
skip_comments_line (char **data) {

    while (**data == 'c' || **data == '%' || **data == '\n') {
        while (**data != '\n')
            *data += 1;
        *data += 1;
    }
}

int
get_line_length(char **data) {

    /*
     *  Lines must be properly formatted otherwise result will be inaccurate, ie.
     *  [int][single_space][int][single_space][int]... [0][newline]
     */

    int num = 0;
    while (**data != '0') {

        /* Will skip either minus sign or first digit. */
        *data += 1;

        /* Will skip remaining digits if any. */
        while (isdigit(**data)) *data += 1;

#if SEVERAL_BLANKS
        while (isblank(**data))
#endif

            *data += 1;
        num += 1;
    }

    *data += 2;
    return num;
}

int **
parse_cnf (char *data) {
	int line_length;

    skip_comments_line(&data);

    /* Expect 'p cnf K P' line where K is the max integer value and P the number of lines. */
    if (*data != 'p')
        return NULL;

    /* Position data on column number. */
    while (!isdigit(*data)) data += 1;
    while (isdigit(*data)) data += 1;
    while (!isdigit(*data)) data += 1;

    int column_number = strtol(data, &data, 10);
    data += 1;
    int **array = malloc(sizeof(int *) * (column_number + 1));
    if (__builtin_expect(!array, 0))
        return NULL;

    /* Parsing. */
    for (int k = 0; k < column_number;) {
        skip_comments_line(&data);

        /* We need to iterate twice over the line, keep data at the beginning of next line and work on copy. */
        char *line = data;
		line_length = get_line_length(&data);
		if (line_length > 0) {
        	array[k] = malloc(sizeof(int) * (line_length + 1));
        	if (__builtin_expect(!array[k], 0))
            	return NULL;

        	/* Map values. */
        	for (int p = 0; *line != '\n'; p += 1) {
            	int val = (int)strtol(line, &line, 10);
            	if ((array[k][p] = val) == 0)
                	break;
            	line += 1;
        	}

        	/* Zero terminate the array. */
        	if (++k == column_number) {
            	array[k] = 0;
            	break;
        	}
		}
    }

    return array;
}

int **
read_cnf (char const *filename) {

    int **array;

    /* Process file. */
    if (filename) {
        int const fd = open(filename, O_RDONLY);
        if (fd == -1)
            return NULL;

        struct stat s;
        if (stat(filename, &s) == -1)
            return NULL;

        void *m = mmap(NULL, s.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
        if (m == MAP_FAILED)
            return NULL;

        array = parse_cnf((char *)m);
        munmap(m, s.st_size);

    /* Read from standard input. */
    } else {
        char buff[BUFSIZ];
        char *data = NULL;
        size_t pos = 0;

        for (size_t bytes = 0; (bytes = read(STDIN_FILENO, buff, BUFSIZ)); ) {
            if (bytes == (size_t)-1)
                return NULL;
            data = realloc(data, pos + bytes);
            strncpy(&data[pos], buff, bytes);
            pos += bytes;
        }

        size_t len = strlen(buff);
        data = realloc(data, pos + len);
        strncpy(&data[pos], buff, len);

        array = parse_cnf(data);
    }

    return array;
}

/*
 *
 *	SOLVER SECTION
 *
 */

/*
 *  SAMPLE PARAM is the number of random trials in order to find an existing unsatisfied clause
 *  MILESTONE_PARAM is the number of milestones in the char* constraints
 */

#define SAMPLE_PARAM 10
#define MILESTONE_PARAM 100 

int		num_variables;
int		num_clauses;
int		*hold_size;
int		**hold;
int		num_constraints;
char	*constraints;
char 	*solution;
int     *milestones;
int     step;

int
abs(int x) {
	if (x < 0)
		return (-x);
	return (x);
}

void
get_size (int **cnf) {
	int	i;
	int	j;
	int	size;

	size = 0;
	i = 0;
	while (cnf[i]) {
		j = 0;
		while (cnf[i][j]) {
			if (cnf[i][j] > size)
				size = cnf[i][j];
			if (-cnf[i][j] > size)
				size = -cnf[i][j];
			j++;
		}
		i++;
	}
	num_variables = size;
	num_clauses = i;
}

char
is_solved(int **cnf, int i) {
	int		j;

	j = 0;
	while (cnf[i][j] && cnf[i][j] * (solution[abs(cnf[i][j])] - '|') <= 0)
		j++;
	if (cnf[i][j] == 0)
		return ('F');
	return ('T');
}

char
insert(int i) {
    int     j;

	if (constraints[i] == 'y')
		return ('E'); // exists already
	j = 0;
    while (j * step <= i)
        j++;
    while (j * step < num_clauses) {
        milestones[j]++;
        j++;
    }
    milestones[j]++;
    constraints[i] = 'y';
	num_constraints++;
	return ('C'); // is created
}

char
extract(int i) {
    int     j;

	if (constraints[i] == 'n')
		return ('E'); // exists already
	j = 0;
    while (j * step <= i)
        j++;
    while (j * step < num_clauses) {
        milestones[j]--;
        j++;
    }
    milestones[j]--;
    constraints[i] = 'n';
	num_constraints--;
	return ('C'); // is created
}

void
initiate(int **cnf) {
	int		i;
	int		j;
	int		k;

	solution = malloc(sizeof(char) * (num_variables + 2));
	solution[0] = 's';
	i = 1;
	while (i <= num_variables) {
		solution[i] = '|';
		i++;
	}
	solution[i] = '\0';

	constraints = malloc(sizeof(char) * (num_clauses + 1));
	i = 0;
	while (i < num_clauses) {
		constraints[i] = 'y';
		i++;
	}
	constraints[i] = '\0';
	num_constraints = num_clauses;

	hold_size = malloc(sizeof(int) * (2 * (num_variables + 1) + 1));
	i = 0;
	while (i <= 2 * (num_variables + 1)) {
		hold_size[i] = 0;
		i++;
	}
	i = 0;
	while (cnf[i]) {
		j = 0;
		while (cnf[i][j]) {
			hold_size[num_variables + cnf[i][j] + 1]++;
			j++;
		}
		i++;
	}
	hold = malloc(sizeof(int*) * (2 * (num_variables + 1) + 1));
	i = 0;
	while (i <= 2 * (num_variables + 1)) {
		hold[i] = malloc(sizeof(int) * (hold_size[i] + 1));
		hold[i][0] = -1;
		i++;
	}
	i = 0;
	while (cnf[i]) {
		j = 0;
		while (cnf[i][j]) {
			k = 0;
			while (hold[num_variables + cnf[i][j] + 1][k] >= 0)
				k++;
			hold[num_variables + cnf[i][j] + 1][k] = i;
			hold[num_variables + cnf[i][j] + 1][k + 1] = -1;
			j++;
		}
		i++;
	}
    
    step = num_clauses / MILESTONE_PARAM;
    if (step < 100)
        step = 100;
    i = 0;
    while (i * step < num_clauses)
        i++;
    milestones = malloc(sizeof(int) * (i + 1));
    i = 0;
    while (i * step < num_clauses) {
        milestones[i] = i * step;
        i++;
    }
    milestones[i] = num_clauses;
}

void
terminate(int **cnf) {
	int		i;

	free(solution);
	free(constraints);
	free(hold_size);
	i = 0;
	while (i <= 2 * (num_variables + 1)) {
		free(hold[i]);
		i++;
	}
	free(hold);
	i = 0;
	while (i < num_clauses) {
		free(cnf[i]);
		i++;
	}
	free(cnf);
}

int
verify(int **cnf) {
	int		i;

	i = 0;
	while (cnf[i]) {
		if (is_solved(cnf, i) == 'F')
			return (0); // not a licit solution
		i++;
	}
	return (1);
}

int
find(int r) {
	int		a;
	int		i;
    int     j;
	char	*ret;

	if (num_clauses / num_constraints < SAMPLE_PARAM) { 
		a = 0;
		while (a < SAMPLE_PARAM) {
			i = rand() % num_clauses;
			if (constraints[i] == 'y')
				return (i);
			a++;
		}
    }
    j = 0;
    while (j * step < num_clauses && milestones[j] <= r)
        j++;
    a = milestones[j - 1];
	ret = constraints + (j - 1) * step - 1;
	while (a <= r) {
		ret++;
		ret = strchr(ret, 'y');
		a++;
	}
	return (int)(ret - constraints);
}

int		buffer[69];

int
elect(int **cnf, int i) {
	int		a;
	int		j;

	buffer[0] = 0;
	a = 0;
	j = 0;
	while (cnf[i][j]) {
		if (solution[abs(cnf[i][j])] == '|') {
			buffer[a] = cnf[i][j];
			a++;
			buffer[a] = 0;
		}
		j++;
	}
	if (a > 0) {
		a = rand() % a;
		return (buffer[a]);
	}
	j = rand() % j;
	return (cnf[i][j]);
}

void
solve(int **cnf) {
	int		i;
	int		k;
	int		x;

	while (num_constraints > 0) {
		i = find(rand() % num_constraints);
		x = elect(cnf, i);
		if (solution[abs(x)] == '|') {
			solution[abs(x)] = (x > 0 ? '}' : '{');
			k = 0;
			while (hold[num_variables + x + 1][k] >= 0) {
				i = hold[num_variables + x + 1][k];
				extract(i);
				k++;
			}
			k = 0;
			while (hold[num_variables - x + 1][k] >= 0) {
				i = hold[num_variables - x + 1][k];
				if (constraints[i] == 'n' && is_solved(cnf, i) == 'F')
					insert(i);
				k++;
			}
		} else {
			solution[abs(x)] = '|';
			k = 0;
			while (hold[num_variables + x + 1][k] >= 0) {
				i = hold[num_variables + x + 1][k];
				if (constraints[i] == 'n' && is_solved(cnf, i) == 'F')
					insert(i);
				k++;
			}
			k = 0;
			while (hold[num_variables - x + 1][k] >= 0) {
				i = hold[num_variables - x + 1][k];
				if (constraints[i] == 'n' && is_solved(cnf, i) == 'F')
					insert(i);
				k++;
			}
		}
	}
}

int
main (int argc, char const **argv) {
    int 	**cnf = read_cnf(argc == 1 ? NULL : argv[1]);

    if (cnf == NULL) {
        printf("Invalid\n");
        return EXIT_FAILURE;
    }
#if DEBUG_MODE
        /* Display for testing. */
        for (int k = 0; cnf[k]; k += 1) {
            for (int p = 0; cnf[k][p]; p += 1)
                printf("[%d]", cnf[k][p]);
            printf("\n");
        }
#endif
	srand(42);
	get_size(cnf);
	initiate(cnf);
	solve(cnf);
	if (verify(cnf) == 1) {
		printf("%s\n", solution);
	} else {
		printf("Solution error\n");
	}
	terminate(cnf);
	return EXIT_SUCCESS;
}