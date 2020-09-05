// Hi, this is my Project Euler stuff

#include <stdio.h>
#include <stdlib.h>


////////////////////////////

int CalcSumMultiples(int num1, int num2, int max) {
	int mult1 = num1;
	int mult2 = num2;

	int sum = 0;

	for (;;) {
		int x;
		if (mult1 == mult2) {
			x = mult1;
			mult1 += num1;
			mult2 += num2;
		}
		else if (mult1 < mult2) {
			x = mult1;
			mult1 += num1;
		}
		else {
			x = mult2;
			mult2 += num2;
		}

		if (x >= max) {
			break;
		}

		sum += x;
	}

	return sum;
}

void RunCalcSumMultiples(int num1, int num2, int max) {
	printf("Sum of multiples of %d and %d under %d = %d\n", num1, num2, max, CalcSumMultiples(num1, num2, max));
}


////////////////////////////

unsigned long CalcEvenFibonacciSum(unsigned long max) {
	unsigned long fibPrev = 0;
	unsigned long fibCurr = 1;

	unsigned long sum = 0;

	for (;;) {
		if (fibCurr >= max) {
			break;
		}

		if ((fibCurr & 1UL) == 0) {
			sum += fibCurr;
		}

		unsigned long newFib = fibPrev + fibCurr;
		fibPrev = fibCurr;
		fibCurr = newFib;
	}

	return sum;
}

void RunEvenFibonacciSum(unsigned long max) {
	printf("Sum of even Fibonacci numbers below %u = %u\n", max, CalcEvenFibonacciSum(max));
}


////////////////////////////



int main(int argc, char** argv) {
	if (argc <= 1) {
		printf("Usage:  ProjectEuler <problem#>\n\n");
		return 0;
	}

	const char* problemArg = argv[1];
	int problemNum = atoi(problemArg);
	printf("Solving problem #%d\n\n", problemNum);
	switch (problemNum) {
	case 1:
		RunCalcSumMultiples(3, 5, 10);
		RunCalcSumMultiples(3, 5, 1000);
		break;
	case 2:
		RunEvenFibonacciSum(56);
		RunEvenFibonacciSum(4000000);
		break;
	default:
		printf("'%s' is not a valid problem number!\n\n", problemArg);
		break;
	}

	return 0;
}

