// Hi, this is my Project Euler stuff

#include <stdio.h>


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
	printf("Sum of multiples of %d and %d under %d = %d\n\n", num1, num2, max, CalcSumMultiples(num1, num2, max));
}

////////////////////////////



int main(int argc, char** argv) {
	printf("Cool story, bro\n\n");

	RunCalcSumMultiples(3, 5, 10);
	RunCalcSumMultiples(3, 5, 1000);

	return 0;
}

