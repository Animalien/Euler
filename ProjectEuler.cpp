// Hi, this is my Project Euler stuff

#include <math.h>
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

long long CalcLargestPrimeFactor(long long num) {
	long long currNum = num;
	long long max = currNum / 2;

	long long largestPrimeFactor = 0;

	for (long long possiblePrime = 2; possiblePrime <= max; ++possiblePrime) {
		if (currNum == 1) {
			break;
		}

		for (;;) {
			lldiv_t divRem = lldiv(currNum, possiblePrime);
			if (divRem.quot == 0) {
				break;
			}
			if (divRem.rem != 0) {
				break;
			}

			largestPrimeFactor = possiblePrime;
			currNum = divRem.quot;
		}
	}

	return largestPrimeFactor;
}

void RunLargestPrimeFactor(long long num) {
	printf("Largest prime factor of %lld = %lld\n", num, CalcLargestPrimeFactor(num));
}


////////////////////////////

bool IsNumPalindrome(int num) {
	//printf("num %d\n", num);

	const double log = log10((double)num);
	
	int numDigits = (int)log + 1;
	for (;;) {
		if (numDigits <= 1) {
			break;
		}

		const int highDigitDenom = (int)pow(10.0, (double)(numDigits - 1));
		const int highDigit = num / highDigitDenom;
		const int lowDigit = num % 10;
		//printf("%d: %d-%d\n", num, highDigit, lowDigit);

		if (highDigit != lowDigit) {
			return false;
		}

		num = (num % highDigitDenom) / 10;
		numDigits -= 2;
	}

	return true;
}


void RunLargestPalindromeProduct(int numToTest) {
	printf("Num %d is %sa palindrome!\n", numToTest, IsNumPalindrome(numToTest) ? "" : "NOT ");
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
	case 3:
		RunLargestPrimeFactor(13195UL);
		RunLargestPrimeFactor(600851475143UL);
		break;
	case 4:
		RunLargestPalindromeProduct(122);
		RunLargestPalindromeProduct(1221);
		RunLargestPalindromeProduct(9009);
		RunLargestPalindromeProduct(19009);
		for (int i = 1; i < 1000; ++i) {
			RunLargestPalindromeProduct(i);
		}
		break;
	default:
		printf("'%s' is not a valid problem number!\n\n", problemArg);
		break;
	}

	return 0;
}

