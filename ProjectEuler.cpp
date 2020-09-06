// Hi, this is my Project Euler stuff

#include <map>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>


////////////////////////////
////////////////////////////
// General tools

typedef long long BigInt;

////////////////////////////
// Factorization

class Factorization : public std::map<BigInt, BigInt> {
public:
	Factorization() : std::map<BigInt, BigInt>() { }

	bool IsPrime() const {
		return ((size() == 1) && (begin()->second == 1));
	}

	void Absorb(const Factorization& other) {
		for (auto iter = other.begin(); iter != other.end(); ++iter) {
			Absorb(iter->first, iter->second);
		}
	}

	BigInt CalcProduct() const {
		BigInt product = 1;
		for (auto iter = begin(); iter != end(); ++iter) {
			for (BigInt i = 0; i < iter->second; ++i) {
				product *= iter->first;
			}
		}
		return product;
	}

private:
	void Absorb(BigInt number, BigInt numFactors) {
		auto iter = find(number);
		if (iter != end()) {
			iter->second = std::max(iter->second, numFactors);
		}
		else {
			insert(value_type(number, numFactors));
		}
	}
};

class FactorizationCache : public std::map<BigInt, Factorization> {
public:
	FactorizationCache() : std::map<BigInt, Factorization>() { }

	void PopulateCache(BigInt num) {
		Factorize(num * 2);
	}

	const Factorization& Factorize(BigInt num) {
		iterator fiter = find(num);
		if (fiter == end()) {
			fiter = NewFactorize(num);
		}

		return fiter->second;
	}

private:
	iterator NewFactorize(BigInt num) {
		auto newValue = insert(value_type(num, Factorization()));
		iterator newIter = newValue.first;
		Factorization& newFactorization = newIter->second;

		const BigInt halfNum = num / 2;
		BigInt prodRemaining = num;
		for (BigInt i = 2; i <= halfNum; ++i) {
			const Factorization& f = Factorize(i);
			if (f.IsPrime()) {
				// i is prime, so see how many i factors fit into this number
				BigInt numFactors = 0;
				for (;;) {
					auto divRem = div(prodRemaining, i);
					if (divRem.rem != 0) {
						break;
					}
					++numFactors;
					prodRemaining = divRem.quot;
				}
				if (numFactors > 0) {
					newFactorization.emplace(i, numFactors);
				}
			}
		}
		if (newFactorization.empty()) {
			newFactorization.emplace(num, 1);
		}

		return newIter;
	}
};

static FactorizationCache s_factorizationCache;

void TestFactorization(BigInt num) {
	printf("%lld:  ", num);

	const Factorization& f = s_factorizationCache.Factorize(num);
	if (f.IsPrime()) {
		printf("prime!  ");
	}

	for (auto iter = f.begin(); iter != f.end(); ++iter) {
		printf("(%lldn of %lld) ", iter->second, iter->first);
	}

	printf("\n");
}

void TestFactorizationRange(BigInt max) {
	s_factorizationCache.PopulateCache(max);

	for (BigInt i = 2; i <= max; ++i) {
		TestFactorization(i);
	}
}

////////////////////////////
////////////////////////////
// Problems

////////////////////////////
// Problem 1 - Sum of multiples

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
// Problem 2 - Even fibonacci sum

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
// Problem 3 - Largest prime factor

BigInt CalcLargestPrimeFactor(BigInt num) {
	BigInt currNum = num;
	BigInt max = currNum / 2;

	BigInt largestPrimeFactor = 0;

	for (BigInt possiblePrime = 2; possiblePrime <= max; ++possiblePrime) {
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

void RunLargestPrimeFactor(BigInt num) {
	printf("Largest prime factor of %lld = %lld\n", num, CalcLargestPrimeFactor(num));
}


////////////////////////////
// Problem 4 - Largest palindrome product

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

int CalcLargestPalindromeProduct(int numDigits) {
	const int min = (int)pow(10.0, (double)(numDigits - 1));
	const int max = (int)pow(10.0, (double)numDigits) - 1;

	int largestProduct = -1;

	for (int num1 = max;  num1 >= min;  --num1) {
		if ((largestProduct > 0) && ((num1 * num1) < largestProduct)) {
			break;
		}

		for (int num2 = num1; num2 >= min; --num2) {
			int product = num1 * num2;
			if ((largestProduct > 0) && (product < largestProduct)) {
				break;
			}

			if (IsNumPalindrome(product)) {
				largestProduct = product;
			}
		}
	}

	return largestProduct;
}

void RunLargestPalindromeProduct(int numDigits) {
	printf("Largest palindrome product between two numbers of %d digits = %d!\n", numDigits, CalcLargestPalindromeProduct(numDigits));
}


////////////////////////////
// Problem 5 - Smallest multiple

BigInt CalcSmallestMultiple(BigInt max) {
	s_factorizationCache.PopulateCache(max);

	Factorization f;
	for (BigInt i = 1; i <= max; ++i) {
		f.Absorb(s_factorizationCache.Factorize(i));
	}

	return f.CalcProduct();
}

void RunSmallestMultiple(BigInt max) {
	printf("Smallest multiple of all numbers from 1 to %lld = %lld\n", max, CalcSmallestMultiple(max));
}


////////////////////////////
// Problem 6 - Sum square difference

BigInt CalcSumSquareDifference(BigInt max) {
	BigInt sum = 0;
	BigInt sumSq = 0;
	for (BigInt i = 1; i <= max; ++i) {
		sum += i;
		sumSq += (i * i);
	}

	const BigInt sqSum = sum * sum;

	return sqSum - sumSq;
}

void SumSquareDifference(BigInt max) {
	printf("Sum square difference of first %lld natural numbers = %lld\n", max, CalcSumSquareDifference(max));
}


////////////////////////////



int main(int argc, char** argv) {
	if (argc <= 1) {
		printf(
			"Usages:\n"
			"  ProjectEuler <problem#>\n"
			"  ProjectEuler factorization\n");
		return 0;
	}

	const char* problemArg = argv[1];
	if (strcmp(problemArg, "factorization") == 0) {
		TestFactorizationRange(100);
		return 0;
	}

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
		RunLargestPalindromeProduct(1);
		RunLargestPalindromeProduct(2);
		RunLargestPalindromeProduct(3);
		RunLargestPalindromeProduct(4);
		break;
	case 5:
		RunSmallestMultiple(10);
		RunSmallestMultiple(20);
		RunSmallestMultiple(30);
		break;
	case 6:
		SumSquareDifference(10);
		SumSquareDifference(20);
		SumSquareDifference(100);
		break;
	default:
		printf("'%s' is not a valid problem number!\n\n", problemArg);
		break;
	}

	return 0;
}

