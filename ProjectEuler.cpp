// Hi, this is my Project Euler stuff

#include <algorithm>
#include <assert.h>
#include <deque>
#include <map>
#include <math.h>
#include <numeric>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <vector>


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
// PrimeFinder

class PrimeFinder : public std::vector<BigInt> {
public:
	PrimeFinder()
		: std::vector<BigInt>(), m_windowBase(3), m_windowOffset(0) {

		// start the primes list with 2, and start the window base at the very next value, 3

		push_back(2);
	}

	void Reset() {
		clear();
		push_back(2);
		m_windowBase = 3;
		m_windowOffset = 0;
	}

	void FindPrimes(BigInt windowSize = 128) {
		// reinitialize window
		std::fill(m_windowFlags.begin(), m_windowFlags.end(), true);
		m_windowFlags.resize(windowSize, true);
		assert(std::find(m_windowFlags.begin(), m_windowFlags.end(), false) == m_windowFlags.end());
		m_windowOffset = 0;

		// mark non-primes based on pre-existing primes
		//printf("Marking non-primes based on previous non-primes\n");
		for (auto iter = begin(); iter != end(); ++iter) {
			MarkNonPrimes(*iter);
		}

		// walk through window, adding new primes and marking more non-primes as we go
		//printf("Walking through window to find more primes\n");
		const BigInt maxPossiblePrime = m_windowBase + m_windowFlags.size();
		for (BigInt currPossiblePrime = m_windowBase; currPossiblePrime < maxPossiblePrime; ++currPossiblePrime) {
			const bool isPrime = m_windowFlags[currPossiblePrime - m_windowBase];
			m_windowOffset++;

			if (isPrime) {
				//printf("%lld is prime!\n", currPossiblePrime);
				push_back(currPossiblePrime);
				MarkNonPrimes(currPossiblePrime);
			}
			//else {
			//	printf("%lld is NOT prime!\n", currPossiblePrime);
			//}
		}

		// move window for next time
		m_windowBase += m_windowFlags.size();
	}

	BigInt FindNthPrime(BigInt n) {
		const BigInt windowSize = 2 * n;
		while ((BigInt)size() < n) {
			FindPrimes(windowSize);
			//PrintPrimes();
		}
		return (*this)[n - 1];
	}

	void FindPrimesBelow(BigInt max) {
		if (max <= m_windowBase) {
			Reset();
		}

		FindPrimes(max - m_windowBase);
	}

	void PrintPrimes() {
		for (auto iter = begin(); iter != end(); ++iter) {
			printf("%lld ", *iter);
		}
	}


private:
	void MarkNonPrimes(BigInt num) {
		//printf("Marking non-primes:  num = %lld\n", num);
		const BigInt firstNum = m_windowBase + m_windowOffset;
		//printf("firstNum %lld = base %lld + offset %lld\n", firstNum, m_windowBase, m_windowOffset);

		const auto devRem = lldiv(firstNum, num);
		//printf("firstNum %lld / %lld =  %lld q, %lld r\n", firstNum, num, devRem.quot, devRem.rem);

		BigInt firstQuot = devRem.quot;
		if (devRem.rem > 0) {
			++firstQuot;
		}
		//printf("firstQuot = %lld\n", firstQuot);

		BigInt firstNonPrime = firstQuot * num;
		//printf("firstNonPrime = %lld\n", firstNonPrime);
		const BigInt maxNonPrime = m_windowBase + m_windowFlags.size();

		for (BigInt currNonPrime = firstNonPrime; currNonPrime < maxNonPrime; currNonPrime += num) {
			//printf("Marking %lld as non-prime\n", currNonPrime);
			m_windowFlags[currNonPrime - m_windowBase] = false;
		}
	}

	BigInt				m_windowBase;
	BigInt				m_windowOffset;
	std::vector<bool>	m_windowFlags;
};

static PrimeFinder s_primeFinder;

void TestPrimeFinder(BigInt window) {
	s_primeFinder.FindPrimes(window);
	printf("Prime finder window of %lld resulted in these primes:  ", window);
	s_primeFinder.PrintPrimes();
	printf("\n\n");
	
	s_primeFinder.FindPrimes(window);
	printf("Prime finder window of %lld more resulted in these primes:  ", window);
	s_primeFinder.PrintPrimes();
	printf("\n\n");
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
// Problem 7 - 10001st prime

BigInt CalcNthPrime(BigInt n) {
	return s_primeFinder.FindNthPrime(n);
}

void RunNthPrime(BigInt n) {
	printf("Prime #%lld = %lld\n", n, CalcNthPrime(n));
}


////////////////////////////
// Problem 8 - Largest product in series

static const std::string s_largestProductInSeriesSeries =
	"73167176531330624919225119674426574742355349194934"
	"96983520312774506326239578318016984801869478851843"
	"85861560789112949495459501737958331952853208805511"
	"12540698747158523863050715693290963295227443043557"
	"66896648950445244523161731856403098711121722383113"
	"62229893423380308135336276614282806444486645238749"
	"30358907296290491560440772390713810515859307960866"
	"70172427121883998797908792274921901699720888093776"
	"65727333001053367881220235421809751254540594752243"
	"52584907711670556013604839586446706324415722155397"
	"53697817977846174064955149290862569321978468622482"
	"83972241375657056057490261407972968652414535100474"
	"82166370484403199890008895243450658541227588666881"
	"16427171479924442928230863465674813919123162824586"
	"17866458359124566529476545682848912883142607690042"
	"24219022671055626321111109370544217506941658960408"
	"07198403850962455444362981230987879927244284909188"
	"84580156166097919133875499200524063689912560717606"
	"05886116467109405077541002256983155200055935729725"
	"71636269561882670428252483600823257530420752963450";

BigInt CalcLargestProductInSeries(BigInt numDigits) {
	const BigInt seriesLength = s_largestProductInSeriesSeries.length();

	std::deque<BigInt> factorDeque;

	// now roll through the entire series, looking for the largest product of adjacent digits
	// note: keep track of '0' digits separately because they zero-stomp a product,
	//			and don't multiply them into the current product
	BigInt largestProduct = 0;
	BigInt currProduct = 1;
	BigInt numZeroes = 0;
	for (BigInt i = 0; i < seriesLength; ++i) {
		// first get rid of the oldest factor (if we are at num digits)
		if (i >= numDigits) {
			const BigInt oldestFactor = factorDeque.front();
			if (oldestFactor == 0) {
				--numZeroes;
			}
			else {
				currProduct /= oldestFactor;
				//printf("%lld / %lld = %lld\n", currProduct * oldestFactor, oldestFactor, currProduct);
			}
			factorDeque.pop_front();
		}

		// now multiply in the new factor
		const BigInt newFactor = (BigInt)(s_largestProductInSeriesSeries[i] - '0');
		//printf("%c", s_largestProductInSeriesSeries[i]);

		if (newFactor == 0) {
			++numZeroes;
		}
		else {
			currProduct *= newFactor;
			//printf("%lld * %lld = %lld\n", currProduct / newFactor, newFactor, currProduct);
		}
		factorDeque.push_back(newFactor);

		// finally compare to see if this is the new largest product
		// (but only if we have enough digits and there are no zeroes in the sequence)
		if ((i >= numDigits) && (numZeroes <= 0) && (currProduct > largestProduct)) {
			largestProduct = currProduct;
		}
	}

	return largestProduct;
}

void RunLargestProductInSeries(BigInt numDigits) {
	printf("Largest product in 1000 digit series using %lld adjacent digits = %lld\n", numDigits, CalcLargestProductInSeries(numDigits));
}


////////////////////////////
// Problem 9 - Special Pythagorean triplet

void RunSpecialPythagoreanTriplet() {
	for (BigInt a = 1; a < 1000; ++a) {
		for (BigInt b = a + 1; b < 1000; ++b) {
			double doubleC = sqrt((double)a * (double)a + (double)b * (double)b);
			BigInt intC = (BigInt)doubleC;
			if (doubleC == (double)intC) {
				printf("Found Pyth triplet:  %lld^2 + %lld^2 = %lld^2;  a+b+c = %lld;  abc = %lld\n", a, b, intC, a+b+intC, a*b*intC);
				if ((a + b + intC) == 1000) {
					printf("Found triplet with sum of 1000!\n");
					return;
				}
			}
		}
	}

}


////////////////////////////
// Problem 10 - Summation of primes

BigInt CalcSumOfPrimesBelow(BigInt max) {
	s_primeFinder.FindPrimesBelow(max);
	//s_primeFinder.PrintPrimes();
	return std::accumulate(s_primeFinder.begin(), s_primeFinder.end(), 0LL);
}

void RunSummationOfPrimes(BigInt max) {
	printf("Sum of primes under %lld = %lld\n", max, CalcSumOfPrimesBelow(max));
}


////////////////////////////



int main(int argc, char** argv) {
	if (argc <= 1) {
		printf(
			"Usages:\n"
			"  ProjectEuler <problem#>\n"
			"  ProjectEuler factorization\n"
			"  ProjectEuler primeFinder\n");
		return 0;
	}

	const char* problemArg = argv[1];
	if (strcmp(problemArg, "factorization") == 0) {
		TestFactorizationRange(20);
		return 0;
	}
	else if (strcmp(problemArg, "primeFinder") == 0) {
		TestPrimeFinder(10);
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
	case 7:
		RunNthPrime(6);
		RunNthPrime(50);
		RunNthPrime(10001);
		break;
	case 8:
		RunLargestProductInSeries(4);
		RunLargestProductInSeries(10);
		RunLargestProductInSeries(13);
		break;
	case 9:
		RunSpecialPythagoreanTriplet();
		break;
	case 10:
		RunSummationOfPrimes(10);
		RunSummationOfPrimes(100);
		RunSummationOfPrimes(2000000);
		RunSummationOfPrimes(100);
		RunSummationOfPrimes(10);
		break;
	default:
		printf("'%s' is not a valid problem number!\n\n", problemArg);
		break;
	}

	return 0;
}

