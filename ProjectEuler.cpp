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

	void PrintFactors() const {
		for (auto iter = begin(); iter != end(); ++iter) {
			printf("(%lldn of %lld) ", iter->second, iter->first);
		}
	}

	BigInt CalcNumDivisors() const {
		if (IsPrime()) {
			// if prime, then number of divisors is simply:  1, and itself
			return 2;
		}

		BigInt numDivisors = 1;
		// the number of divisors will be the numbers of combinations of prime factors.
		// in a given divisor, each prime factor can be included from 0 to N times, where
		// N is the number of times that prime factor exists in the original number.
		// (the divisor with ZERO of any prime factors included, is the divisor 1, which every number has.)
		for (auto iter = begin(); iter != end(); ++iter) {
			numDivisors *= (iter->second + 1);
		}
		// add 1 more for the original number, being one of its own divisors
		numDivisors += 1;

		return numDivisors;
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
					const lldiv_t divRem = lldiv(prodRemaining, i);
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

			if (prodRemaining == 1) {
				break;
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

	f.PrintFactors();

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
// HugeInt

class HugeInt {
public:
	HugeInt() : m_backwards(true) { }
	HugeInt(BigInt num) : m_string(std::to_string(num)), m_backwards(false) { }
	HugeInt(const char* st) : m_string(st), m_backwards(false) { }
	HugeInt(std::string st) : m_string(st), m_backwards(false) { }

	void Print() const {
		printf("%s", GetString());
	}
	const char* GetString() const {
		SetForwards();
		return m_string.c_str();
	}

	HugeInt operator+ (const HugeInt& other) const {
		const HugeInt*const list[2] = { this, &other };
		return CalcSum<2>(list);
	}

	template <int NumItems>
	static HugeInt CalcSum(const HugeInt list[NumItems]) {
		return CalcSum(ListIterator(list, NumItems));
	}
	template <int NumItems>
	static HugeInt CalcSum(const HugeInt*const list[NumItems]) {
		return CalcSum(ListIterator(list, NumItems));
	}

private:
	void SetForwards() const {
		if (m_backwards) {
			Flip();
		}
	}
	void SetBackwards() const {
		if (!m_backwards) {
			Flip();
		}
	}

	void Flip() const {
		std::reverse(m_string.begin(), m_string.end());
		m_backwards = !m_backwards;
	}

	class ConstIterator {
	public:
		// Note: This iterator iterates from ones place on up to increasing digit place values.
		//			For example, with the int "451", we will iterate thusly:  "1", then "5", then "4"

		ConstIterator(const HugeInt& parent) : m_string(parent.m_string) {
			if (parent.m_backwards) {
				// the int is already backwards, so just interate from start to finish
				m_index = 0;
				m_endIndex = m_string.length();
				m_increment = +1;
			}
			else {
				// the int is not backwards, i.e. it is in readable form, so we must iterate backwards from the end
				m_index = m_string.length() - 1;
				m_endIndex = -1;
				m_increment = -1;
			}
		}

		bool IsAtEnd() const {
			return (m_index == m_endIndex);
		}
		void Increment() {
			if (!IsAtEnd()) {
				m_index += m_increment;
			}
		}

		BigInt GetDigit() const {
			if (IsAtEnd()) {
				return 0;
			}
			return (BigInt)m_string[m_index] - (BigInt)'0';
		}


	private:
		const std::string&	m_string;
		BigInt				m_index;
		BigInt				m_endIndex;
		BigInt				m_increment;
	};

	class ListIterator {
	public:
		ListIterator(const HugeInt* itemList, BigInt numItems) : m_ptr(itemList), m_ptrptr(nullptr), m_num(numItems) {
		}
		ListIterator(const HugeInt*const* itemList, BigInt numItems) : m_ptr(nullptr), m_ptrptr(itemList), m_num(numItems) {
		}

		BigInt GetNum() const {
			return m_num;
		}

		bool IsAtEnd() const {
			return (m_num <= 0);
		}
		void Increment() {
			if (IsAtEnd()) {
				return;
			}

			if (m_ptr) {
				++m_ptr;
			}
			else {
				++m_ptrptr;
			}
			--m_num;
		}

		const HugeInt& operator*() const {
			if (m_ptr) {
				return *m_ptr;
			}
			else {
				return **m_ptrptr;
			}
		}

	private:
		const HugeInt*			m_ptr;
		const HugeInt*const*	m_ptrptr;
		BigInt					m_num;
	};

	static HugeInt CalcSum(ListIterator& listIter) {
		std::vector<ConstIterator> iterList;
		iterList.reserve(listIter.GetNum());

		// populate the list of individual iterators
		for (; !listIter.IsAtEnd(); listIter.Increment()) {
			iterList.push_back(ConstIterator(*listIter));
		}

		HugeInt sum;
		BigInt carryOver = 0;

		// now iterate through the digits, starting from ones' place,
		// adding each input number's contribution from that digit,
		// and including any carry-over from previous digits

		for (;;) {
			bool haveMoreDigits = false;
			BigInt digitSum = carryOver;

			for (auto iterListIter = iterList.begin(); iterListIter != iterList.end(); ++iterListIter) {
				ConstIterator& currIter = *iterListIter;
				digitSum += currIter.GetDigit();
				currIter.Increment();
				if (!currIter.IsAtEnd()) {
					haveMoreDigits = true;
				}
			}

			if ((digitSum <= 0) && !haveMoreDigits) {
				// we are done!
				break;
			}

			const lldiv_t divRem = lldiv(digitSum, 10);
			const char newDigit = (char)(divRem.rem + '0');
			sum.m_string += newDigit;

			carryOver = divRem.quot;
		}

		return sum;
	}

	mutable std::string		m_string;
	mutable bool			m_backwards;
};


void TestHugeInt() {
	HugeInt n1 = 135;
	HugeInt n2 = "2005";
	HugeInt n3 = 52;

	printf("TestHugeInt:  n1 = %s, n2 = %s, n3 = %s, n1 + n2 = %s, n1 + n2 + n3 = %s\n", n1.GetString(), n2.GetString(), n3.GetString(), (n1 + n2).GetString(), (n1 + n2 + n3).GetString());
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
			const lldiv_t divRem = lldiv(currNum, possiblePrime);
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
// Problem 11 - Largest grid product

static const BigInt s_largestGridGridSize = 20;
static BigInt s_largestGridGrid[s_largestGridGridSize][s_largestGridGridSize] = {
	{  8,  2, 22, 97, 38, 15,  0, 40,  0, 75,  4,  5,  7, 78, 52, 12, 50, 77, 91,  8 },
	{ 49, 49, 99, 40, 17, 81, 18, 57, 60, 87, 17, 40, 98, 43, 69, 48,  4, 56, 62,  0 },
	{ 81, 49, 31, 73, 55, 79, 14, 29, 93, 71, 40, 67, 53, 88, 30,  3, 49, 13, 36, 65 },
	{ 52, 70, 95, 23,  4, 60, 11, 42, 69, 24, 68, 56,  1, 32, 56, 71, 37,  2, 36, 91 },
	{ 22, 31, 16, 71, 51, 67, 63, 89, 41, 92, 36, 54, 22, 40, 40, 28, 66, 33, 13, 80 },
	{ 24, 47, 32, 60, 99,  3, 45,  2, 44, 75, 33, 53, 78, 36, 84, 20, 35, 17, 12, 50 },
	{ 32, 98, 81, 28, 64, 23, 67, 10, 26, 38, 40, 67, 59, 54, 70, 66, 18, 38, 64, 70 },
	{ 67, 26, 20, 68,  2, 62, 12, 20, 95, 63, 94, 39, 63,  8, 40, 91, 66, 49, 94, 21 },
	{ 24, 55, 58,  5, 66, 73, 99, 26, 97, 17, 78, 78, 96, 83, 14, 88, 34, 89, 63, 72 },
	{ 21, 36, 23,  9, 75,  0, 76, 44, 20, 45, 35, 14,  0, 61, 33, 97, 34, 31, 33, 95 },
	{ 78, 17, 53, 28, 22, 75, 31, 67, 15, 94,  3, 80,  4, 62, 16, 14,  9, 53, 56, 92 },
	{ 16, 39,  5, 42, 96, 35, 31, 47, 55, 58, 88, 24,  0, 17, 54, 24, 36, 29, 85, 57 },
	{ 86, 56,  0, 48, 35, 71, 89,  7,  5, 44, 44, 37, 44, 60, 21, 58, 51, 54, 17, 58 },
	{ 19, 80, 81, 68,  5, 94, 47, 69, 28, 73, 92, 13, 86, 52, 17, 77,  4, 89, 55, 40 },
	{ 04, 52,  8, 83, 97, 35, 99, 16,  7, 97, 57, 32, 16, 26, 26, 79, 33, 27, 98, 66 },
	{ 88, 36, 68, 87, 57, 62, 20, 72,  3, 46, 33, 67, 46, 55, 12, 32, 63, 93, 53, 69 },
	{ 04, 42, 16, 73, 38, 25, 39, 11, 24, 94, 72, 18,  8, 46, 29, 32, 40, 62, 76, 36 },
	{ 20, 69, 36, 41, 72, 30, 23, 88, 34, 62, 99, 69, 82, 67, 59, 85, 74,  4, 36, 16 },
	{ 20, 73, 35, 29, 78, 31, 90,  1, 74, 31, 49, 71, 48, 86, 81, 16, 23, 57,  5, 54 },
	{ 01, 70, 54, 71, 83, 51, 54, 69, 16, 92, 33, 48, 61, 43, 52,  1, 89, 19, 67, 48 },
};

BigInt CalcLargestGridProduct(BigInt sequenceLength, BigInt xStart, BigInt yStart, BigInt xDelta, BigInt yDelta, BigInt sliceLength) {
	assert(xDelta == 0 || xDelta == +1 || xDelta == -1);
	assert(yDelta == 0 || yDelta == +1);

	BigInt largestProduct = 0;
	BigInt currProduct = 1;
	BigInt numZeroes = 0;

	std::deque<BigInt> deque;
	BigInt xPos = xStart;
	BigInt yPos = yStart;
	for (BigInt i = 0; i < sliceLength; ++i) {
		// deincorporate oldest factor
		if ((BigInt)deque.size() >= sequenceLength) {
			const BigInt oldestFactor = deque.front();
			if (oldestFactor == 0) {
				--numZeroes;
			}
			else {
				currProduct /= oldestFactor;
			}
			deque.pop_front();
		}

		// incorporate new factor
		const BigInt newFactor = s_largestGridGrid[yPos][xPos];
		if (newFactor == 0) {
			++numZeroes;
		}
		else {
			currProduct *= newFactor;
		}
		deque.push_back(newFactor);
		//printf("new factor: %lld\n", newFactor);

		if (((BigInt)deque.size() >= sequenceLength) && (numZeroes <= 0) && (currProduct > largestProduct)) {
			largestProduct = currProduct;
			/*
			printf("%lld:  ", largestProduct);
			for (auto iter = deque.begin(); iter != deque.end(); ++iter) {
				printf("%lld ", *iter);
			}
			printf("\n");
			*/
		}

		xPos += xDelta;
		yPos += yDelta;
	}

	return largestProduct;
}

BigInt CalcLargestGridProduct(
		BigInt sequenceLength, 
		BigInt xStart, BigInt yStart, 
		BigInt xSliceDelta, BigInt ySliceDelta, 
		BigInt xDelta, BigInt yDelta,
		BigInt sliceLengthStart, BigInt sliceLengthDelta, 
		BigInt numSlices) {
	assert(xSliceDelta == 0 || xSliceDelta == +1 || xSliceDelta == -1);
	assert(ySliceDelta == 0 || ySliceDelta == +1);

	BigInt xPos = xStart;
	BigInt yPos = yStart;
	BigInt sliceLength = sliceLengthStart;

	BigInt largestProduct = 0;
	for (BigInt i = 0; i < numSlices; ++i) {
		const BigInt currProduct = CalcLargestGridProduct(sequenceLength, xPos, yPos, xDelta, yDelta, sliceLength);
		if (currProduct > largestProduct) {
			largestProduct = currProduct;
		}

		xPos += xSliceDelta;
		yPos += ySliceDelta;
		sliceLength += sliceLengthDelta;
	}

	return largestProduct;
}

BigInt CalcLargestGridProduct(BigInt sequenceLength) {
	BigInt largestProduct = 0;
	BigInt product;

#if 1
	// left-to-right slices
	product = CalcLargestGridProduct(sequenceLength, 0, 0, 0, +1, +1, 0, s_largestGridGridSize, 0, s_largestGridGridSize);
	if (product > largestProduct) {
		largestProduct = product;
	}
#endif

#if 1
	// top-to-bottom slices
	product = CalcLargestGridProduct(sequenceLength, 0, 0, +1, 0, 0, +1, s_largestGridGridSize, 0, s_largestGridGridSize);
	if (product > largestProduct) {
		largestProduct = product;
	}
#endif

#if 1
	// upper-left-to-lower-right diagonal slices
	product = CalcLargestGridProduct(sequenceLength, 0, 0, +1, 0, +1, +1, s_largestGridGridSize, -1, s_largestGridGridSize - sequenceLength + 1);
	if (product > largestProduct) {
		largestProduct = product;
	}
	product = CalcLargestGridProduct(sequenceLength, 0, 1, 0, +1, +1, +1, s_largestGridGridSize - 1, -1, s_largestGridGridSize - sequenceLength);
	if (product > largestProduct) {
		largestProduct = product;
	}
#endif

#if 1
	// upper-right-to-lower-left diagonal slices
	product = CalcLargestGridProduct(sequenceLength, sequenceLength - 1, 0, +1, 0, -1, +1, sequenceLength, +1, s_largestGridGridSize - sequenceLength + 1);
	if (product > largestProduct) {
		largestProduct = product;
	}
	product = CalcLargestGridProduct(sequenceLength, s_largestGridGridSize - 1, 1, 0, +1, -1, +1, s_largestGridGridSize - 1, -1, s_largestGridGridSize - sequenceLength);
	if (product > largestProduct) {
		largestProduct = product;
	}
#endif

	return largestProduct;
}

void RunLargestGridProduct(BigInt sequenceLength) {
	printf("Largest grid product of length %lld = %lld\n", sequenceLength, CalcLargestGridProduct(sequenceLength));
}



////////////////////////////
// Problem 12 - Highly divisible triangle number

BigInt CalcFirstHighlyDivTriNumber(BigInt moreThanNumDivisors, bool verbose) {
	BigInt triangleNumber = 1;
	BigInt nextNaturalNumber = 2;
	if (verbose) {
		printf("Triangle number #1 = %lld\n", triangleNumber);
	}

	for (;;) {
		triangleNumber = triangleNumber + nextNaturalNumber;
		if (verbose) {
			printf("Triangle number #%lld = %lld", nextNaturalNumber, triangleNumber);
		}
		nextNaturalNumber++;

		const Factorization& f = s_factorizationCache.Factorize(triangleNumber);
		BigInt numDivisors = f.CalcNumDivisors();
		if (numDivisors > moreThanNumDivisors) {
			printf("\nFound more than %lld divisors (%lld).  Prime factors:  ", moreThanNumDivisors, numDivisors);
			f.PrintFactors();
			printf("\n");
			break;
		}

		if (verbose) {
			printf(", numDivisors = %lld\n", numDivisors);
		}
	}

	return triangleNumber;
}

void RunHighlyDivisibleTriangleNumber(BigInt moreThanNumDivisors, bool verbose) {
	printf("The first triangle number to have more than %lld divisors = %lld\n", moreThanNumDivisors, CalcFirstHighlyDivTriNumber(moreThanNumDivisors, verbose));
}


////////////////////////////
// Problem 13 - Large sum

static HugeInt s_largeSumTable[] = {
	"37107287533902102798797998220837590246510135740250",
	"46376937677490009712648124896970078050417018260538",
	"74324986199524741059474233309513058123726617309629",
	"91942213363574161572522430563301811072406154908250",
	"23067588207539346171171980310421047513778063246676",
	"89261670696623633820136378418383684178734361726757",
	"28112879812849979408065481931592621691275889832738",
	"44274228917432520321923589422876796487670272189318",
	"47451445736001306439091167216856844588711603153276",
	"70386486105843025439939619828917593665686757934951",
	"62176457141856560629502157223196586755079324193331",
	"64906352462741904929101432445813822663347944758178",
	"92575867718337217661963751590579239728245598838407",
	"58203565325359399008402633568948830189458628227828",
	"80181199384826282014278194139940567587151170094390",
	"35398664372827112653829987240784473053190104293586",
	"86515506006295864861532075273371959191420517255829",
	"71693888707715466499115593487603532921714970056938",
	"54370070576826684624621495650076471787294438377604",
	"53282654108756828443191190634694037855217779295145",
	"36123272525000296071075082563815656710885258350721",
	"45876576172410976447339110607218265236877223636045",
	"17423706905851860660448207621209813287860733969412",
	"81142660418086830619328460811191061556940512689692",
	"51934325451728388641918047049293215058642563049483",
	"62467221648435076201727918039944693004732956340691",
	"15732444386908125794514089057706229429197107928209",
	"55037687525678773091862540744969844508330393682126",
	"18336384825330154686196124348767681297534375946515",
	"80386287592878490201521685554828717201219257766954",
	"78182833757993103614740356856449095527097864797581",
	"16726320100436897842553539920931837441497806860984",
	"48403098129077791799088218795327364475675590848030",
	"87086987551392711854517078544161852424320693150332",
	"59959406895756536782107074926966537676326235447210",
	"69793950679652694742597709739166693763042633987085",
	"41052684708299085211399427365734116182760315001271",
	"65378607361501080857009149939512557028198746004375",
	"35829035317434717326932123578154982629742552737307",
	"94953759765105305946966067683156574377167401875275",
	"88902802571733229619176668713819931811048770190271",
	"25267680276078003013678680992525463401061632866526",
	"36270218540497705585629946580636237993140746255962",
	"24074486908231174977792365466257246923322810917141",
	"91430288197103288597806669760892938638285025333403",
	"34413065578016127815921815005561868836468420090470",
	"23053081172816430487623791969842487255036638784583",
	"11487696932154902810424020138335124462181441773470",
	"63783299490636259666498587618221225225512486764533",
	"67720186971698544312419572409913959008952310058822",
	"95548255300263520781532296796249481641953868218774",
	"76085327132285723110424803456124867697064507995236",
	"37774242535411291684276865538926205024910326572967",
	"23701913275725675285653248258265463092207058596522",
	"29798860272258331913126375147341994889534765745501",
	"18495701454879288984856827726077713721403798879715",
	"38298203783031473527721580348144513491373226651381",
	"34829543829199918180278916522431027392251122869539",
	"40957953066405232632538044100059654939159879593635",
	"29746152185502371307642255121183693803580388584903",
	"41698116222072977186158236678424689157993532961922",
	"62467957194401269043877107275048102390895523597457",
	"23189706772547915061505504953922979530901129967519",
	"86188088225875314529584099251203829009407770775672",
	"11306739708304724483816533873502340845647058077308",
	"82959174767140363198008187129011875491310547126581",
	"97623331044818386269515456334926366572897563400500",
	"42846280183517070527831839425882145521227251250327",
	"55121603546981200581762165212827652751691296897789",
	"32238195734329339946437501907836945765883352399886",
	"75506164965184775180738168837861091527357929701337",
	"62177842752192623401942399639168044983993173312731",
	"32924185707147349566916674687634660915035914677504",
	"99518671430235219628894890102423325116913619626622",
	"73267460800591547471830798392868535206946944540724",
	"76841822524674417161514036427982273348055556214818",
	"97142617910342598647204516893989422179826088076852",
	"87783646182799346313767754307809363333018982642090",
	"10848802521674670883215120185883543223812876952786",
	"71329612474782464538636993009049310363619763878039",
	"62184073572399794223406235393808339651327408011116",
	"66627891981488087797941876876144230030984490851411",
	"60661826293682836764744779239180335110989069790714",
	"85786944089552990653640447425576083659976645795096",
	"66024396409905389607120198219976047599490197230297",
	"64913982680032973156037120041377903785566085089252",
	"16730939319872750275468906903707539413042652315011",
	"94809377245048795150954100921645863754710598436791",
	"78639167021187492431995700641917969777599028300699",
	"15368713711936614952811305876380278410754449733078",
	"40789923115535562561142322423255033685442488917353",
	"44889911501440648020369068063960672322193204149535",
	"41503128880339536053299340368006977710650566631954",
	"81234880673210146739058568557934581403627822703280",
	"82616570773948327592232845941706525094512325230608",
	"22918802058777319719839450180888072429661980811197",
	"77158542502016545090413245809786882778948721859617",
	"72107838435069186155435662884062257473692284509516",
	"20849603980134001723930671666823555245252804609722",
	"53503534226472524250874054075591789781264330331690",
};

void RunFirstDigitsOfLargeSum(BigInt numDigits) {
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
		if (argc >= 3) {
			TestFactorization(atoi(argv[2]));
		}
		else {
			TestFactorizationRange(20);
		}
		return 0;
	}
	else if (strcmp(problemArg, "primeFinder") == 0) {
		TestPrimeFinder(10);
		return 0;
	}
	else if (strcmp(problemArg, "HugeInt") == 0) {
		TestHugeInt();
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
	case 11:
		RunLargestGridProduct(1);
		RunLargestGridProduct(2);
		RunLargestGridProduct(4);
		break;
	case 12:
		RunHighlyDivisibleTriangleNumber(2, true);
		RunHighlyDivisibleTriangleNumber(5, true);
		RunHighlyDivisibleTriangleNumber(100, false);
		RunHighlyDivisibleTriangleNumber(500, true);
		break;
	case 13:
		RunFirstDigitsOfLargeSum(10);
		break;
	default:
		printf("'%s' is not a valid problem number!\n\n", problemArg);
		break;
	}

	return 0;
}

