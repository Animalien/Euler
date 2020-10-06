// Hi, this is my Project Euler stuff

#include <algorithm>
#include <assert.h>
#include <deque>
#include <functional>
#include <map>
#include <math.h>
#include <numeric>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <utility>
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

void PrintFactorization(BigInt num) {
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
		PrintFactorization(i);
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

	void Reset(bool backwards = true) {
		m_string.clear();
		m_backwards = backwards;
	}
	
	void SetTo(BigInt num) {
		m_string = std::to_string(num);
		m_backwards = false;
	}
	void AppendDigit(BigInt digit) {
		assert(digit >= 0);
		assert(digit < 10);
		m_string.push_back((char)(digit + '0'));
	}

	void Print() const {
		printf("%s", GetString());
	}
	const char* GetString() const {
		SetForwards();
		return m_string.c_str();
	}

	void PrintDigits(BigInt numDigits) const {
		SetForwards();

		const BigInt totalNumDigits = GetNumDigits();
		if (numDigits >= totalNumDigits) {
			printf("%s", m_string.c_str());
		}
		else {
			printf("%s", m_string.substr(0, numDigits).c_str());
		}
	}

	BigInt GetNumDigits() const {
		return m_string.length();
	}

	BigInt CalcSumDigits() const {
		BigInt sum = 0;
		ConstIterator iter(*this);
		while (!iter.IsAtEnd()) {
			sum += iter.GetDigit();
			iter.Increment();
		}

		return sum;
	}

	HugeInt operator+ (const HugeInt& other) const {
		const HugeInt* list[2] = { this, &other };
		return GetCalcedSum(list, 2);
	}

	void SetToSum(const HugeInt& left, const HugeInt& right) {
		const HugeInt* list[2] = { &left, &right };
		CalcSum(list, 2);
	}

	static HugeInt GetCalcedSum(const HugeInt* list, BigInt numItems) {
		return GetCalcedSum(ListIterator(list, numItems));
	}
	static HugeInt GetCalcedSum(const HugeInt* const* list, BigInt numItems) {
		return GetCalcedSum(ListIterator(list, numItems));
	}
	void CalcSum(const HugeInt* list, BigInt numItems) {
		CalcSum(ListIterator(list, numItems));
	}
	void CalcSum(const HugeInt* const* list, BigInt numItems) {
		CalcSum(ListIterator(list, numItems));
	}

	void Swap(HugeInt& other) {
		m_string.swap(other.m_string);
		std::swap(m_backwards, other.m_backwards);
	}

	void SetToProduct(const HugeInt& leftSide, BigInt rightSide) {
		assert(rightSide > 0);		// zero is pointless

		Reset();

		BigInt carryOver = 0;
		for (ConstIterator iter(leftSide); !iter.IsAtEnd(); iter.Increment()) {
			const BigInt digit = iter.GetDigit();
			const BigInt num = digit * rightSide + carryOver;

			const lldiv_t divRem = lldiv(num, 10);
			const char outputDigit = (char)(divRem.rem + '0');
			m_string.push_back(outputDigit);

			carryOver = divRem.quot;
		}

		while (carryOver > 0) {
			const lldiv_t divRem = lldiv(carryOver, 10);
			const char outputDigit = (char)(divRem.rem + '0');
			m_string.push_back(outputDigit);

			carryOver = divRem.quot;
		}
	}

	void SetToDivision(const HugeInt& numer, BigInt denom, BigInt* remainder = nullptr) {
		assert(denom > 0);		// zero is pointless

		//printf("%s / %lld:\n", numer.GetString(), denom);

		Reset(false);

		ConstIterator iter(numer, false);

		BigInt numerTemp = 0;
		while ((numerTemp < denom) && !iter.IsAtEnd()) {
			numerTemp *= 10;
			numerTemp += iter.GetDigit();
			iter.Increment();
		}

		//printf("  numerTemp = %lld\n", numerTemp);

		if ((numerTemp < denom) && iter.IsAtEnd()) {
			SetTo(0);
			if (remainder != nullptr) {
				*remainder = numerTemp;
			}
			return;
		}

		for (;;) {
			const lldiv_t div = lldiv(numerTemp, denom);
			assert(div.quot >= 0);
			assert(div.quot < 10);

			m_string.push_back('0' + (char)div.quot);

			if (iter.IsAtEnd()) {
				if (remainder != nullptr) {
					*remainder = div.rem;
				}
				return;
			}

			numerTemp = div.rem * 10 + iter.GetDigit();
			iter.Increment();
		}
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
		ConstIterator(const HugeInt& parent, bool lowToHigh = true) : m_string(parent.m_string) {
			if (parent.m_backwards == lowToHigh) {
				// the digits are already in the direction we want them, so just interate from start to finish
				m_index = 0;
				m_endIndex = m_string.length();
				m_increment = +1;
			}
			else {
				// the digits are in the opposite direction we want to iterate them in, so we must iterate backwards from the end
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

	static HugeInt GetCalcedSum(ListIterator& listIter) {
		HugeInt sum;
		sum.CalcSum(listIter);
		return sum;
	}

	void CalcSum(ListIterator & listIter) {
		Reset();

		std::vector<ConstIterator> iterList;
		iterList.reserve(listIter.GetNum());

		// populate the list of individual iterators
		for (; !listIter.IsAtEnd(); listIter.Increment()) {
			iterList.push_back(ConstIterator(*listIter));
		}

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
			m_string += newDigit;

			carryOver = divRem.quot;
		}
	}

	mutable std::string		m_string;
	mutable bool			m_backwards;
};


void TestHugeInt() {
	HugeInt n1 = 135;
	HugeInt n2 = "2005";
	HugeInt n3 = 52;

	printf("TestHugeInt:  n1 = %s, n2 = %s, n3 = %s, n1 + n2 = %s, n1 + n2 + n3 = %s\n", n1.GetString(), n2.GetString(), n3.GetString(), (n1 + n2).GetString(), (n1 + n2 + n3).GetString());

	HugeInt product1, product2, product3;
	product1.SetToProduct(n1, 2);
	product2.SetToProduct(n2, 2);
	product3.SetToProduct(n3, 2);
	printf("TestHugeInt product:  n1 * 2 = %s, n2 * 2 = %s, n3 * 2 = %s\n", product1.GetString(), product2.GetString(), product3.GetString());

	HugeInt numer1 = 1000;
	BigInt denom1 = 200;
	HugeInt numer2 = 3;
	BigInt denom2 = 5;
	HugeInt numer3 = 146;
	BigInt denom3 = 12;
	BigInt remainder1, remainder2, remainder3;
	HugeInt quot1, quot2, quot3;

	quot1.SetToDivision(numer1, denom1, &remainder1);
	quot2.SetToDivision(numer2, denom2, &remainder2);
	quot3.SetToDivision(numer3, denom3, &remainder3);

	printf("TestHugeInt divison:  %s / %lld = (%s, %lld), %s / %lld = (%s, %lld), %s / %lld (%s, %lld)\n",
		numer1.GetString(), denom1, quot1.GetString(), remainder1,
		numer2.GetString(), denom2, quot2.GetString(), remainder2,
		numer3.GetString(), denom3, quot3.GetString(), remainder3);
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

static const HugeInt s_largeSumTable[] = {
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
	const HugeInt sum = HugeInt::GetCalcedSum(s_largeSumTable, sizeof(s_largeSumTable) / sizeof(s_largeSumTable[0]));
	printf("Sum of huge numbers in table = %s (total num digits = %lld)\n", sum.GetString(), sum.GetNumDigits());
	printf("First %lld digits = ", numDigits);
	sum.PrintDigits(numDigits);
	printf("\n");
}


////////////////////////////
// Problem 14 - Longest Collatz sequence

BigInt CalcLengthCollatzSequence(BigInt num) {
	//printf("%lld", num);
	BigInt len = 1;

	while (num > 1) {
		if (num & 1) {
			// odd
			num = 3 * num + 1;
		}
		else {
			// even
			num = num >> 1;
		}

		//printf(" -> %lld", num);
		++len;
	}

	//printf(" (len = %lld)\n", len);

	return len;
}

BigInt FindLongestCollatzSequence(BigInt max) {
	BigInt numOfLongest = -1;
	BigInt longestSequence = 0;
	for (BigInt num = 1; num < max; ++num) {
		const BigInt len = CalcLengthCollatzSequence(num);
		if (len > longestSequence) {
			numOfLongest = num;
			longestSequence = len;
		}
		else if (len == longestSequence) {
			printf("Found an equal!  (%lld seq len %lld, vs %lld seq len %lld)\n", numOfLongest, longestSequence, num, len);
		}
	}

	return numOfLongest;
}

void RunLongestCollatzSequence(BigInt max) {
	printf("Longest Collatz sequence under %lld results from starting with the number %lld\n", max, FindLongestCollatzSequence(max));
}


////////////////////////////
// Problem 15 - Lattice paths

// The way to solve this is to think about the diagonal of points
// across the square grid, from lower left to upper right.
// If the grid is N units along each side, then this diagonal
// will be N+1 points in length.
// The total number of paths through the grid is equal to 
// the sum of the numbers of paths through each of the diagonal
// points.
// For a given single diagonal point, the number of paths through it
// is equal to the number of paths that could arrive at the point,
// times the number of paths that could lead away from the point.
// The path grid is symmetrical about the diagonal, so for each
// diagonal point you can simply consider how many paths go from 
// that point to the destination corner, and multiply that number
// times itself.
// At this point you can break down the path calculation as a
// recursive function.
// Along a diagonal string of points, the end points only each have
// a single path to get them home.  The middle points have a number
// of paths equal to the number of paths along its "left route" plus
// the number of paths along its "right route".

BigInt CalcNumLatticePathsFromPoint(BigInt pointIndex, BigInt numPoints) {
	if ((pointIndex <= 0) || (pointIndex >= (numPoints - 1))) {
		// this is an edge point, and it only has one possible path back home,
		// as it gets "corralled" by the converging edges of the grid.
		return 1;
	}

	// otherwise this is a middle point, and the num paths is equal to
	// the num paths on the "left" side plus the num paths on the "right" side.
	// either side is going to take us into the "next diagonal", which has one
	// less number of points than this one.

	const BigInt numLeftSidePaths = CalcNumLatticePathsFromPoint(pointIndex - 1, numPoints - 1);
	const BigInt numRightSidePaths = CalcNumLatticePathsFromPoint(pointIndex, numPoints - 1);

	return numLeftSidePaths + numRightSidePaths;
}

BigInt CalcNumLatticePaths(BigInt gridSize) {
	const BigInt diagonalLength = gridSize + 1;

	BigInt numPaths = 0;
	for (BigInt i = 0; i < diagonalLength; ++i) {
		const BigInt numPathsFromPoint = CalcNumLatticePathsFromPoint(i, diagonalLength);
		const BigInt numPathsThroughPoint = numPathsFromPoint * numPathsFromPoint;

		numPaths += numPathsThroughPoint;
	}

	return numPaths;
}

void RunLatticePaths(BigInt gridSize) {
	printf("Num paths through a grid of size %lld = %lld\n", gridSize, CalcNumLatticePaths(gridSize));
}


////////////////////////////
// Problem 16 - Power digit sum

HugeInt CalcPower2Num(BigInt power) {
	HugeInt result = 1;
	HugeInt newProduct;

	for (BigInt i = 0; i < power; ++i) {
		newProduct.SetToProduct(result, 2);
		result.Swap(newProduct);
	}

	return result;
}

BigInt CalcPowerDigitSum(BigInt power) {
	HugeInt num = CalcPower2Num(power);
	printf("2 ^ %lld = %s\n", power, num.GetString());
	return num.CalcSumDigits();
}

void RunPowerDigitSum(BigInt power) {
	printf("Power digit sum of 2^%lld = %lld\n", power, CalcPowerDigitSum(power));
}


////////////////////////////
// Problem 17 - Number letter counts

static BigInt s_numLettersTable_Under20[] = {
	4,		// zero
	3,		// one
	3,		// two
	5,		// three
	4,		// four
	4,		// five
	3,		// six
	5,		// seven
	5,		// eight
	4,		// nine
	3,		// ten
	6,		// eleven
	6,		// twelve
	8,		// thirteen
	8,		// fourteen
	7,		// fifteen
	7,		// sixteen
	9,		// seventeen
	8,		// eighteen
	8,		// nineteen
};

static BigInt s_numLettersTable_Tens[] = {
	0,		// N/A
	1,		// N/A
	6,		// twenty
	6,		// thirty
	5,		// forty
	5,		// fifty
	5,		// sixty
	7,		// seventy
	6,		// eighty
	6,		// ninety
};

BigInt CalcNumberLetters(BigInt num, bool verbose) {
	assert(num <= 1000);

	const BigInt origNum = num;
	BigInt numLetters = 0;

	bool hadThousandsOrHundreds = false;

	if (num >= 1000) {
		numLetters += 3 + 8;  // one thousand

		num = num - 1000;
		hadThousandsOrHundreds = true;

		if (verbose) {
			printf("  one thousand (11)");
		}
	}

	lldiv_t divRem = lldiv(num, 100);
	const BigInt numHundreds = divRem.quot;
	if (numHundreds > 0) {
		assert(numHundreds < 10);

		numLetters += s_numLettersTable_Under20[numHundreds];
		numLetters += 7;	// hundred

		num = divRem.rem;
		hadThousandsOrHundreds = true;

		if (verbose) {
			printf("  %lld hundred (%lld)", numHundreds, s_numLettersTable_Under20[numHundreds] + 7);
		}
	}

	if (num > 0) {
		if (hadThousandsOrHundreds) {
			numLetters += 3;	// and

			if (verbose) {
				printf("  and (3)");
			}
		}

		if (num >= 20) {
			divRem = lldiv(num, 10);

			const BigInt tensPlace = divRem.quot;
			assert(tensPlace < 10);
			numLetters += s_numLettersTable_Tens[tensPlace];

			const BigInt under10 = divRem.rem;
			assert(under10 < 10);
			if (under10 > 0) {
				numLetters += s_numLettersTable_Under20[under10];
			}

			if (verbose) {
				printf("  %lldx10 + %lld (%lld)", tensPlace, under10, s_numLettersTable_Tens[tensPlace] + ((under10 > 0)? s_numLettersTable_Under20[under10] : 0));
			}
		}
		else {
			numLetters += s_numLettersTable_Under20[num];

			if (verbose) {
				printf("  %lld (%lld)", num, s_numLettersTable_Under20[num]);
			}
		}
	}

	if (verbose) {
		printf("\n");
	}

	printf("Number of letters in %lld = %lld\n", origNum, numLetters);

	return numLetters;
}

BigInt CalcNumberLetterCount(BigInt max) {
	BigInt count = 0;
	for (BigInt i = 1; i <= max; ++i) {
		count += CalcNumberLetters(i, true);
	}
	return count;
}

void RunNumberLetterCounts(BigInt max) {
	printf("The total number of letters in all numbers from 1 to %lld = %lld\n", max, CalcNumberLetterCount(max));
}


////////////////////////////
// Problem 18 - Maximum path sum 1

static BigInt s_maxPathSum1SmallTri[] = {
	      3,
	    7,  4,
 	  2,  4,  6,
	8,  5,  9,  3, 
};

static BigInt s_maxPathSum1BigTri[] = {
	                            75,
	                          95, 64,
	                        17, 47, 82,
	                      18, 35, 87, 10,
	                    20,  4, 82, 47, 65,
	                  19,  1, 23, 75,  3, 34,
	                88,  2, 77, 73,  7, 63, 67,
	              99, 65,  4, 28,  6, 16, 70, 92,
	            41, 41, 26, 56, 83, 40, 80, 70, 33,
	          41, 48, 72, 33, 47, 32, 37, 16, 94, 29,
	        53, 71, 44, 65, 25, 43, 91, 52, 97, 51, 14,
	      70, 11, 33, 28, 77, 73, 17, 78, 39, 68, 17, 57,
	    91, 71, 52, 38, 17, 14, 91, 43, 58, 50, 27, 29, 48,
	  63, 66,  4, 68, 89, 53, 67, 30, 73, 16, 69, 87, 40, 31,
	04, 62, 98, 27, 23,  9, 70, 98, 73, 93, 38, 53, 60,  4, 23, 
};

struct MaxTriPathNode {
	BigInt total;
	std::vector<BigInt> path;
};

void IterateMaxPath(BigInt nextRowSize, const std::vector<MaxTriPathNode>& prevRow, std::vector<MaxTriPathNode>& nextRow, const BigInt* nextRowSource) {
	nextRow.resize(nextRowSize);

	for (BigInt i = 0; i < nextRowSize; ++i) {
		const MaxTriPathNode* chosenPrevNode = nullptr;
		if (!prevRow.empty()) {
			chosenPrevNode = &prevRow[i];

			const MaxTriPathNode& rightNode = prevRow[i+1];
			if (rightNode.total > chosenPrevNode->total) {
				chosenPrevNode = &rightNode;
			}
		}

		const BigInt nextRowSourceValue = nextRowSource[i];
		MaxTriPathNode& nextNode = nextRow[i];
		if (chosenPrevNode) {
			nextNode.total = chosenPrevNode->total + nextRowSourceValue;
			nextNode.path = chosenPrevNode->path;
		}
		else {
			nextNode.total = nextRowSourceValue;
			nextNode.path.resize(0);
		}
		nextNode.path.push_back(nextRowSourceValue);
	}
}

BigInt CalcMaxPathFromTri(const BigInt* valueList, BigInt triHeight) {
	std::vector<MaxTriPathNode> prevRow;
	prevRow.reserve(triHeight);
	std::vector<MaxTriPathNode> nextRow;
	nextRow.reserve(triHeight);

	// start from the bottom row and move upwards in the triangle
	valueList += (triHeight * (triHeight + 1)) / 2;

	for (BigInt rowSize = triHeight; rowSize >= 1; --rowSize) {
		prevRow.swap(nextRow);
		valueList -= rowSize;

		IterateMaxPath(rowSize, prevRow, nextRow, valueList);
	}

	assert(nextRow.size() == 1);

	const MaxTriPathNode& theWinner = nextRow[0];

	printf("Winning path:  ");
	for (auto iter = theWinner.path.rbegin(); iter != theWinner.path.rend(); ++iter) {
		printf("%lld ", *iter);
	}
	printf("\n");

	return theWinner.total;
}

void RunMaxPathSum1() {
	printf("Max path from small tri = %lld\n", CalcMaxPathFromTri(s_maxPathSum1SmallTri, 4));
	printf("Max path from big tri = %lld\n", CalcMaxPathFromTri(s_maxPathSum1BigTri, 15));
}


////////////////////////////
// Problem 19 - Counting Sundays

bool IsLeapYear(BigInt year) {
	const bool divisibleBy4 = (year & ~3) == 0;
	const bool divisibleBy100 = (year % 100) == 0;
	const bool divisibleBy400 = (year % 400) == 0;

	return (divisibleBy4 && (!divisibleBy100 || divisibleBy400));
}

static const BigInt NUM_DAYS_IN_WEEK = 7;
enum DaysOfTheWeek {
	SUNDAY = 0,
	MONDAY,
	TUESDAY,
	WEDNESDAY,
	THURSDAY,
	FRIDAY,
	SATURDAY,
};

static const BigInt NUM_DAYS_IN_YEAR = 365;
static const BigInt NUM_DAYS_IN_LEAP_YEAR = 366;
static const BigInt NUM_FEBRUARY_DAYS = 28;
static const BigInt NUM_FEBRUARY_DAYS_IN_LEAP_YEAR = 29;
static const BigInt NUM_DAYS_IN_SHORT_MONTH = 30;
static const BigInt NUM_DAYS_IN_LONG_MONTH = 31;

enum Months {
	JANUARY,
	FEBRUARY,
	MARCH,
	APRIL,
	MAY,
	JUNE,
	JULY,
	AUGUST,
	SEPTEMBER,
	OCTOBER,
	NOVEMBER,
	DECEMBER,
};

BigInt CountSundays() {
	BigInt numSundays = 0;

	// start with Jan 1, 1900, which was a Monday
	BigInt day = MONDAY;
	
	// skip the year 1900 because it is not included in our specified range
	const BigInt numDaysIn1900 = IsLeapYear(1900) ? NUM_DAYS_IN_LEAP_YEAR : NUM_DAYS_IN_YEAR;
	day = (day + numDaysIn1900) % NUM_DAYS_IN_WEEK;

	// now loop through all the months of all the years, tallying up Sundays
	for (BigInt year = 1901; year <= 2000; ++year) {
		const bool isLeapYear = IsLeapYear(year);
		for (BigInt month = JANUARY; month <= DECEMBER; ++month) {
			// tally another sunday if the first of the month is one
			if (day == SUNDAY) {
				++numSundays;
			}

			// step past this month
			switch (month) {
			case FEBRUARY:
				day += isLeapYear ? NUM_FEBRUARY_DAYS_IN_LEAP_YEAR : NUM_FEBRUARY_DAYS;
				break;
			case SEPTEMBER:
			case APRIL:
			case JUNE:
			case NOVEMBER:
				day += NUM_DAYS_IN_SHORT_MONTH;
				break;
			default:
				day += NUM_DAYS_IN_LONG_MONTH;
				break;
			}

			day %= NUM_DAYS_IN_WEEK;
		}
	}

	return numSundays;
}

void RunCountingSundays() {
	printf("There were %lld first-of-the-month Sundays in the 20th Century.\n", CountSundays());
}


////////////////////////////
// Problem 20 - Factorial digit sum

BigInt CalcFactorialDigitSum(BigInt num) {
	HugeInt f = 1;
	HugeInt other;
	while (num > 1) {
		other.Swap(f);
		f.SetToProduct(other, num);
		--num;
	}

	return f.CalcSumDigits();
}

void RunFactorialDigitSum(BigInt num) {
	printf("The sum of the digits of %lld! = %lld\n", num, CalcFactorialDigitSum(num));
}


////////////////////////////
// Problem 21 - Amicable numbers

BigInt CalcSumProperDivisors(BigInt num, bool verbose = false) {
	if (verbose) {
		printf("Proper divisors of %lld:  1 ", num);
	}

	BigInt sum = 1;

	const BigInt maxDiv = num / 2;
	for (BigInt i = 2; i <= maxDiv; ++i) {
		if (num % i == 0) {
			if (verbose) {
				printf("%lld ", i);
			}
			sum += i;
		}
	}
	if (verbose) {
		printf("\n");
	}

	return sum;
}

BigInt CalcSumAmicableNumbers(BigInt max) {
	std::vector<bool> amicableFlags;
	amicableFlags.resize(max, false);

	BigInt sum = 0;
	for (BigInt i = 1; i < max; ++i) {
		if (amicableFlags[i]) {
			continue;
		}

		const BigInt other = CalcSumProperDivisors(i);
		if (other == i) {
			continue;
		}

		const BigInt sumProperDivOther = CalcSumProperDivisors(other);
		if (sumProperDivOther == i) {
			assert(other > i);	// otherwise we should have already dealt with the smaller one and its partner, and already done an early out on its true amicable flag

			// add both this and the other to the sum
			sum += i;
			sum += other;

			// no need to flag this one since we are already moving past it

			// flag the other one
			amicableFlags[other] = true;
		}
	}

	return sum;
}

void TestCalcSumProperDivisors(BigInt num) {
	printf("The sum of the proper divisors of %lld = %lld\n", num, CalcSumProperDivisors(num, true));
}

void TestSumAllAmicableNumbers(BigInt max) {
	printf("The sum of all amicable numbers under %lld = %lld\n", max, CalcSumAmicableNumbers(max));
}

void RunAmicableNumbers() {
	TestCalcSumProperDivisors(220);
	TestCalcSumProperDivisors(284);

	TestSumAllAmicableNumbers(10);
	TestSumAllAmicableNumbers(100);
	TestSumAllAmicableNumbers(1000);
	TestSumAllAmicableNumbers(10000);
}


////////////////////////////
// Problem 22 - Names scores

void LoadNames(std::vector<std::string>& list) {
	list.clear();

	FILE* file = fopen("p022_names.txt", "rt");
	assert(file);

	std::string currString;
	int c = 0;
	while ((c = fgetc(file)) != EOF) {
		if (c == (int)',') {
			assert(currString.empty());
		}
		else if (c == (int)'\"') {
			if (!currString.empty()) {
				//printf("%s\n", currString.c_str());
				list.push_back(std::string());
				currString.swap(list.back());
				assert(currString.empty());
			}
		}
		else {
			currString += (char)c;
		}
	}
}

void SortNames(std::vector<std::string>& list) {
	std::sort(list.begin(), list.end());
	/*
	for (BigInt i = 0; i < (BigInt)list.size(); ++i) {
		printf("%s\n", list[i].c_str());
	}
	*/
}

BigInt CalcNameValue(const std::string& name) {
	BigInt value = 0;
	for (BigInt i = 0; i < (BigInt)name.length(); ++i) {
		value += ((BigInt)name[i] - (BigInt)'A' + 1);
	}
	return value;
}

void CalcNameValues(const std::vector<std::string>& nameList, std::vector<BigInt>& valueList) {
	const BigInt nameListSize = (int)nameList.size();
	valueList.clear();
	for (BigInt i = 0; i < nameListSize; ++i) {
		const BigInt nameValue = CalcNameValue(nameList[i]);
		valueList.push_back(nameValue);
		//printf("Value of %s = %lld\n", nameList[i].c_str(), nameValue);
	}
}

void TestSingleNameScore(const std::vector<std::string>& nameList, const std::vector<BigInt>& valueList, const char* name) {
	auto iter = std::find(nameList.begin(), nameList.end(), name);
	assert(iter != nameList.end());

	const BigInt nameIndex = (BigInt)(iter - nameList.begin());
	const BigInt nameNumber = nameIndex + 1;
	printf("Score of %s = %lld x %lld = %lld\n", iter->c_str(), nameNumber, valueList[nameIndex], nameNumber * valueList[nameIndex]);
}

BigInt CalcSumNameScores(const std::vector<std::string>& nameList, const std::vector<BigInt>& valueList) {
	BigInt sum = 0;

	for (BigInt i = 0; i < (BigInt)valueList.size(); ++i) {
		const BigInt score = (i + 1) * valueList[i];
		sum += score;
		//printf("Name score of %s = %lld\n", nameList[i].c_str(), score);
	}

	return sum;
}

void RunNamesScores() {
	std::vector<std::string> nameList;
	LoadNames(nameList);
	SortNames(nameList);

	std::vector<BigInt> valueList;
	CalcNameValues(nameList, valueList);

	TestSingleNameScore(nameList, valueList, "COLIN");

	printf("The sum of all name scores = %lld\n", CalcSumNameScores(nameList, valueList));
}



////////////////////////////
// Problem 23 - Non-abundant sums

bool IsAbundant(BigInt num) {
	if (num <= 0) {
		return false;
	}

	const BigInt sumProperDivisors = CalcSumProperDivisors(num, false);
	const bool isAbundant = (sumProperDivisors > num);

	/*
	printf("%lld sum of proper divisors = %lld, ", num, sumProperDivisors);
	if (isAbundant) {
		printf(" abundant\n");
	}
	else if (sumProperDivisors == num) {
		printf(" perfect\n");
	}
	else {
		printf(" deficient\n");
	}
	*/

	return isAbundant;
}

void DetermineAbundantness(std::vector<bool>& flagList, BigInt numNums) {
	flagList.resize(0);
	flagList.reserve(numNums);

	for (BigInt num = 0; num < numNums; ++num) {
		flagList.push_back(IsAbundant(num));
	}
}

bool CanBeWrittenAsSumOfAbundantNumbers(BigInt num, const std::vector<bool>& abundantFlagList) {
	assert((BigInt)abundantFlagList.size() > num);

	bool canBe = false;

	const BigInt halfNum = num / 2;
	for (BigInt i = 1; i <= halfNum; ++i) {
		const BigInt other = num - i;
		if (abundantFlagList[i] && abundantFlagList[other]) {
			canBe = true;
			//printf("%lld can be written as the sum of abundant numbers %lld and %lld\n", num, i, other);
			break;
		}
	}

	/*
	if (!canBe) {
		printf("%lld CANNOT be written as the sum of two abundant numbers\n", num);
	}
	*/

	return canBe;
}

BigInt CalcSumCannotBeWrittenAsSumOfTwoAbundantNumbers(BigInt max) {
	BigInt sum = 0;

	std::vector<bool> abundantFlagList;
	DetermineAbundantness(abundantFlagList, max + 1);

	for (BigInt i = 1; i <= max; ++i) {
		const bool canBeWritten = CanBeWrittenAsSumOfAbundantNumbers(i, abundantFlagList);
		if (!canBeWritten) {
			sum += i;
			//printf("Sum %lld + %lld = %lld\n", sum - i, i, sum);
		}
	}

	return sum;
}

void RunNonAbundantSums(BigInt max) {
	printf("The sum of all the positive integers from 1 to %lld inclusive which cannot be written as the sum of two abundant numbers = %lld\n", 
		max, CalcSumCannotBeWrittenAsSumOfTwoAbundantNumbers(max));
}



////////////////////////////
// Problem 24 - Lexicographic permutations

bool RecurseLexicoPermut(char* begin, char* middle, char* end, std::function<bool(const char*)> func) {
	const BigInt numChars = (BigInt)(end - middle);
	if (numChars <= 1) {
		return func(begin);
	}

	for (BigInt i = 0; i < numChars; ++i) {
		std::swap(middle[0], middle[i]);
		if (!RecurseLexicoPermut(begin, middle + 1, end, func)) {
			return false;
		}
	}

	std::rotate(middle, middle + 1, end);

	return true;
}

void RunLexicographicPermutations(const std::string& origSt, BigInt desiredPermut) {
	std::string st = origSt;

	char* begin = &st[0];
	char* end = begin + st.length();
	BigInt index = 0;
	const BigInt desiredPermutIndex = desiredPermut - 1;
	RecurseLexicoPermut(
		begin, begin, end,
		[&](const char* st) {
			//printf("permut[%lld] = %s\n", index, st);
			if (index >= desiredPermutIndex - 1 && index <= desiredPermutIndex + 1) {
				printf("Permutation # %lld = %s\n", index + 1, st);
				if (index >= desiredPermutIndex + 1) {
					return false;
				}
			}
			++index;
			return true;
		});

	printf("Back to %s\n", st.c_str());
}


////////////////////////////
// Problem 25 - 1000 digit Fibonacci

void RunNDigitFibonacci(BigInt numDigits) {
	assert(numDigits > 0);
	if (numDigits == 1) {
		printf("The first Fibonacci number to have 1 digit is:  Fib(1) = 1\n");
		return;
	}

	printf("Fib(1) = 1\nFib(2) = 1\n");

	HugeInt num;
	HugeInt prev = 1;
	HugeInt prevPrev = 1;
	BigInt fibNum = 3;

	for (;;) {
		num = prev + prevPrev;
		printf("Fib(%lld) = %s\n", fibNum, num.GetString());

		if (num.GetNumDigits() >= numDigits) {
			break;
		}

		prevPrev.Swap(prev);
		prev.Swap(num);
		++fibNum;
	};

	printf("The first Fibonacci number to have %lld digits is:  Fib(%lld) = %s\n", numDigits, fibNum, num.GetString());
}


////////////////////////////
// Problem 26 - Reciprocal Cycles

BigInt CalcNumFactors(BigInt numer, BigInt denom, BigInt* remainder = nullptr) {
	BigInt numFactors = 0;
	for (;;) {
		const lldiv_t div = lldiv(numer, denom);
		if (div.rem != 0) {
			break;
		}

		++numFactors;
		numer = div.quot;
	}

	if (remainder != nullptr) {
		*remainder = numer;
	}

	return numFactors;
}

BigInt CalcReciprocalCycleLength(BigInt denom) {
	printf("denom = %lld:  ", denom);

	const BigInt numFactors2 = CalcNumFactors(denom, 2, &denom);
	const BigInt numFactors5 = CalcNumFactors(denom, 5, &denom);
	printf("nf2(%lld), nf5(%lld), ", numFactors2, numFactors5);

	const BigInt numTens = std::max(numFactors2, numFactors5);

	const BigInt tens = (BigInt)pow(10.0, numTens);
	printf("tens = %lld (10^%lld)", tens, numTens);

	HugeInt nines;
	if (denom > 1) {
		for (;;) {
			nines.AppendDigit(9);

			HugeInt div;
			BigInt remainder;
			div.SetToDivision(nines, denom, &remainder);

			if (remainder == 0) {
				break;
			}
		}
	}

	printf(", num nines = %lld\n", nines.GetNumDigits());

	return nines.GetNumDigits();
}

void RunReciprocalCycles(BigInt maxDenom) {
	BigInt longestCycleLength = 0;
	BigInt longestCycleDenom = 0;

	for (BigInt denom = 2; denom < maxDenom; ++denom) {
		const BigInt cycLen = CalcReciprocalCycleLength(denom);
		if (cycLen > longestCycleLength) {
			longestCycleLength = cycLen;
			longestCycleDenom = denom;
		}
	}

	printf("The longest decimal cycle for 1 / d where d < %lld is:  d = %lld, cycleLength = %lld\n", maxDenom, longestCycleDenom, longestCycleLength);
}



////////////////////////////
////////////////////////////
// Main

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
			PrintFactorization(atoi(argv[2]));
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
	case 14:
		RunLongestCollatzSequence(5);
		RunLongestCollatzSequence(20);
		RunLongestCollatzSequence(100);
		RunLongestCollatzSequence(10000);
		RunLongestCollatzSequence(100000);
		RunLongestCollatzSequence(1000000);
		break;
	case 15:
		RunLatticePaths(2);
		RunLatticePaths(4);
		RunLatticePaths(10);
		RunLatticePaths(20);
		break;
	case 16:
		RunPowerDigitSum(3);
		RunPowerDigitSum(15);
		RunPowerDigitSum(100);
		RunPowerDigitSum(1000);
		break;
	case 17:
		//RunNumberLetterCounts(5);
		//RunNumberLetterCounts(10);
		//RunNumberLetterCounts(20);
		//RunNumberLetterCounts(100);
		RunNumberLetterCounts(1000);
		break;
	case 18:
		RunMaxPathSum1();
		break;
	case 19:
		RunCountingSundays();
		break;
	case 20:
		RunFactorialDigitSum(10);
		RunFactorialDigitSum(100);
		break;
	case 21:
		RunAmicableNumbers();
		break;
	case 22:
		RunNamesScores();
		break;
	case 23:
		//RunNonAbundantSums(20);
		//RunNonAbundantSums(100);
		//RunNonAbundantSums(1000);
		RunNonAbundantSums(28123);
		break;
	case 24:
		//RunLexicographicPermutations("0123", 3);
		//RunLexicographicPermutations("012345", 500);
		RunLexicographicPermutations("0123456789", 1000000);
		break;
	case 25:
		//RunNDigitFibonacci(3);
		//RunNDigitFibonacci(10);
		//RunNDigitFibonacci(100);
		RunNDigitFibonacci(1000);
		break;
	case 26:
		//RunReciprocalCycles(10);
		//RunReciprocalCycles(20);
		//RunReciprocalCycles(100);
		RunReciprocalCycles(1000);
		break;
	default:
		printf("'%s' is not a valid problem number!\n\n", problemArg);
		break;
	}

	return 0;
}

