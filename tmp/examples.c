#include <stdlib.h>
#include <stdint.h>
 

int sum_1(int *array, int length)
__CPROVER_requires(length <= 100)
__CPROVER_requires(__CPROVER_forall { int i; (0 <= i && i < length) ==> (array[i]==1)})
__CPROVER_ensures(__CPROVER_return_value == length)
{
	int res = 0;
	for (int i = 0; i < length; i++)
		__CPROVER_loop_invariant(0<=i && i<=length)
		__CPROVER_decreases(length - i)
	{
		res += array[i];
	}
	return res;
}
 
// the proof harness
int main()
{
	int a[2]={1,1};
	int res = sum_1(a,2);
	__CPROVER_assert(res == 2, "sum sumthin");
}