#include <stdio.h>
#include <assert.h>

int main() {
    int reach = 1;
    __CPROVER_assert(reach == 0, "Do I reach here? Should be fail");
    return 0;
}