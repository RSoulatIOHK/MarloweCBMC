int constr_non_det_int(int min, int max){
	int res_ret;
	__CPROVER_assume(min <= res_ret && res_ret <= max);
	return res_ret;
}