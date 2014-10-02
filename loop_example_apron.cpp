#include <stdio.h>

#include "ap_global0.h"
#include "ap_global1.h"

#include "box.h"

ap_manager_t *man;
ap_environment_t *env;

static void init_abstract_array(ap_abstract1_t *R, int size)
{
    int i;

    for (i = 0; i < size; i++)
        R[i] = ap_abstract1_bottom(man, env);        
}

/* dest := c */
static ap_abstract1_t assign_const(ap_abstract1_t abs, char *dest, int c)
{
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_linexpr1_set_list(&expr,
		       AP_CST_S_INT, c,
		       AP_END);
    fprintf(stdout, "Assignement (side-effect) in abstract value of x by "
           "expression:\n");
    ap_linexpr1_fprint(stdout, &expr);    

    abs = ap_abstract1_assign_linexpr(man, true, &abs, dest, &expr, NULL);
    fprintf(stdout, "\n");
    ap_abstract1_fprint(stdout, man, &abs);
    ap_linexpr1_clear(&expr);    

    return abs;
}

/* Creation of constraint x < 1000 (-x + 1000 > 0) */
static ap_abstract1_t create_constraint1()
{
    ap_lincons1_array_t array = ap_lincons1_array_make(env, 1);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_lincons1_t cons = ap_lincons1_make(AP_CONS_SUP, &expr, NULL);
    ap_lincons1_set_list(&cons, 
            AP_COEFF_S_INT, -1, "x",
            AP_CST_S_INT, 1000,
            AP_END);
    ap_lincons1_array_set(&array, 0, &cons);
    ap_abstract1_t abs = ap_abstract1_of_lincons_array(man, env, &array);
//    fprintf(stdout, "-x + 1000 > 0: Abstract value:\n");
//    ap_abstract1_fprint(stdout, man, &abs);
    ap_lincons1_array_clear(&array);

    return abs;
}

/* dest := x + c */
static ap_abstract1_t assign_bin_exp(ap_abstract1_t abs, char *dest,
        char *x, int c)
{
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_linexpr1_set_list(&expr,
		       AP_COEFF_S_INT, 1, x,
               AP_CST_S_INT, c,
		       AP_END);
//    fprintf(stdout, "Assignement (side-effect) in abstract value of x by "
//           "expression:\n");
//    ap_linexpr1_fprint(stdout, &expr);    

    abs = ap_abstract1_assign_linexpr(man, true, &abs, dest, &expr, NULL);
//    fprintf(stdout, "\n");
//    ap_abstract1_fprint(stdout, man, &abs);
    ap_linexpr1_clear(&expr);    

    return abs;
}

/* Creation of constraint x >= 1000 (x - 1000 >= 0) */
static ap_abstract1_t create_constraint2()
{
    ap_lincons1_array_t array = ap_lincons1_array_make(env, 1);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_lincons1_t cons = ap_lincons1_make(AP_CONS_SUPEQ, &expr, NULL);
    ap_lincons1_set_list(&cons, 
            AP_COEFF_S_INT, 1, "x",
            AP_CST_S_INT, -1000,
            AP_END);
    ap_lincons1_array_set(&array, 0, &cons);
    ap_abstract1_t abs = ap_abstract1_of_lincons_array(man, env, &array);
    fprintf(stdout, "x - 1000 >= 0: Abstract value:\n");
    ap_abstract1_fprint(stdout, man, &abs);
    ap_lincons1_array_clear(&array);

    return abs;
}

/* Creation of constraint x != 1000 (x - 1000 != 0) */
static ap_abstract1_t create_constraint3()
{
    ap_lincons1_array_t array = ap_lincons1_array_make(env, 1);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_lincons1_t cons = ap_lincons1_make(AP_CONS_DISEQ, &expr, NULL);
    ap_lincons1_set_list(&cons, 
            AP_COEFF_S_INT, 1, "x",
            AP_CST_S_INT, -1000,
            AP_END);
    ap_lincons1_array_set(&array, 0, &cons);
    ap_abstract1_t abs = ap_abstract1_of_lincons_array(man, env, &array);
    fprintf(stdout, "x - 1000 != 0: Abstract value:\n");
    ap_abstract1_fprint(stdout, man, &abs);
    ap_lincons1_array_clear(&array);

    return abs;
}

static void loop_example(void)
{
    /* One integer vars, none real */
    ap_var_t name_of_dim[] = { (ap_var_t)"x" };
    env = ap_environment_alloc(&name_of_dim[0], 1, NULL,0);

    /* Set all as bottom because there are 'joins' before assignments */
    ap_abstract1_t R[7], abs_temp;
    init_abstract_array(R, 7);

    int x;

    printf("Library %s, version %s\n", man->library, man->version);

    /* concrete: R[0] = {x ∈ Z} */
    /* abstract: R[0] = Top */
    R[0] = ap_abstract1_top(man, env);
    x = 7;
    /* R[1] = [x := 7]#R[0] = x ∈ [7, 7] */
    R[1] = assign_const(R[0], "x", 7);
    fprintf(stdout, "R[1] (x := 7):\n");
    ap_abstract1_fprint(stdout, man, &R[1]);

Label0:
    /* R[2] = R[1] U R[4] */
    R[2] = ap_abstract1_join(man, false, &R[1], &R[4]);
//    fprintf(stdout, "R[2] (join of R[1] and R[4]):\n");
//    ap_abstract1_fprint(stdout, man, &R[2]);

    /* while (x < 1000) */
    if (!(x < 1000))
        goto Label1;

    /* Concrete: R[3] = intersect(R[2], {s | s(x) < 1000}) */
    /* Abstract: R[3] = meet(R[2], [-inf, 999]) */
    abs_temp = create_constraint1();
    R[3] = ap_abstract1_meet(man, false, &R[2], &abs_temp);
//    fprintf(stdout,"Abstract value R[3] (meet of R[2] and x<1000):\n");
//    ap_abstract1_fprint(stdout, man, &R[3]);

    ++x;
    
    /* Concrete: R[4] = [x := x+1]R[3] */
    /* abstract: R[4] = R[3] + [1, 1] */
    R[4] = assign_bin_exp(R[3], "x", "x", 1);

    /* End of while scope */
    goto Label0;

Label1:
    fprintf(stdout, "R[4] ([x:=x+1]R[3]):\n");
    ap_abstract1_fprint(stdout, man, &R[4]);
    fprintf(stdout, "R[2] (join of R[1] and R[4]):\n");
    ap_abstract1_fprint(stdout, man, &R[2]);

    /* Concrete: R[5] = intersect(R[2], {s | s(x) >= 1000}) */
    /* Abstract: R[5] = meet(R[2], [1000, inf]) */
    abs_temp = create_constraint2();
    R[5] = ap_abstract1_meet(man, false, &R[2], &abs_temp);
    fprintf(stdout, "R[5]: meet(R[2], x >= 1000):\n");
    ap_abstract1_fprint(stdout, man, &R[5]);


    if (!(x == 1000))
    {
        /* Concrete: R[6] = intersect(R[5], x != 1000) */
        /* Concrete: R[6] = intersect(R[5],x<=999) U intersect(R[5],x>=1001) */
        /* Abstract: R[6] = Join(Meet(R[5],[-inf,999]),Meet(R[5],[1001,inf])) */
        abs_temp = create_constraint3();
        R[6] = ap_abstract1_meet(man, false, &R[5], &abs_temp);
        fprintf(stdout, "R[6]: Abstract value:\n");
        ap_abstract1_fprint(stdout, man, &R[6]);
        printf("Unable to prove x == 1000!\n");
    }
}

int main(void)
{
    man = box_manager_alloc();

    loop_example();

    ap_manager_free(man);

    return 0;
}
