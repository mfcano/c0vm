 #include <assert.h>
 #include <stdio.h>
 #include <limits.h>
 #include <stdlib.h>

 #include "lib/xalloc.h"
 #include "lib/contracts.h"
 #include "lib/stacks.h"
 #include "lib/c0vm.h"
 #include "lib/c0vm_c0ffi.h"
 #include "lib/c0vm_abort.h"

 /* call stack frames */
 typedef struct frame * frame;
 struct frame {
   c0_value *V; /* local variables */
   stack S;     /* operand stack */
   ubyte *P;    /* function body */
   size_t pc;   /* return address */
 };

 /* TODO: implement execute function */
 int execute(struct bc0_file *bc0) {

   /* Variables used for bytecode interpreter. You will need to initialize
      these appropriately. */

   /* callStack to hold frames when functions are called */

   stack callStack = NULL;
    (void) callStack;
    callStack = stack_new();
   /* initial program is the "main" function, function 0 (which must exist) */

   struct function_info *main_fn = bc0->function_pool;

   /* array to hold local variables for function */
   c0_value *V = NULL;
   //(void) V;
   V = xmalloc(sizeof(c0_value)*(main_fn->num_vars));
   /* stack for operands for computations */
   stack S;
   S = stack_new();
   /* array of (unsigned) bytes that make up the program */
   ubyte *P;
   P = main_fn->code;
   /* program counter that holds "address" of next bytecode to interpret from
      program P */
   size_t pc;
   pc = 0;
   while (true) {

 #ifdef DEBUG
     fprintf(stderr,
             "Opcode %x -- Operand stack size: %zu -- Program counter: %zu\n",
             P[pc], stack_size(S), pc);
 #endif

     switch (P[pc]) {

       /* GENERAL INSTRUCTIONS: Implement the following cases for each of the
          possible bytecodes.  Read the instructions in the assignment to see
          how far you should go before you test your code at each stage.  Do
          not try to write all of the code below at once!  Remember to update
          the program counter (pc) for each case, depending on the number of
          bytes needed for each bytecode operation.  See PROG_HINTS.txt for
          a few more hints.

          IMPORTANT NOTE: For each case, the case should end with a break
          statement to prevent the execution from continuing on into the
          next case.  See the POP case for an example.  To introduce new
          local variables in a case, use curly braces to create a new block.
          See the DUP case for an example.

          See C_IDIOMS.txt for further information on idioms you may find
          useful.
       */

     /* Additional stack operation: */

     case POP: {
       pc++;  //inc counter
       pop(S); // pop item
       break;
     }

     case DUP: {
       pc++;
       c0_value v = pop(S);
       push(S,v);
       push(S,v);
       break;
     }

     case SWAP: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       push(S, v);
       push(S, w);
       break;
     }
     /* Returning from a function */

     case RETURN: {
       pc++;
       c0_value v = pop(S);
       stack_free(S, &free);
       free(V);
       if (stack_empty(callStack)) {
         //free call stack and return int (the final return)
         stack_free(callStack, &free);
         return INT(v);
       }
       //if returning from a function then:
       frame callFrame = pop(callStack);
       V = callFrame->V;
       S = callFrame->S;
       P = callFrame->P;
       pc = callFrame->pc;
       free(callFrame);
       //push return value into operand stack of calling function
       push(S, v);

       break;
     }

     /* Arithmetic and Logical operations */

     case IADD: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       int sum =  INT(v) +  INT(w);
       push(S, VAL(sum));
       break;
     }

     case ISUB: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       int diff = INT(w) -  INT(v);
       push(S, VAL(diff));
       break;
     }

     case IMUL: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       int prod = INT(v) * INT(w);
       push(S, VAL(prod));
       break;
     }
     case IDIV: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       if (INT(v) == 0) {
         c0_arith_error("div by 0");
       }
       else if (INT(w) == INT_MIN && INT(v) == -1) {
         c0_arith_error("div of int_min by -1");
       }
       int quo = INT(w) / INT(v);
       push(S, VAL(quo));
       break;
     }

     case IREM: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       if (INT(v) == 0) {
         c0_arith_error("mod by 0");
       }
       else if (INT(w) == INT_MIN && INT(v) == -1) {
         c0_arith_error("mod of int_min by -1");
       }
       int rem = INT(w) % INT(v);
       push(S, VAL(rem));
       break;
     }

     case IAND:{
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       int and_val = INT(v) & INT(w);
       push(S, VAL(and_val));
       break;
     }

     case IOR: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       int or_val = INT(v) | INT(w);
       push(S, VAL(or_val));
       break;
     }

     case IXOR: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       int xor_val = INT(v) ^ INT(w);
       push(S, VAL(xor_val));
       break;
     }

     case ISHL: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       if (INT(v) < 0) {
         c0_arith_error("shift by negative");
       }
       else if (INT(v) > 31) {
         c0_arith_error("shift by more than 31");
       }
       int shl = INT(w) << INT(v);
       push(S, VAL(shl));
       break;
     }

     case ISHR: {
       pc++;
       c0_value v = pop(S);
       c0_value w = pop(S);
       if (INT(v) < 0) {
         c0_arith_error("shift by negative");
       }
       else if (INT(v) > 31) {
         c0_arith_error("shift by more than 31");
       }
       int shl = INT(w) >> INT(v);
       push(S, VAL(shl));
       break;
     }


     /* Pushing small constants */

     case BIPUSH: {
       pc++;
       //double cast to avoid sign extension issues
       int32_t val = (int32_t)(int8_t)(P[pc]);
       pc++;
       push(S, VAL(val));
       break;
     }

     /* Operations on local variables */

     case VLOAD: {
       pc++;
       uint8_t l_index = (P[pc]);
       c0_value value = V[l_index];
       push(S, value);
       pc++;
       break;
     }
     case VSTORE: {
       pc++;
       c0_value v = pop(S);
       uint8_t s_index = (P[pc]);
       V[s_index] = v;
       pc++;
       break;
     }
     case ACONST_NULL: {
       pc++;
       push(S, NULL);
       break;
     }
     case ILDC: {
       pc++;
       //first half of the number
       uint16_t c1 = (uint16_t)(P[pc]);
       pc++;
       //second half
       uint16_t c2 = (uint16_t)(P[pc]);
       pc++;
       //join them into one number
       uint16_t ldc_index = ((c1 << 8) | c2);
       push(S, VAL(bc0->int_pool[ldc_index]));
       break;
     }
     case ALDC: {
       pc++;
       //first half
       uint16_t a_c1 = (uint16_t)(P[pc]);
       pc++;
       //second half
       uint16_t a_c2 = (uint16_t)(P[pc]);
       pc++;
       //join
       uint16_t aldc_index = ((a_c1 << 8) | a_c2);
       push(S, (c0_value)(&bc0->string_pool[aldc_index]));
       break;
     }
     /* Control flow operations */

     case NOP: {
       pc++;
     }

     case IF_CMPEQ: {
       int v = INT(pop(S));
       int w = INT(pop(S));
       pc++;
       uint16_t o1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t o2 = (uint16_t)(P[pc]);
       if (v == w) {
         pc += (int16_t)(((o1<<8) | o2) - 2);
       }
       else {
         pc++;
       }
       break;
     }

     case IF_CMPNE: {
       int v = INT(pop(S));
       int w = INT(pop(S));
       pc++;
       uint16_t o1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t o2 = (uint16_t)(P[pc]);
       if (v != w) {
         pc += (int16_t)(((o1<<8) | o2) - 2);
       }
       else {
         pc++;
       }
       break;
     }

     case IF_ICMPLT: {
       int v = INT(pop(S));
       int w = INT(pop(S));
       pc++;
       uint16_t o1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t o2 = (uint16_t)(P[pc]);
       if (w < v) {
         pc += (int16_t)(((o1<<8) | o2) - 2);
       }
       else {
         pc++;
       }
       break;
     }

     case IF_ICMPGE:{
       int v = INT(pop(S));
       int w = INT(pop(S));
       pc++;
       uint16_t o1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t o2 = (uint16_t)(P[pc]);
       if (w >= v) {
         pc += (int16_t)(((o1<<8) | o2) - 2);
       }
       else {
         pc++;
       }
       break;
     }


     case IF_ICMPGT: {
       int v = INT(pop(S));
       int w = INT(pop(S));
       pc++;
       uint16_t o1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t o2 = (uint16_t)(P[pc]);

       if (w > v) {
         pc += (int16_t)(((o1<<8) | o2) - 2);
       }
       else {
         pc++;
       }
       break;
     }

     case IF_ICMPLE: {
       int v = INT(pop(S));
       int w = INT(pop(S));

       pc++;
       uint16_t o1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t o2 = (uint16_t)(P[pc]);
       if (w <= v) {
         pc += (((o1<<8) | o2) - 2);
       }
       else {
         pc++;
       }
       break;
     }


     case GOTO: {
       pc++;
       uint16_t o1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t o2 = (uint16_t)(P[pc]);
       //no condition for jump
       pc += (int16_t)(((o1<<8) | o2) - 2);
       break;
     }
     case ATHROW:{
       char* a = (char*)pop(S);
       c0_user_error(a);
       break;
     }
     case ASSERT: {
       pc++;
       char* a = (char*)pop(S);
       int flag = INT(pop(S));
       if (flag == 0) {
         c0_assertion_failure(a);
         break;
       }
       break;
     }
     /* Function call operations: */

     case INVOKESTATIC: {

       pc++;
       uint16_t a_c1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t a_c2 = (uint16_t)(P[pc]);
       pc++;
       uint16_t index = ((a_c1 << 8) | a_c2);

       struct function_info *fn = bc0->function_pool + index;

       frame cFrame = xmalloc(sizeof(struct frame));;
       cFrame->V = V; //current locals
       cFrame->S = S; //current operand stack
       cFrame->P = P; //current code pointer
       cFrame->pc = pc; //current pc
       push(callStack, cFrame);

       int argNum = fn->num_args;

       V = xmalloc(sizeof(c0_value) * (fn->num_vars));

       int i = 0;

       while (i < argNum) { //pop fn->num_args values off the stack and put them
                            // into the new locals array.
         V[argNum-1-i] = pop(S);
         i++;
       }

       P = fn->code; //load the new code into the program array
       S = stack_new(); //create a new, empty operand stack
       pc = 0; //set program counter to 0
       break;
     }
     case INVOKENATIVE: {
       pc++;
       uint16_t a_c1 = (uint16_t)(P[pc]);
       pc++;
       uint16_t a_c2 = (uint16_t)(P[pc]);
       pc++;
       uint16_t index = ((a_c1 << 8) | a_c2);

       struct native_info *fn = bc0->native_pool + index;

       int size = fn->num_args;

       c0_value *array = xmalloc(sizeof(c0_value)*size);

       int i = 0;
       //place the arguments from the stack on an array
       while (i < size) {
         array[size-1-i] = pop(S);
         i++;
         }
       uint16_t native_index = fn->function_table_index;
       //call the function form the table with the array
       c0_value returned_value  =  (native_function_table[native_index])(array);
       push(S, returned_value);
       free(array);
       break;
     }

     /* Memory allocation operations: */

     case NEW: {
       pc++;
       uint8_t size = (uint8_t)P[pc];
       uint8_t *a = xcalloc(size, sizeof(uint8_t));
       push(S, (c0_value)a);
       pc++;
       break;
     }
     case NEWARRAY: {
       pc++;
       int n = INT(pop(S));
       if (n <= 0) {
         c0_memory_error("negative element count");
         break;
       }

       //create struct//
       c0_array newArray = xcalloc(1, sizeof(struct c0_array_header));
       newArray->count = n;
       newArray->elt_size = (int)P[pc];

       if (newArray->elt_size == 0) {
         c0_memory_error("0 sized elements");
         break;
       }
       c0_value *array = xcalloc(n*newArray->elt_size, sizeof(uint8_t));
       newArray->elems = array;
       /////////////////

       push(S, (newArray));
       pc++;
       break;
     }

     case ARRAYLENGTH: {
       pc++;
       c0_array arrayStruct = (c0_array)(pop(S));
       if (arrayStruct == NULL) {
         c0_memory_error("NULL");
         break;
       }
       push(S, VAL(arrayStruct->count));
       break;
     }

     /* Memory access operations: */

     case AADDF:
       pc++;
       uint8_t offset = P[pc];
       uint8_t* addr = (uint8_t*)pop(S);
       if (addr == NULL) {
         c0_memory_error("the addr is null, let's be honest");
         break;
       } //check that addr isn't null

       push(S, (addr+offset));
       pc++;
       break;

     case AADDS: {
       pc++;
       int32_t i = INT(pop(S));
       c0_array array = (pop(S));
       //check if array is null:
       if (array == NULL) {
         c0_memory_error("the array is null, let's be honest");
       }

       int count = array->count;
       //check for index out of bounds:
       if (i >= count || i < 0) {
         c0_memory_error("i KNOW u ain't tryna access out of bounds");
       }

       int elt_size = array->elt_size;
       char *arr = (char*)(array->elems);
       push(S, &arr[i*elt_size]);
       break;
     }

     case IMLOAD: {
       pc++;
       //cast to int pointer, check if it's null
       int* address = (int*)(pop(S));
       if (address == NULL) {
         c0_memory_error("null");
         break;
       }
       push(S, VAL((*address))); //VAL(*(address));
       break;
     }
     case IMSTORE: {
       pc++;
       //same as above expect we place an int at an address
       int value = INT(pop(S));
       int* address = (int*)(pop(S));
       if (address == NULL) {
         c0_memory_error("null");
       }
       *address = value;
       break;
     }
     case AMLOAD: {
       pc++;
       //pointer of a void pointer (void**)
       c0_value *address = (pop(S));
       if (address == NULL) {
         c0_memory_error("null");
       }
       push(S, (*address));
       break;
     }
     case AMSTORE: {
       pc++;
       c0_value addr = (pop(S));
       //pointer of a void pointer (void**)
       c0_value* addrofaddr = (pop(S));
       if (addrofaddr == NULL) {
         c0_memory_error("null");
         break;
       }
       *addrofaddr = addr;
       break;
     }
     case CMLOAD: {
       pc++;
       //cast to char pointer
       char *addr = (char*)(pop(S));
       if (addr == NULL) {
         c0_memory_error("null");
       }
       push(S, VAL((int32_t)(*addr)));
       break;
     }
     case CMSTORE: {
       pc++;
       int32_t val = INT(pop(S));
       char* addr = (char*)(pop(S));
       if (addr == NULL) {
         c0_memory_error("null");
         break;
       }
       *addr = (char)(val & 0x7F);
       break;
     }

     default:
       fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
       abort();
     }
   }

   /* cannot get here from infinite loop */
   assert(false);
 }

