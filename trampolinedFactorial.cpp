#include <cstdio>

struct Param
{
  void *func;
  int num;
  int res;
};

Param trampolinedFactorial (int num, int res)
{
  if (num == 1)
    return Param{ NULL, num - 1, res };
  else
    return Param{ trampolinedFactorial, num - 1, num * res };
}

int main ()
{
  Param param{ trampolinedFactorial, 4, 1 };
  while (param.func) {
    param = ((decltype (trampolinedFactorial) *)param.func) (param.num, param.res);
  }
  printf ("%d\n", param.res);

  return 0;
}