from math import sqrt

from z3 import z3
from src.utils import toNum


def solveSpin(x, y, vectorX, vectorY):
    f = x * x + y * y

    newX = z3.Real("newX")
    newY = z3.Real("newY")

    exp = [newX * newX + newY * newY == f] + \
          [x * newY > y * newX] + \
          [vectorX * f == ((newX * x) + (newY * y)) * sqrt(vectorX * vectorX + vectorY * vectorY)]

    solver = z3.Solver()
    solver.add(exp)
    z3.set_option(rational_to_decimal=True)
    z3.set_option(precision=2)

    if solver.check() == z3.sat:
        model = solver.model()
        newX = toNum(model.evaluate(newX))
        newY = toNum(model.evaluate(newY))
        return newX, newY

    return 0, 0