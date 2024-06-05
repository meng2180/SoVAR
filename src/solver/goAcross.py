import random
import z3
from z3 import Or
from src.utils import toNum


def solveGoAcross(end, laneAndDirection, laneCount, width):
    direction = laneAndDirection[0]

    endX = end[0]
    endY = end[1]
    endSpeed = end[2]

    w1X = z3.Real("w1X")
    w2X = z3.Real("w2X")
    w3X = z3.Real("w3X")
    w4X = z3.Real("w4X")
    w5X = z3.Real("w5X")
    w1Y = z3.Real("w1Y")
    w2Y = z3.Real("w2Y")
    w3Y = z3.Real("w3Y")
    w4Y = z3.Real("w4Y")
    w5Y = z3.Real("w5Y")
    speed = z3.Real("speed")

    speedExp = [z3.And(speed >= endSpeed, speed <= endSpeed)]

    positionExp = None
    if direction == 1:
        positionExp = [w1X == w5X] + \
                      [w2X == w5X] + \
                      [w3X == w5X] + \
                      [w4X == w5X] + \
                      [w5X == endX] + \
                      [w5Y - w1Y == 6 * laneCount * width] + \
                      [w2Y - w1Y > 0] + \
                      [w3Y - w2Y > 0] + \
                      [w4Y - w3Y > 0] + \
                      [z3.And(w5Y == endY, w5Y - w4Y > 0)]
    if direction == 2:
        positionExp = [w1Y == w5Y] + \
                      [w2Y == w5Y] + \
                      [w3Y == w5Y] + \
                      [w4Y == w5Y] + \
                      [w5Y == endY] + \
                      [w5X - w1X == 6 * laneCount * width] + \
                      [w2X - w1X > 0] + \
                      [w3X - w2X > 0] + \
                      [w4X - w3X > 0] + \
                      [z3.And(w5X == endX, w5X - w4X > 0)]
    if direction == 3:
        positionExp = [w1X == w5X] + \
                      [w2X == w5X] + \
                      [w3X == w5X] + \
                      [w4X == w5X] + \
                      [w5X == endX] + \
                      [w1Y - w5Y == 6 * laneCount * width] + \
                      [w1Y - w2Y > 0] + \
                      [w2Y - w3Y > 0] + \
                      [w3Y - w4Y > 0] + \
                      [z3.And(w5Y == endY, w4Y - w5Y > 0)]
    if direction == 4:
        positionExp = [w1Y == w5Y] + \
                      [w2Y == w5Y] + \
                      [w3Y == w5Y] + \
                      [w4Y == w5Y] + \
                      [w5Y == endY] + \
                      [w1X - w5X == 6 * laneCount * width] + \
                      [w1X - w2X > 0] + \
                      [w2X - w3X > 0] + \
                      [w3X - w4X > 0] + \
                      [z3.And(w5X == endX, w4X - w5X > 0)]

    solver = z3.Solver()
    solver.add(speedExp + positionExp)
    z3.set_option(rational_to_decimal=True)
    z3.set_option(precision=1)

    res = []
    i = 0
    while solver.check() == z3.sat and i < 1000:
        i += 1
        model = solver.model()
        waypoints = [[toNum(model.evaluate(w1X)), toNum(model.evaluate(w1Y)), toNum(model.evaluate(speed)), 0, 0, 0],
                     [toNum(model.evaluate(w2X)), toNum(model.evaluate(w2Y)), toNum(model.evaluate(speed)), 0, 0, 0],
                     [toNum(model.evaluate(w3X)), toNum(model.evaluate(w3Y)), toNum(model.evaluate(speed)), 0, 0, 0],
                     [toNum(model.evaluate(w4X)), toNum(model.evaluate(w4Y)), toNum(model.evaluate(speed)), 0, 0, 0],
                     [toNum(model.evaluate(w5X)), toNum(model.evaluate(w5Y)), toNum(model.evaluate(speed)), 0, 0, 0]]
        res.append(waypoints)

        solver.add(Or(w1X == model[w1X] + 2, w2X == model[w2X] + 2,
                      w3X == model[w3X] + 2, w4X == model[w4X] + 2,
                      w1Y == model[w1Y] + 2, w2Y == model[w2Y] + 2,
                      w3Y == model[w3Y] + 2, w4Y == model[w4Y] + 2))

    return res[random.randint(0, len(res) - 1)]