import random
import z3
from z3 import Or
from src.utils import toNum


def solveRetrograde(end, laneAndDirection, laneCount, width, intersection):
    direction = laneAndDirection[0]
    lane = laneAndDirection[1]

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
        if intersection == "yes":
            positionExp = [w5X == endX] + \
                          [w1X - w2X > 0] + \
                          [w2X - w3X > 0] + \
                          [w3X - w4X > 0] + \
                          [w4X - w5X > 0] + \
                          [z3.And(w1X > (laneCount + lane - 1) * width + 1, w1X < (laneCount + lane) * width - 1)] + \
                          [w5Y == endY] + \
                          [w2Y - w1Y > 0] + \
                          [w3Y - w2Y > 0] + \
                          [w4Y - w3Y > 0] + \
                          [w5Y - w4Y > 0] + \
                          [w5Y - w1Y > 2 * laneCount * width]
        else:
            positionExp = [w5X == endX] + \
                          [w1X - w2X > 0] + \
                          [w2X - w3X > 0] + \
                          [w3X - w4X > 0] + \
                          [w4X - w5X > 0] + \
                          [z3.And(w1X > (lane - 1) * width + 1, w1X < lane * width - 1)] + \
                          [w5Y == endY] + \
                          [w2Y - w1Y > 0] + \
                          [w3Y - w2Y > 0] + \
                          [w4Y - w3Y > 0] + \
                          [w5Y - w4Y > 0] + \
                          [w5Y - w1Y > 2 * laneCount * width]
    if direction == 2:
        if intersection == "yes":
            positionExp = [w5X == endX] + \
                          [w2X - w1X > 0] + \
                          [w3X - w2X > 0] + \
                          [w4X - w3X > 0] + \
                          [w5X - w4X > 0] + \
                          [w5X - w1X > 2 * laneCount * width] + \
                          [w5Y == endY] + \
                          [w2Y - w1Y > 0] + \
                          [w3Y - w2Y > 0] + \
                          [w4Y - w3Y > 0] + \
                          [w5Y - w4Y > 0] + \
                          [w1Y > (laneCount - lane) * width + 1] + \
                          [w1Y < (laneCount - lane + 1) * width - 1]
        else:
            positionExp = [w5X == endX] + \
                          [w2X - w1X > 0] + \
                          [w3X - w2X > 0] + \
                          [w4X - w3X > 0] + \
                          [w5X - w4X > 0] + \
                          [w5X - w1X > 2 * laneCount * width] + \
                          [w5Y == endY] + \
                          [w2Y - w1Y > 0] + \
                          [w3Y - w2Y > 0] + \
                          [w4Y - w3Y > 0] + \
                          [w5Y - w4Y > 0] + \
                          [w1Y > - lane * width + 1] + \
                          [w1Y < (- lane + 1) * width - 1]
    if direction == 3:
        if intersection == "yes":
            positionExp = [w5X == endX] + \
                          [w1X - w2X < 0] + \
                          [w2X - w3X < 0] + \
                          [w3X - w4X < 0] + \
                          [w4X - w5X < 0] + \
                          [z3.And(w1X > (laneCount - lane) * width + 1, w1X < (laneCount - lane + 1) * width - 1)] + \
                          [w5Y == endY] + \
                          [w1Y - w2Y > 0] + \
                          [w2Y - w3Y > 0] + \
                          [w3Y - w4Y > 0] + \
                          [w4Y - w5Y > 0] + \
                          [w1Y - w5Y > 2 * laneCount * width]

        else:
            positionExp = [w5X == endX] + \
                          [w1X - w2X < 0] + \
                          [w2X - w3X < 0] + \
                          [w3X - w4X < 0] + \
                          [w4X - w5X < 0] + \
                          [z3.And(w1X > - lane * width + 1, w1X < (- lane + 1) * width - 1)] + \
                          [w5Y == endY] + \
                          [w1Y - w2Y > 0] + \
                          [w2Y - w3Y > 0] + \
                          [w3Y - w4Y > 0] + \
                          [w4Y - w5Y > 0] + \
                          [w1Y - w5Y > 2 * laneCount * width]
    if direction == 4:
        if intersection == "yes":
            positionExp = [w5X == endX] + \
                          [w1X - w2X > 0] + \
                          [w2X - w3X > 0] + \
                          [w3X - w4X > 0] + \
                          [w4X - w5X > 0] + \
                          [w1X - w5X > 2 * laneCount * width] + \
                          [w5Y == endY] + \
                          [w2Y - w1Y < 0] + \
                          [w3Y - w2Y < 0] + \
                          [w4Y - w3Y < 0] + \
                          [w5Y - w4Y < 0] + \
                          [w1Y > (laneCount + lane - 1) * width + 1] + \
                          [w1Y < (laneCount + lane) * width - 1]
        else:
            positionExp = [w5X == endX] + \
                          [w1X - w2X > 0] + \
                          [w2X - w3X > 0] + \
                          [w3X - w4X > 0] + \
                          [w4X - w5X > 0] + \
                          [w1X - w5X > 2 * laneCount * width] + \
                          [w5Y == endY] + \
                          [w2Y - w1Y < 0] + \
                          [w3Y - w2Y < 0] + \
                          [w4Y - w3Y < 0] + \
                          [w5Y - w4Y < 0] + \
                          [w1Y > (lane - 1) * width + 1] + \
                          [w1Y < lane * width - 1]

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

        solver.add(Or(w1X == model[w1X] + 0.5, w2X == model[w2X] + 0.5,
                      w3X == model[w3X] + 0.5, w4X == model[w4X] + 0.5,
                      w1Y == model[w1Y] + 0.5, w2Y == model[w2Y] + 0.5,
                      w3Y == model[w3Y] + 0.5, w4Y == model[w4Y] + 0.5))

    return res[random.randint(0, len(res) - 1)]