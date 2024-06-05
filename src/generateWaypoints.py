import math
from solver.changeLane import solveChangeLane
from solver.followLane import solveFollowLane
from solver.stop import solveStop
from solver.turnAround import solveTurnAround
from solver.turnRight import solveTurnRight
from solver.turnLeft import solveTurnLeft
from src.solver.driveInto import solveDriveInto
from src.solver.driveOff import solveDriveOff
from src.solver.goAcross import solveGoAcross
from src.solver.halfU import solveHalfU
from src.solver.retrograde import solveRetrograde
from utils import combine


def generateWaypoints(carInfoList, laneAndDirectionList, laneCount, width, crashPoint, intersection, speed, striker, impactPoint):
    waypointList = []
    costTimeList = []
    tag = -1

    for i in range(len(carInfoList)):
        behaviors = carInfoList[i]["behaviors"]

        if behaviors[-1][0] == "stop":
            tag = i

    for i in range(len(carInfoList)):
        carInfo = carInfoList[i]
        laneAndDirection = laneAndDirectionList[i]
        waypointSet = []

        strikerTag = False
        if striker == 'V' + str(i + 1):
            strikerTag = True

        crashSpeed = speed[i]
        direction = 0
        bound = 0
        laneNumber = 0
        end = [crashPoint[i][0], crashPoint[i][1], crashSpeed, direction, bound, laneNumber]
        crashEnd = [crashPoint[i][0], crashPoint[i][1], crashSpeed, direction, bound, laneNumber]
        behaviors = carInfo["behaviors"]
        j = len(behaviors) - 1
        while j >= 0:
            behavior = behaviors[j]
            if behavior[0] not in ["intended", "stop"]:
                waypoints = generateForOne(behavior, end, laneAndDirection[j], laneCount, width, intersection)
                end = waypoints[0]
                waypointSet.append(waypoints)
            j -= 1
        if tag != -1 and i != tag:
            waypointSet.append(solveFollowLane(end, laneAndDirection[j], width))

        waypointRes = combine(crashEnd, waypointSet)
        waypointList.append(waypointRes)
        costTimeList.append(calculateTime(waypointRes))

    if tag == -1:
        maxTime = max(costTimeList)
        for i in range(len(carInfoList)):
            idle = maxTime - costTimeList[i]

            if striker == 'V' + str(i + 1):
                if impactPoint == 2:
                    idle += 2
                if impactPoint == 3:
                    idle += 3

            if idle != 0:
                direction = laneAndDirectionList[i][0][0]
                speed = waypointList[i][0][2]
                x = waypointList[i][0][0]
                y = waypointList[i][0][1]
                start = None
                deta = idle * speed / 3.6
                if direction == 1:
                    start = [x, y - deta, speed, 0, 0, 0]
                elif direction == 2:
                    start = [x - deta, y, speed, 0, 0, 0]
                elif direction == 3:
                    start = [x, y + deta, speed, 0, 0, 0]
                elif direction == 4:
                    start = [x + deta, y, speed, 0, 0, 0]
                waypointList[i].insert(0, start)


    return waypointList


def generateWaypointsForSingle(carInfoList, laneAndDirectionList, laneCount, width, crashPoint, intersection, speed):
    waypointList = []

    carInfo = carInfoList[0]
    laneAndDirection = laneAndDirectionList[0]
    waypointSet = []

    crashSpeed = speed[0]
    end = [crashPoint[0][0], crashPoint[0][1], crashSpeed]
    crashEnd = [crashPoint[0][0], crashPoint[0][1], crashSpeed]

    behaviors = carInfo["behaviors"]
    j = len(behaviors) - 1
    while j >= 0:
        behavior = behaviors[j]
        if behavior[0] not in ["intended", "stop"]:
            waypoints = generateForOne(behavior, end, laneAndDirection[j], laneCount, width, intersection)
            end = waypoints[0]
            waypointSet.append(waypoints)
        j -= 1

    waypointList.append(combine(crashEnd, waypointSet))
    costTime = calculateTime(waypointList[0])

    if costTime == 0:
        costTime = 5

    pedestrainSpeed = 3.6 * getDist(crashPoint[0], crashPoint[1]) / costTime

    waypointList.append([[crashPoint[1][0], crashPoint[1][1], pedestrainSpeed], [crashPoint[0][0], crashPoint[0][1], pedestrainSpeed]])

    return waypointList


def calculateTime(waypointList):
    time = 0
    for i in range(1, len(waypointList)):
        time += getDist(waypointList[i - 1], waypointList[i]) * 3.6 / waypointList[i][2]

    return time


def getDist(x, y):
    return math.sqrt((x[0] - y[0]) ** 2 + (x[1] - y[1]) ** 2)


def generateForOne(behavior, end, laneAndDirection, laneCount, width, intersection):
    if behavior[0] == "follow lane":
        return solveFollowLane(end, laneAndDirection, width)

    if behavior[0] == "retrograde":
        return solveRetrograde(end, laneAndDirection, laneCount, width, intersection)

    if behavior[0] == "turn right":
        return solveTurnRight(end, laneAndDirection, laneCount, width)

    if behavior[0] == "turn left":
        return solveTurnLeft(end, laneAndDirection, laneCount, width)

    if behavior[0] == "turn around":
        return solveTurnAround(end, laneAndDirection, laneCount, width, intersection)

    if behavior[0] == "stop":
        return solveStop(end)

    if behavior[0] == "change lane":
        return solveChangeLane(end, laneAndDirection, laneCount, width, behavior[1], intersection)

    if behavior[0] == "go across":
        return solveGoAcross(end, laneAndDirection, laneCount, width)

    if behavior[0] == "drive off":
        return solveDriveOff(end, laneAndDirection, laneCount, width)

    if behavior[0] == "drive into":
        return solveDriveInto(end, laneAndDirection, laneCount, width, intersection)

    if behavior[0] == "halfU":
        return solveHalfU(end, laneAndDirection, laneCount, width, intersection)

    return []