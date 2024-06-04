import json
import os
from generateWaypoints import generateWaypoints, generateWaypointsForSingle
from src.search import search, getFinalWaypointList

from src.gpt import gptProcessReport
from utils import findCrashPoint, caculateLaneAndDirections, isFan, findCrashPointForApollo, findCrashPointForSingle


def containsLeft(carInformation, car):
    behaviors = carInformation["V" + str(car)]["behaviors"]
    for behavior in behaviors:
        if behavior[0] == "turn left":
            return True
    return False


def containsRight(carInformation, car):
    behaviors = carInformation["V" + str(car)]["behaviors"]
    for behavior in behaviors:
        if behavior[0] == "turn right":
            return True
    return False


def containsDriveInto(behaviors):
    for behavior in behaviors:
        if behavior[0] == "drive into":
            return True
    return False


def containsTurnAround(behaviors):
    for behavior in behaviors:
        if behavior[0] == "turn around":
            return True
    return False


def transformDirection(direction):
    if direction.startswith('north'):
        return 1
    if direction.startswith('east'):
        return 2
    if direction.startswith('south'):
        return 3
    if direction.startswith('west'):
        return 4
    if direction == 'unknown':
        return 0


def caculateWaypoints(speed, ego, index):
    gptProcessReport()

    path = os.path.join(os.path.abspath(os.path.dirname(__file__)).split('BigModelRacer-latest')[0], "BigModelRacer-latest/src/file/result.txt")
    f = open(path, encoding='utf-8')
    requirements = json.load(f)
    f.close()

    carInformation = requirements["carInformation"]
    carCount = requirements["carCount"]

    if carCount == 1:
        return caculateWaypointsForSingle(requirements, speed, index)

    laneCount = 2
    intersection = requirements["intersection"]
    T = requirements["T"]

    striker = requirements["striker"]
    if striker == "unknown":
        striker = "V1"

    impactPoint = requirements["impactPart"]
    if impactPoint == 0:
        impactPoint = 1

    oPoint = search(laneCount, intersection, T, index)
    width = oPoint[4]

    lastActionList = []
    laneAndDirectionList = []
    carInfoList = []

    carInformation["V1"]["direction"] = transformDirection(carInformation["V1"]["direction"])
    carInformation["V2"]["direction"] = transformDirection(carInformation["V2"]["direction"])


    if len(carInformation["V1"]["behaviors"]) == 0:
        carInformation["V1"]["behaviors"].append(["follow lane"])

    if len(carInformation["V2"]["behaviors"]) == 0:
        carInformation["V2"]["behaviors"].append(["follow lane"])

    if carInformation["V1"]["direction"] == 0 and carInformation["V2"]["direction"] == 0:
        carInformation["V1"]["direction"] = 1
        carInformation["V2"]["direction"] = 1

    if carInformation["V1"]["direction"] == 0:
        if carInformation["V2"]["behaviors"][-1][0] == "retrograde":
            fan = [0, 3, 4, 1, 2]
            carInformation["V1"]["direction"] = fan[carInformation["V2"]["direction"]]
        else:
            carInformation["V1"]["direction"] = carInformation["V2"]["direction"]

    if carInformation["V2"]["direction"] == 0:
        if carInformation["V1"]["behaviors"][-1][0] == "retrograde":
            fan = [0, 3, 4, 1, 2]
            carInformation["V2"]["direction"] = fan[carInformation["V1"]["direction"]]
        else:
            carInformation["V2"]["direction"] = carInformation["V1"]["direction"]

    if carInformation["V1"]["laneNumber"] == 0 or carInformation["V1"]["laneNumber"] > laneCount:
        carInformation["V1"]["laneNumber"] = 1
    else:
        carInformation["V1"]["laneNumber"] = laneCount - carInformation["V1"]["laneNumber"] + 1

    if carInformation["V2"]["laneNumber"] == 0 or carInformation["V2"]["laneNumber"] > laneCount:
        carInformation["V2"]["laneNumber"] = 1
    else:
        carInformation["V2"]["laneNumber"] = laneCount - carInformation["V2"]["laneNumber"] + 1

    if len(carInformation["V1"]["behaviors"]) > 1 and carInformation["V1"]["behaviors"][-1][0] == 'stop':
        carInformation["V1"]["behaviors"].pop()

    if len(carInformation["V2"]["behaviors"]) > 1 and carInformation["V2"]["behaviors"][-1][0] == 'stop':
        carInformation["V2"]["behaviors"].pop()

    if carInformation["V1"]["behaviors"][-1][0] == "retrograde":
        fan = [0, 3, 4, 1, 2]
        carInformation["V2"]["direction"] = fan[carInformation["V1"]["direction"]]

    if carInformation["V2"]["behaviors"][-1][0] == "retrograde":
        fan = [0, 3, 4, 1, 2]
        carInformation["V1"]["direction"] = fan[carInformation["V2"]["direction"]]


    if T == "yes":
        curV1D = carInformation["V1"]["direction"]
        curV2D = carInformation["V2"]["direction"]

        if curV1D > 2:
            fan = [0, 3, 4, 1, 2]
            carInformation["V1"]["direction"] = fan[curV1D]
            carInformation["V2"]["direction"] = fan[curV2D]

        curV1D = carInformation["V1"]["direction"]
        curV2D = carInformation["V2"]["direction"]

        if curV1D == 1:
            if containsLeft(carInformation, 1):
                if curV2D == 1:
                    if containsRight(carInformation, 2):
                        carInformation["V1"]["direction"] = 1
                        carInformation["V2"]["direction"] = 1
                    else:
                        carInformation["V1"]["direction"] = 4
                        carInformation["V2"]["direction"] = 4
                if curV2D == 2:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 4
                        carInformation["V2"]["direction"] = 1
                if curV2D == 3:
                    carInformation["V1"]["direction"] = 4
                    carInformation["V2"]["direction"] = 2
            elif containsRight(carInformation, 1):
                if curV2D == 1:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 1
                        carInformation["V2"]["direction"] = 1
                    else:
                        carInformation["V1"]["direction"] = 2
                        carInformation["V2"]["direction"] = 2
                if curV2D == 3:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 2
                        carInformation["V2"]["direction"] = 4
            else:
                if curV2D == 1:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 4
                        carInformation["V2"]["direction"] = 4
                    elif containsRight(carInformation, 2):
                        carInformation["V1"]["direction"] = 2
                        carInformation["V2"]["direction"] = 2
                if curV2D == 2:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 4
                        carInformation["V2"]["direction"] = 1
                if curV2D == 3:
                    carInformation["V1"]["direction"] = 2
                    carInformation["V2"]["direction"] = 4
                if curV2D == 4:
                    if containsLeft(carInformation, 2) or containsRight(carInformation, 2):
                        carInformation["V1"]["direction"] = 2
                        carInformation["V2"]["direction"] = 1
        if curV1D == 2:
            if containsLeft(carInformation, 1):
                if curV2D == 1:
                    carInformation["V1"]["direction"] = 1
                    carInformation["V2"]["direction"] = 4
                if curV2D == 2:
                    if containsLeft(carInformation, 2) or containsRight(carInformation, 2):
                        carInformation["V1"]["direction"] = 1
                        carInformation["V2"]["direction"] = 1
                    else:
                        carInformation["V1"]["direction"] = 4
                        carInformation["V2"]["direction"] = 4
                if curV2D == 3:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 4
                        carInformation["V2"]["direction"] = 1
                    else:
                        carInformation["V1"]["direction"] = 1
                        carInformation["V2"]["direction"] = 2
                if curV2D == 4:
                    carInformation["V1"]["direction"] = 4
                    carInformation["V2"]["direction"] = 2
            elif containsRight(carInformation, 1):
                if curV2D == 2:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 1
                        carInformation["V2"]["direction"] = 1
                if curV2D == 3:
                    carInformation["V1"]["direction"] = 1
                    carInformation["V2"]["direction"] = 2
            else:
                if curV2D == 2:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 4
                        carInformation["V2"]["direction"] = 4
                if curV2D == 3:
                    if containsLeft(carInformation, 2):
                        carInformation["V1"]["direction"] = 1
                        carInformation["V2"]["direction"] = 4
                    else:
                        carInformation["V2"]["direction"] = 1
    else:
        if intersection == 'no':
            if carInformation["V1"]["direction"] == 2:
                carInformation["V1"]["direction"] = 1
            if carInformation["V1"]["direction"] == 4:
                carInformation["V1"]["direction"] = 3

            if carInformation["V2"]["direction"] == 2:
                carInformation["V2"]["direction"] = 1
            if carInformation["V2"]["direction"] == 4:
                carInformation["V2"]["direction"] = 3

    if carInformation["V1"]["laneNumber"] == carInformation["V2"]["laneNumber"] and carInformation["V1"]["direction"] == carInformation["V2"]["direction"]:
        if carInformation["V1"]["behaviors"][-1][0] == "change lane":
            carInformation["V1"]["behaviors"].pop()

        if carInformation["V2"]["behaviors"][-1][0] == "change lane":
            carInformation["V2"]["behaviors"].pop()

    if carInformation["V1"]["behaviors"][-1][0] == "turn around" and carInformation["V1"]["direction"] == carInformation["V2"]["direction"]:
        carInformation["V1"]["behaviors"].pop()
        if containsDriveInto(carInformation["V1"]["behaviors"]) is False:
            carInformation["V1"]["behaviors"].append(["halfU"])
        if carInformation["V1"]["laneNumber"] == carInformation["V2"]["laneNumber"]:
            carInformation["V1"]["laneNumber"] = laneCount
            carInformation["V2"]["laneNumber"] = 1

    if carInformation["V2"]["behaviors"][-1][0] == "turn around" and carInformation["V1"]["direction"] == carInformation["V2"]["direction"]:
        carInformation["V2"]["behaviors"].pop()
        if containsDriveInto(carInformation["V2"]["behaviors"]) is False:
            carInformation["V2"]["behaviors"].append(["halfU"])
        if carInformation["V1"]["laneNumber"] == carInformation["V2"]["laneNumber"]:
            carInformation["V2"]["laneNumber"] = laneCount
            carInformation["V1"]["laneNumber"] = 1

    if intersection == "no" and T == "no":
        if carInformation["V1"]["behaviors"][-1][0] == "go across":
            carInformation["V1"]["behaviors"].pop()
            carInformation["V1"]["behaviors"].append(["follow lane"])

        if carInformation["V2"]["behaviors"][-1][0] == "go across":
            carInformation["V2"]["behaviors"].pop()
            carInformation["V2"]["behaviors"].append(["follow lane"])

        if carInformation["V1"]["behaviors"][-1][0] == "turn left":
            if carInformation["V1"]["direction"] != carInformation["V2"]["direction"]:
                carInformation["V1"]["behaviors"].pop()
                carInformation["V1"]["behaviors"].append(["retrograde"])
            else:
                carInformation["V1"]["behaviors"].pop()
                carInformation["V1"]["behaviors"].append(["halfU"])
                if carInformation["V1"]["laneNumber"] == carInformation["V2"]["laneNumber"]:
                    carInformation["V1"]["laneNumber"] = laneCount
                    carInformation["V2"]["laneNumber"] = 1
        if carInformation["V2"]["behaviors"][-1][0] == "turn left":
            if carInformation["V1"]["direction"] != carInformation["V2"]["direction"]:
                carInformation["V2"]["behaviors"].pop()
                carInformation["V2"]["behaviors"].append(["retrograde"])
            else:
                carInformation["V2"]["behaviors"].pop()
                carInformation["V2"]["behaviors"].append(["halfU"])
                if carInformation["V1"]["laneNumber"] == carInformation["V2"]["laneNumber"]:
                    carInformation["V2"]["laneNumber"] = laneCount
                    carInformation["V1"]["laneNumber"] = 1

    if isFan(carInformation["V1"]["direction"], carInformation["V2"]["direction"]):
        if carInformation["V1"]["behaviors"][-1][0] == "change lane":
            carInformation["V1"]["behaviors"].pop()
            if not containsLeft(carInformation, 2):
                carInformation["V1"]["behaviors"].append(["retrograde"])
            else:
                carInformation["V1"]["behaviors"].append(["go across"])

        if carInformation["V2"]["behaviors"][-1][0] == "change lane":
            carInformation["V2"]["behaviors"].pop()
            if not containsLeft(carInformation, 1):
                carInformation["V2"]["behaviors"].append(["retrograde"])
            else:
                carInformation["V2"]["behaviors"].append(["go across"])

    if intersection == "yes" or T == "yes":
        if (carInformation["V1"]["behaviors"][-1][0] == "stop" or carInformation["V1"]["behaviors"][-1][0] == "follow lane") and carInformation["V2"]["behaviors"][-1][0] == "go across":
            carInformation["V2"]["behaviors"].pop()
            carInformation["V2"]["behaviors"].append(["follow lane"])

        if (carInformation["V2"]["behaviors"][-1][0] == "stop" or carInformation["V2"]["behaviors"][-1][0] == "follow lane") and carInformation["V1"]["behaviors"][-1][0] == "go across":
            carInformation["V1"]["behaviors"].pop()
            carInformation["V1"]["behaviors"].append(["follow lane"])

        if carInformation["V1"]["direction"] != carInformation["V2"]["direction"]:
            if carInformation["V1"]["behaviors"][-1][0] in ['follow lane', 'stop', 'change lane', 'drive into', 'drive off'] and carInformation["V2"]["behaviors"][-1][0] != "retrograde":
                carInformation["V1"]["behaviors"].pop()
                carInformation["V1"]["behaviors"].append(["go across"])

            if carInformation["V2"]["behaviors"][-1][0] in ['follow lane', 'stop', 'change lane', 'drive into', 'drive off'] and carInformation["V1"]["behaviors"][-1][0] != "retrograde":
                carInformation["V2"]["behaviors"].pop()
                carInformation["V2"]["behaviors"].append(["go across"])

        if carInformation["V1"]["direction"] == carInformation["V2"]["direction"]:
            if carInformation["V1"]["behaviors"][-1][0] == "turn right" or carInformation["V1"]["behaviors"][-1][0] == "turn left":
                if carInformation["V2"]["behaviors"][-1][0] == 'follow lane':
                    carInformation["V2"]["behaviors"].pop()
                    carInformation["V2"]["behaviors"].append(["go across"])

            if carInformation["V2"]["behaviors"][-1][0] == "turn right" or carInformation["V2"]["behaviors"][-1][0] == "turn left":
                if carInformation["V1"]["behaviors"][-1][0] == 'follow lane':
                    carInformation["V1"]["behaviors"].pop()
                    carInformation["V1"]["behaviors"].append(["go across"])

        if carInformation["V1"]["behaviors"][-1][0] in ["go across", "stop"] and (containsLeft(carInformation, 1) or containsRight(carInformation, 1)):
            carInformation["V1"]["behaviors"].pop()

        if carInformation["V2"]["behaviors"][-1][0] in ["go across", "stop"] and (containsLeft(carInformation, 2) or containsRight(carInformation, 2)):
            carInformation["V2"]["behaviors"].pop()

    if containsTurnAround(carInformation["V1"]["behaviors"]) and carInformation["V1"]["behaviors"][-1][0] != "turn around":
        carInformation["V1"]["behaviors"].pop()

    if containsTurnAround(carInformation["V2"]["behaviors"]) and carInformation["V2"]["behaviors"][-1][0] != "turn around":
        carInformation["V2"]["behaviors"].pop()


    for i in range(carCount):
        curV = carInformation["V" + str(i + 1)]
        curActions = curV["behaviors"]

        for j in range(len(curActions)):
            curAction = curActions[j]
            if curAction[0] == 'drive into' and curV["direction"] == 0:
                curV["direction"] = carInformation["V1"]["direction"] + carInformation["V2"]["direction"]

            if len(curAction) > 1:
                if curAction[1] == 0 or curAction[1] > laneCount:
                    curAction[1] = 1
                else:
                    curAction[1] = laneCount - curAction[1] + 1

        carInfoList.append(curV)

        index = len(curActions) - 1
        while curActions[index][0] == "intended":
            index -= 1

        lastActionList.append(curActions[index])

        curLaneAndDirections = caculateLaneAndDirections(curActions, curV["direction"], curV["laneNumber"])
        if curLaneAndDirections == "erro":
            return [], 0, False
        laneAndDirectionList.append(curLaneAndDirections)


    if ego:
        crashPoint = findCrashPointForApollo(lastActionList, laneAndDirectionList, laneCount, width, intersection)
    else:
        resPoint = findCrashPoint(lastActionList, laneAndDirectionList, laneCount, width, intersection)
        crashPoint = [resPoint, resPoint]

    if crashPoint == "erro" or crashPoint[0] == "erro":
        return [], 0, False

    print(crashPoint)

    if intersection == "yes" or T == "yes":
        intersection = "yes"

    waypointList = generateWaypoints(carInfoList, laneAndDirectionList, laneCount, width, crashPoint, intersection, speed, striker, impactPoint)

    getFinalWaypointList(waypointList, oPoint)

    return waypointList, isFan(carInformation["V1"]["direction"], carInformation["V2"]["direction"]), False


def caculateWaypointsForSingle(requirements, speed, index):
    carInformation = requirements["carInformation"]
    laneCount = 2
    intersection = requirements["intersection"]
    T = requirements["T"]

    oPoint = search(laneCount, intersection, T, index)
    width = oPoint[4]

    lastActionList = []
    laneAndDirectionList = []
    carInfoList = []

    carInformation["V1"]["direction"] = transformDirection(carInformation["V1"]["direction"])

    if len(carInformation["V1"]["behaviors"]) == 0:
        carInformation["V1"]["behaviors"].append(["follow lane"])

    if carInformation["V1"]["direction"] == 0:
        carInformation["V1"]["direction"] = 1

    if carInformation["V1"]["laneNumber"] == 0 or carInformation["V1"]["laneNumber"] > laneCount:
        carInformation["V1"]["laneNumber"] = 1
    else:
        carInformation["V1"]["laneNumber"] = laneCount - carInformation["V1"]["laneNumber"] + 1


    if len(carInformation["V1"]["behaviors"]) > 1 and carInformation["V1"]["behaviors"][-1][0] == 'stop':
        carInformation["V1"]["behaviors"].pop()

    if T == "yes":
        carInformation["V1"]["direction"] = 1
        if carInformation["V1"]["behaviors"][-1][0] == "go across":
            carInformation["V1"]["direction"] = 2

    if intersection == "no" and T == "no":
        if carInformation["V1"]["behaviors"][-1][0] == "go across":
            carInformation["V1"]["behaviors"].pop()
            carInformation["V1"]["behaviors"].append(["follow lane"])

        if carInformation["V1"]["behaviors"][-1][0] == "turn left":
            carInformation["V1"]["behaviors"].pop()
            carInformation["V1"]["behaviors"].append(["retrograde"])

        if carInformation["V1"]["direction"] == 2:
            carInformation["V1"]["direction"] = 1
        if carInformation["V1"]["direction"] == 4:
            carInformation["V1"]["direction"] = 3

    if intersection == "yes" or T == "yes":
        if carInformation["V1"]["behaviors"][-1][0] in ["go across", "stop"] and (containsLeft(carInformation, 1) or containsRight(carInformation, 1)):
            carInformation["V1"]["behaviors"].pop()

    if containsTurnAround(carInformation["V1"]["behaviors"]) and carInformation["V1"]["behaviors"][-1][0] != "turn around":
        carInformation["V1"]["behaviors"].pop()


    curV = carInformation["V1"]
    curActions = curV["behaviors"]

    for j in range(len(curActions)):
        curAction = curActions[j]
        if len(curAction) > 1:
            if curAction[1] == 0 or curAction[1] > laneCount:
                curAction[1] = 1
            else:
                curAction[1] = laneCount - curAction[1] + 1

    carInfoList.append(curV)

    index = len(curActions) - 1
    while curActions[index][0] == "intended":
        index -= 1

    lastActionList.append(curActions[index])

    curLaneAndDirections = caculateLaneAndDirections(curActions, curV["direction"], curV["laneNumber"])
    if curLaneAndDirections == "erro":
        return [], 0, True

    laneAndDirectionList.append(curLaneAndDirections)

    crashPoint = findCrashPointForSingle(lastActionList, laneAndDirectionList, laneCount, width, intersection)


    if crashPoint == "erro" or crashPoint[0] == "erro":
        return [], 0, True

    print(crashPoint)

    if intersection == "yes" or T == "yes":
        intersection = "yes"

    waypointList = generateWaypointsForSingle(carInfoList, laneAndDirectionList, laneCount, width, crashPoint, intersection, speed)

    getFinalWaypointList(waypointList, oPoint)

    return waypointList, 0, True
