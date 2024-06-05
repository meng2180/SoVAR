import random
import os
from src.gpt import getAnalysisResult, preprocessReport


def getResultFromGPT(id):
    root_path = os.path.abspath(os.path.dirname(__file__)).split('BigModelRacer-latest')[0]
    path = os.path.join(root_path, "BigModelRacer-latest/src/file/report/" + id + ".txt")
    f = open(path, "r")
    lines = f.readlines()
    f.close()

    reportContent = ""
    for line in lines:
        reportContent += line

    ppr = preprocessReport(reportContent)
    res = getAnalysisResult(ppr)
    pres = processResult(res)
    writeAnalysisResultIntoFile(pres)


def writeAnalysisResultIntoFile(result):
    fileName = os.path.join(os.path.abspath(os.path.dirname(__file__)).split('BigModelRacer-latest')[0],
                            "BigModelRacer-latest/src/file/result.txt")
    f = open(fileName, "w")
    f.write(result)
    f.close()


def processResult(result):
    start = result.index("{")
    end = result.rindex("}")
    return result[start:end + 1]


def toNum(val):
    val = str(val)
    if val[-1] == '?':
        val = val[:-1]
    return float(val)


def combine(end, waypointSet):
    newWaypoints = []

    i = len(waypointSet) - 1
    while i >= 0:
        for j in range(0, 4):
            newWaypoints.append(waypointSet[i][j])
        i -= 1

    newWaypoints.append(end)
    return newWaypoints


def caculateLaneAndDirections(behaviors, direction, laneNumber):
    pre = [direction, laneNumber]
    res = [[direction, laneNumber]]
    for i in range(len(behaviors) - 1):
        action = behaviors[i]
        if action[0] in ["follow lane", "stop", "go across", "drive into"]:
            res.append([pre[0], pre[1]])
        elif action[0] == "change lane":
            res.append([pre[0], action[1]])
        elif action[0] == "turn around":
            newDirections = [0, 3, 4, 1, 2]
            res.append([newDirections[pre[0]], action[1]])
        elif action[0] == "turn left":
            newDirections = [0, 4, 1, 2, 3]
            res.append([newDirections[pre[0]], action[1]])
        elif action[0] == "turn right":
            newDirections = [0, 2, 3, 4, 1]
            res.append([newDirections[pre[0]], action[1]])
        else:
            return "erro"
    return res


def addToX(waypointList, index, deta):
    for i in range(len(waypointList[index])):
        waypointList[index][i][0] += deta


def addToY(waypointList, index, deta):
    for i in range(len(waypointList[index])):
        waypointList[index][i][1] += deta


def isFan(direction1, direction2):
    fanDirection = [0, 3, 4, 1, 2]
    return direction2 == fanDirection[direction1]


def findGoAcrossGoAcrossDistrict(direction1, lane1, direction2, lane2, laneCount, width):
    xL = laneCount * width
    xR = laneCount * width
    yD = laneCount * width
    yU = laneCount * width

    if direction1 == 1:
        xL = (laneCount + lane1 - 1) * width
        xR = (laneCount + lane1) * width
    if direction1 == 2:
        yD = (laneCount - lane1) * width
        yU = (laneCount - lane1 + 1) * width
    if direction1 == 3:
        xL = (laneCount - lane1) * width
        xR = (laneCount - lane1 + 1) * width
    if direction1 == 4:
        yD = (laneCount + lane1 - 1) * width
        yU = (laneCount + lane1) * width

    if direction2 == 1:
        xL = (laneCount + lane2 - 1) * width
        xR = (laneCount + lane2) * width
    if direction2 == 2:
        yD = (laneCount - lane2) * width
        yU = (laneCount - lane2 + 1) * width
    if direction2 == 3:
        xL = (laneCount - lane2) * width
        xR = (laneCount - lane2 + 1) * width
    if direction2 == 4:
        yD = (laneCount + lane2 - 1) * width
        yU = (laneCount + lane2) * width

    x = round(random.uniform(xL + 1, xR - 1), 1)
    y = round(random.uniform(yD + 1, yU - 1), 1)
    return [x, y]


def findGoAcrossTurnAroundDistrict(direction1, lane1, destLane2, laneCount, width):
    bi = round(1.0 * lane1 ** 4 / (destLane2 ** 4), 2)
    xL = (laneCount - lane1) * width + 1
    xR = (laneCount - lane1 + 1) * width - 1
    x = round(random.uniform(xL, xR), 1)
    y = destLane2 * width * bi

    if direction1 == 3:
        y = - y
    if direction1 == 4:
        temp = x
        x = - y
        y = 2 * laneCount * width - temp
    if direction1 == 1:
        x = 2 * laneCount * width - x
        y = 2 * laneCount * width + y
    if direction1 == 2:
        temp = x
        x = 2 * laneCount * width + y
        y = temp

    return [x, y]


def findFollowLaneTurnAroundDistrict(direction1, lane1, destLane2, laneCount, width):
    bi = round(1.0 * lane1 ** 4 / (destLane2 ** 4), 2)
    xL = (lane1 - 1) * width + 1
    xR = lane1 * width - 1
    x = round(random.uniform(xL, xR), 1)
    y = destLane2 * width * bi

    if direction1 == 3:
        x = - x
        y = - y
    if direction1 == 4:
        temp = x
        x = - y
        y = temp
    if direction1 == 1:
        x = x
        y = y
    if direction1 == 2:
        temp = x
        x = y
        y = - temp

    return [x, y]


def findGoAcrossTurnLeftDistrict(direction1, lane1, direction2, lane2, destlane2, laneCount, width):
    xL = 0
    xR = 0
    yD = 0
    yU = 0

    if direction1 == 1:
        xL = (laneCount + lane1 - 1) * width + 1
        xR = (laneCount + lane1) * width - 1
        if direction2 == 1:
            yD = laneCount * width
            yU = (laneCount + 1) * width
        if direction2 == 2:
            deta = destlane2 - lane1
            yD = (2 * laneCount - deta - 1) * width
            yU = (2 * laneCount - deta) * width
        if direction2 == 3:
            deta = 2 * laneCount - destlane2 - lane1
            yD = deta * width
            yU = (deta + 1) * width
        if direction2 == 4:
            yD = (laneCount + lane2 - 1) * width
            yU = yD

    if direction1 == 2:
        yD = (laneCount - lane1) * width + 1
        yU = (laneCount - lane1 + 1) * width - 1
        if direction2 == 1:
            xL = (laneCount + lane2 - 1) * width
            xR = xL
        if direction2 == 2:
            xL = laneCount * width
            xR = (laneCount + 1) * width
        if direction2 == 3:
            deta = destlane2 - lane1
            xL = (2 * laneCount - deta - 1) * width
            xR = (2 * laneCount - deta) * width
        if direction2 == 4:
            deta = 2 * laneCount - destlane2 - lane1
            xL = deta * width
            xR = (deta + 1) * width

    if direction1 == 3:
        xL = (laneCount - lane1) * width + 1
        xR = (laneCount - lane1 + 1) * width - 1
        if direction2 == 1:
            deta = 2 * laneCount - destlane2 - lane1
            yD = (2 * laneCount - deta - 1) * width
            yU = (2 * laneCount - deta) * width
        if direction2 == 2:
            yD = (laneCount - lane2 + 1) * width
            yU = yD
        if direction2 == 3:
            yD = (laneCount - 1) * width
            yU = laneCount * width
        if direction2 == 4:
            deta = destlane2 - lane1
            yD = deta * width
            yU = (deta + 1) * width

    if direction1 == 4:
        yD = (laneCount + lane1 - 1) * width + 1
        yU = (laneCount + lane1) * width - 1
        if direction2 == 1:
            deta = destlane2 - lane1
            xL = deta * width
            xR = (deta + 1) * width
        if direction2 == 2:
            deta = 2 * laneCount - destlane2 - lane1
            xL = (2 * laneCount - deta - 1) * width
            xR = (2 * laneCount - deta) * width
        if direction2 == 3:
            xL = (laneCount - lane2 + 1) * width
            xR = xL
        if direction2 == 4:
            xL = (laneCount - 1) * width
            xR = laneCount * width

    x = round(random.uniform(xL, xR), 1)
    y = round(random.uniform(yD, yU), 1)
    return [x, y]


def findGoAcrossTurnRightDistrict(direction1, lane1, lane2, laneCount, width):
    xL = 0
    xR = 0
    yD = 0
    yU = 0

    if direction1 == 1:
        xL = (laneCount + lane1 - 1) * width + 1
        xR = (laneCount + lane1) * width - 1
        yD = (laneCount + lane2) * width
        yU = yD

    if direction1 == 2:
        yD = (laneCount - lane1) * width + 1
        yU = (laneCount - lane1 + 1) * width - 1
        xL = (laneCount + lane2) * width
        xR = xL

    if direction1 == 3:
        xL = (laneCount - lane1) * width + 1
        xR = (laneCount - lane1 + 1) * width - 1
        yD = (laneCount - lane2) * width
        yU = yD

    if direction1 == 4:
        yD = (laneCount + lane1 - 1) * width + 1
        yU = (laneCount + lane1) * width - 1
        xL = (laneCount - lane2) * width
        xR = xL


    x = round(random.uniform(xL, xR), 1)
    y = round(random.uniform(yD, yU), 1)
    return [x, y]


def findCrashPoint(lastActionList, laneAndDirectionList, laneCount, width, intersection):
    lastAction1 = lastActionList[0]
    lastAction2 = lastActionList[1]

    if len(lastAction1) == 1:
        lastAction1.append(1)
    if len(lastAction2) == 1:
        lastAction2.append(1)

    direction1 = laneAndDirectionList[0][-1][0]
    direction2 = laneAndDirectionList[1][-1][0]
    curLane1 = laneAndDirectionList[0][-1][1]
    curLane2 = laneAndDirectionList[1][-1][1]

    if lastAction1[0] == "change lane":
        if lastAction2[0] in ["change lane", "follow lane", "retrograde", "stop", "drive into", "halfU"]:
            destLane = lastAction1[1]
            if direction1 != direction2 and lastAction2[0] != "retrograde":
                return "erro"
            if lastAction2[0] == "change lane" and destLane != lastAction2[1]:
                lastAction2[1] = destLane
            if lastAction2[0] in ["follow lane", "stop"] and destLane != curLane2:
                destLane = curLane2
                lastAction1[1] = curLane2

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [length, 0]
                if direction1 == 2:
                    return [0, - length]
                if direction1 == 3:
                    return [- length, 0]
                if direction1 == 4:
                    return [0, length]
            else:
                if direction1 == 1:
                    return [width * laneCount + length, 0]
                if direction1 == 4:
                    return [2 * width * laneCount, width * laneCount + length]
                if direction1 == 3:
                    return [width * laneCount - length, 2 * width * laneCount]
                if direction1 == 2:
                    return [0, width * laneCount - length]

        if lastAction2[0] == "turn around":
            if not isFan(direction1, direction2):
                return "erro"

            if lastAction1[1] > lastAction2[1]:
                lastAction1[1] = lastAction2[1]

            return findFollowLaneTurnAroundDistrict(direction1, lastAction1[1], lastAction2[1], laneCount, width)

        return "erro"


    if lastAction1[0] == "follow lane":
        if lastAction2[0] in ["change lane", "follow lane", "retrograde", "stop", "drive into", "halfU"]:
            destLane = curLane1
            if direction1 != direction2 and lastAction2[0] != "retrograde":
                return "erro"
            if lastAction2[0] == "change lane" and destLane != lastAction2[1]:
                lastAction2[1] = destLane

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [length, 0]
                if direction1 == 2:
                    return [0, - length]
                if direction1 == 3:
                    return [- length, 0]
                if direction1 == 4:
                    return [0, length]
            else:
                if direction1 == 1:
                    return [width * laneCount + length, 0]
                if direction1 == 4:
                    return [2 * width * laneCount, width * laneCount + length]
                if direction1 == 3:
                    return [width * laneCount - length, 2 * width * laneCount]
                if direction1 == 2:
                    return [0, width * laneCount - length]

        if lastAction2[0] == "turn around":
            if not isFan(direction1, direction2):
                return "erro"

            if curLane1 > lastAction2[1]:
                lastAction2[1] = curLane1

            return findFollowLaneTurnAroundDistrict(direction1, curLane1, lastAction2[1], laneCount, width)

        return "erro"


    if lastAction1[0] == "go across":
        destLane = curLane1
        if lastAction2[0] in ["retrograde", "stop"]:
            if lastAction2[0] == "retrograde":
                if not isFan(direction1, direction2):
                    return "erro"

            if lastAction2[0] == "stop":
                if direction1 != direction2:
                    return "erro"

            length = round(random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
            if direction1 == 1:
                return [laneCount * width + length, 2 * laneCount * width]
            if direction1 == 2:
                return [2 * laneCount * width, laneCount * width - length]
            if direction1 == 3:
                return [laneCount * width - length, 0]
            if direction1 == 4:
                return [0, laneCount * width + length]


        if lastAction2[0] == "go across":
            if isFan(direction1, direction2) or direction1 == direction2:
                return "erro"

            return findGoAcrossGoAcrossDistrict(direction1, curLane1, direction2, curLane2, laneCount, width)

        if lastAction2[0] == "turn around":
            if not isFan(direction1, direction2):
                return "erro"

            if curLane1 > lastAction2[1]:
                lastAction2[1] = curLane1

            return findGoAcrossTurnAroundDistrict(direction1, curLane1, lastAction2[1], laneCount, width)

        if lastAction2[0] == "turn left":
            newDirections = [0, 4, 1, 2, 3]
            if direction1 == newDirections[direction2] and curLane1 > lastAction2[1]:
                lastAction2[1] = curLane1
            if direction1 == direction2 and curLane1 >= curLane2:
                curLane1 = 1
                curLane2 = 2
                laneAndDirectionList[0][-1][1] = curLane1
                laneAndDirectionList[1][-1][1] = curLane2

            return findGoAcrossTurnLeftDistrict(direction1, curLane1, direction2, curLane2, lastAction2[1], laneCount, width)

        if lastAction2[0] == "turn right":
            newDirections = [0, 2, 3, 4, 1]
            if direction1 == newDirections[direction2]:
                if curLane1 < lastAction2[1]:
                    lastAction2[1] = curLane1

                return findGoAcrossTurnRightDistrict(direction1, curLane1, curLane2, laneCount, width)

            if direction1 == direction2:
                if curLane1 <= curLane2:
                    curLane1 = 2
                    curLane2 = 1
                    laneAndDirectionList[0][-1][1] = curLane1
                    laneAndDirectionList[1][-1][1] = curLane2

                destLane = lastAction2[1]
                x = 0
                y = 0
                if direction1 == 1:
                    x = round(laneCount * width + random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
                    y = round(random.uniform((laneCount - destLane) * width + 1, (laneCount - destLane + 1) * width - 1), 1)
                if direction1 == 2:
                    y = round(random.uniform((laneCount - curLane1) * width + 1, (laneCount - curLane1 + 1) * width - 1), 1)
                    x = round(random.uniform((laneCount - destLane) * width + 1, (laneCount - destLane + 1) * width - 1), 1)
                if direction1 == 3:
                    x = round(random.uniform((laneCount - curLane1) * width + 1, (laneCount - curLane1 + 1) * width - 1), 1)
                    y = round(laneCount * width + random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
                if direction1 == 4:
                    y = round(laneCount * width + random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
                    x = round(laneCount * width + random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
                return [x, y]

        return "erro"


    if lastAction1[0] == "retrograde":

        if lastAction2[0] in ["change lane", "follow lane", "stop"]:
            destLane = curLane2
            if lastAction2[0] == "change lane":
                destLane = lastAction2[1]
            if not isFan(direction1, direction2):
                return "erro"

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction2 == 1:
                    return [length, 0]
                if direction2 == 2:
                    return [0, - length]
                if direction2 == 3:
                    return [- length, 0]
                if direction2 == 4:
                    return [0, length]
            else:
                if direction2 == 1:
                    return [width * laneCount + length, 0]
                if direction2 == 4:
                    return [2 * width * laneCount, width * laneCount + length]
                if direction2 == 3:
                    return [width * laneCount - length, 2 * width * laneCount]
                if direction2 == 2:
                    return [0, width * laneCount - length]


        if lastAction2[0] in ["go across", "turn left", "turn right"]:
            destLane = curLane2
            if lastAction2[0] == "turn left":
                destLane = lastAction2[1]
                newDirections = [0, 4, 1, 2, 3]
                if not isFan(direction1, newDirections[direction2]):
                    return "erro"
            if lastAction2[0] == "turn right":
                destLane = lastAction2[1]
                newDirections = [0, 2, 3, 4, 1]
                if not isFan(direction1, newDirections[direction2]):
                    return "erro"

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if direction1 == 1:
                return [laneCount * width - length, 0]
            if direction1 == 2:
                return [0, laneCount * width + length]
            if direction1 == 3:
                return [laneCount * width + length, 2 * laneCount * width]
            if direction1 == 4:
                return [2 * laneCount * width, laneCount * width - length]

        return "erro"


    if lastAction1[0] == "stop":
        if lastAction2[0] in ["follow lane", "change lane", "stop", "retrograde", "drive into", "halfU"]:
            if lastAction2[0] == "retrograde":
                if not isFan(direction1, direction2):
                    return "erro"
            elif direction1 != direction2:
                return "erro"
            if lastAction2[0] == "follow lane" and curLane1 != curLane2:
                curLane2 = curLane1
                laneAndDirectionList[1][-1][1] = curLane2
            if lastAction2[0] == "change lane" and curLane1 != lastAction2[1]:
                lastAction2[1] = curLane1

            length = round(random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [length, 0]
                if direction1 == 2:
                    return [0, - length]
                if direction1 == 3:
                    return [- length, 0]
                if direction1 == 4:
                    return [0, length]
            else:
                if direction1 == 1:
                    return [width * laneCount + length, 0]
                if direction1 == 4:
                    return [2 * width * laneCount, width * laneCount + length]
                if direction1 == 3:
                    return [width * laneCount - length, 2 * width * laneCount]
                if direction1 == 2:
                    return [0, width * laneCount - length]


        if lastAction2[0] == "drive off":
            if direction1 == 1:
                return [laneCount * width + width, 0]
            if direction1 == 2:
                return [0, - laneCount * width - width]
            if direction1 == 3:
                return [- laneCount * width - width, 0]
            if direction1 == 4:
                return [0, laneCount * width + width]

        return "erro"


    if lastAction1[0] == "turn around":
        if lastAction2[0] == "go across":
            if not isFan(direction1, direction2):
                return "erro"
            if lastAction1[1] < curLane2:
                lastAction1[1] = curLane2
            return findGoAcrossTurnAroundDistrict(direction2, curLane2, lastAction1[1], laneCount, width)

        if lastAction2[0] == "turn left":
            if lastAction2[1] > lastAction1[1]:
                lastAction1[1] = lastAction2[1]
            newDirections = [0, 4, 1, 2, 3]
            if not isFan(direction1, newDirections[direction2]):
                return "erro"

            return findGoAcrossTurnAroundDistrict(newDirections[direction2], lastAction2[1], lastAction1[1], laneCount, width)

        if lastAction2[0] == "turn right":
            if lastAction2[1] > lastAction1[1]:
                lastAction1[1] = lastAction2[1]
            newDirections = [0, 2, 3, 4, 1]
            if not isFan(direction1, newDirections[direction2]):
                return "erro"

            return findGoAcrossTurnAroundDistrict(newDirections[direction2], lastAction2[1], lastAction1[1], laneCount, width)

        if lastAction2[0] == "follow lane":
            if not isFan(direction1, direction2):
                return "erro"

            if curLane2 > lastAction1[1]:
                lastAction1[1] = curLane2

            return findFollowLaneTurnAroundDistrict(direction2, curLane2, lastAction1[1], laneCount, width)

        if lastAction2[0] == "change lane":
            if not isFan(direction1, direction2):
                return "erro"

            if lastAction2[1] > lastAction1[1]:
                lastAction2[1] = lastAction1[1]

            return findFollowLaneTurnAroundDistrict(direction2, lastAction2[1], lastAction1[1], laneCount, width)

        return "erro"


    if lastAction1[0] == "turn left":
        if lastAction2[0] == "go across":
            newDirections = [0, 4, 1, 2, 3]
            if direction2 == newDirections[direction1] and curLane2 > lastAction1[1]:
                lastAction1[1] = curLane2
            if direction1 == direction2 and curLane1 <= curLane2:
                curLane1 = 2
                curLane2 = 1
                laneAndDirectionList[0][-1][1] = curLane1
                laneAndDirectionList[1][-1][1] = curLane2

            return findGoAcrossTurnLeftDistrict(direction2, curLane2, direction1, curLane1, lastAction1[1], laneCount, width)

        if lastAction2[0] == "retrograde":
            newDirections = [0, 4, 1, 2, 3]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            destLane = lastAction1[1]
            length = round(random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
            if direction1 == 4:
                return [laneCount * width - length, 0]
            if direction1 == 1:
                return [0, laneCount * width + length]
            if direction1 == 2:
                return [laneCount * width + length, 2 * laneCount * width]
            if direction1 == 3:
                return [2 * laneCount * width, laneCount * width - length]

        if lastAction2[0] == "turn around":
            if lastAction1[1] > lastAction2[1]:
                lastAction2[1] = lastAction1[1]
            newDirections = [0, 4, 1, 2, 3]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            return findGoAcrossTurnAroundDistrict(newDirections[direction1], lastAction1[1], lastAction2[1], laneCount, width)

        if lastAction2[0] == "turn left":
            return [laneCount * width, laneCount * width]

        if lastAction2[0] == "turn right":
            if not isFan(direction1, direction2):
                return "erro"
            if lastAction1[1] < lastAction2[1]:
                lastAction1[1] = lastAction2[1]

            x = 0
            y = 0
            if direction1 == 1:
                x = round(random.uniform(0, width / 2), 1)
                y = round((laneCount + lastAction1[1] - 1) * width + random.uniform(0, width / 2), 1)
            if direction1 == 2:
                y = round((2 * laneCount - 1) * width + random.uniform(0, width / 2), 1)
                x = round((laneCount + lastAction1[1] - 1) * width + random.uniform(0, width / 2), 1)
            if direction1 == 3:
                x = round((2 * laneCount - 1) * width + random.uniform(0, width / 2), 1)
                y = round((laneCount - lastAction1[1] + 1) * width - random.uniform(0, width / 2), 1)
            if direction1 == 4:
                y = round(random.uniform(0, width / 2), 1)
                x = round((laneCount - lastAction1[1] + 1) * width - random.uniform(0, width / 2), 1)
            return [x, y]

        return "erro"


    if lastAction1[0] == "turn right":
        if lastAction2[0] == "go across":
            newDirections = [0, 2, 3, 4, 1]
            if direction2 == newDirections[direction1]:
                if curLane2 < lastAction1[1]:
                    lastAction1[1] = curLane2

                return findGoAcrossTurnRightDistrict(direction2, curLane2, curLane1, laneCount, width)

            if direction1 == direction2:
                if curLane2 <= curLane1:
                    curLane1 = 1
                    curLane2 = 2
                    laneAndDirectionList[0][-1][1] = curLane1
                    laneAndDirectionList[1][-1][1] = curLane2

                destLane = lastAction1[1]
                x = 0
                y = 0
                if direction1 == 1:
                    x = round(laneCount * width + random.uniform((curLane2 - 1) * width + 1, curLane2 * width - 1), 1)
                    y = round(random.uniform((laneCount - destLane) * width + 1, (laneCount - destLane + 1) * width - 1), 1)
                if direction1 == 2:
                    y = round(random.uniform((laneCount - curLane2) * width + 1, (laneCount - curLane2 + 1) * width - 1), 1)
                    x = round(random.uniform((laneCount - destLane) * width + 1, (laneCount - destLane + 1) * width - 1), 1)
                if direction1 == 3:
                    x = round(random.uniform((laneCount - curLane2) * width + 1, (laneCount - curLane2 + 1) * width - 1), 1)
                    y = round(laneCount * width + random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
                if direction1 == 4:
                    y = round(laneCount * width + random.uniform((curLane2 - 1) * width + 1,  curLane2 * width - 1), 1)
                    x = round(laneCount * width + random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
                return [x, y]


        if lastAction2[0] == "retrograde":
            newDirections = [0, 2, 3, 4, 1]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            destLane = lastAction1[1]
            length = round(random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
            if direction1 == 2:
                return [laneCount * width - length, 0]
            if direction1 == 3:
                return [0, laneCount * width + length]
            if direction1 == 4:
                return [laneCount * width + length, 2 * laneCount * width]
            if direction1 == 1:
                return [2 * laneCount * width, laneCount * width - length]

        if lastAction2[0] == "turn around":
            if lastAction1[1] > lastAction2[1]:
                lastAction2[1] = lastAction1[1]
            newDirections = [0, 2, 3, 4, 1]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            return findGoAcrossTurnAroundDistrict(newDirections[direction1], lastAction1[1], lastAction2[1], laneCount, width)

        if lastAction2[0] == "turn left":
            if not isFan(direction1, direction2) or lastAction2[1] < lastAction1[1]:
                return "erro"

            x = 0
            y = 0
            if direction1 == 3:
                x = round(random.uniform(0, width / 2), 1)
                y = round((laneCount + lastAction1[1] - 1) * width + random.uniform(0, width / 2), 1)
            if direction1 == 4:
                y = round((2 * laneCount - 1) * width + random.uniform(0, width / 2), 1)
                x = round((laneCount + lastAction1[1] - 1) * width + random.uniform(0, width / 2), 1)
            if direction1 == 1:
                x = round((2 * laneCount - 1) * width + random.uniform(0, width / 2), 1)
                y = round((laneCount - lastAction1[1] + 1) * width - random.uniform(0, width / 2), 1)
            if direction1 == 2:
                y = round(random.uniform(0, width / 2), 1)
                x = round((laneCount - lastAction1[1] + 1) * width - random.uniform(0, width / 2), 1)
            return [x, y]

        if lastAction2[0] == "turn right":
            if direction1 != direction2:
                return "erro"

            destLane = lastAction1[1]
            length = round(random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
            if direction1 == 1:
                return [2 * laneCount * width, laneCount * width - length]
            if direction1 == 2:
                return [laneCount * width - length, 0]
            if direction1 == 3:
                return [0, laneCount * width + length]
            if direction1 == 4:
                return [laneCount * width + length, 2 * laneCount * width]

        return "erro"


    if lastAction1[0] == "drive into":
        if lastAction2[0] in ["change lane", "follow lane", "stop"]:
            if direction1 != direction2:
                return "erro"

            destLane = curLane2
            if lastAction2[0] == "change lane":
                destLane = lastAction2[1]

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [length, 0]
                if direction1 == 2:
                    return [0, - length]
                if direction1 == 3:
                    return [- length, 0]
                if direction1 == 4:
                    return [0, length]
            else:
                if direction1 == 1:
                    return [width * laneCount + length, 0]
                if direction1 == 4:
                    return [2 * width * laneCount, width * laneCount + length]
                if direction1 == 3:
                    return [width * laneCount - length, 2 * width * laneCount]
                if direction1 == 2:
                    return [0, width * laneCount - length]

        return "erro"


    if lastAction1[0] == "halfU":
        if lastAction2[0] in ["change lane", "follow lane", "stop"]:
            if direction1 != direction2:
                return "erro"

            destLane = curLane2
            if lastAction2[0] == "change lane":
                destLane = lastAction2[1]

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [length, 0]
                if direction1 == 2:
                    return [0, - length]
                if direction1 == 3:
                    return [- length, 0]
                if direction1 == 4:
                    return [0, length]
            else:
                if direction1 == 1:
                    return [width * laneCount + length, 0]
                if direction1 == 4:
                    return [2 * width * laneCount, width * laneCount + length]
                if direction1 == 3:
                    return [width * laneCount - length, 2 * width * laneCount]
                if direction1 == 2:
                    return [0, width * laneCount - length]

        return "erro"


    if lastAction1[0] == "drive off":
        if lastAction2[0] != "stop":
            return "erro"

        if direction1 == 1:
            return [laneCount * width + width, 0]
        if direction1 == 2:
            return [0, - laneCount * width - width]
        if direction1 == 3:
            return [- laneCount * width - width, 0]
        if direction1 == 4:
            return [0, laneCount * width + width]

    return "erro"


def findCrashPointForSingle(lastActionList, laneAndDirectionList, laneCount, width, intersection):
    lastAction1 = lastActionList[0]

    if len(lastAction1) == 1:
        lastAction1.append(1)

    direction1 = laneAndDirectionList[0][-1][0]
    curLane1 = laneAndDirectionList[0][-1][1]


    if lastAction1[0] in ["change lane", "follow lane", "stop"]:
        destLane = lastAction1[1]
        if lastAction1[0] in ["follow lane", "stop"]:
            destLane = curLane1

        length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
        if intersection == 'no':
            if direction1 == 1:
                return [[length, 0], [(laneCount + 1) * width, 0]]
            if direction1 == 2:
                return [[0, - length], [0, - (laneCount + 1) * width]]
            if direction1 == 3:
                return [[- length, 0], [- (laneCount + 1) * width, 0]]
            if direction1 == 4:
                return [[0, length], [0, (laneCount + 1) * width]]
        else:
            if direction1 == 1:
                return [[width * laneCount + length, -10], [width * (2 * laneCount + 1), -10]]
            if direction1 == 4:
                return [[2 * width * laneCount + 10, width * laneCount + length], [2 * width * laneCount + 10, width * (2 * laneCount + 1)]]
            if direction1 == 3:
                return [[width * laneCount - length, 2 * width * laneCount + 10], [- width, 2 * width * laneCount + 10]]
            if direction1 == 2:
                return [[-10, width * laneCount - length], [-10, - width]]

        return "erro"


    if lastAction1[0] == "go across":
        destLane = curLane1

        length = round(random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
        if direction1 == 1:
            return [[laneCount * width + length, 2 * laneCount * width + 10], [(2 * laneCount + 1) * width, 2 * laneCount * width + 10]]
        if direction1 == 2:
            return [[2 * laneCount * width + 10, laneCount * width - length], [2 * laneCount * width + 10, - width]]
        if direction1 == 3:
            return [[laneCount * width - length, -10], [- width, -10]]
        if direction1 == 4:
            return [[-10, laneCount * width + length], [-10, (2 * laneCount + 1) * width]]


        return "erro"


    if lastAction1[0] == "retrograde":
        destLane = 1

        length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
        if intersection == 'no':
            if direction1 == 3:
                return [[length, 0], [(laneCount + 1) * width, 0]]
            if direction1 == 4:
                return [[0, - length], [0, - (laneCount + 1) * width]]
            if direction1 == 1:
                return [[- length, 0], [- (laneCount + 1) * width, 0]]
            if direction1 == 2:
                return [[0, length], [0, (laneCount + 1) * width]]
        else:
            if direction1 == 3:
                return [[width * laneCount + length, -10], [width * (2 * laneCount + 1), -10]]
            if direction1 == 2:
                return [[2 * width * laneCount + 10, width * laneCount + length],
                        [2 * width * laneCount + 10, width * (2 * laneCount + 1)]]
            if direction1 == 1:
                return [[width * laneCount - length, 2 * width * laneCount + 10],
                        [- width, 2 * width * laneCount + 10]]
            if direction1 == 4:
                return [[-10, width * laneCount - length], [-10, - width]]

        return "erro"


    if lastAction1[0] == "turn around":
        if intersection == "yes":
            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            if direction1 == 3:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * (2 * laneCount + 1), 2 * width * laneCount + 10]]
            if direction1 == 4:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, - width]]
            if direction1 == 1:
                return [[width * laneCount - length1, -10], [- width, -10]]
            if direction1 == 2:
                return [[-10, width * laneCount + length1], [-10, width * (2 * laneCount + 1)]]
        else:
            length1 = round(random.uniform(width * (lastAction1[1] - 1) + 1, width * lastAction1[1] - 1), 1)
            if direction1 == 3:
                return [[length1, 2 * width], [(laneCount + 1) * width, 2 * width]]
            if direction1 == 4:
                return [[2 * width, - length1], [2 * width, - (laneCount + 1) * width]]
            if direction1 == 1:
                return [[- length1, - 2 * width], [- (laneCount + 1) * width, - 2 * width]]
            if direction1 == 2:
                return [[- 2 * width, length1], [- 2 * width, (laneCount + 1) * width]]

        return "erro"


    if lastAction1[0] == "turn left":
        length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
        if direction1 == 1:
            return [[-10, width * laneCount + length1], [-10, (2 * laneCount + 1) * width]]
        if direction1 == 2:
            return [[width * laneCount + length1, 2 * width * laneCount + 10], [(2 * laneCount + 1) * width, 2 * width * laneCount + 10]]
        if direction1 == 3:
            return [[2 * width * laneCount + 10, width * laneCount - length1], [2 * width * laneCount + 10,  - width]]
        if direction1 == 4:
            return [[width * laneCount - length1, -10], [- width, -10]]

        return "erro"


    if lastAction1[0] == "turn right":
        length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
        if direction1 == 3:
            return [[-10, width * laneCount + length1], [-10, (2 * laneCount + 1) * width]]
        if direction1 == 4:
            return [[width * laneCount + length1, 2 * width * laneCount + 10],
                    [(2 * laneCount + 1) * width, 2 * width * laneCount + 10]]
        if direction1 == 1:
            return [[2 * width * laneCount + 10, width * laneCount - length1], [2 * width * laneCount + 10, - width]]
        if direction1 == 2:
            return [[width * laneCount - length1, -10], [- width, -10]]
        return "erro"


    if lastAction1[0] == "drive into":
        destLane = 1
        length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
        if intersection == 'no':
            if direction1 == 1:
                return [[length, 0], [(laneCount + 1) * width, 0]]
            if direction1 == 2:
                return [[0, - length], [0, - (laneCount + 1) * width]]
            if direction1 == 3:
                return [[- length, 0], [- (laneCount + 1) * width, 0]]
            if direction1 == 4:
                return [[0, length], [0, (laneCount + 1) * width]]
        else:
            if direction1 == 1:
                return [[width * laneCount + length, -10], [width * (2 * laneCount + 1), -10]]
            if direction1 == 4:
                return [[2 * width * laneCount + 10, width * laneCount + length],
                        [2 * width * laneCount + 10, width * (2 * laneCount + 1)]]
            if direction1 == 3:
                return [[width * laneCount - length, 2 * width * laneCount + 10],
                        [- width, 2 * width * laneCount + 10]]
            if direction1 == 2:
                return [[-10, width * laneCount - length], [-10, - width]]

        return "erro"


    if lastAction1[0] == "drive off":
        if direction1 == 1:
            return [[laneCount * width + width, 0], [laneCount * width + width, - 10]]
        if direction1 == 2:
            return [[0, - laneCount * width - width], [- 10, - laneCount * width - width]]
        if direction1 == 3:
            return [[- laneCount * width - width, 0], [- laneCount * width - width, 10]]
        if direction1 == 4:
            return [[0, laneCount * width + width], [10, laneCount * width + width]]
        return "erro"


    return "erro"



def findCrashPointForApollo(lastActionList, laneAndDirectionList, laneCount, width, intersection):
    lastAction1 = lastActionList[0]
    lastAction2 = lastActionList[1]

    if len(lastAction1) == 1:
        lastAction1.append(1)
    if len(lastAction2) == 1:
        lastAction2.append(1)

    direction1 = laneAndDirectionList[0][-1][0]
    direction2 = laneAndDirectionList[1][-1][0]
    curLane1 = laneAndDirectionList[0][-1][1]
    curLane2 = laneAndDirectionList[1][-1][1]

    if lastAction1[0] == "change lane":
        if lastAction2[0] in ["change lane", "follow lane", "retrograde", "stop", "drive into", "halfU"]:
            destLane = lastAction1[1]
            if direction1 != direction2 and lastAction2[0] != "retrograde":
                return "erro"
            if lastAction2[0] == "change lane" and destLane != lastAction2[1]:
                lastAction2[1] = destLane
            if lastAction2[0] in ["follow lane", "stop"] and destLane != curLane2:
                destLane = curLane2
                lastAction1[1] = curLane2

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [[length, 0], [length, 0]]
                if direction1 == 2:
                    return [[0, - length], [0, - length]]
                if direction1 == 3:
                    return [[- length, 0], [- length, 0]]
                if direction1 == 4:
                    return [[0, length], [0, length]]
            else:
                if direction1 == 1:
                    return [[width * laneCount + length, -10], [width * laneCount + length, -10]]
                if direction1 == 4:
                    return [[2 * width * laneCount + 10, width * laneCount + length], [2 * width * laneCount + 10, width * laneCount + length]]
                if direction1 == 3:
                    return [[width * laneCount - length, 2 * width * laneCount + 10], [width * laneCount - length, 2 * width * laneCount + 10]]
                if direction1 == 2:
                    return [[-10, width * laneCount - length], [-10, width * laneCount - length]]

        if lastAction2[0] == "turn around":
            if not isFan(direction1, direction2):
                return "erro"

            if lastAction1[1] > lastAction2[1]:
                lastAction1[1] = lastAction2[1]

            length1 = round(random.uniform(width * (lastAction1[1] - 1) + 1, width * lastAction1[1] - 1), 1)
            length2 = round(random.uniform(width * (lastAction2[1] - 1) + 1, width * lastAction2[1] - 1), 1)
            if direction1 == 1:
                return [[length1, 2 * width], [length2, 2 * width]]
            if direction1 == 2:
                return [[2 * width, - length1], [2 * width, - length2]]
            if direction1 == 3:
                return [[- length1, - 2 * width], [- length2, - 2 * width]]
            if direction1 == 4:
                return [[- 2 * width, length1], [- 2 * width, length2]]

        return "erro"


    if lastAction1[0] == "follow lane":
        if lastAction2[0] in ["change lane", "follow lane", "retrograde", "stop", "drive into", "halfU"]:
            destLane = curLane1
            if direction1 != direction2 and lastAction2[0] != "retrograde":
                return "erro"
            if lastAction2[0] == "change lane" and destLane != lastAction2[1]:
                lastAction2[1] = destLane

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [[length, 0], [length, 0]]
                if direction1 == 2:
                    return [[0, - length], [0, - length]]
                if direction1 == 3:
                    return [[- length, 0], [- length, 0]]
                if direction1 == 4:
                    return [[0, length], [0, length]]
            else:
                if direction1 == 1:
                    return [[width * laneCount + length, -10], [width * laneCount + length, -10]]
                if direction1 == 4:
                    return [[2 * width * laneCount + 10, width * laneCount + length],
                            [2 * width * laneCount + 10, width * laneCount + length]]
                if direction1 == 3:
                    return [[width * laneCount - length, 2 * width * laneCount + 10],
                            [width * laneCount - length, 2 * width * laneCount + 10]]
                if direction1 == 2:
                    return [[-10, width * laneCount - length], [-10, width * laneCount - length]]

        if lastAction2[0] == "turn around":
            if not isFan(direction1, direction2):
                return "erro"

            if curLane1 > lastAction2[1]:
                lastAction2[1] = curLane1

            length1 = round(random.uniform(width * (curLane1 - 1) + 1, width * curLane1 - 1), 1)
            length2 = round(random.uniform(width * (lastAction2[1] - 1) + 1, width * lastAction2[1] - 1), 1)
            if direction1 == 1:
                return [[length1, 2 * width], [length2, 2 * width]]
            if direction1 == 2:
                return [[2 * width, - length1], [2 * width, - length2]]
            if direction1 == 3:
                return [[- length1, - 2 * width], [- length2, - 2 * width]]
            if direction1 == 4:
                return [[- 2 * width, length1], [- 2 * width, length2]]

        return "erro"


    if lastAction1[0] == "go across":
        if lastAction2[0] in ["retrograde", "stop"]:
            destLane = curLane1
            if lastAction2[0] == "retrograde":
                if not isFan(direction1, direction2):
                    return "erro"

            if lastAction2[0] == "stop":
                if direction1 != direction2:
                    return "erro"

            length = round(random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
            if direction1 == 1:
                return [[laneCount * width + length, 2 * laneCount * width + 10], [laneCount * width + length, 2 * laneCount * width + 10]]
            if direction1 == 2:
                return [[2 * laneCount * width + 10, laneCount * width - length], [2 * laneCount * width + 10, laneCount * width - length]]
            if direction1 == 3:
                return [[laneCount * width - length, -10], [laneCount * width - length, -10]]
            if direction1 == 4:
                return [[-10, laneCount * width + length], [-10, laneCount * width + length]]


        if lastAction2[0] == "go across":
            if isFan(direction1, direction2):
                return "erro"

            res = []
            length1 = round(random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
            if direction1 == 1:
                res.append([width * laneCount + length1, 2 * width * laneCount + 10])
            if direction1 == 2:
                res.append([2 * width * laneCount + 10, width * laneCount - length1])
            if direction1 == 3:
                res.append([width * laneCount - length1, -10])
            if direction1 == 4:
                res.append([-10, width * laneCount + length1])

            length2 = round(random.uniform((curLane2 - 1) * width + 1, curLane2 * width - 1), 1)
            if direction2 == 1:
                res.append([width * laneCount + length2, 2 * width * laneCount + 10])
            if direction2 == 2:
                res.append([2 * width * laneCount + 10, width * laneCount - length2])
            if direction2 == 3:
                res.append([width * laneCount - length2, -10])
            if direction2 == 4:
                res.append([-10, width * laneCount + length2])
            return res


        if lastAction2[0] == "turn around":
            if not isFan(direction1, direction2):
                return "erro"

            if curLane1 > lastAction2[1]:
                lastAction2[1] = curLane1

            length1 = round(random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction1 == 1:
                return [[width * laneCount + length1, 2 * width * laneCount + 10], [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction1 == 2:
                return [[2 * width * laneCount + 10, width * laneCount - length1], [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction1 == 3:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction1 == 4:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        if lastAction2[0] == "turn left":
            newDirections = [0, 4, 1, 2, 3]
            if direction1 == newDirections[direction2] and curLane1 > lastAction2[1]:
                lastAction2[1] = curLane1
            if direction1 == direction2 and curLane1 >= curLane2:
                curLane1 = 1
                curLane2 = 2
                laneAndDirectionList[0][-1][1] = curLane1
                laneAndDirectionList[1][-1][1] = curLane2

            res = []
            length1 = round(random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
            if direction1 == 1:
                res.append([width * laneCount + length1, 2 * width * laneCount + 10])
            if direction1 == 2:
                res.append([2 * width * laneCount + 10, width * laneCount - length1])
            if direction1 == 3:
                res.append([width * laneCount - length1, -10])
            if direction1 == 4:
                res.append([-10, width * laneCount + length1])

            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction2 == 1:
                res.append([-10, width * laneCount + length2])
            if direction2 == 2:
                res.append([width * laneCount + length2, 2 * width * laneCount + 10])
            if direction2 == 3:
                res.append([2 * width * laneCount + 10, width * laneCount - length2])
            if direction2 == 4:
                res.append([width * laneCount - length2, -10])
            return res


        if lastAction2[0] == "turn right":
            newDirections = [0, 2, 3, 4, 1]
            if direction1 == newDirections[direction2]:
                if curLane1 < lastAction2[1]:
                    lastAction2[1] = curLane1

                res = []
                length1 = round(random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
                length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
                if direction1 == 1:
                    res.append([width * laneCount + length1, 2 * width * laneCount + 10])
                    res.append([width * laneCount + length2, 2 * width * laneCount + 10])
                if direction1 == 2:
                    res.append([2 * width * laneCount + 10, width * laneCount - length1])
                    res.append([2 * width * laneCount + 10, width * laneCount - length2])
                if direction1 == 3:
                    res.append([width * laneCount - length1, -10])
                    res.append([width * laneCount - length2, -10])
                if direction1 == 4:
                    res.append([-10, width * laneCount + length1])
                    res.append([-10, width * laneCount + length2])
                return res


            if direction1 == direction2:
                if curLane1 <= curLane2:
                    curLane1 = 2
                    curLane2 = 1
                    laneAndDirectionList[0][-1][1] = curLane1
                    laneAndDirectionList[1][-1][1] = curLane2

                res = []
                length1 = round(random.uniform((curLane1 - 1) * width + 1, curLane1 * width - 1), 1)
                length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
                if direction1 == 1:
                    res.append([width * laneCount + length1, 2 * width * laneCount + 10])
                    res.append([2 * width * laneCount + 10, width * laneCount - length2])
                if direction1 == 2:
                    res.append([2 * width * laneCount + 10, width * laneCount - length1])
                    res.append([width * laneCount - length2, -10])
                if direction1 == 3:
                    res.append([width * laneCount - length1, -10])
                    res.append([-10, width * laneCount + length2])
                if direction1 == 4:
                    res.append([-10, width * laneCount + length1])
                    res.append([width * laneCount + length2, 2 * width * laneCount + 10])
                return res


        return "erro"


    if lastAction1[0] == "retrograde":
        if lastAction2[0] in ["change lane", "follow lane", "stop"]:
            destLane = curLane2
            if lastAction2[0] == "change lane":
                destLane = lastAction2[1]
            if not isFan(direction1, direction2):
                return "erro"

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction2 == 1:
                    return [[length, 0], [length, 0]]
                if direction2 == 2:
                    return [[0, - length], [0, - length]]
                if direction2 == 3:
                    return [[- length, 0], [- length, 0]]
                if direction2 == 4:
                    return [[0, length], [0, length]]
            else:
                if direction2 == 1:
                    return [[width * laneCount + length, -10], [width * laneCount + length, -10]]
                if direction2 == 4:
                    return [[2 * width * laneCount + 10, width * laneCount + length],
                            [2 * width * laneCount + 10, width * laneCount + length]]
                if direction2 == 3:
                    return [[width * laneCount - length, 2 * width * laneCount + 10],
                            [width * laneCount - length, 2 * width * laneCount + 10]]
                if direction2 == 2:
                    return [[-10, width * laneCount - length], [-10, width * laneCount - length]]


        if lastAction2[0] in ["go across", "turn left", "turn right"]:
            destLane = curLane2
            if lastAction2[0] == "turn left":
                destLane = lastAction2[1]
                newDirections = [0, 4, 1, 2, 3]
                if not isFan(direction1, newDirections[direction2]):
                    return "erro"
            if lastAction2[0] == "turn right":
                destLane = lastAction2[1]
                newDirections = [0, 2, 3, 4, 1]
                if not isFan(direction1, newDirections[direction2]):
                    return "erro"

            length = round(random.uniform((destLane - 1) * width + 1, destLane * width - 1), 1)
            if direction1 == 3:
                return [[laneCount * width + length, 2 * laneCount * width + 10],
                        [laneCount * width + length, 2 * laneCount * width + 10]]
            if direction1 == 4:
                return [[2 * laneCount * width + 10, laneCount * width - length],
                        [2 * laneCount * width + 10, laneCount * width - length]]
            if direction1 == 1:
                return [[laneCount * width - length, -10], [laneCount * width - length, -10]]
            if direction1 == 2:
                return [[-10, laneCount * width + length], [-10, laneCount * width + length]]

        return "erro"


    if lastAction1[0] == "stop":
        if lastAction2[0] in ["follow lane", "change lane", "stop", "retrograde", "drive into", "halfU"]:
            if lastAction2[0] == "retrograde":
                if not isFan(direction1, direction2):
                    return "erro"
            elif direction1 != direction2:
                return "erro"
            if lastAction2[0] == "follow lane" and curLane1 != curLane2:
                curLane2 = curLane1
                laneAndDirectionList[1][-1][1] = curLane2
            if lastAction2[0] == "change lane" and curLane1 != lastAction2[1]:
                lastAction2[1] = curLane1

            length = round(random.uniform(width * (curLane1 - 1) + 1, width * curLane1 - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [[length, 0], [length, 0]]
                if direction1 == 2:
                    return [[0, - length], [0, - length]]
                if direction1 == 3:
                    return [[- length, 0], [- length, 0]]
                if direction1 == 4:
                    return [[0, length], [0, length]]
            else:
                if direction1 == 1:
                    return [[width * laneCount + length, -10], [width * laneCount + length, -10]]
                if direction1 == 4:
                    return [[2 * width * laneCount + 10, width * laneCount + length],
                            [2 * width * laneCount + 10, width * laneCount + length]]
                if direction1 == 3:
                    return [[width * laneCount - length, 2 * width * laneCount + 10],
                            [width * laneCount - length, 2 * width * laneCount + 10]]
                if direction1 == 2:
                    return [[-10, width * laneCount - length], [-10, width * laneCount - length]]


        if lastAction2[0] == "drive off":
            if direction1 == 1:
                return [[laneCount * width + width, 0], [laneCount * width + width, 0]]
            if direction1 == 2:
                return [[0, - laneCount * width - width], [0, - laneCount * width - width]]
            if direction1 == 3:
                return [[- laneCount * width - width, 0], [- laneCount * width - width, 0]]
            if direction1 == 4:
                return [[0, laneCount * width + width], [0, laneCount * width + width]]

        return "erro"


    if lastAction1[0] == "turn around":
        if lastAction2[0] == "go across":
            if not isFan(direction1, direction2):
                return "erro"
            if lastAction1[1] < curLane2:
                lastAction1[1] = curLane2

            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            length2 = round(random.uniform((curLane2 - 1) * width + 1, curLane2 * width - 1), 1)
            if direction1 == 3:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction1 == 4:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction1 == 1:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction1 == 2:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        if lastAction2[0] == "turn left":
            if lastAction2[1] > lastAction1[1]:
                lastAction1[1] = lastAction2[1]
            newDirections = [0, 4, 1, 2, 3]
            if not isFan(direction1, newDirections[direction2]):
                return "erro"

            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction1 == 3:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction1 == 4:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction1 == 1:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction1 == 2:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        if lastAction2[0] == "turn right":
            if lastAction2[1] > lastAction1[1]:
                lastAction1[1] = lastAction2[1]
            newDirections = [0, 2, 3, 4, 1]
            if not isFan(direction1, newDirections[direction2]):
                return "erro"

            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction1 == 3:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction1 == 4:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction1 == 1:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction1 == 2:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        if lastAction2[0] == "follow lane":
            if not isFan(direction1, direction2):
                return "erro"

            if curLane2 > lastAction1[1]:
                lastAction1[1] = curLane2

            length1 = round(random.uniform(width * (lastAction1[1] - 1) + 1, width * lastAction1[1] - 1), 1)
            length2 = round(random.uniform(width * (curLane2 - 1) + 1, width * curLane2 - 1), 1)
            if direction1 == 3:
                return [[length1, 2 * width], [length2, 2 * width]]
            if direction1 == 4:
                return [[2 * width, - length1], [2 * width, - length2]]
            if direction1 == 1:
                return [[- length1, - 2 * width], [- length2, - 2 * width]]
            if direction1 == 2:
                return [[- 2 * width, length1], [- 2 * width, length2]]


        if lastAction2[0] == "change lane":
            if not isFan(direction1, direction2):
                return "erro"

            if lastAction2[1] > lastAction1[1]:
                lastAction2[1] = lastAction1[1]

            length1 = round(random.uniform(width * (lastAction1[1] - 1) + 1, width * lastAction1[1] - 1), 1)
            length2 = round(random.uniform(width * (lastAction2[1] - 1) + 1, width * lastAction2[1] - 1), 1)
            if direction1 == 3:
                return [[length1, 2 * width], [length2, 2 * width]]
            if direction1 == 4:
                return [[2 * width, - length1], [2 * width, - length2]]
            if direction1 == 1:
                return [[- length1, - 2 * width], [- length2, - 2 * width]]
            if direction1 == 2:
                return [[- 2 * width, length1], [- 2 * width, length2]]

        return "erro"


    if lastAction1[0] == "turn left":
        if lastAction2[0] == "go across":
            newDirections = [0, 4, 1, 2, 3]
            if direction2 == newDirections[direction1] and curLane2 > lastAction1[1]:
                lastAction1[1] = curLane2
            if direction1 == direction2 and curLane1 <= curLane2:
                curLane1 = 2
                curLane2 = 1
                laneAndDirectionList[0][-1][1] = curLane1
                laneAndDirectionList[1][-1][1] = curLane2

            res = []
            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            if direction1 == 1:
                res.append([-10, width * laneCount + length1])
            if direction1 == 2:
                res.append([width * laneCount + length1, 2 * width * laneCount + 10])
            if direction1 == 3:
                res.append([2 * width * laneCount + 10, width * laneCount - length1])
            if direction1 == 4:
                res.append([width * laneCount - length1, -10])

            length2 = round(random.uniform((curLane2 - 1) * width + 1, curLane2 * width - 1), 1)
            if direction2 == 1:
                res.append([width * laneCount + length2, 2 * width * laneCount + 10])
            if direction2 == 2:
                res.append([2 * width * laneCount + 10, width * laneCount - length2])
            if direction2 == 3:
                res.append([width * laneCount - length2, -10])
            if direction2 == 4:
                res.append([-10, width * laneCount + length2])
            return res


        if lastAction2[0] == "retrograde":
            newDirections = [0, 4, 1, 2, 3]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            length = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            if direction2 == 3:
                return [[laneCount * width + length, 2 * laneCount * width + 10],
                        [laneCount * width + length, 2 * laneCount * width + 10]]
            if direction2 == 4:
                return [[2 * laneCount * width + 10, laneCount * width - length],
                        [2 * laneCount * width + 10, laneCount * width - length]]
            if direction2 == 1:
                return [[laneCount * width - length, -10], [laneCount * width - length, -10]]
            if direction2 == 2:
                return [[-10, laneCount * width + length], [-10, laneCount * width + length]]


        if lastAction2[0] == "turn around":
            if lastAction1[1] > lastAction2[1]:
                lastAction2[1] = lastAction1[1]
            newDirections = [0, 4, 1, 2, 3]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction2 == 3:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction2 == 4:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction2 == 1:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction2 == 2:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        if lastAction2[0] == "turn left":
            res = []
            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            if direction1 == 1:
                res.append([-10, width * laneCount + length1])
            if direction1 == 2:
                res.append([width * laneCount + length1, 2 * width * laneCount + 10])
            if direction1 == 3:
                res.append([2 * width * laneCount + 10, width * laneCount - length1])
            if direction1 == 4:
                res.append([width * laneCount - length1, -10])

            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction2 == 1:
                res.append([-10, width * laneCount + length1])
            if direction2 == 2:
                res.append([width * laneCount + length1, 2 * width * laneCount + 10])
            if direction2 == 3:
                res.append([2 * width * laneCount + 10, width * laneCount - length1])
            if direction2 == 4:
                res.append([width * laneCount - length1, -10])
            return res


        if lastAction2[0] == "turn right":
            if not isFan(direction1, direction2):
                return "erro"
            if lastAction1[1] < lastAction2[1]:
                lastAction1[1] = lastAction2[1]

            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction1 == 2:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction1 == 3:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction1 == 4:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction1 == 1:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        return "erro"


    if lastAction1[0] == "turn right":
        if lastAction2[0] == "go across":
            newDirections = [0, 2, 3, 4, 1]
            if direction2 == newDirections[direction1]:
                if curLane2 < lastAction1[1]:
                    lastAction1[1] = curLane2

                res = []
                length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
                length2 = round(random.uniform((curLane2 - 1) * width + 1, curLane2 * width - 1), 1)
                if direction2 == 1:
                    res.append([width * laneCount + length1, 2 * width * laneCount + 10])
                    res.append([width * laneCount + length2, 2 * width * laneCount + 10])
                if direction2 == 2:
                    res.append([2 * width * laneCount + 10, width * laneCount - length1])
                    res.append([2 * width * laneCount + 10, width * laneCount - length2])
                if direction2 == 3:
                    res.append([width * laneCount - length1, -10])
                    res.append([width * laneCount - length2, -10])
                if direction2 == 4:
                    res.append([-10, width * laneCount + length1])
                    res.append([-10, width * laneCount + length2])
                return res

            if direction1 == direction2:
                if curLane2 <= curLane1:
                    curLane1 = 1
                    curLane2 = 2
                    laneAndDirectionList[0][-1][1] = curLane1
                    laneAndDirectionList[1][-1][1] = curLane2

                res = []
                length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
                length2 = round(random.uniform((curLane2 - 1) * width + 1, curLane2 * width - 1), 1)
                if direction2 == 1:
                    res.append([2 * width * laneCount + 10, width * laneCount - length2])
                    res.append([width * laneCount + length1, 2 * width * laneCount + 10])
                if direction2 == 2:
                    res.append([width * laneCount - length2, -10])
                    res.append([2 * width * laneCount + 10, width * laneCount - length1])
                if direction2 == 3:
                    res.append([-10, width * laneCount + length2])
                    res.append([width * laneCount - length1, -10])
                if direction2 == 4:
                    res.append([width * laneCount + length2, 2 * width * laneCount + 10])
                    res.append([-10, width * laneCount + length1])
                return res


        if lastAction2[0] == "retrograde":
            newDirections = [0, 2, 3, 4, 1]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            length = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            if direction2 == 3:
                return [[laneCount * width + length, 2 * laneCount * width + 10],
                        [laneCount * width + length, 2 * laneCount * width + 10]]
            if direction2 == 4:
                return [[2 * laneCount * width + 10, laneCount * width - length],
                        [2 * laneCount * width + 10, laneCount * width - length]]
            if direction2 == 1:
                return [[laneCount * width - length, -10], [laneCount * width - length, -10]]
            if direction2 == 2:
                return [[-10, laneCount * width + length], [-10, laneCount * width + length]]


        if lastAction2[0] == "turn around":
            if lastAction1[1] > lastAction2[1]:
                lastAction2[1] = lastAction1[1]
            newDirections = [0, 2, 3, 4, 1]
            if not isFan(direction2, newDirections[direction1]):
                return "erro"

            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction2 == 3:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction2 == 4:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction2 == 1:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction2 == 2:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        if lastAction2[0] == "turn left":
            if not isFan(direction1, direction2) or lastAction2[1] < lastAction1[1]:
                return "erro"

            length1 = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            length2 = round(random.uniform((lastAction2[1] - 1) * width + 1, lastAction2[1] * width - 1), 1)
            if direction2 == 2:
                return [[width * laneCount + length1, 2 * width * laneCount + 10],
                        [width * laneCount + length2, 2 * width * laneCount + 10]]
            if direction2 == 3:
                return [[2 * width * laneCount + 10, width * laneCount - length1],
                        [2 * width * laneCount + 10, width * laneCount - length2]]
            if direction2 == 4:
                return [[width * laneCount - length1, -10], [width * laneCount - length2, -10]]
            if direction2 == 1:
                return [[-10, width * laneCount + length1], [-10, width * laneCount + length2]]


        if lastAction2[0] == "turn right":
            if direction1 != direction2:
                return "erro"

            length = round(random.uniform((lastAction1[1] - 1) * width + 1, lastAction1[1] * width - 1), 1)
            if direction1 == 1:
                return [[2 * laneCount * width + 10, laneCount * width - length], [2 * laneCount * width + 10, laneCount * width - length]]
            if direction1 == 2:
                return [[laneCount * width - length, -10], [laneCount * width - length, -10]]
            if direction1 == 3:
                return [[-10, laneCount * width + length], [-10, laneCount * width + length]]
            if direction1 == 4:
                return [[laneCount * width + length, 2 * laneCount * width + 10], [laneCount * width + length, 2 * laneCount * width + 10]]

        return "erro"


    if lastAction1[0] == "drive into":
        if lastAction2[0] in ["change lane", "follow lane", "stop"]:
            if direction1 != direction2:
                return "erro"

            destLane = curLane2
            if lastAction2[0] == "change lane":
                destLane = lastAction2[1]

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [[length, 0], [length, 0]]
                if direction1 == 2:
                    return [[0, - length], [0, - length]]
                if direction1 == 3:
                    return [[- length, 0], [- length, 0]]
                if direction1 == 4:
                    return [[0, length], [0, length]]
            else:
                if direction1 == 1:
                    return [[width * laneCount + length, -10], [width * laneCount + length, -10]]
                if direction1 == 4:
                    return [[2 * width * laneCount + 10, width * laneCount + length],
                            [2 * width * laneCount + 10, width * laneCount + length]]
                if direction1 == 3:
                    return [[width * laneCount - length, 2 * width * laneCount + 10],
                            [width * laneCount - length, 2 * width * laneCount + 10]]
                if direction1 == 2:
                    return [[-10, width * laneCount - length], [-10, width * laneCount - length]]

        return "erro"


    if lastAction1[0] == "halfU":
        if lastAction2[0] in ["change lane", "follow lane", "stop"]:
            if direction1 != direction2:
                return "erro"

            destLane = curLane2
            if lastAction2[0] == "change lane":
                destLane = lastAction2[1]

            length = round(random.uniform(width * (destLane - 1) + 1, width * destLane - 1), 1)
            if intersection == 'no':
                if direction1 == 1:
                    return [[length, 0], [length, 0]]
                if direction1 == 2:
                    return [[0, - length], [0, - length]]
                if direction1 == 3:
                    return [[- length, 0], [- length, 0]]
                if direction1 == 4:
                    return [[0, length], [0, length]]
            else:
                if direction1 == 1:
                    return [[width * laneCount + length, -10], [width * laneCount + length, -10]]
                if direction1 == 4:
                    return [[2 * width * laneCount + 10, width * laneCount + length],
                            [2 * width * laneCount + 10, width * laneCount + length]]
                if direction1 == 3:
                    return [[width * laneCount - length, 2 * width * laneCount + 10],
                            [width * laneCount - length, 2 * width * laneCount + 10]]
                if direction1 == 2:
                    return [[-10, width * laneCount - length], [-10, width * laneCount - length]]

        return "erro"


    if lastAction1[0] == "drive off":
        if lastAction2[0] != "stop":
            return "erro"

        if direction1 == 1:
            return [[laneCount * width + width, 0], [laneCount * width + width, 0]]
        if direction1 == 2:
            return [[0, - laneCount * width - width], [0, - laneCount * width - width]]
        if direction1 == 3:
            return [[- laneCount * width - width, 0], [- laneCount * width - width, 0]]
        if direction1 == 4:
            return [[0, laneCount * width + width], [0, laneCount * width + width]]

    return "erro"