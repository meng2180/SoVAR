import json
import os
from src.solver.spin import solveSpin


def search(laneCount, intersection, T, index):
    root_path = os.path.abspath(os.path.dirname(__file__)).split('BigModelRacer-latest')[0]
    path = os.path.join(root_path, "BigModelRacer-latest/src/file/map.txt")
    f = open(path, encoding='utf-8')
    requirements = json.load(f)
    f.close()

    if T == 'yes':
        return requirements["T"][laneCount - 1][index]
    if intersection == 'yes':
        return requirements["intersection"][laneCount - 1][index]
    else:
        return requirements["straight"][laneCount - 1][index]


def getFinalWaypointList(waypointList, oPoint):
    vectorX = oPoint[2] - oPoint[0]
    vectorY = oPoint[3] - oPoint[1]

    for i in range(len(waypointList)):
        for j in range(len(waypointList[i])):
            waypointList[i][j][0], waypointList[i][j][1] = solveSpin(waypointList[i][j][0], waypointList[i][j][1], vectorX, vectorY)
            waypointList[i][j][0] += oPoint[0]
            waypointList[i][j][1] += oPoint[1]