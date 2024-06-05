import math
import random
from environs import Env
import lgsvl
from lgsvl import Transform, Vector
from src.caculator import caculateWaypoints


def getVehicleWaypoints(waypoints, position, rotation):
    npc_waypoints = []
    if len(waypoints) <= 1:
        npc_waypoints.append(
            lgsvl.DriveWaypoint(position, 0, angle=rotation, idle=0))
        return npc_waypoints

    for i in range(1, len(waypoints)):
        transform_former = Vector(waypoints[i - 1][0], 10.2, waypoints[i - 1][1])
        transform = Vector(waypoints[i][0], 10.2, waypoints[i][1])

        rotation_vector = transform - transform_former
        newRotation = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector.x, rotation_vector.z)), 0)
        npc_waypoints.append(lgsvl.DriveWaypoint(transform, waypoints[i][2], angle=newRotation, idle=0))

    return npc_waypoints


def simulateReport():
    env = Env()
    sim = lgsvl.Simulator(env.str("LGSVL__SIMULATOR_HOST", lgsvl.wise.SimulatorSettings.simulator_host),
                          env.int("LGSVL__SIMULATOR_PORT", lgsvl.wise.SimulatorSettings.simulator_port))
    if sim.current_scene == lgsvl.wise.DefaultAssets.map_sanfrancisco:
        sim.reset()
    else:
        sim.load(lgsvl.wise.DefaultAssets.map_sanfrancisco)

    speed = [10, 10]
    mapIndex = random.randint(0, 2)
    waypointList, isFan, isSingle = caculateWaypoints(speed, False, mapIndex)

    if len(waypointList) == 0:
        print("construct failed.....")
        exit(0)


    if isSingle:
        position1_former = Vector(waypointList[0][0][0], 10.2, waypointList[0][0][1])
        position2_former = Vector(waypointList[1][0][0], 10.2, waypointList[1][0][1])
        rotation1 = None
        rotation2 = None

        position2 = Vector(waypointList[1][1][0], 10.2, waypointList[1][1][1])
        rotation_vector2 = position2 - position2_former
        rotation2 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)), 0)

        if len(waypointList[0]) <= 1:
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)) - 90, 0)
        else:
            position1 = Vector(waypointList[0][1][0], 10.2, waypointList[0][1][1])
            rotation_vector1 = position1 - position1_former
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector1.x, rotation_vector1.z)), 0)

        w1 = getVehicleWaypoints(waypointList[0], position1_former, rotation1)
        w2 = getVehicleWaypoints(waypointList[1], position2_former, rotation2)

        state1 = lgsvl.AgentState()
        state1.transform = Transform(position1_former, rotation1)
        npc1 = sim.add_agent("SUV", lgsvl.AgentType.NPC, state1)

        state2 = lgsvl.AgentState()
        state2.transform = Transform(position2_former, rotation2)
        npc2 = sim.add_agent("Bob", lgsvl.AgentType.PEDESTRIAN, state2)

        npc1.follow(w1)
        npc2.follow(w2)
    else:
        position1_former = Vector(waypointList[0][0][0], 10.2, waypointList[0][0][1])
        position2_former = Vector(waypointList[1][0][0], 10.2, waypointList[1][0][1])
        rotation1 = None
        rotation2 = None

        if len(waypointList[0]) <= 1:
            position2 = Vector(waypointList[1][1][0], 10.2, waypointList[1][1][1])
            rotation_vector2 = position2 - position2_former
            rotation2 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)), 0)
            if isFan:
                rotation1 = lgsvl.Vector(0, 180 + math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)), 0)
            else:
                rotation1 = rotation2
        elif len(waypointList[1]) <= 1:
            position1 = Vector(waypointList[0][1][0], 10.2, waypointList[0][1][1])
            rotation_vector1 = position1 - position1_former
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector1.x, rotation_vector1.z)), 0)
            if isFan:
                rotation2 = lgsvl.Vector(0, 180 + math.degrees(math.atan2(rotation_vector1.x, rotation_vector1.z)), 0)
            else:
                rotation2 = rotation1
        else:
            position1 = Vector(waypointList[0][1][0], 10.2, waypointList[0][1][1])
            position2 = Vector(waypointList[1][1][0], 10.2, waypointList[1][1][1])
            rotation_vector1 = position1 - position1_former
            rotation_vector2 = position2 - position2_former
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector1.x, rotation_vector1.z)), 0)
            rotation2 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)), 0)

        w1 = getVehicleWaypoints(waypointList[0], position1_former, rotation1)
        w2 = getVehicleWaypoints(waypointList[1], position2_former, rotation2)

        state1 = lgsvl.AgentState()
        state1.transform = Transform(position1_former, rotation1)
        npc1 = sim.add_agent("SUV", lgsvl.AgentType.NPC, state1)

        state2 = lgsvl.AgentState()
        state2.transform = Transform(position2_former, rotation2)
        npc2 = sim.add_agent("Sedan", lgsvl.AgentType.NPC, state2)

        npc1.follow(w1)
        npc2.follow(w2)


    cameraPosition = Vector(waypointList[0][-1][0], 100, waypointList[0][-1][1])
    cameraRotation = Vector(90, 0, 0)
    camera = Transform(cameraPosition, cameraRotation)

    sim.set_sim_camera(camera)
    sim.run(30)


simulateReport()





