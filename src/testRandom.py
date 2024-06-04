import math
import random
import time

from lgsvl import Transform, Vector
from datetime import datetime
from environs import Env
import lgsvl
from src.caculator import caculateWaypoints


def solveNpc(crashPoint):
    x = crashPoint[0]
    y = crashPoint[1]
    xl = x - 5
    xr = x + 5
    yd = y - 5
    yu = y + 5

    endX = round(random.uniform(xl, xr), 2)
    endY = round(random.uniform(yd, yu), 2)

    xl = x - 30
    xr = x + 30
    yd = y - 30
    yu = y + 30

    startX = round(random.uniform(xl, xr), 2)
    startY = round(random.uniform(yd, yu), 2)

    return [[startX, startY], [endX, endY]]


def getNpcWaypoints(npcPoint, speed):
    startX = npcPoint[0][0]
    startY = npcPoint[0][1]
    detaX = (npcPoint[1][0] - npcPoint[0][0]) / 4.0
    detaY = (npcPoint[1][1] - npcPoint[0][1]) / 4.0

    waypoints = []
    for i in range(5):
        waypoints.append([startX + i * detaX, startY + i * detaY, speed])

    return waypoints


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
        npc_waypoints.append(
            lgsvl.DriveWaypoint(transform, waypoints[i][2], angle=newRotation, idle=0))

    return npc_waypoints


def on_collision(agent1, agent2, contact):
    raise Exception("{} collided with {}".format(agent1, agent2))
    sys.exit()


def testApolloRandom(tag):
    env = Env()

    SIMULATOR_HOST = env.str("LGSVL__SIMULATOR_HOST", "127.0.0.1")
    SIMULATOR_PORT = env.int("LGSVL__SIMULATOR_PORT", 8181)
    BRIDGE_HOST = env.str("LGSVL__AUTOPILOT_0_HOST", "127.0.0.1")
    BRIDGE_PORT = env.int("LGSVL__AUTOPILOT_0_PORT", 9090)

    LGSVL__AUTOPILOT_HD_MAP = env.str("LGSVL__AUTOPILOT_HD_MAP", "SanFrancisco")
    LGSVL__AUTOPILOT_0_VEHICLE_CONFIG = env.str("LGSVL__AUTOPILOT_0_VEHICLE_CONFIG", 'Lincoln2017MKZ')
    LGSVL__SIMULATION_DURATION_SECS = 50.0

    vehicle_conf = env.str("LGSVL__VEHICLE_0", lgsvl.wise.DefaultAssets.ego_lincoln2017mkz_apollo6_modular)
    scene_name = env.str("LGSVL__MAP", lgsvl.wise.DefaultAssets.map_sanfrancisco_correct)
    sim = lgsvl.Simulator(SIMULATOR_HOST, SIMULATOR_PORT)

    if sim.current_scene == scene_name:
        sim.reset()
    else:
        sim.load(scene_name)

    sim.set_date_time(datetime(2022, 6, 22, 11, 0, 0, 0), True)

    speed = [2, 2]
    mapIndex = random.randint(0, 2)
    waypointList, isFan, isSingle = caculateWaypoints(speed, True, mapIndex)

    if len(waypointList) == 0:
        print("construct failed.....")
        exit(0)

    if isSingle:
        position1_former = Vector(waypointList[0][0][0], 10.2, waypointList[0][0][1])
        position2_former = Vector(waypointList[1][0][0], 10.2, waypointList[1][0][1])

        position2 = Vector(waypointList[1][1][0], 10.2, waypointList[1][1][1])
        rotation_vector2 = position2 - position2_former

        if len(waypointList[0]) <= 1:
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)) - 90, 0)
        else:
            position1 = Vector(waypointList[0][1][0], 10.2, waypointList[0][1][1])
            rotation_vector1 = position1 - position1_former
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector1.x, rotation_vector1.z)), 0)

        crashPoint = [waypointList[0][-1][0], waypointList[0][-1][1]]

        egoState = lgsvl.AgentState()
        egoState.transform = Transform(position1_former, rotation1)
        destination = [waypointList[0][-1][0], waypointList[0][-1][1]]
    else:
        position1_former = Vector(waypointList[0][0][0], 10.2, waypointList[0][0][1])
        position2_former = Vector(waypointList[1][0][0], 10.2, waypointList[1][0][1])

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

        if tag == 1:
            crashPoint = [waypointList[0][-1][0], waypointList[0][-1][1]]

            egoState = lgsvl.AgentState()
            egoState.transform = Transform(position1_former, rotation1)
            destination = [waypointList[0][-1][0], waypointList[0][-1][1]]
        else:
            crashPoint = [waypointList[1][-1][0], waypointList[1][-1][1]]

            egoState = lgsvl.AgentState()
            egoState.transform = Transform(position2_former, rotation2)
            destination = [waypointList[1][-1][0], waypointList[1][-1][1]]


    npcPoint = solveNpc(crashPoint)
    npcWaypoints = getVehicleWaypoints(getNpcWaypoints(npcPoint, speed[0]), Vector(0, 0, 0), Vector(0, 0, 0))
    npcStart = Vector(npcPoint[0][0], 10.2, npcPoint[0][1])
    npcRotationVector = Vector(npcPoint[1][0], 10.2, npcPoint[1][1]) - npcStart
    npcRotation = lgsvl.Vector(0, math.degrees(math.atan2(npcRotationVector.x, npcRotationVector.z)), 0)
    npcState = lgsvl.AgentState()
    npcState.transform = Transform(npcStart, npcRotation)

    if isSingle:
        npc = sim.add_agent("SUV", lgsvl.AgentType.PEDESTRIAN, npcState)
    else:
        npc = sim.add_agent("SUV", lgsvl.AgentType.NPC, npcState)

    npc.follow(npcWaypoints)

    print("Loading vehicle {}...".format(vehicle_conf))
    ego = sim.add_agent(vehicle_conf, lgsvl.AgentType.EGO, egoState)
    print("Connecting to bridge...")
    ego.connect_bridge(BRIDGE_HOST, BRIDGE_PORT)
    ego.on_collision(on_collision)

    dv = lgsvl.dreamview.Connection(sim, ego, BRIDGE_HOST)
    dv.set_hd_map(LGSVL__AUTOPILOT_HD_MAP)
    dv.set_vehicle(LGSVL__AUTOPILOT_0_VEHICLE_CONFIG)

    default_modules = [
        'Localization',
        'Transform',
        'Routing',
        'Prediction',
        'Planning',
        'Control',
        'Recorder'
    ]

    dv.disable_apollo()
    time.sleep(5)
    dv.setup_apollo(destination[0], destination[1], default_modules)


    cameraPosition = Vector(destination[0], 80, destination[1])
    cameraRotation = Vector(90, 0, 0)
    camera = Transform(cameraPosition, cameraRotation)
    sim.set_sim_camera(camera)

    sim.run(LGSVL__SIMULATION_DURATION_SECS)


testApolloRandom(1)