import math
import time
import random
from lgsvl import Transform, Vector
from datetime import datetime
from environs import Env
import lgsvl
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
        npc_waypoints.append(
            lgsvl.DriveWaypoint(transform, waypoints[i][2], angle=newRotation, idle=0))

    return npc_waypoints


def on_collision(agent1, agent2, contact):
    raise Exception("{} collided with {}".format(agent1, agent2))
    sys.exit()


def testApollo(tag):
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

    if tag == 1:
        speed = [2, 10]
    else:
        speed = [10, 2]

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
        rotation2 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)), 0)

        if len(waypointList[0]) <= 1:
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector2.x, rotation_vector2.z)) - 90, 0)
        else:
            position1 = Vector(waypointList[0][1][0], 10.2, waypointList[0][1][1])
            rotation_vector1 = position1 - position1_former
            rotation1 = lgsvl.Vector(0, math.degrees(math.atan2(rotation_vector1.x, rotation_vector1.z)), 0)

        w1 = getVehicleWaypoints(waypointList[1], position2_former, rotation2)
        state1 = lgsvl.AgentState()
        state1.transform = Transform(position2_former, rotation2)
        npc = sim.add_agent("Bob", lgsvl.AgentType.PEDESTRIAN, state1)
        npc.follow(w1)

        state2 = lgsvl.AgentState()
        state2.transform = Transform(position1_former, rotation1)
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

        if tag == 2:
            w1 = getVehicleWaypoints(waypointList[0], position1_former, rotation1)
            state1 = lgsvl.AgentState()
            state1.transform = Transform(position1_former, rotation1)
            npc = sim.add_agent("SUV", lgsvl.AgentType.NPC, state1)
            npc.follow(w1)

            state2 = lgsvl.AgentState()
            state2.transform = Transform(position2_former, rotation2)
            destination = [waypointList[1][-1][0], waypointList[1][-1][1]]
        else:
            w1 = getVehicleWaypoints(waypointList[1], position2_former, rotation2)
            state1 = lgsvl.AgentState()
            state1.transform = Transform(position2_former, rotation2)
            npc = sim.add_agent("SUV", lgsvl.AgentType.NPC, state1)
            npc.follow(w1)

            state2 = lgsvl.AgentState()
            state2.transform = Transform(position1_former, rotation1)
            destination = [waypointList[0][-1][0], waypointList[0][-1][1]]


    print("Loading vehicle {}...".format(vehicle_conf))
    ego = sim.add_agent(vehicle_conf, lgsvl.AgentType.EGO, state2)
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

    cameraPosition = Vector(destination[0], 100, destination[1])
    cameraRotation = Vector(90, 0, 0)
    camera = Transform(cameraPosition, cameraRotation)
    sim.set_sim_camera(camera)

    sim.run(LGSVL__SIMULATION_DURATION_SECS)


testApollo(1)




