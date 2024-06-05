This repository provides the code of SoVAR.



### The structure of the repository

---

```
The structure of folder "src" is as follows:
src
├── file
│   ├── report        				crash reports                  
│   ├── result                      information extracted from crash reports   
│   ├── apiKey.txt                  write your openai api-key here          
│   ├── extractionPrompt.txt        prompt with linguistic patterns            
│   ├── map.txt                     road information  
│   ├── report.txt                  input of SoVAR  
│   └── result.txt                  output of gpt        
├── solver							solvers of car actions               
├── caculator.py                    main caculator of SoVAR  
├── generateWaypoints.py            generate waypoints          
├── gpt.py                          chat with gpt
├── search.py                       adjust points       
├── simulateReport.py               entrance to simulate report                 
├── testApollo.py                   entrance to test apollo car     
├── testRandom.py                   entrance to test apollo car with random npc
└── utils.py                        some basic methods     
```





### Requirements

---

* Python version : 3.10 or higher.

* Basic dependencies : see in requirements.txt.

* Core API  : LGSVL PythonAPI.

* Car simulator : LGSVL simulator v2021.3.

* Autopilot platform : Apollo 6.0.

* Operation system : Ubuntu 21.10.

* Hardware condition (Not mandatory) : 

  * GPU : Intel (R) Core (TM) i7-1070K.

  * Internal memory : 32GB.
  * Display : NVIDIA GeForce RTX 4070.





### Installation

---

**1. Install LGSVL**

LGSVL simulator can be installed from https://github.com/lgsvl/simulator. The tutorial is on it as well.


**2. Install Apollo6.0**

1) clone source code.

2) pull docker image and enter the container.

```bash
$ sudo bash ./docker/scripts/dev_start.sh
$ sudo bash ./docker/scripts/dev_into.sh
```



3) build Apollo.

```bash
sudo ./apollo.sh build
```



4) start dreamviewer.

```bash
sudo bash scripts/bootstrap.sh
```



5) bridge Apollo with LGSVL.

```bash
bash scripts/bridge.sh
```



**3. Install SoVAR**

1) clone source code.

```bash
$ git clone https://github.com/meng2180/SoVAR.git
```



2) install dependencies.

```bash
pip install -r requirements.txt
```



3) import LGSVL PythonAPI.

Download python-api from https://github.com/lgsvl/PythonAPI/tree/master. After download, put the package "lgsvl" under the package "src" of SoVAR.





### Experiments

---

**E1: Reconstruct 2-NPCs car accident  from an accident report.**

* Start lgsvl simulator.
* Copy the summary part of the report in XML format to report.txt.
* Run simulateReport.py.

The two cars' behaviors are the same as the report.



**E2: test 1-EGO-and-1-NPC car accident in Apollo from an accident report.**

* Start lgsvl simulator.
* Start Apollo6.0 and connect it with lgsvl simulator.
* Copy the summary part of the report in XML format to report.txt.
* Run testApollo.py.

The NPC car's behavior is same as the report while the EGO car has the same start point and destination point as the report.



**E3: test 1-EGO-and-1-random-NPC car accident in Apollo from an accident report.**

* Start lgsvl simulator.
* Start Apollo6.0 and connect it with lgsvl simulator.
* Copy the summary part of the report in XML format to report.txt.
* Run testApollo.py.

The EGO car has the same start point and destination point as the report. But the random NPC car has a random start point and destination point.



**Q** : How to run the experiments RQ1, RQ2 and RQ3 in the paper ?

Experiments above are the usage mode of SoVAR in practical application. You can rerun RQ1, RQ2 and RQ3 in the paper by modifying a few codes based on E1, E2 and E3.

