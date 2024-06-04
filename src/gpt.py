import requests
import os

from src.utils import processResult


def readExtractionPrompt():
    fileName = os.path.join(os.path.abspath(os.path.dirname(__file__)).split('BigModelRacer-latest')[0],
                            "BigModelRacer-latest/src/file/extractionPrompt.txt")
    f = open(fileName, "r")
    lines = f.readlines()
    f.close()

    prompt = ""
    for line in lines:
        prompt += line
    return prompt


def getApiKey():
    fileName = os.path.join(os.path.abspath(os.path.dirname(__file__)).split('BigModelRacer-latest')[0],
                            "BigModelRacer-latest/src/file/apiKey.txt")
    f = open(fileName, "r")
    key = f.readlines()[0]
    f.close()

    return key


api_key = getApiKey()


def preprocessReport(report):
    prompt = "You should help me process a car accident description. You should analyse each sentence in the description. Once you found a sentence that contains impact actions, then drop all the sentences after." + \
             "Output the processed description." + \
             "The accident description is : " + report

    headers = {
        "Authorization": 'Bearer ' + api_key,
    }

    params = {
        "messages": [
            {
                "role": 'user',
                "content": prompt
            }
        ],
        "model": 'gpt-4'
    }

    response = requests.post(
        "https://cfcus02.opapi.win/v1/chat/completions",
        headers=headers,
        json=params,
        stream=False
    )

    res = response.json()
    return res['choices'][0]['message']['content']


def getAnalysisResult(report):
    headers = {
        "Authorization": 'Bearer ' + api_key,
    }

    params = {
        "messages": [
            {
                "role": 'user',
                "content": readExtractionPrompt() + report
            }
        ],
        "model": 'gpt-4'
    }

    response = requests.post(
        "https://cfcus02.opapi.win/v1/chat/completions",
        headers=headers,
        json=params,
        stream=False
    )

    res = response.json()
    return res['choices'][0]['message']['content']


def gptProcessReport():
    rootPath = os.path.abspath(os.path.dirname(__file__)).split('BigModelRacer-latest')[0]
    path = os.path.join(rootPath, "BigModelRacer-latest/src/file/report.txt")
    f = open(path, "r")
    lines = f.readlines()
    f.close()

    reportContent = ""
    for line in lines:
        reportContent += line

    ppr = preprocessReport(reportContent)
    res = getAnalysisResult(ppr)
    pres = processResult(res)

    fileName = os.path.join(rootPath, "BigModelRacer-latest/src/file/result.txt")
    f = open(fileName, "w")
    f.write(pres)
    f.close()