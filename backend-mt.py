#!/usr/bin/env python
# Copyright 2019 Ligios Michele <michele.ligios@linksfoundation.com>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
'''
---------------------------------------------------------------------------------------------------------------
Simple REST server for Python (3). Built to be multithreaded.
---------------------------------------------------------------------------------------------------------------
* TO BE DONE: UPDATE DESCRIPTION HERE! (proper verification of response.status_code)
@Version 3.0.3
                                           Storage4Grid EU Project
                                      Implementation of DSF connectors
* ----------------------------------------------------------------------------------------------------------- *
                                              API Description:
  * Because of visibility permissions, these such APIs will be accessible only from VPN.
  * Consequently, the only ip-valid target will be the VPN one: 10.8.0.50
* Weather:
  * http://10.8.0.50:18081/weather/{lat},{lon}/
  * http://10.8.0.50:18081/weather/+90.00,-11.00/
* PV:
  * http://10.8.0.50:18081/pv/{date_from}/{date_to}/{lat},{lon}/{tilt}/{horizon_declination}/
  * http://10.8.0.50:18081/pv/2018.10.01/2018.10.02/46.29,11.20/0/90/
  * http://10.8.0.50:18081/pv/{date_from}/{date_to}/{lat},{lon}/
  * http://10.8.0.50:18081/pv/2018.10.01/2018.10.02/46.29,11.20/
* AggregatedLoads (EDYNA RESIDENTIAL):
  * http://10.8.0.50:18081/EDYNA/residential/aggregatedloads/{date_from}/{number_of_days}
  * http://10.8.0.50:18081/EDYNA/residential/aggregatedloads/2019.06.15/10
* AggregatedLoads (EDYNA COMMERCIAL) == DSF-EVA (Because over there only EV CU, no Loads)
  * http://10.8.0.50:18081/EVA/{WeekDay}
  * http://10.8.0.50:18081/EVA/Today
  * http://10.8.0.50:18081/EVA/{OverallNumEV}
  * http://10.8.0.50:18081/EVA/10
* Grid & Prices (EDYNA):
  * http://10.8.0.50:18081/EDYNA/grid
  * http://10.8.0.50:18081/EDYNA/lines        <<<<
  * http://10.8.0.50:18081/EDYNA/linecodes    <<<<
  * http://10.8.0.50:18081/EDYNA/loads        <<<<
  * http://10.8.0.50:18081/EDYNA/nodes        <<<<
  * http://10.8.0.50:18081/EDYNA/substations
  * http://10.8.0.50:18081/EDYNA/transformers <<<<
* Grid & Prices (ENIIG):
  * http://10.8.0.50:18081/ENIIG/grid
  * http://10.8.0.50:18081/ENIIG/lines
  * http://10.8.0.50:18081/ENIIG/linecodes
  * http://10.8.0.50:18081/ENIIG/loads
  * http://10.8.0.50:18081/ENIIG/nodes
  * http://10.8.0.50:18081/ENIIG/substations
  * http://10.8.0.50:18081/ENIIG/transformers
* Prices:
  * http://10.8.0.50:18081/EDYNA/commercial/prices
  * http://10.8.0.50:18081/ENIIG/commercial/prices
  * http://10.8.0.50:18081/GENERIC/{AREA-CODE-ID}/prices
* ----------------------------------------------------------------------------------------------------------- *
@Author Ligios Michele
@update: 2019-03-19
@update final
'''
# ------------------------------------------------------------------------------------ #
# Generic Libraries:
import sys, os, re, shutil, json

import urllib.request, urllib.parse, urllib.error
from urllib.request import urlopen

import http.server
from http.server import HTTPServer as BaseHTTPServer

import requests # Used to simplify redirection

from requests.auth import HTTPBasicAuth

import socketserver
from socketserver import ThreadingMixIn
# ------------------------------------------------------------------------------------ #
import datetime
from datetime import *

# ------------------------------------------------------------------------------------ #
import pysolar
import numpy as np
import pytz as tz
import pandas as pd
# ------------------------------------------------------------------------------------ #
import xmltodict
# ------------------------------------------------------------------------------------ #

# To find correct locations
import geopy
from geopy.geocoders import Nominatim

import codecs
# ------------------------------------------------------------------------------------ #
# EVA related
import calendar
import math
import configparser
# ------------------------------------------------------------------------------------ #
# PLOT for debugging purposes:
# import matplotlib.pyplot as plt
# enablePrintsPlot = True


here    = os.path.dirname(os.path.realpath(__file__))
records = {}
# ------------------------------------------------------------------------------------ #
# Full Numpy array (Avoid compression of data)
np.set_printoptions(threshold=np.inf)

# ------------------------------------------------------------------------------------ #
# 		Global temporary flags to enable print logging:
# ------------------------------------------------------------------------------------ #
# 1. Enable Control Flow prints about main logic
# ------------------------------------------------------------------------------------ #
enablePrints         = True
# ------------------------------------------------------------------------------------ #
# 2. Enable Content results prints about Run-time evaluation
# ------------------------------------------------------------------------------------ #
enableResultsContent = True
# ------------------------------------------------------------------------------------ #
# 3. Enable Control Flow prints about HTTP Server
# ------------------------------------------------------------------------------------ #
enableHTTPPrints     = True
# ------------------------------------------------------------------------------------ #
# 4. Enable Time-Monitoring features to verify delays introduced by the HTTP server
# ------------------------------------------------------------------------------------ #
enableTimingEval     = False

# ------------------------------------------------------------------------------------ #
# 			WEATHER AND PHOTOVOLTAIC PRODUCTION FORECAST
# ------------------------------------------------------------------------------------ #
# WEATHER API EXAMPLE:
# http://api.weatherunlocked.com/api/trigger/51.50,-0.12/forecast 2014.04.24.12,2014.04.25.12 temperature gt 16?app_id={APP_ID}&app_key={APP_KEY}
# http://api.weatherunlocked.com/api/forecast/51.50,-0.12?app_id={APP_ID}&app_key={APP_KEY}
# path + lat,lon + forecast + fromDate, toDate + app_id={}&app_key={}
# ------------------------------------------------------------------------------------ #
weather_service_path = ''
weather_service_id   = ''
weather_service_key  = ''
# ------------------------------------------------------------------------------------ #
# Global var to manage error messages
pv_error_message = ""
# ------------------------------------------------------------------------------------ #

# ---------------------- #
# Influx Database auth:
# ---------------------- #
username = ""
password = ""
# ---------------------- #
config_file = "/usr/src/app/config.properties"
# ------------------------------------------------------------------------------------ #
# PV utilities
def moving_average(a, n=3):
    ret = np.cumsum(a, dtype=float)
    ret[n:] = ret[n:] - ret[:-n]
    return ret[n - 1:] / n


def convolution(array):
	box_pts = 21
	box = np.ones(box_pts) / box_pts
	return np.convolve(array, box, mode='same')

def addNoise(irrad, sim_step,weather_url):
	global pv_error_message
	if(enablePrints == True):
		print(('[WEATHER] URL: ' + weather_url))

	response = requests.get(weather_url)
	# --------------------------------------------------------------------------- #
	# We rely on a thirty party service!
	# IMPOSSIBLE TO GUARANTEE THAT IT WILL BE ALWAYS REACHABLE!
    	# Verify first len! [Empty response will be like: {"Days":[]}, len = 11 byte]
	# --------------------------------------------------------------------------- #
	# Otherwise len will be something like 40361 byte
	# Let's assume that a good threshold is about 1000 byte.
	# --------------------------------------------------------------------------- #
	# print(response.url)
   
	# if(len(response.text) < 100):
	if(response.status_code != 200):
		# Following prints are always enabled to log somehow this lack of service
		if(enablePrints == True):
			print("WeatherUnlocked Service unavailable for the given location! " + str(response.url))

		# print(response.text)
		pv_error_message = ("Service unavailable for the given location! " + str(response.url))
		fake_array = np.array([0])
		return (fake_array,fake_array)

	try:
		cloud_presence = []
		temperature = []
		for d in range(len(response.json()['Days'])):
			for h in range(len(response.json()['Days'][d]['Timeframes'])):
				cloud_presence.append(response.json()['Days'][d]['Timeframes'][h]['cloudtotal_pct'])
				temperature.append(response.json()['Days'][d]['Timeframes'][h]['temp_c'])

		# Following fixed numbers are related to the weather forecast XML response:
		# It returns 8 sections per day. It means that each section is related to a 3 hour time-window.
		# Considering a sim_step of 60 seconds, weather must be repeated 3 times * (3600 seconds / 60 seconds) = 180 minutes = 3 hours
		df_weather = pd.DataFrame(dict(cloud_presence=np.array(cloud_presence).repeat(3 * (3600 / sim_step)),temperature=np.array(temperature).repeat(3 * (3600 / sim_step))))

		blank_cloud_array = np.zeros(len(irrad))
		if len(df_weather) >= len(irrad):
			cloud_array = df_weather['cloud_presence'][:len(irrad)]
		elif len(df_weather) < len(irrad):
			cloud_array = df_weather['cloud_presence']

		pdf_func = lambda j: np.mean(np.random.choice(2, 10, 2, p=[j, 1 - j]))
		pdf_func_vect = np.vectorize(pdf_func)
		pdfs = pdf_func_vect(cloud_array / 100)
		resulting_radiation = irrad * pdfs

		return resulting_radiation, df_weather
	except Exception as e:
		if(enablePrints == True):
			print("[LOG] Raised Exception! (addNoise issue about vector sizes): %s" %e)
		pv_error_message = ("(addNoise service failed due to vectors sizes): %s" %e)
		fake_array = np.array([0])
		return (fake_array,fake_array)

# ------------------------------------------------------------------------------------ #  
def exec_pv_default(dt_start,dt_end,lat,lon):
	global pv_error_message
	# ---------------------------------------------------------------------------- #
	# Fixed example values
	# dt_start = datetime(2015, 10, 2, 0, 0, 0, tzinfo=tz.utc)
	# dt_end = datetime(2015, 10, 8, 0, 0, 0, tzinfo=tz.utc)
	# lat, lon, elevation = 56.87470835, 25.87113221, 100
	# step = 60
	# tilt = 10;
	# declination = 10
	# ---------------------------------------------------------------------------- #
	if(enablePrints == True):
		print("[LOG] exec_pv_default START")

	if(enableTimingEval == True):
		start = datetime.utcnow()

	# ---------------------------------------------------------------------------- #
	# DEFAULT Values:
	tilt        = 10
	declination = 10
	elevation   = 100
	step        = 60
	# ---------------------------------------------------------------------------- #
	if(enablePrints == True):
		print("[LOG] Run prediction with default values about tilt(" + str(tilt) + ") and declination(" + str(declination) + ")")
		print("[LOG] Run prediction with elevation(" + str(elevation) + ") and step(" + str(step) +")")

	alt_func = lambda t: pysolar.solar.get_altitude(lat, lon, t)
	alt_func_vect = np.vectorize(alt_func)
	if(enablePrints == True):
		print("[LOG] PV vectorized")

	sec = timedelta(seconds=step)

	if(enablePrints == True):
		print("[LOG] PV timedelta worked")

	sim_time_array = np.arange(dt_start, dt_end, sec).astype(datetime)

	if(enablePrints == True):
		print("[LOG] PV arange worked")

	for i in range(len(sim_time_array)):
		sim_time_array[i] = sim_time_array[i].replace(tzinfo=tz.utc)

	if(enablePrints == True):
		print("[LOG] PV tzone set correctly")
		print("[LOG] PV math evaluations starts")

	altitudes = alt_func_vect(sim_time_array)

	rad_func = lambda dateArray, altitude_deg: pysolar.radiation.get_radiation_direct(dateArray, altitude_deg)

	rad_func_vect = np.vectorize(rad_func)

	radiations = rad_func_vect(sim_time_array, altitudes)

	radiations[altitudes <= 0] = 0

	irradiations = radiations * np.sin(np.deg2rad(altitudes))
	if(enablePrints == True):
		print("[LOG] PV math evaluations finished")

	weather_url = weather_service_path + str(lat) + ',' + str(lon) + '?app_id=' + weather_service_id + '&app_key=' + weather_service_key

	A, j = addNoise(irradiations, step, weather_url)

	if(len(A) == 1 and len(j) == 1):
		return pv_error_message

	if(enablePrints == True):
		print("[LOG] PV addNoise (via weather service) finished")

	try:
		final_results = convolution(A)

		if(enablePrints == True):
			print("[LOG] PV data convolution finished")

		# from <class 'numpy.ndarray'> to list()
		final_results = final_results.tolist()

		# from list() to string
		json_result = json.dumps(final_results)

		if(enablePrints == True):
			print("[LOG] PV data convolution json conversion finished")
			if(enableResultsContent == True):
				print(json_result)
				print("	# ---------------------------------------------------------------------------- # ")

		if(enableTimingEval == True):
			end = datetime.utcnow()
			print("[LOG] PV API last: " + str(end - start))

		return json_result

	except Exception as e:
		print("[LOG] Raised Exception! (exec_pv_default: convolution issue): %s" %e)
		pv_error_message = ("(exec_pv_default: convolution issue): %s" %e)
		return pv_error_message



def exec_pv(dt_start,dt_end,lat,lon,tilt,declination):
	global pv_error_message
	# ---------------------------------------------------------------------------- #
	# Fixed example values
	# dt_start = datetime(2015, 10, 2, 0, 0, 0, tzinfo=tz.utc)
	# dt_end = datetime(2015, 10, 8, 0, 0, 0, tzinfo=tz.utc)
	# lat, lon, elevation = 56.87470835, 25.87113221, 100
	# step = 60
	# tilt = 10;
	# declination = 10
	# ---------------------------------------------------------------------------- #
	if(enableTimingEval == True):
		start = datetime.utcnow()

	# ------------------------------------------------------------ #
	# Default Values:
	elevation = 100
	step      = 60
	# ------------------------------------------------------------ #
	if(enablePrints == True):
		print("[LOG] Run prediction with given values about tilt(" + str(tilt) + ") and declination(" + str(declination) + ")")
		print("[LOG] Run prediction with elevation(" + str(elevation) + ") and step(" + str(step) +")")

	alt_func = lambda t: pysolar.solar.get_altitude(lat, lon, t)

	# "vectorize": Define a vectorized function which takes a nested sequence of objects
	# or numpy arrays as inputs and returns a single numpy array or a tuple of numpy arrays.
	alt_func_vect = np.vectorize(alt_func)

	# "arange": Return evenly spaced values within a given interval.
	# "astype": To convert the type of the array
	sim_time_array = np.arange(dt_start, dt_end, timedelta(seconds=step)).astype(datetime)

	# ------------------------------------------------------------ #
	# Replace non-aware datetime values with UTC 
	# (equally spaced [step] from 00:00 to 23:59)
	# ------------------------------------------------------------ #
	for i in range(len(sim_time_array)):
		sim_time_array[i] = sim_time_array[i].replace(tzinfo=tz.utc)

	altitudes = alt_func_vect(sim_time_array)
	# ---------------------------------------------------------------------------------------------- #
	# Lambda is a tool for building functions, or more precisely, for building function objects
	# https://pythonconquerstheuniverse.wordpress.com/2011/08/29/lambda_tutorial/
	# https://github.com/pingswept/pysolar/blob/master/pysolar/radiation.py
	# ---------------------------------------------------------------------------------------------- #
	rad_func = lambda dateArray, altitude_deg: pysolar.radiation.get_radiation_direct(dateArray, altitude_deg)
	# ---------------------------------------------------------------------------------------------- #
	# Consequently, rad_func is a function
	rad_func_vect = np.vectorize(rad_func)
	# ---------------------------------------------------------------------------------------------- #
	# Consequently, rad_func_vect is a vector of functions (?)
	# where:
	# sim_time_array is the date array in UTC
	# altitudes is the array of altitudes about the given coordinates:
	radiations = rad_func_vect(sim_time_array, altitudes)
	# ---------------------------------------------------------------------------------------------- #
	radiations[altitudes <= 0] = 0
	# if(enablePrintsPlot == True):
	#	print("Radiations: ")
	#	plt.plot(radiations) 
	#	plt.show()

	irradiations = radiations * np.sin(np.deg2rad(altitudes))

	weather_url = weather_service_path + str(lat) + ',' + str(lon) + '?app_id=' + weather_service_id + '&app_key=' + weather_service_key

	A, j = addNoise(irradiations, step, weather_url)

	# j = weather results
	# if(enablePrintsPlot == True):
	#	print("-------------------------------------------------------------")
	#	print("Weather: " + str(j))
	#	print("-------------------------------------------------------------")
	#	print("TEMPORARY: " + str(A))
	#	plt.plot(A) # plotting by columns
	#	plt.show()

	if(len(A) == 1 and len(j) == 1):
		return pv_error_message

	try:
		final_results = convolution(A)

		# res_tmp = np.array_repr(final_results).replace('\n      ', '')
		final_results = final_results.tolist()
		# from list() to string
		json_result = json.dumps(final_results)

		if(enablePrints == True):
			print("[LOG] PV data convolution json conversion finished")
			if(enableResultsContent == True):
				print(json_result)
				print("	# ---------------------------------------------------------------------------- # ")

		if(enableTimingEval == True):
			end = datetime.utcnow()
			print("[LOG] PV API last: " + str(end - start))

		return json_result

	except Exception as e:
		if(enablePrints == True):
			print("[LOG] Raised Exception! (exec_pv: convolution issue): %s" %e)
		pv_error_message = ("(exec_pv: convolution issue): %s" %e)
		return pv_error_message
# ------------------------------------------------------------------------------------ #
# WEATHER SERVICE:
# Remember that it returns only one week! (Make sense, it is a weather forecast service)
# [But it works also by requesting dates far in the future!]
# This means that PV production forecast can't manage more than 1 week of time-window
# ------------------------------------------------------------------------------------ #
def get_weather(handler):
	words = handler.path
	latitude_tmp = words.split("/")[2].split(",")[0]
	longitude_tmp = words.split("/")[2].split(",")[1]

	# Verify if valid lat,lon values
	latitude = latitude_tmp.replace("+","")
	longitude = longitude_tmp.replace("+","")

	weather_url = weather_service_path + str(latitude) + ',' + str(longitude) + '?app_id=' + weather_service_id + '&app_key=' + weather_service_key
	if(enablePrints == True):
		print(('URL: ' + weather_url))

	if(float(latitude) > 90 or float(longitude) > 180):
		if(enablePrints == True):
			print("WeatherUnlocked Service unavailable for the given location! Latitude and Longitude must be less than 90 degree  " +str(latitude)+","+str(longitude))
		return str("WeatherUnlocked Service unavailable for the given location! Latitude and Longitude must be less than 90 degree")


	# Extract from request API the rquired target (date & location)
	response = requests.get(weather_url)
	# if(len(response.text) < 1000):
	if(response.status_code != 200):
		# Following prints are always enabled to log somehow this lack of service
		if(enablePrints == True):
			print("Service unavailable for the given location! " + str(response.url))
		return ("Service unavailable for the given location! " + str(response.url))

	return response.json()
	
# ------------------------------------------------------------------------------------ #
def get_pv(handler):
	words = handler.path

	fromDate_tmp = words.split("/")[2]
	fromDate = fromDate_tmp.replace("-",".")

	toDate_tmp = words.split("/")[3]
	toDate = toDate_tmp.replace("-",".")

	latitude_tmp = words.split("/")[4].split(",")[0]
	longitude_tmp = words.split("/")[4].split(",")[1]

	# Verify if valid lat,lon values
	latitude = latitude_tmp.replace("+","")
	longitude = longitude_tmp.replace("+","")

	if(enablePrints == True):
		print('PV production about (' + latitude + ',' +  longitude + ') from: (' + fromDate + ') to: (' + toDate + ')')

	latitude  = float(latitude)
	longitude = float(longitude)

	if(float(latitude) > 90 or float(longitude) > 180):
		if(enablePrints == True):
			print("WeatherUnlocked Service unavailable for the given location! Latitude and Longitude must be less than 90 degree: " +str(latitude)+","+str(longitude))
		return str("WeatherUnlocked Service unavailable for the given location! Latitude and Longitude must be less than 90 degree")

	# Build real datetime objects to avoid compatibility issue
	# Verify if correct date
	year, month, day = fromDate.split('.')
	try:
		fromDate = datetime(int(year), int(month), int(day),0, 0, 0, tzinfo=tz.utc)
	except ValueError:
		return "Wrong Date: " + fromDate

	# Verify if correct date
	year, month, day = toDate.split('.')
	try:
		toDate = datetime(int(year), int(month), int(day), 0, 0, 0, tzinfo=tz.utc)
	except ValueError:
		return "Wrong Date: " + toDate


	# Verify if starting date is before ending date
	if(fromDate > toDate):
		return str("Bad Date Ordering:  FROM = [" + str(fromDate) + "]   TO = [" + str(toDate) + "]")

	# Verify if Time-Window is more than 7 days
	# Limit about weatherunlocked forecast service
	# 2019-02-22 
	# if((toDate - fromDate).days//7 > 0):
	if((toDate - fromDate).days//7 >= 1):
		if(enablePrints == True):
			print("[LOG] Distance between dates: " + str((toDate - fromDate).days//7) + " == (more than an entire week)")
		return str("Bad Time-Window: Not allowed for more than 7 days! FROM = [" + str(fromDate) + "]   TO = [" + str(toDate) + "]")

	if(enablePrints == True):
		print("[LOG] Distance between dates: " + str((toDate - fromDate).days//7) + " == (less than an entire week)")

	return exec_pv_default(fromDate,toDate,latitude,longitude)
# --------------------------------------------------------------------------------------------------------------- #
def get_precise_pv(handler):
	words = handler.path

	fromDate_tmp = words.split("/")[2]
	fromDate = fromDate_tmp.replace("-",".")

	toDate_tmp = words.split("/")[3]
	toDate = toDate_tmp.replace("-",".")

	latitude_tmp = words.split("/")[4].split(",")[0]
	longitude_tmp = words.split("/")[4].split(",")[1]

	# Verify if valid lat,lon values
	latitude = latitude_tmp.replace("+","")
	longitude = longitude_tmp.replace("+","")

	tilt_tmp = words.split("/")[5]
	tilt = tilt_tmp.replace("+","")

	horizon_declination =  words.split("/")[6]
	if(enablePrints == True):
		print('PV (precise) production about (' + latitude + ',' +  longitude + ') tilt: (' + tilt + ') horizon: (' + horizon_declination + ') on (' + fromDate + ') to: (' + toDate + ')')
		
	if(float(latitude) > 90 or float(longitude) > 180):
		if(enablePrints == True):
			print("WeatherUnlocked Service unavailable for the given location! Latitude and Longitude must be less than 90 degree: " +str(latitude)+","+str(longitude))
		return str("WeatherUnlocked Service unavailable for the given location! Latitude and Longitude must be less than 90 degree")


	# Verify if correct date
	year, month, day = fromDate.split('.')
	try:
		fromDate = datetime(int(year), int(month), int(day),0, 0, 0, tzinfo=tz.utc)
	except ValueError:
		return "Wrong Date: " + fromDate

	# Verify if correct date
	year, month, day = toDate.split('.')
	try:
		toDate = datetime(int(year), int(month), int(day), 0, 0, 0, tzinfo=tz.utc)
	except ValueError:
		return "Wrong Date: " + toDate


	# Verify if starting date is before ending date
	if(fromDate > toDate):
		return str("Bad Date Ordering:  FROM = [" + str(fromDate) + "]   TO = [" + str(toDate) + "]")

	# Verify if Time-Window is more than 7 days
	# Limit about weatherunlocked forecast service
	# 2019-02-22 
	# if((toDate - fromDate).days//7 > 0):
	if((toDate - fromDate).days//7 >= 1):
		if(enablePrints == True):
			print("[LOG] Distance between dates: " + str((toDate - fromDate).days//7) + " == (more than an entire week)")

		return str("Bad Time-Window: Not allowed for more than 7 days! FROM = [" + str(fromDate) + "]   TO = [" + str(toDate) + "]")

	if(enablePrints == True):
		print("[LOG] Distance between dates: " + str((toDate - fromDate).days//7) + " == (less than an entire week)")


	latitude  = float(latitude)
	longitude = float(longitude)

	return exec_pv(fromDate,toDate,latitude,longitude,tilt,horizon_declination)

# --------------------------------------------------------------------------------------------------------------- #
# 				ENERGY PRICES
# GUIDE: https://transparency.entsoe.eu/content/static_content/Static%20content/web%20api/Guide.html#_request_methods
# LIST of AREAs: https://transparency.entsoe.eu/content/static_content/Static%20content/web%20api/Guide.html#_areas
# RestfulAPI: https://transparency.entsoe.eu/content/static_content/download?path=/Static%20content/web%20api/RestfulAPI_IG.pdf
# 
# https://transparency.entsoe.eu/api?securityToken=183229c7-c9f5-4fd2-a2fc-51111d475000&documentType=A44&In_Domain=10Y1001A1001A885&Out_Domain=10Y1001A1001A885&periodStart=201811132300&periodEnd=201811142300
# --------------------------------------------------------------------------------------------------------------- #
def get_edyna_prices(handler):
	domain_map = {}
	price_service_path = "https://transparency.entsoe.eu/api?securityToken=183229c7-c9f5-4fd2-a2fc-51111d475000"
	price_service_field = "&documentType=A44" # Other services are not required
	# ----------------------------------------- #
	domain_map['EDYNA'] = "10Y1001A1001A885" # IT
	domain_map['ENIIG'] = "10YDK-1--------W" # DK
	domain_map['UPB']   = "10YRO-TEL------P" # RO
	# ----------------------------------------- #
	priceskeyword = ["&In_Domain=","&Out_Domain=","&periodStart=","&periodEnd="]

	if(enableTimingEval == True):
		start = datetime.utcnow()

	today    = datetime.utcnow()
	tomorrow = datetime.utcnow() + timedelta(1)

	# 2018 11 13 23 00
	startDate = today.strftime('%Y%m%d')
	startDate += "0000"
	endDate   = tomorrow.strftime('%Y%m%d')
	endDate += "0000"

	price_url = price_service_path + price_service_field 
	price_url += priceskeyword[0] + domain_map['EDYNA'] + priceskeyword[1] + domain_map['EDYNA'] 
	price_url += priceskeyword[2] + str(startDate) + priceskeyword[3] + str(endDate)

	# print(('URL: ' + price_url))

	xmlResp = requests.get(price_url)

	# if(len(xmlResp.text) < 100 or (xmlResp.status_code != 200)):
	if(xmlResp.status_code != 200):
		if(enablePrints == True):
			# Following prints are always enabled to log somehow this lack of service
			print("Service unavailable for the given Time or location! " + str(xmlResp.url))	
		return ("Service unavailable for the given Time or location! " + str(xmlResp.url))

	jsonString = json.dumps(xmltodict.parse(xmlResp.content))
	jsonString = jsonString.replace('\\"',"\"")


	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] Edyna Prices API last: " + str(end - start))	

	# print(jsonString)
	return json.loads(jsonString)

# --------------------------------------------------------------------------------------------------------------- #
def get_eniig_prices(handler):
	domain_map = {}
	price_service_path = "https://transparency.entsoe.eu/api?securityToken=183229c7-c9f5-4fd2-a2fc-51111d475000"
	price_service_field = "&documentType=A44" # Other services are not required
	# ----------------------------------------- #
	# domain_map['EDYNA'] = "10Y1001A1001A885" # IT
	domain_map['ENIIG'] = "10YDK-1--------W" # DK
	# domain_map['UPB']   = "10YRO-TEL------P" # RO
	# ----------------------------------------- #
	priceskeyword = ["&In_Domain=","&Out_Domain=","&periodStart=","&periodEnd="]

	if(enableTimingEval == True):
		start = datetime.utcnow()

	today    = datetime.utcnow()
	tomorrow = datetime.utcnow() + timedelta(1)

	# 2018 11 13 23 00
	startDate = today.strftime('%Y%m%d')
	startDate += "0000"
	endDate   = tomorrow.strftime('%Y%m%d')
	endDate += "0000"

	price_url = price_service_path + price_service_field 
	price_url += priceskeyword[0] + domain_map['ENIIG'] + priceskeyword[1] + domain_map['ENIIG'] 
	price_url += priceskeyword[2] + str(startDate) + priceskeyword[3] + str(endDate)

	# print(('URL: ' + price_url))

	xmlResp = requests.get(price_url)

	# if(len(xmlResp.text) < 100 or (xmlResp.status_code != 200)):
	if(xmlResp.status_code != 200):
		if(enablePrints == True):
			# Following prints are always enabled to log somehow this lack of service
			print("Service unavailable for the given Time or location! " + str(xmlResp.url))	
		return ("Service unavailable for the given Time or location! " + str(xmlResp.url))

	jsonString = json.dumps(xmltodict.parse(xmlResp.content))
	jsonString = jsonString.replace('\\"',"\"")

	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] Eniig Prices API last: " + str(end - start))
	
	return json.loads(jsonString)

# --------------------------------------------------------------------------------------------------------------- #

def get_prices(handler):
	words = handler.path

	if(enableTimingEval == True):
		start = datetime.utcnow()

	domain_map = {}
	price_service_path = "https://transparency.entsoe.eu/api?securityToken=183229c7-c9f5-4fd2-a2fc-51111d475000"
	price_service_field = "&documentType=A44" # Other services are not required
	# ----------------------------------------- #
	# domain_map['EDYNA'] = "10Y1001A1001A885" # IT
	# domain_map['ENIIG'] = "10YDK-1--------W" # DK
	# domain_map['UPB']   = "10YRO-TEL------P" # RO
	# ----------------------------------------- #
	priceskeyword = ["&In_Domain=","&Out_Domain=","&periodStart=","&periodEnd="]

	domain = words.split("/")[2]

	today    = datetime.utcnow()
	tomorrow = datetime.utcnow() + timedelta(1)

	# 2018 11 13 23 00
	startDate = today.strftime('%Y%m%d')
	startDate += "0000"
	endDate   = tomorrow.strftime('%Y%m%d')
	endDate   += "0000"

	price_url = price_service_path + price_service_field 
	price_url += priceskeyword[0] + str(domain) + priceskeyword[1] + str(domain)
	price_url += priceskeyword[2] + str(startDate) + priceskeyword[3] + str(endDate)

	# print(('URL: ' + price_url))

	xmlResp = requests.get(price_url)

	# if(len(xmlResp.text) < 100 or (xmlResp.status_code != 200)):
	if(xmlResp.status_code != 200):
		if(enablePrints == True):
			# Following prints are always enabled to log somehow this lack of service
			print("Service unavailable for the given Time or location! " + str(xmlResp.url))	
		return ("Service unavailable for the given Time or location! " + str(xmlResp.url))

	jsonString = json.dumps(xmltodict.parse(xmlResp.content))
	jsonString = jsonString.replace('\\"',"\"")

	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] Generic Prices API last: " + str(end - start))	

	# print(jsonString)
	return json.loads(jsonString)

# --------------------------------------------------------------------------------------------------------------- #
# Changes requested:
# From:
# http://10.8.0.50:18081/EDYNA/commercial/prices
# http://10.8.0.50:18081/ENIIG/commercial/prices
# http://10.8.0.50:18081/GENERIC/{AREA-CODE-ID}/prices
# TO:
# EL Prices:
# http://10.8.0.50:18081/{latitude},{longitude}/{type}/prices
# {type}= commercial,residential?

# Exploit following lines to find out the correct Country:
# geolocator = Nominatim()
# location = geolocator.reverse("46.29000, 11.0293506")
# print(location.raw['address']['country'])
# --------------------------------------------------------------------------------------------------------------- #
def get_prices_from_location(handler):
	words = handler.path

	if(enableTimingEval == True):
		start = datetime.utcnow()

	domain_map = {}
	price_service_path = "https://transparency.entsoe.eu/api?securityToken=183229c7-c9f5-4fd2-a2fc-51111d475000"
	price_service_field = "&documentType=A44" # Other services are not required

	# ----------------------------------------- #
	# The only country of interest for S4G
	# To extend the service for other country
	# add the mapping here.  
	# ----------------------------------------- #
	domain_map['Italia']  = "10Y1001A1001A885" # IT
	domain_map['Danmark'] = "10YDK-1--------W" # DK
	domain_map['UPB']     = "10YRO-TEL------P" # RO
	# ----------------------------------------- #

	latitude_tmp = words.split("/")[1].split(",")[0]
	longitude_tmp = words.split("/")[1].split(",")[1]

	# Verify if valid lat,lon values
	latitude = latitude_tmp.replace("+","")
	longitude = longitude_tmp.replace("+","")

	if(float(latitude) > 90 or float(longitude) > 180):
		if(enablePrints == True):
			print("Service unavailable for the given location! Latitude and Longitude must be less than 90 degree " +str(latitude)+","+str(longitude))
		return str("Service unavailable for the given location! Latitude and Longitude must be less than 90 degree")

	intLat = int(float(latitude))
	intLon = int(float(longitude))

	if(intLat == 46 and intLon == 11):
		country = "Italia"
	elif(intLat == 56 and intLon == 9):
		country = "Danmark"
	else:
		try:
			geolocator = Nominatim()
			location = geolocator.reverse(str(latitude) + ', ' + str(longitude))
			if(enablePrints == True):
				print("Selected Location: " + str(location.raw['address']['country']))
			country = str(location.raw['address']['country'])
		except Exception as e:
			if(enablePrints == True):
				print("GeoPy Service Error for the given location! " + str(latitude) + ', ' + str(longitude))
			return str("GeoPy Service Error for the given location! " + str(latitude) + ', ' + str(longitude))


	try:
		transparencyID = domain_map[str(country)]
	except Exception as e:
		if(enablePrints == True):
			print("S4G Service Error for the given country! Out of Scope! " + str(location.raw['address']['country']))
		return str("S4G Service Error for the given country! Out of Scope! " + str(location.raw['address']['country']))
						

	priceskeyword = ["&In_Domain=","&Out_Domain=","&periodStart=","&periodEnd="]

	today    = datetime.utcnow()
	tomorrow = datetime.utcnow() + timedelta(1)

	# 2018 11 13 23 00
	startDate = today.strftime('%Y%m%d')
	startDate += "0000"
	endDate   = tomorrow.strftime('%Y%m%d')
	endDate   += "0000"

	price_url = price_service_path + price_service_field 
	price_url += priceskeyword[0] + str(transparencyID) + priceskeyword[1] + str(transparencyID)
	price_url += priceskeyword[2] + str(startDate) + priceskeyword[3] + str(endDate)

	# print(('URL: ' + price_url))

	xmlResp = requests.get(price_url)

	# if(len(xmlResp.text) < 100 or (xmlResp.status_code != 200)):
	if(xmlResp.status_code != 200):
		if(enablePrints == True):
			# Following prints are always enabled to log somehow this lack of service
			print("Transparency Service unavailable for the given Time or location! " + str(xmlResp.url))	
		return str("Transparency Service unavailable for the given Time or location! " + str(xmlResp.url))

	jsonString = json.dumps(xmltodict.parse(xmlResp.content))
	jsonString = jsonString.replace('\\"',"\"")

	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] Generic Prices API last: " + str(end - start))	


	return json.loads(jsonString)


def get_prices_complete(handler):
	words = handler.path

	if(enableTimingEval == True):
		start = datetime.utcnow()

	domain_map = {}
	price_service_path = "https://transparency.entsoe.eu/api?securityToken=183229c7-c9f5-4fd2-a2fc-51111d475000"
	price_service_field = "&documentType=A44" # Other services are not required

	# ----------------------------------------- #
	# The only country of interest for S4G
	# To extend the service for other country
	# add the mapping here.  
	# ----------------------------------------- #
	domain_map['Italia']  = "10Y1001A1001A885" # IT
	domain_map['Danmark'] = "10YDK-1--------W" # DK
	domain_map['UPB']     = "10YRO-TEL------P" # RO
	# ----------------------------------------- #

	latitude_tmp = words.split("/")[1].split(",")[0]
	longitude_tmp = words.split("/")[1].split(",")[1]

	# Verify if valid lat,lon values
	latitude = latitude_tmp.replace("+","")
	longitude = longitude_tmp.replace("+","")

	if(float(latitude) > 90 or float(longitude) > 180):
		if(enablePrints == True):
			print("Service unavailable for the given location! Latitude and Longitude must be less than 90 degree " +str(latitude)+","+str(longitude))
		return str("Service unavailable for the given location! Latitude and Longitude must be less than 90 degree")

	#if(enablePrints == True):
	#	print("Going to evaluate loaction with: [" + str(latitude) + " , " + str(longitude) + "]")

	intLat = int(float(latitude))
	intLon = int(float(longitude))

	if(intLat == 46 and intLon == 11):
		country = "Italia"
	elif(intLat == 56 and intLon == 9):
		country = "Danmark"
	else:
		try:
			geolocator = Nominatim()
			location = geolocator.reverse(str(latitude) + ', ' + str(longitude))
			if(enablePrints == True):
				print("Selected Location: " + str(location.raw['address']['country']))
			country = str(location.raw['address']['country'])
		except Exception as e:
			if(enablePrints == True):
				print("GeoPy Service Error for the given location! " + str(latitude) + ', ' + str(longitude))
			return str("GeoPy Service Error for the given location! " + str(latitude) + ', ' + str(longitude))


	try:
		transparencyID = domain_map[str(country)]
	except Exception as e:
		if(enablePrints == True):
			print("S4G Service Error for the given country! Out of Scope! " + str(location.raw['address']['country']))
		return str("S4G Service Error for the given country! Out of Scope! " + str(location.raw['address']['country']))
						

	priceskeyword = ["&In_Domain=","&Out_Domain=","&periodStart=","&periodEnd="]

	fromDate_tmp = words.split("/")[3]
	fromDate = fromDate_tmp.replace("-",".")

	toDate_tmp = words.split("/")[4]
	toDate = toDate_tmp.replace("-",".")

	# Build real datetime objects to avoid compatibility issue
	# Verify if correct date
	year, month, day = fromDate.split('.')
	try:
		fromDate = datetime(int(year), int(month), int(day),0, 0, 0, tzinfo=tz.utc)
	except ValueError:
		return "Wrong Date: " + fromDate

	# Verify if correct date
	year, month, day = toDate.split('.')
	try:
		toDate = datetime(int(year), int(month), int(day), 0, 0, 0, tzinfo=tz.utc)
	except ValueError:
		return "Wrong Date: " + toDate

	# Verify if starting date is before ending date
	if(fromDate > toDate):
		return str("Bad Date Ordering:  FROM = [" + str(fromDate) + "]   TO = [" + str(toDate) + "]")


	#today    = datetime.utcnow()
	#tomorrow = datetime.utcnow() + timedelta(1)

	# 2018 11 13 23 00
	startDate = fromDate.strftime('%Y%m%d')
	startDate += "0000"
	endDate   = toDate.strftime('%Y%m%d')
	endDate   += "0000"

	price_url = price_service_path + price_service_field 
	price_url += priceskeyword[0] + str(transparencyID) + priceskeyword[1] + str(transparencyID)
	price_url += priceskeyword[2] + str(startDate) + priceskeyword[3] + str(endDate)

	if(enablePrints == True):
		print(('[LOG] URL: ' + price_url))

	xmlResp = requests.get(price_url)

	# if(len(xmlResp.text) < 100 or (xmlResp.status_code != 200)):
	if(xmlResp.status_code != 200):
		if(enablePrints == True):
			# Following prints are always enabled to log somehow this lack of service
			print("Transparency Service unavailable for the given Time or location! " + str(xmlResp.url))	
		return str("Transparency Service unavailable for the given Time or location! " + str(xmlResp.url))

	jsonString = json.dumps(xmltodict.parse(xmlResp.content))
	jsonString = jsonString.replace('\\"',"\"")

	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] Generic Prices API last: " + str(end - start))	

	# print(jsonString)
	return json.loads(jsonString)



# --------------------------------------------------------------------------------------------------------------- #
################### USER INPUTS #########################
# forecast_start = '17-06-2019'
# forecast_horizon = 25 # days
# STEP = 900 # seconds
#########################################################
LOAD_PREFIX = str(here) + "/EDYNA/LOAD_AGGREGATED_RES_STATS/"
# --------------------------------------------------------------------------------------------------------------- #
def get_residential_aggregatedloads_dynamic(handler):
	words = handler.path
	STEP = 900 # seconds

	if(enableTimingEval == True):
		start = datetime.utcnow()

	if(enablePrints == True):
		print("get_residential_aggregatedloads_dynamic")

	try:
		forecast_start   = words.split("/")[4]
		forecast_start.replace("-",".")

		forecast_horizon = int(words.split("/")[5])
		if(forecast_horizon == 0):
			if(enablePrints == True):
				print("get_residential_aggregatedloads_dynamic Not allowed value! "+ str(forecast_horizon))
			return str("get_residential_aggregatedloads_dynamic Not allowed value! "+ str(forecast_horizon))

		means_weekend     = pd.read_csv(LOAD_PREFIX + 'means_weekends.txt', header=None)[0].values
		std_weekend       = pd.read_csv(LOAD_PREFIX +'stds_weekends.txt', header=None)[0].values
		means_workingdays = pd.read_csv(LOAD_PREFIX +'means_workingdays.txt', header=None)[0].values
		std_workingdays   = pd.read_csv(LOAD_PREFIX +'stds_workingdays.txt', header=None)[0].values


		# forecast_start_dt = datetime.strptime(forecast_start, '%d-%m-%Y')
		forecast_start_dt = datetime.strptime(forecast_start, '%Y-%m-%d')
		forecast_end_dt = datetime.combine(forecast_start_dt + 
				               timedelta(days=forecast_horizon), 
				               time(0,0,0))

		forecast_horizon_dt = np.arange(forecast_start_dt, forecast_end_dt, timedelta(seconds=STEP)).astype(datetime)
		# forecast_horizon_dt_str = [step_.strftime("%d/%m/%Y %H:%M") for step_ in forecast_horizon_dt]
		forecast_horizon_dt_str = [step_.strftime("%Y/%m/%d %H:%M") for step_ in forecast_horizon_dt]

		MC_repeats = 2 # This is supposed to be a Monte carlo Coeff., but it is simplified given that there is not enough data 
		blank_array = np.array([])
		time_temp_var = forecast_horizon_dt[0].weekday()

		for i in range(forecast_horizon):
			if time_temp_var>6:
				time_temp_var = 0

			if time_temp_var >= 5:
				generated_from_stat = (std_weekend* np.random.randn(MC_repeats,96) + means_weekend).T.mean(axis=1)
			else:
				generated_from_stat = (std_workingdays* np.random.randn(MC_repeats,96) + means_workingdays).T.mean(axis=1)

			time_temp_var+=1
			blank_array = np.append(blank_array, generated_from_stat)

		output_result = []
		for key in range(len(blank_array)):
			temp_dict = dict(DateTime = forecast_horizon_dt_str[key],Loads = blank_array[key]/1e3,Unit = 'kW')
			output_result.append(temp_dict)

		final_results = json.dumps(output_result)

		########################################################################
		# Required JSON conversion:
		jsonString = final_results.replace('\\"',"\"")

		# JSON string to dictionary 
		# (parse again to provide different output format):
		mydict = json.loads(jsonString)
		if(enablePrints == True):
			print("JSON Results:")
			print(type(mydict))
			print(mydict)

	except Exception as e:
		if(enablePrints == True):
			print("get_residential_aggregatedloads_dynamic exception: %s" %e)
		return str("get_residential_aggregatedloads_dynamic exception: %s" %e)

	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] get_residential_aggregatedloads_dynamic API last: " + str(end - start))

	return mydict

# --------------------------------------------------------------------------------------------------------------- #
def get_house_load(handler):
	words = handler.path

	if(enableTimingEval == True):
		start = datetime.utcnow()

	if(enablePrints == True):
		print("get_house_load")

	try:		
		########################################################################
		# Extract from a generic Fronius deployment the data related to: P-Load
		# Extract data from the same day of the previous week
		start     = datetime.utcnow() - timedelta(7)	
		startDate = start.strftime('%Y-%m-%d')
		startDate += " 00:00:00"
		end       = datetime.utcnow() - timedelta(6)
		endDate   = end.strftime('%Y-%m-%d')
		endDate   += " 00:00:00"

		service_path_1 = "http://10.8.0.50:8086/query?db=S4G-DWH-TEST&q=select mean(\"P-Load\") from \"InstallationHouse24\""
		service_path_2 = " where time > " + "\'" + str(startDate) + "\' and time < " + "\'" + str(endDate) + "\'"
		service_path_3 = " GROUP BY time(15m)"
		service_path   = service_path_1 + service_path_2 + service_path_3

		if(enablePrints == True):
			print("[LOG] INFLUX API: " + service_path)

		try:
			response = requests.get(service_path, auth=HTTPBasicAuth(username,password))
		except Exception as e:
			if(enablePrints == True):
				print("[LOG] INFLUX API: " + service_path)
			return str("Influx Service Not reachable/available %s" %e)
	
	except Exception as e:
		if(enablePrints == True):
			print("get_house_load exception: %s" %e)
		return str("get_house_load exception: %s" %e)

	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] get_house_load API last: " + str(end - start))

	return response.json()

# --------------------------------------------------------------------------------------------------------------- #
def get_house_load_specific(handler):
	words = handler.path

	if(enableTimingEval == True):
		start = datetime.utcnow()

	if(enablePrints == True):
		print("get_house_load_specific")

	try:
		measurement_id   = words.split("/")[1]
		########################################################################
		# Extract from a generic Fronius deployment the data related to: P-Load
		# Extract data from the same day of the previous week
		start     = datetime.utcnow() - timedelta(7)	
		startDate = start.strftime('%Y-%m-%d')
		startDate += " 00:00:00"
		end       = datetime.utcnow() - timedelta(6)
		endDate   = end.strftime('%Y-%m-%d')
		endDate   += " 00:00:00"

		service_path_1 = "http://10.8.0.50:8086/query?db=S4G-DWH-TEST&q=select mean(\"P-Load\") from \"" + str(measurement_id) + "\""
		service_path_2 = " where time > " + "\'" + str(startDate) + "\' and time < " + "\'" + str(endDate) + "\'"
		service_path_3 = " GROUP BY time(15m)"
		service_path   = service_path_1 + service_path_2 + service_path_3

		if(enablePrints == True):
			print("[LOG] INFLUX API: " + service_path)

		try:
			response = requests.get(service_path, auth=HTTPBasicAuth(username,password))
		except Exception as e:
			if(enablePrints == True):
				print("[LOG] INFLUX API: " + service_path)
			return str("Influx Service Not reachable/available %s" %e)
	
	except Exception as e:
		if(enablePrints == True):
			print("get_house_load_specific exception: %s" %e)
		return str("get_house_load_specific exception: %s" %e)

	if(enableTimingEval == True):
		end = datetime.utcnow()
		print("[LOG] get_house_load_specific API last: " + str(end - start))

	return response.json()



# -------------------------------------------------------------------- #
# DEPRECATED
# -------------------------------------------------------------------- #
# FROM:
# http://10.8.0.50:18081/EDYNA/commercial/aggregatedloads
# TO:
# http://10.8.0.50:18081/{latitude},{longitude}/{type}/aggregatedloads
# {type}= commercial,residential?

# Exploit following lines to find out the correct Country:
# geolocator = Nominatim()
# location = geolocator.reverse("46.29000, 11.0293506")
# print(location.raw['address']['country'])
# Bucharest: 44.439663, 26.096306

#def get_load_from_location(handler):
#	words = handler.path
#
#	if(enableTimingEval == True):
#		start = datetime.utcnow()
#
#	if(enablePrints == True):
#		print("Start get_load_from_location")
#
#	countryProvidersMap = {}
#	countryProvidersMap['Italia']  = "EDYNA"
#	countryProvidersMap['Danmark'] = "ENIIG"
#
#	domain_map = {}
#	price_service_path = "https://transparency.entsoe.eu/api?securityToken=183229c7-c9f5-4fd2-a2fc-51111d475000"
#	price_service_field = "&documentType=A44" # Other services are not required
#
#	# ----------------------------------------- #
#	# The only country of interest for S4G
#	# To extend the service for other country
#	# add the mapping here.  
#	# ----------------------------------------- #
#	domain_map['Italia']  = "10Y1001A1001A885" # IT
#	domain_map['Danmark'] = "10YDK-1--------W" # DK
#	domain_map['România'] = "10YRO-TEL------P" # RO
#	# ----------------------------------------- #
#
#	latitude_tmp  = words.split("/")[1].split(",")[0]
#	longitude_tmp = words.split("/")[1].split(",")[1]
#
#	# Verify if valid lat,lon values
#	latitude = latitude_tmp.replace("+","")
#	longitude = longitude_tmp.replace("+","")
#
#	if(enablePrints == True):
#		print("Values extracted!")
#
#
#	if(float(latitude) > 90 or float(longitude) > 180):
#		if(enablePrints == True):
#			print("Service unavailable for the given location! Latitude and Longitude must be less than 90 degree " +str(latitude)+","+str(longitude))
#		return str("Service unavailable for the given location! Latitude and Longitude must be less than 90 degree")
#
#	try:
#		geolocator = Nominatim()
#		location = geolocator.reverse(str(latitude) + ', ' + str(longitude))
#
#		if(enablePrints == True):
#			print("Selected Location: " + str(location.raw))
#
#		if('address' in location.raw):
#			if('country' in location.raw['address']):
#				country = str(location.raw['address']['country'])
#			else:
#				country = "Unknown"
#				raise Exception('Country Exception')
#		else:
#			country = "Unknown"
#			raise Exception('Country Exception')
#
#		if(enablePrints == True):
#			print("Selected Location: " + str(location.raw['address']['country']))
#
#	except Exception as e:
#		if(enablePrints == True):
#			print("GeoPy Service Error for the given location! " + str(country))
#		return str("GeoPy Service Error for the given location! " + str(country))
#
#
#	try:
#		# Find Energy Provider from country
#		provider = countryProvidersMap[str(country)]
#	except Exception as e:
#		if(enablePrints == True):
#			print("S4G Service Error for the given country! Out of Scope! Selected: " + str(location.raw['address']['country']))
#		return str("S4G Service Error for the given country! Out of Scope! Selected: " + str(location.raw['address']['country']))
#						
#
#	# ---------------------------------------------------------------- #
#	# today    = datetime.utcnow()
#	# tomorrow = datetime.utcnow() + timedelta(1)
#	# 2018 11 13 23 00
#	# startDate = today.strftime('%Y%m%d')
#	# startDate += "0000"
#	# endDate   = tomorrow.strftime('%Y%m%d')
#	# endDate   += "0000"
#	# ---------------------------------------------------------------- #
#
#
#	# Build the path to the static file [TEMPORARY]
#	# [WHENEVER THE DYNAMIC SERVICE WILL BE READY THESE WILL CHANGE ]
#	# [It works also in case of folders with spaces]
#	pathFile = str(here) + '/' + str(provider) + "/aggregated-loads.json"
#	if(enablePrints == True):
#		print("Static File Located at: " + str(pathFile))
#
#	try:
#		data = json.load(codecs.open(str(pathFile), 'r', 'utf-8-sig'))
#		# print(data)
#	except Exception as e:
#		if(enablePrints == True):
#			print("S4G Service Error! Load Not Found! %s" %e)
#		return str("S4G Service Error! Load Not Found! %s" %e)
#
#
#	if(enableTimingEval == True):
#		end = datetime.utcnow()
#		print("[LOG] get_load_from_location API last: " + str(end - start))							
#
#	return data
#
# ------------------------------------------------------------------------------------ #

# ------------------------------------------------------------------------------------ #
# PATH (files under a inner folder: EVstats)
EV_PREFIX     = str(here) + "/EVstats/"
MAX_EV_NUMBER = 99999
# The prediction made by the following API is always made respect the current day.
# The only exception is managed when the user set a weekday specific in the API.
# In the last case, it will be provided the forecast for that weekday!
# [Concerning a time window of months, the weekday prediction will be always the same]
# This is the reason behind the choise to avoid to put a specific day as a time prefix.
# http://10.8.0.50:18081/EVA/11
# http://10.8.0.50:18081/EVA/Monday
# 
def get_ev_profile(handler):
	words = handler.path

	if(enableTimingEval == True):
		start = datetime.utcnow()

	if(enablePrints == True):
		print("Start get_ev_profile")

	# In case userinput is a number it is related to the amount of EV to manage
	# In case userinput is "Today", then must be converted on the current day and then converted exploiting the inner file
	# In case userinput is a weekday, then must be converted exploiting the inner file
	userinput  = words.split("/")[2]

	weekFlag = False

	if(userinput.isdigit() == True):
		number_of_EVs = int(userinput)
	else:
		if(userinput == "Today"):
			model_input = calendar.day_name[datetime.now().weekday()]
		else:
			# Already valid because verified via regex
			model_input = userinput
			weekFlag = True

		weekday = model_input.capitalize()
		rdf = pd.read_csv(EV_PREFIX+'WEEK_DAYS_NUMBER.txt', header = None)
		rdf.columns = ['day', 'mean','sigma']

		num_mu, num_sigma = rdf[rdf['day'] == weekday]['mean'], rdf[rdf['day'] == weekday]['sigma']
		num_sigma /= 2
		number_of_EVs = abs(math.ceil(np.random.normal(num_mu, num_sigma, 1)[0]))

	if(enablePrints == True):
		print("userinput: " + str(userinput))
		print("number_of_EVs: " + str(number_of_EVs))
		print("Going to Read plugTime")


	if(number_of_EVs > MAX_EV_NUMBER):
		print("Number of EV too high (with current settings this API last too much time): ask IT")
		return("Number of EV too high (with current settings this API last too much time): ask IT ")
	elif(number_of_EVs == 0):
		print("Number of EV inconsistent: zero EV?")
		return("Number of EV inconsistent: zero EV?")

	try:
		# the data so far have high standard deviation because of the trend .... To BE HANDLED later in a more elegant way!	
		##### reading probability distribution data from the dedicated file for plugging time 
		df_plug = pd.read_csv(EV_PREFIX+'plugTime', sep='	',  header='infer')
		df_plug.columns = ['Time','pdf']

		# tries to distribute fairely, with round or ceil the elements under zero are pushed towards either 0 or 1
		distr_factor = 1000 
		dist_list = [[i]*int(round(df_plug['pdf'][i] * distr_factor)) for i in list(df_plug.index)]
		dist_list = np.concatenate(dist_list)

		plugging_time = np.random.choice(dist_list, number_of_EVs)

		#number of EVS per every slot of 15 minutes
		num_per_slot = pd.DataFrame(np.zeros(len(df_plug['Time'].values)))
		df_x =  df_plug['Time'].values

		num_per_slot.index = df_plug['Time'][df_x].index
		num_per_slot.columns = ['EV per slot']
		
		vc = pd.Series(df_plug['Time'][plugging_time].index).value_counts()

		df_ = pd.DataFrame(list(vc.values), df_plug['Time'][list(vc.index)].values)
		num_per_slot.columns =['Number of vehicle to plug in']

		num_per_slot.values[vc.index.values.astype(int)] = df_.values


		# the EV_dict is a charing profile table for the entire fleet, containing "PLUGGING TIME", "PARKING DURATION" and "ENERGY NEEDED"
		EV_dict = {'EV'+str(i):{'plug_time':None,'energy_need':None,'park_duration':None,} for i in range(number_of_EVs)}
		for i in range(len(EV_dict.keys())):
		    EV_dict[list(EV_dict.keys())[i]]['plug_time'] = plugging_time[i]

	except Exception as e:
		if(enablePrints == True):
			print("S4G Service Error! plugTime Error! %s" %e)
		return str("S4G Service Error! plugTime Error! %s" %e) 


	if(enablePrints == True):
		print("Going to Read parking")


	try:
		##### reading data from "parking" probability distribution which distributes all the fleet within differnt time hours 
		df_ = None
		df_p = pd.read_csv(EV_PREFIX+'parking', sep='	',  header='infer')
		df_p = df_p.fillna(0)
		df_p.columns = ['Time','mu (hours)','sigma (hours)']

		for (i,j) in EV_dict.items():
		    mu = df_p['mu (hours)'][j['plug_time']]
		    sigma = df_p['sigma (hours)'][j['plug_time']]
		    p = np.random.normal(mu, sigma, 1)
		    EV_dict[i]['park_duration'] = abs(p)[0]

	except Exception as e:
		if(enablePrints == True):
			print("S4G Service Error! parking Error! %s" %e)
		return str("S4G Service Error! parking Error! %s" %e) 

	if(enablePrints == True):
		print("Going to Read energy")

	try:
		#### reading probability data for energy to be received by each EV
		df_ = None
		df_e = pd.read_csv(EV_PREFIX+'energy', sep='	',  header='infer')
		df_e = df_e.fillna(0)
		df_e.columns = ['Time', 'sigma (hours)', 'mu (hours)']
		
		# the power consumed estimation
		charging_levels = [3.5, 6, 10, 22]
		for (i,j) in EV_dict.items():
		    energy_mu = df_e['mu (hours)'][j['plug_time']]
		    energy_sigma = df_e['sigma (hours)'][j['plug_time']]
		    e = np.random.normal(energy_mu, energy_sigma, 1)
		    EV_dict[i]['energy_need'] = abs(e)[0]
		    if (EV_dict[i]['energy_need']/EV_dict[i]['park_duration'] > max(charging_levels)): EV_dict[i]['energy_need'] = EV_dict[i]['park_duration'] * max(charging_levels)	
		
	except Exception as e:
		if(enablePrints == True):
			print("S4G Service Error! energy Error! %s" %e)
		return str("S4G Service Error! energy Error! %s" %e) 
	
	if(enablePrints == True):
		print("Going to build DataFrame")

	EV_dict = pd.DataFrame(EV_dict)

	# the prediction horizon is two time of the requested because 
	# what remains after midnight for the next day would be added 
	# to the corresponding time of the current day  
	blank_array = np.zeros(2 * len(df_plug))
	sim_slot = 0.25 ### this says that simulation steps are in 15 minutes
	powers=[]
	for (i,j) in EV_dict.items():
		power = j['energy_need'] / j['park_duration']
		if power < 3.5:
			power=3.5
			active_charging_time = j['energy_need'] / power
		elif (power>3.5 and power<6):
			power=6
			active_charging_time = j['energy_need'] / power
		elif (power>6 and power<10):
			power=10
			active_charging_time = j['energy_need'] / power
		elif (power>10 and power<16):
			power=16
			active_charging_time = j['energy_need'] / power
		elif (power>16):
			power=22
			active_charging_time = j['energy_need'] / power
		powers.append(power)
		park_in_sim_slot = math.ceil(active_charging_time  / sim_slot)
		blank_array[int(j['plug_time']): int(j['plug_time'] + park_in_sim_slot)] += power 


	if(enablePrints == True):
		print("Going to build Array")

	flag = 0

	if not flag:
		flag +=1 
		blank_array[:int(len(blank_array) / 2)] += blank_array[int(len(blank_array) / 2):]
		blank_array = blank_array[:int(len(blank_array) / 2)]
		blank_array = pd.DataFrame(blank_array, columns=['EV Total Charging Profile'])	
		blank_array.index = df_plug['Time'].values
	try:

		if(enablePrints == True):
			print("JSON Conversion of results")
			print(type(blank_array.index))
			#print(blank_array.index)
			print(blank_array)


		# Required JSON conversion:
		final_results = blank_array.to_json()
		jsonString = final_results.replace('\\"',"\"")

		########################################################################
		# 2019-05-02 # JSON string to dictionary 
		# (parse again to provide different output format):
		mydict = json.loads(jsonString)
		if(enablePrints == True):
			print("JSON Results:")
			print(type(mydict))
			print(mydict)


		if(weekFlag == True):
			evaDay     = model_input
		else:
			evaDay     = datetime.utcnow().strftime('%d/%m/%Y')

		evaList    = []
		
		for z,w in mydict.items():
			# z is the title!
			# We can drop it!
			for x,y in w.items():
				# Then we iterate for each row (time) and we split it
				nestedElem = {}
				nestedElem['DateTime'] = str(evaDay)+ " " +str(x)
				nestedElem['EVs']      = y
				nestedElem['Unit']     = "KW"
				evaList.append(nestedElem)

		# print(evaList)
		########################################################################
		if(enableTimingEval == True):
			end = datetime.utcnow()
			print("[LOG] Generic get_ev_profile API last: " + str(end - start))

		return evaList

	except Exception as e:
		if(enablePrints == True):
			print("S4G Service Error! blank_array conversion error! %s" %e)
		return str("S4G Service Error! blank_array conversion error! %s" %e) 


# ------------------------------------------------------------------------------------ #
# 				HTTP REST SERVER
# ------------------------------------------------------------------------------------ #
# MULTI-THREAD IMPLEMENTATION:
class ThreadingHTTPServer(socketserver.ThreadingMixIn, BaseHTTPServer):
    pass

# ------------------------------------------------------------------------------------ #
def rest_call_json(url, payload=None, with_payload_method='PUT'):
	'REST call with JSON decoding of the response and JSON payloads'
	if payload:
		if not isinstance(payload, str):
        		payload = json.dumps(payload)

		req = urllib.request.Request(url)
		# PUT or POST
		response = urlopen(MethodRequest(url, payload, {'Content-Type': 'application/json'}, method=with_payload_method))
	else:
		# GET
		response = urlopen(url)

	response = response.read().decode()
	return json.loads(response)


class MethodRequest(urllib.request.Request):
	'See: https://gist.github.com/logic/2715756'
	def __init__(self, *args, **kwargs):
		if 'method' in kwargs:
			self._method = kwargs['method']
			del kwargs['method']
		else:
			self._method = None
		return urllib2.request.__init__(self, *args, **kwargs)


	def get_method(self, *args, **kwargs):
		return self._method if self._method is not None else urllib.request.Request.get_method(self, *args, **kwargs)

class RESTRequestHandler(http.server.BaseHTTPRequestHandler):
	def __init__(self, *args, **kwargs):
		self.routes = {
### Generic Prices (From transparency AREA-CODE-ID)
		r'^/GENERIC/[A-Za-z0-9\-]+/prices$': {'GET': get_prices, 'media_type': 'application/json'},
### Generic Prices (From latitude and longitude)
		# http://10.8.0.50:18081/{latitude},{longitude}/{type}/prices/
		# r'^/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-8][0-9]|90).\d+/[A-Za-z0-9\-]+/prices$': {'GET': get_prices_from_location, 'media_type': 'application/json'},
		# NOTE: [A-Za-z0-9\-]+ is not yet used! Future purposes [type of contract: commercial/residential]
		r'^/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-9][0-9]|1[0-8][0-9]|190).\d+/[A-Za-z0-9\-]+/prices$': {'GET': get_prices_from_location, 'media_type': 'application/json'},
		r'^/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-9][0-9]|1[0-8][0-9]|190).\d+/prices/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])$': {'GET': get_prices_complete, 'media_type': 'application/json'},
### Generic House Load (fixed to InstallationHouse24):
		r'^/GENERIC/houseload$': {'GET': get_house_load, 'media_type': 'application/json'},
### Specific House Load:
		r'^/[A-Za-z0-9\-]+/houseload$': {'GET': get_house_load_specific, 'media_type': 'application/json'},
### Price & Grid
		r'^/EDYNA/commercial/prices$': {'GET': get_edyna_prices, 'media_type': 'application/json'},
		r'^/EDYNA/residential/aggregatedloads/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/\d+$': {'GET': get_residential_aggregatedloads_dynamic, 'media_type': 'application/json'},
### Generic Aggregated Loads (From latitude and longitude)
		# http://10.8.0.50:18081/{latitude},{longitude}/{type}/aggregatedloads 
		# r'^/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-8][0-9]|90).\d+/[A-Za-z0-9\-]+/aggregatedloads$': {'GET': get_load_from_location, 'media_type': 'application/json'},
# DEPRECATED
		# r'^/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-9][0-9]|1[0-8][0-9]|190).\d+/[A-Za-z0-9\-]+/aggregatedloads$': {'GET': get_load_from_location, 'media_type': 'application/json'},
# Residential
		r'^/EDYNA/grid$': {'file': 'EDYNA/grid.json', 'media_type': 'application/json'},
		r'^/EDYNA/lines$': {'file': 'EDYNA/lines.json', 'media_type': 'application/json'},
		r'^/EDYNA/linecodes$': {'file': 'EDYNA/linecodes.json', 'media_type': 'application/json'},
		r'^/EDYNA/loads$': {'file': 'EDYNA/loads.json', 'media_type': 'application/json'},
		r'^/EDYNA/loadshapes$': {'file': 'EDYNA/loadshapes.json', 'media_type': 'application/json'},
		r'^/EDYNA/nodes$': {'file': 'EDYNA/nodes.json', 'media_type': 'application/json'},
		r'^/EDYNA/PV_absorb_effs$': {'file': 'EDYNA/PV_absorb_effs.json', 'media_type': 'application/json'},
		r'^/EDYNA/PVs$': {'file': 'EDYNA/pvs.json', 'media_type': 'application/json'},
		r'^/EDYNA/PV_temp_effs$': {'file': 'EDYNA/PV_temp_effs.json', 'media_type': 'application/json'},
		r'^/EDYNA/source$': {'file': 'EDYNA/source.json', 'media_type': 'application/json'},
		r'^/EDYNA/storages$': {'file': 'EDYNA/storages.json', 'media_type': 'application/json'},
		r'^/EDYNA/substations$': {'file': 'EDYNA/substations.json', 'media_type': 'application/json'},
		r'^/EDYNA/transformers$': {'file': 'EDYNA/transformers.json', 'media_type': 'application/json'},
# Commercial
		r'^/EDYNA/commercial/evs$': {'file': 'EDYNA/commercial/evs.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/feeders$': {'file': 'EDYNA/commercial/feeders.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/lines$': {'file': 'EDYNA/commercial/lines.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/linecodes$': {'file': 'EDYNA/commercial/linecodes.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/loads$': {'file': 'EDYNA/commercial/loads.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/loadshapes$': {'file': 'EDYNA/commercial/loadshapes.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/nodes$': {'file': 'EDYNA/commercial/nodes.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/PVs$': {'file': 'EDYNA/commercial/pvs.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/source$': {'file': 'EDYNA/commercial/source.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/storages$': {'file': 'EDYNA/commercial/storages.json', 'media_type': 'application/json'},
		r'^/EDYNA/commercial/transformers$': {'file': 'EDYNA/commercial/transformers.json', 'media_type': 'application/json'},

### Price & Grid
		r'^/ENIIG/commercial/prices$': {'GET': get_eniig_prices, 'media_type': 'application/json'},
		r'^/ENIIG/commercial/aggregatedloads$': {'file': 'ENIIG/aggregated-loads.json', 'media_type': 'application/json'},
		r'^/ENIIG/grid$': {'file': 'ENIIG/grid.json', 'media_type': 'application/json'},
		r'^/ENIIG/lines$': {'file': 'ENIIG/lines.json', 'media_type': 'application/json'},
		r'^/ENIIG/linecodes$': {'file': 'ENIIG/linecodes.json', 'media_type': 'application/json'},
		r'^/ENIIG/loadshapes$': {'file': 'ENIIG/loadshapes.json', 'media_type': 'application/json'},
		r'^/ENIIG/loads$': {'file': 'ENIIG/loads.json', 'media_type': 'application/json'},
		r'^/ENIIG/nodes$': {'file': 'ENIIG/nodes.json', 'media_type': 'application/json'},
		r'^/ENIIG/PV_absorb_effs$': {'file': 'ENIIG/PV_absorb_effs.json', 'media_type': 'application/json'},
		r'^/ENIIG/PVs$': {'file': 'ENIIG/pvs.json', 'media_type': 'application/json'},
		r'^/ENIIG/PV_temp_effs$': {'file': 'ENIIG/PV_temp_effs.json', 'media_type': 'application/json'},
		r'^/ENIIG/source$': {'file': 'ENIIG/source.json', 'media_type': 'application/json'},
#		r'^/ENIIG/storages$': {'file': 'ENIIG/storages.json', 'media_type': 'application/json'},
#		r'^/ENIIG/substations$': {'file': 'ENIIG/substations.json', 'media_type': 'application/json'},
		r'^/ENIIG/transformers$': {'file': 'ENIIG/transformers.json', 'media_type': 'application/json'},

		# http://10.8.0.50:18081/weather/{lat},{lon}/
		# r'^/weather/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-8][0-9]|90).\d+/$': {'GET': get_weather, 'media_type': 'application/json'},
		r'^/weather/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-9][0-9]|1[0-8][0-9]|190).\d+/$': {'GET': get_weather, 'media_type': 'application/json'},
### EVA (profiles) |[0-9][0-9]
		r'^/EVA/(([0-9]+)|(Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday|Today))$': {'GET': get_ev_profile, 'media_type': 'application/json'},
### PV 
		# http://10.8.0.50:18081/pv/{date_from}/{date_to}/{lat},{lon}/{tilt}/{horizon_declination}/
		# r'^/pv/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-8][0-9]|90).\d+/[+]?([0-9]|[0-9][0-9]|1[0-7][0-9]|180)/[-+]?([0-9]|[0-8][0-9]|90)/$': {'GET': get_precise_pv, 'media_type': 'application/json'},
		# r'^/pv/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-8][0-9]|90).\d+/$': {'GET': get_pv, 'media_type': 'application/json'}}
		r'^/pv/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-9][0-9]|1[0-8][0-9]|190).\d+/[+]?([0-9]|[0-9][0-9]|1[0-7][0-9]|180)/[-+]?([0-9]|[0-8][0-9]|90)/$': {'GET': get_precise_pv, 'media_type': 'application/json'},
		r'^/pv/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/20[0-9][0-9](\.|-)(0[1-9]|1[0-2])(\.|-)(0[1-9]|1[0-9]|2[0-9]|3[0-1])/[-+]?([0-9]|[0-8][0-9]|90).\d+,[-+]?([0-9]|[0-9][0-9]|1[0-8][0-9]|190).\d+/$': {'GET': get_pv, 'media_type': 'application/json'}}
        
		return http.server.BaseHTTPRequestHandler.__init__(self, *args, **kwargs)


	def do_HEAD(self):
		self.handle_method('HEAD')
    
	def do_GET(self):
		self.handle_method('GET')

	def do_POST(self):
		self.handle_method('POST')

	def do_PUT(self):
		self.handle_method('PUT')

	def do_DELETE(self):
		self.handle_method('DELETE')
    
	def get_payload(self):
		payload_len = int(self.headers.getheader('content-length', 0))
		payload = self.rfile.read(payload_len)
		payload = json.loads(payload)
		return payload

        # HTTP Response Method:
	def handle_method(self, method):		
		if(enableHTTPPrints == True):
			print("[LOG] handle_method START")

		route = self.get_route()
		if route is None:
			if(enableHTTPPrints == True):
				print("[LOG] route None")
			self.send_response(404)
			self.end_headers()
			# The following case should be very fast
			# That's why should not be required a dedicated try catch
			# to manage clients that disconnects before receiving responses
			self.wfile.write('Route not found\n'.encode('UTF-8'))
		else:
			if(enableHTTPPrints == True):
				print("[LOG] route: " + str(route))
			if method == 'HEAD':
				self.send_response(200)
				if 'media_type' in route:
					self.send_header('Content-type', route['media_type'])
				self.end_headers()
			else:
				if 'file' in route:
					if(enableHTTPPrints == True):
						print("[LOG] File Request!")

					if method == 'GET':
						if(enableHTTPPrints == True):
							print("[LOG] GET Request Recognized!")
						try:
							f = open(os.path.join(here, route['file']), 'rb')
							if(enableHTTPPrints == True):
								print("[LOG] File opened!")
							try:
								self.send_response(200)
								if(enableHTTPPrints == True):
									print("[LOG] Response sent!")

								if 'media_type' in route:
									self.send_header('Content-type', route['media_type'])
								self.end_headers()
								if(enableHTTPPrints == True):
									print("[LOG] Headers closed!")
								shutil.copyfileobj(f, self.wfile)
								if(enableHTTPPrints == True):
									print("[LOG] File object copy ended!")
							finally:
								# The following case should be very fast
								# That's why should not be required a dedicated try catch
								# to manage clients that disconnects before receiving responses
								f.close()
						except Exception as e:
							if(enableHTTPPrints == True):
								print("[LOG] Raised Exception! (Missing file?) %s " %e)
							self.send_response(404)
							self.end_headers()
							self.wfile.write('File not found\n'.encode('UTF-8'))
					else:
						if(enableHTTPPrints == True):
							print("[LOG] NoN-GET Request Recognized!")
						self.send_response(405)
						self.end_headers()
						# The following case should be very fast
						# That's why should not be required a dedicated try catch
						# to manage clients that disconnects before receiving responses
						self.wfile.write('Only GET is supported\n'.encode('UTF-8'))
				else:
					if(enableHTTPPrints == True):
						print("[LOG] Method Request!")
					try:
						if method in route:
							if(enableHTTPPrints == True):
								print("[LOG] Request in Known Routes!")
							content = route[method](self)
							if content is not None:
								if(enableHTTPPrints == True):
									print("[LOG] Request content not None!")

								self.send_response(200)
								if 'media_type' in route:
									self.send_header('Content-type', route['media_type'])
								self.end_headers()
								if method != 'DELETE':
		                        				self.wfile.write(json.dumps(content).encode('UTF-8'))
							else:
					                    self.send_response(404)
					                    self.end_headers()
		                			    self.wfile.write('Not found\n'.encode('UTF-8'))
						else:
							self.send_response(405)
							self.end_headers()
							self.wfile.write(method + ' is not supported\n'.encode('UTF-8'))
					except Exception as e:
						print("[LOG] Raised Exception! (Client disconnected badly): %s" %e)
                    
# ------------------------------------------------------------------------------------ #    
# Find out which APIs to dispatch
	def get_route(self):
		for path, route in list(self.routes.items()):
			if re.match(path, self.path):
				return route
		return None

# Start REST server 
# ------------------------------------------------------------------------------------ #
def rest_server(server_class=ThreadingHTTPServer, handler_class=RESTRequestHandler):
	'Starts the REST server'
	# It is better to force the docker container to filter those messages!
	ip   = '0.0.0.0'     # Every Network Interface
	port = 18081

	# Multi-threaded
	http_server = server_class((ip, port),handler_class)

	# Single-threaded
	# http_server = http.server.HTTPServer((ip, port), RESTRequestHandler)

	print(('Starting MT HTTP server at %s:%d' % (ip, port)))
	try:
        	http_server.serve_forever()
	except KeyboardInterrupt:
		pass
	print('Stopping HTTP server')
	http_server.server_close()

def main(argv):
	global weather_service_path 
	global weather_service_id   
	global weather_service_key  
	global username 
	global password 

	print((sys.version_info))
	try:
		config = configparser.ConfigParser()
		config.read(config_file)
		config.sections()
		
		weather_service_path = config['WEATHER']['PATH']
		weather_service_id   = config['WEATHER']['ID']
		weather_service_key  = config['WEATHER']['KEY']

		username = config['INFLUX']['USER']  
		password = config['INFLUX']['PASS'] 
	except Exception as e:
		print("Configuration file Exception! %s [not configured]" %e)
		return

	rest_server()

if __name__ == '__main__':
	main(sys.argv[1:])

