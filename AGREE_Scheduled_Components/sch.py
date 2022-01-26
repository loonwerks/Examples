#
# Introducing scheduling semantics to AGREE Lustre model
#
# Syntax: python sch.py -i input_lustre_file_name.lus -s schedule_file_name.txt 
# Example: python sch.py -i downsample.lus -s downsample_sch.txt
# downsample.lus: Lustre model generated from the AADL model by AGREE
# downsample_sch.txt: schedule definition
#
# Output: a Lustre file with name input_lustre_file_name_sch.lus
# Example: downsample_sch.lus
#
import re, os, sys, getopt

def main(argv): 
	usage = 'Usage: sch.py -i <lustre_file> -s <schedule_file>'
	inputfile = ""
	schedulefile = ""
	try:
		opts, args = getopt.getopt(argv,"hi:s:",["ifile=","sfile="])
	except getopt.GetoptError:
		print(usage)
		sys.exit(2)	
	for opt, arg in opts:
		if opt == '-h':
			print(usage)
			sys.exit()
		elif opt in ("-i", "--ifile"):
			inputfile = arg
		elif opt in ("-s", "--sfile"):
			schedulefile = arg
		else:
			print(usage)
			sys.exit(2)
	if inputfile:
		print ('INFO: Input Lustre file [' + inputfile + ']')
	else:
		print 'ERROR: missing Lustre file'
		print(usage)
		sys.exit(2)
	if schedulefile:
		print ('INFO: Input schedule file [' + schedulefile	+ ']')
	else:
		print 'ERROR: missing schedule file'
		print(usage)
		sys.exit(2)
	list = inputfile.split(".")
	inputFileName = list[0]
	outputFile = inputFileName + "_sch.lus"
	print('INFO: Output Lustre file [' + outputFile + ']')	
####################################################################	
	# process schedule file	
	fsch = open(schedulefile, "rt")
	#  __ASSUME0 = ((((((((A_Dispatch = ((tick = 1) or (tick = 5))) and (A_Complete = ((tick = 2)...
	schedule = '  __ASSUME999 = '
	firtline = True
	components = []
	maxNumber = 1
	for line in fsch:
		if firtline:
			firtline = False
		else:
			schedule = schedule + ' and '
		list = line.split(" ")
		#print(list)
		if '_Dispatch' in list[0]:
			component = list[0].replace("_Dispatch", "")
			components.append(component)
		schedule = schedule + '(' + list[0] + ' = ('
		firtNum = True
		for number in list[1:]:	
			if firtNum:
				firtNum = False
			else:
				schedule = schedule + ' or '
			if '\n' in number:
				number = number.strip()
			schedule = schedule +  '(tick = ' + number + ')'			
			maxNumber = max(maxNumber, int(number))
		schedule = schedule + '))'
	#print(schedule + ';\n')	
	fsch.close()
##########################################################	
	fin = open(inputfile, "rt")
	fout = open(outputFile, "wt")
	fout.write ("-- AUTO GENERATED \n")
	period = maxNumber	
	inMainNode = False
	inputDatas = []	
	inputEvents = []
	inputsFlag = False
	inputFreezeAssumptions = []
	inNodeInterface = False
	assumptionNames = []
	for line in fin:
		newline = line
		if 'node main(' in line:  
			inMainNode = True
		if 'tel;\n' in line: 
			inMainNode = False
########################################################################			
		# get system inputs		
		if inMainNode and inputsFlag:
			if '  time : real\n' in line:
				inputsFlag = False
			elif '_EVENT_' in line:
				words = line.split(" : ")
				inputEvents.append(words[0].strip())
			else:
				words = line.split(" : ")
				inputDatas.append(words[0].strip())
		if inMainNode and '__time : ' in line:
			inputsFlag = True
			inputDatas = []	
			inputEvents = []				
		# add component Dispatch Complete declaration
		if inMainNode and '  time : real\n' in line:
			for component in components:
				declaration = '  ' + component + "_Dispatch : bool;\n"
				fout.write(declaration)
				declaration = '  ' + component + "_Complete : bool;\n"
				fout.write(declaration)
			fout.write("  tick : int;\n")
#			fout.write(line)

		# add schedule assumption declaration
		if inMainNode and '  __GUARANTEE0 : bool;\n' in line:
			declaration = "  __ASSUME999 : bool;\n"
			fout.write(declaration)
			for name in assumptionNames:
				declaration = '  ' + name + ' : bool;\n'
				fout.write(declaration)
		# Augment Complete to system-level property
		pattern = '  __GUARANTEE\d+ = '
		match = re.search(pattern, line)
		if inMainNode and match:
			property = re.sub('(  __GUARANTEE\d+ = )', '\\1(tick = ' + str(period) + ') => ', line)
			# print(property)
			fout.write(property)
			continue
		if inMainNode and 'assert true;' in line:
			# add schedule assumption
			fout.write(schedule + ';\n')
			fout.write('  assert __ASSUME999;\n')
			# add tick definition
			assertion = '  assert (tick = __CircularCounter(1, 1, (false -> (pre(tick = ' + str(period) + ')))));\n'
			# print(assertion)
			fout.write(assertion)	
			# add system input data freeze assumption
			#__ASSUME2 = ((not A_sub_Dispatch) => (true -> (Input = pre(Input)));
			for inputData in inputDatas:
				assertion = '  assert (not ' + '(tick = 1)' +') => (true -> (' + inputData + \
						' = pre(' + inputData + ')));\n'
				#print(assertion)
				fout.write(assertion)	
			# insert system input event freeze assertion
			for inputEvent in inputEvents:
				assertion = '  assert (not ' + '(tick = 1)' +') => (' + inputEvent + \
					' = (false -> pre(' + inputEvent + ')));\n'
				# print(assertion)
				fout.write(assertion)
		# add component input freeze assumptions
		if inMainNode and '  --%PROPERTY __GUARANTEE0;\n' in line:
			for assumption in inputFreezeAssumptions:
				property = '  --%PROPERTY ' + assumption +';\n'
				#print(property)
				fout.write(property)
		# get component inputs
		if not inMainNode and inNodeInterface and '  time : real;' in line:
			inNodeInterface = False	
		if not inMainNode and inNodeInterface and not 'ASSUME' in line:
			#print(line)	
			list = line.split(" : ")
			input = list[0].strip()
			assumptionName = node + '__' + input + '_ASSUME'
			#print(assumptionName)
			assumptionNames.append(assumptionName)
		if not inMainNode and 'node _TOP__' in line:
			list = line.split("__")
			text = list[1]
			node = text[:-2]
			#print(node)			
			inNodeInterface = True			

###################################################################################################	
		match = False
		for component in components:
			pattern = '\s+assert\s+_TOP\_+' + component + '\('
			match = re.search(pattern, newline)
			if match:
				#print(component)
				dispatch = component + '_Dispatch'
				complete = component + '_Complete'
				condact = 'assert condact(' + complete + ','
				newline = newline.replace('assert', condact)
				newline = newline.replace(';', ', true);')
				#print(newline)
				fout.write(newline)
				list = line.split("time, ")
				# get component inputs and input events
				#print(list[0])
				text = list[0]
				inputs = text.split(", ")
				inputs.pop()
				inputs.pop(0)
				#print(inputs)
				for input in inputs:
					if not ('____ASSUME' in input):
						assumptionName = input + '_ASSUME'
						inputFreezeAssumptions.append(assumptionName)
						assumption = '  ' + assumptionName + ' = (__Between('+dispatch+', '+ complete\
							+') => (true -> (' + input + ' = pre(' + input + '))));\n'
						#print(assumption)
						fout.write(assumption)
				# get component outputs and output events (including local variables)				
				text = list[1] 
				# remove tail ');\n'
				text = text[:-3]
				outputs = text.split(", ")
				#print(outputs)
				outputDatas = []
				outputEvents = []			
				for output in outputs:
					if '___EVENT_' in output:
						outputEvents.append(output)
					else:
						outputDatas.append(output)
				#print(outputDatas)
				#print(outputEvents)
				# insert output freeze assertion
				for outputData in outputDatas:
				#assert (not MON_REQ_Complete) => (true -> (MON_REQ_alert = pre(MON_REQ_alert)));			
					assertion = '  assert (not ' + complete +') => (true -> (' + outputData + \
						' = pre(' + outputData + ')));\n'
					#print(assertion)
					fout.write(assertion)	
				# insert output event freeze assertion
				for outputEvent in outputEvents:
				# assert (not MON_REQ_Complete) => (MON_REQ_alert_EVENT_ = (false -> pre(MON_REQ_alert_EVENT_)));			
					assertion = '  assert (not ' + complete +') => (' + outputEvent + \
						' = (false -> pre(' + outputEvent + ')));\n'
					#print(assertion)
					fout.write(assertion)
				# get all assumptions
				pattern = component + '____ASSUME\d+'	
				assumptions = re.findall(pattern, line)
				# print(assumptions)
				# insert assumption hold assertion
				for assumption in assumptions:
				#  assert (not WPM_Complete) => (WPM_ASSUME0 = (true -> pre(WPM_ASSUME0)));
					assertion = '  assert (not ' + complete +') => (' + assumption + \
						' = (true -> pre(' + assumption + ')));\n'
					#print(assertion)
					fout.write(assertion)		
				break	
		if not match:
			fout.write(newline)
	# insert circular counter node definition
	line1 = 'node __CircularCounter(\n'
	line2 = '  init : int;\n'
	line3 = '  incr : int;\n'
	line4 = '  reset : bool\n'
	line5 = ') returns (\n'
	line6 = '  count : int\n'
	line7 = ');\n'
	line8 = 'let\n'
	line9 = '  count = (if reset then init else (init -> ((pre count) + incr)));\n'
	line10 = 'tel;\n'
	fout.writelines([line1,line2,line3,line4,line5,line6,line7,line8,line9,line10])		

	line1 = 'node __Between(\n'
	line2 = '  start : bool;\n'
	line3 = '  end : bool\n'
	line4 = ') returns (\n'
	line5 = '  out : bool\n'
	line6 = ');\n'
	line7 = 'let\n'
	line8 = '  out = (if (false -> (pre start)) then true else (if (false -> (pre end)) then false else (false -> (pre out))));\n'
	line9 = 'tel;\n'	
	fout.writelines([line1,line2,line3,line4,line5,line6,line7,line8,line9])		
	
	fin.close()
	fout.close()

	
	print('INFO: done')		
	
if __name__ == "__main__":
   main(sys.argv[1:])