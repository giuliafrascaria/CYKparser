'''
EXECUTION INSTRUCTIONS

From a command line, change directory to the one containing the file
al2015_Frascaria_Giulia_0200327_CYKParser1.py

Type Python al2015_Frascaria_Giulia_0200327_CYKParser1.py and press enter to start the execution.

DESCRIPTION

These Python script implements the Cocke Younger Kasami algorithm for parsing context free
languages and grammars. The productions of the input grammar are parsed and stored in two
different arrays with corresponding indexes: if nonterminal S in in position 0 in the NT array,
its productions are in position 0 in the array G. The algorithm then starts with the elimination
of e-productions, unit productions and useless symbols, with procedure "from above" and "from below".
Afterwards, the Chomsky Normal Form is created, and the CYK algorithm starts the parsing process,
returning the recognition matrix and checking whether the axiom S appears in the final cell.

After the code there are some examples of execution
'''



grammatica = raw_input("Type the grammar in the following format NT->P1|P2|..;NT->PN. :\n\n")
stringa = raw_input("Type the word to be parsed:\n\n")
NT = []
G = []
alphabet = {}

def grammarParser(grammatica):
	i = 0
	j = 0
	firstSymbol = j
	while i < len(grammatica):
		while grammatica[i] != ';' and grammatica[i] != '.':#examines a variable at a time
			print grammatica[i]
			i+=1
		i+=1
		parseSet(grammatica[firstSymbol:i])
		j = i
		firstSymbol = j

def parseSet(string):
	print string
	NT.extend([string[0]])
	productions = []
	singleProduction = []
	for i in range(3, len(string)):
		if string[i] != '|' and string[i] != ';' and string[i] != '.':#divides productions
			singleProduction.extend([string[i]])
		else:
			productions.append(singleProduction)
			singleProduction = []
	G.append(productions)

def alphabetCreation(G, NT):#creates the alphabet of terminal symbols
	for i in range(0, len(G)):
		for j in range(0, len(G[i])):
			for k in range(0, len(G[i][j])):
				if (ord(G[i][j][k]) <= 122 and ord(G[i][j][k]) >= 97) or (ord(G[i][j][k]) <= 57 and ord(G[i][j][k]) >= 48) or (ord(G[i][j][k]) >= 40 and ord(G[i][j][k]) <= 43):
					if not(G[i][j][k] in alphabet):
						alphabet[G[i][j][k]] = []
						alphabet[G[i][j][k]].append(NT[i])
						alphabet[G[i][j][k]] = list(set(alphabet[G[i][j][k]]))
					else:
						alphabet[G[i][j][k]].append(NT[i])
						alphabet[G[i][j][k]] = list(set(alphabet[G[i][j][k]]))
				else:
					if not(G[i][j][k] in NT):
						NT.append(G[i][j][k])

def uselessSymbols(G, NT, alphabet):
	generatori = isGenerator(G, NT, alphabet)
	isReachable(G, NT, alphabet, generatori)

def isReachable(G, NT, alphabet, generatori):
	#S is reachable for the base of induction, the other non terminals are added during the execution
	raggiungibili = ["S"]
	length = len(raggiungibili)
	i = 0
	while i < length:
		if raggiungibili[i] in NT:#if the sybol is a terminal, it is the bottom of recursion
			index = NT.index(raggiungibili[i])
			for j in range(0, len(G[index])):
				for k in range(0, len(G[index][j])):
					if not(G[index][j][k] in raggiungibili):
						raggiungibili.append(G[index][j][k])
				length = len(raggiungibili)
		i = i + 1
	ntlen = len(NT)
	i = 0
	while i < ntlen:
		if not(NT[i] in raggiungibili):
			NT.pop(i)
			G.pop(i)
			ntlen = ntlen - 1
		else:
			raggiungibili.remove(NT[i])
		i = i + 1
	reducedAlphabet = {}
	for key in raggiungibili:
		reducedAlphabet[key] = alphabet[key]
	alphabet = reducedAlphabet

def isGenerator(G, NT, alphabet):#finds symbols that generate terminals
	residui = []
	residui.extend(NT)
	generatori = []
	for key in alphabet:
		generatori.append(key)
		generatori.extend(alphabet[key])
	generatori = list(set(generatori))
	ciclovuoto = False
	while not(ciclovuoto):
		ciclovuoto = True
		for i in range(0, len(G)):
			if not(NT[i] in generatori):
				#check if it generates a generator
				for j in range(0, len(G[i])):
					if all(x in generatori for x in G[i][j]):
						generatori.append(NT[i])
						ciclovuoto = False
						if NT[i] in residui:
							residui.remove(NT[i])
			else:
				if NT[i] in residui:
					residui.remove(NT[i])
	if len(residui) != 0:
		for i in range(0, len(residui)):
			length = len(G)
			j = 0
			while j < length:
				productionslen = len(G[j])
				k = 0
				while k < productionslen:
					if residui[i] in G[j][k]:
						G[j].pop(k)
						k = k - 1
						productionslen = productionslen - 1
					k = k + 1
				if productionslen == 0:
					G.pop(j)
					length = length - 1
					j = j - 1
				j = j + 1
			NT.remove(residui[i])
	return generatori

def eProductions(G, NT, alphabet):
	if "e" in alphabet:
		nullable = []
		nullable.extend(alphabet["e"])
		newSymbol = True
		while newSymbol:
			newSymbol = False
			length = len(G)
			i = 0
			while i < length:
				j = 0
				plength = len(G[i])
				while j < plength:
					if  G[i][j] == ["e"]:
						G[i].remove(G[i][j])
						plength = plength - 1
						j = j - 1
						if len(G[i]) == 0:
							G.pop(i)
							NT.pop(i)
							length = length - 1
							i = i - 1
					else:
						if all(x in nullable for x in G[i][j]) and not(NT[i] in nullable):
							nullable.append(NT[i])
							newSymbol = True
					j = j + 1
				i = i + 1
		expandProductions(nullable, G, NT, alphabet)


def expandProductions(nullable, G, NT, alphabet):#sobstitutes the occurrencies of nullable symbols in all other productions
	for x in range(0, len(nullable)):
		for i in range(0, len(G)):
			length = len(G[i])
			j = 0
			while j < length:
				if (nullable[x] in NT) and (nullable[x] in G[i][j]):
					counter = 0
					original = []
					original.extend(G[i][j])
					G[i].insert(j + 1 + counter, original)
					length = length + 1
					while nullable[x] in G[i][j]:
						G[i][j].remove(nullable[x])
						copy = []
						if len(G[i][j]) == 0:
							copy = ["e"]
						else:
							copy.extend(G[i][j])
						if G[i].count(G[i][j]) == 1:
							counter = counter + 1
							G[i].insert(j + 1 + counter, copy)
							length = length + 1
					G[i].pop(j)
					length = length - 1
					j = j + counter
				if not(nullable[x] in NT) and (nullable[x] in G[i][j]):
					while nullable[x] in G[i][j]:
						G[i][j].remove(nullable[x])
						copy = []
						if len(G[i][j]) == 0:
							copy = ["e"]
							G[i][j] = copy
					if G[i].count(G[i][j]) > 1:
						G[i].remove(G[i][j])
						length = length - 1
				j = j + 1
	if "S" in nullable:
		index = NT.index('S')
		alphabet['e'] = ['S']

	else:
		alphabet.pop("e")
	print "after the elimination of e-productions, this are nonterminals and grammar productions"
	print NT
	print G
	print "\n"

def unitProductions(G, NT):#eliminates unit productions
	backwards = False
	for x in range(0, len(G)):
		for y in range(0, len(G)):
			if [NT[y]] in G[x]:
				G[x].remove([NT[y]])
				for i in range(0, len(G[y])):
					if not(G[y][i] in G[x]):
						copy = []
						copy.extend(G[y][i])
						G[x].append(copy)
				if [NT[x]] in G[x]:
					G[x].remove(NT[x])
				if y > x:
					backwards = True
		if backwards:
			for y in range(len(G) - 1, - 1, -1):
				if [NT[y]] in G[x]:
					G[x].remove([NT[y]])
					for i in range(0, len(G[y])):
						if not(G[y][i] in G[x]):
							copy = []
							copy.extend(G[y][i])
							G[x].append(copy)
					if [NT[x]] in G[x]:
						G[x].remove(NT[x])
	print "after the elimination of unit productions, this is the grammar"
	print G, "\n"

def chomskyform(G, NT):#sobstitutes all occurrencies of terminal symbols with new non terminals
	length = len(NT)
	for i in range(0, length):
		for j in range(0, len(G[i])):
			for k in range(0, len(G[i][j])):
				if not(G[i][j][k] in NT) and (len(G[i][j]) != 1):
					if(G[i][j][k] != "e"):
						letter = findletter(NT)
						alphabet[G[i][j][k]].extend(letter)
						copy = []
						copy.append(G[i][j][k])
						G.append([copy])
						G[i][j][k] = letter
						NT.append(letter)
	for i in range(0, length):#all productions of nonterminals are made of length 2
		plength = len(G[i])
		for j in range(0, plength):
			slength = len(G[i][j])
			while slength > 2:
				if all(x in NT for x in G[i][j]):
					letter = findletter(NT)
					copy = []
					copy.append(G[i][j][0:2])
					G.append(copy)
					NT.append(letter)
					G[i][j][0] = letter
					G[i][j].pop(1)
					slength = slength - 1
	print "this is one of the possible reductions in Chomsky Normal Form"
	print NT
	print G
	print "\n"

def findletter(NT):
	i = 65
	for i in range(65, 90):
		if not(chr(i) in NT):
			return chr(i)

def updatealphabet(alphabet, G, NT):
	newalphabet = alphabet.copy()
	for i in range(0, len(G)):
		for j in range(0, len(G[i])):
			if len(G[i][j]) == 1:
					newalphabet[G[i][j][0]].extend(NT[i])
					newalphabet[G[i][j][0]] = list(set(newalphabet[G[i][j][0]]))
	alphabet = newalphabet
	return alphabet



grammarParser(grammatica)
alphabetCreation(G, NT)

eProductions(G, NT, alphabet)
unitProductions(G, NT)
uselessSymbols(G, NT, alphabet)
chomskyform(G, NT)
alphabet = updatealphabet(alphabet, G, NT)

grammar = G
nonterminali = NT

def CYK(w, alfabeto):#cocke younger kasami algorithm
	assert type(w) == str
	n = len(w)
	matrix = []
	for i in range(0, n + 1):
		matrix.append([0])
		for j in range(0, n - 1):
			matrix[i].extend([0])
	for i in range(0, n):
		matrix[0][i] = w[i]
	for i in range(0, n):
		test = alfabeto.get(w[i])
		if test == None:
			print("one of the symbols is not an acceptable terminal")
			return False
		symbol = alfabeto[w[i]]
		matrix[1][i] = symbol
	#print matrix
	i = 2
	j = n-1

	while i <= n:
		index = 0
		while index < j:
			matrix = esaminatriangolo(matrix, i, index)
			index += 1
		j -= 1
		i += 1
	print "this is the recognition matrix"
	for x in range(0, len(matrix)):
		print matrix[x]
	if "S" in matrix[len(w)][0]:
		return matrix
	return False

def esaminatriangolo(matrix, i, j):#examines preceding cells to fill another one
	cella = []
	for x in range(1, i):
			cella1 = matrix[x][j]
			cella2 = matrix[i-x][j+x]
			if (len(cella1) != 0) and len(cella2) != 0:
				combinazioni = []
				combinazioni = creaCombinazioni(cella1, cella2)
				for z in range(0, len(combinazioni)):
					for t in range(0, len(grammar)):
							for g in range(0, len(grammar[t])):
								if combinazioni[z] == grammar[t][g]:
									cella.extend([nonterminali[t]])
	cella = list(set(cella))#eliminates redundancies in order to improve performances
	matrix[i][j] = cella
	return matrix

def creaCombinazioni(cella1, cella2):#creates all possible combinations of non terminal symbols
	combinazioni = []
	for x in range(0, len(cella1)):
		firstSymbol = cella1[x]
		for y in range(0, len(cella2)):
			secondSymbol = cella2[y]
			combinazioni.append([firstSymbol, secondSymbol])
	return combinazioni

matrix = CYK(stringa, alphabet)
if matrix == False:
	print "the word is not parsable"
else:
	print "the word belongs to L(G)"

'''
------------------------------------------------------------------------------------------
example from the yellow book, page 164:

grammar
	S->CB|FA|FB;A->CS|FD|a;B->FS|CE|b;C->a;D->AA;E->BB;F->b.
word
	aababb

recognition matrix

[['A', 'C'], ['A', 'C'], ['B', 'F'], ['A', 'C'], ['B', 'F'], ['B', 'F']]

[['D'],      ['S'],      ['S'],      ['S'],      ['S', 'E'],          0]

[['A'],      ['A'],      ['B'],      ['A', 'B'], 0,                   0]

[['D'],      ['S'],     ['S', 'E'],  0,          0,        		      0]

[['A'],      ['A', 'B'],  0,         0,          0, 		          0]

[['S', 'D'],  0,          0,         0,          0,                   0]

the word belongs to L(G)
---------------------------------------------------------------------------------------

grammar
	S->AB|BC;A->BA|a;B->CC|b;C->AB|a.

word
	baaba

recognition matrix

[['B'], ['A', 'C'], ['A', 'C'], ['B'], ['A', 'C']]

[['A', 'S'], ['B'], ['S', 'C'], ['A', 'S'],     0]

[[],    ['B'],      ['B'],      0,              0]

[[],    ['A', 'S', 'C'], 0,     0,              0]

[['A', 'S', 'C'], 0, 0,         0,              0]

the word belongs to L(G)

-------------------------------------------------------------------------------------
grammar
	S->ASB|e;A->aAS|a;B->SbS|A|bb.

word
	aaabbbb

recognition matrix

[['A', 'C', 'D', 'I', 'J'], ['A', 'C', 'D', 'I', 'J'], ['A', 'C', 'D', 'I', 'J'], ['B', 'E', 'F', 'G', 'H'], ['B', 'E', 'F', 'G', 'H'], ['B', 'E', 'F', 'G', 'H'], ['B', 'E', 'F', 'G', 'H']]

[['A', 'B', 'L', 'N'], ['A', 'B', 'L', 'N'], ['S'], ['B'], ['B'], ['B'], 0]

[['A', 'S', 'B', 'L', 'N'], ['K', 'S'], ['S', 'M'], [], [], 0, 0]

[['A', 'K', 'B', 'M', 'S'], ['K', 'M', 'S'], ['M'], [], 0, 0, 0]

[['A', 'K', 'B', 'M', 'S'], ['S', 'M'], [], 0, 0, 0, 0]

[['K', 'M', 'S'], ['S', 'M'], 0, 0, 0, 0, 0]

[['K', 'M', 'S'], 0, 0, 0, 0, 0, 0]

the word belongs to the grammar

--------------------------------------------------------------------------------------

'''
