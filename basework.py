#!/usr/bin/python3.11

# A small program that reads rewrite rules from a base Haskell file, applies them in the compiled Haskell files, and adds imports from a YAML config file.

from typing import *
import re
from string import whitespace  # a string containing all whitespace characters
import os
import yaml

inQuotes = re.compile('"(.*?)"')

# Parses a line of the base Haskell file.
# Returns the rewrite rule given, or None if it's not a rewrite rule line.
def parseBaseLine(line: str, linenum: int) -> Tuple[str, str] | None:
    if "--()" == line[:4]:
        sides: List[str]
        sides = line[4:].split("=>")
        if 2 != len(sides): raise Exception("Error at row %d: no (or more than one) =>'s in a rewrite rule" % linenum)
        leftSide = re.search(inQuotes, sides[0])
        if leftSide is None: raise Exception("Error at row %d: illegal left side" % linenum)
        rightSide = re.search(inQuotes, sides[1])
        if rightSide is None: raise Exception("Error at row %d: illegal right side" % linenum)
        return (leftSide.group(1), rightSide.group(1))
    else: return None

# Parses the entire base file given by the module name (without the `.hs` extension).
# Returns the list of the rewrite rules found in the file.
def parseBase(name: str) -> List[Tuple[str, str]]:
    result = list()
    i: int
    i = 1
    with open(name+".hs", 'r') as f:
        for line in f:
            lineResult = parseBaseLine(line, i)
            if not lineResult is None: result.append(lineResult)
            i += 1
    return result

# Whether a line should be kept or commented out.
# We should comment out all imports given, except those that are in the config file as our own modules.
# We should also comment out all the continuations of commented lines (i. e. when they start with whitespace and the previous one was commented out; now we don't have to think about different levels).
def shouldKeepLine(line: str, previousWasKept: bool, modules: List[str]) -> bool:
    if "import " == line[:7]:
      words: List[str]
      words = line.split(' ')[1:] # we cut down 'import'
      for module in modules:
          if module in words: return True
      return False
    elif line[0] in whitespace: return previousWasKept
    else: return True

# Writes our imports to a file given by a file object.
def writeImports(newf, base: str, imports: List[str]) -> None:
    newf.write("import "+base+"\n\n") # another empty row after it

    for module in imports:
        newf.write("import "+module+'\n')
    newf.write('\n')

# Returns the rewritten version of a single line. Comments it out if it is a non-desired import; applies the rewrite rules.
def rewrittenLine(line: str, previousWasKept: bool, modules: List[str], rules: List[Tuple[str, str]]) -> str:
    if not shouldKeepLine(line, previousWasKept, modules):
        line = "-- "+line
    for rule in rules:
        # this might not be too efficient
        line = line.replace(rule[0], rule[1])
    return line

# Rewrites a file given by name (without the `.hs` extension).
def rewriteFile(name: str, base: str, modules: List[str], imports: List[str], rules: List[Tuple[str, str]]) -> None:
    fileName: str
    fileName = name+".hs"
    tempFileName: str
    tempFileName = name+"_tmp.hs"
    
    with open(fileName, 'r') as oldf:
        with open(tempFileName, 'w') as newf:
            line: str
            line = " "
            while "" != line and not ("module "+name+" where") in line:
                line=oldf.readline()
                newf.write(line)
            newf.write('\n') # an empty row after it

            writeImports(newf, base, imports)

            line = oldf.readline()
            previousWasKept: bool
            previousWasKept = True
            while "" != line:
                newLine: str
                newLine = rewrittenLine(line, previousWasKept, modules, rules)
                newf.write(newLine)
                previousWasKept = newLine.count("--") == line.count("--")
                line = oldf.readline()
    # and we replace the original file with the `_tmp` one
    os.replace(tempFileName, fileName)
