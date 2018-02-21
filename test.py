import subprocess
import os

def erroneo(arg):
    task = subprocess.Popen("../../compilador/tiger " + arg, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    data = task.stdout.read()
    err = task.stderr.read()
    if err != "":
        exit("El caso " + arg + " tiro error: " + err)  
    elif "yes!" in data.lower():
        exit("El caso " + arg + " compilo bien y no deberia.")
    else:
        print arg + "... OK"

def correcto(arg):
    task = subprocess.Popen("../../compilador/tiger " + arg, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    data = task.stdout.read()
    err = task.stderr.read()
    if err != "":
        exit("El caso " + arg + " tiro error: " + err)  
    elif "yes!" not in data.lower():
        exit("El caso " + arg + " tiro el error: " + data)
    else:
        print arg + "... OK"
print "###SYNTAX###"
os.chdir("../tests/syntax")
archivos = os.listdir(os.curdir)
for f in archivos:
    erroneo(f)
print "###TYPE###"
os.chdir("../type")
archivos = os.listdir(os.curdir)
for f in archivos:
    erroneo(f)
print "###GOOD###"
os.chdir("../good")
archivos = os.listdir(os.curdir)
for f in archivos:
    correcto(f)
    
