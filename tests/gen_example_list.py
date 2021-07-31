import os

cwd = os.getcwd()
ex = cwd + '/examples/'
print(ex)

with open('example_list.m', 'w') as f:
  for e in os.listdir(ex):
    f.write('load "' + ex + '/' + e + '";\n')

