import os

cwd = os.getcwd()
ex = cwd + '/examples'
print(ex)
count = 1

with open('example_list.m', 'w') as f:
  example_list = os.listdir(ex)
  f.write('print "Running through {0} example files";\n'.format(len(example_list)))
  for e in example_list:
    example_file = ex + '/' + e
    f.write('print "\\t{0}. `{1}`";\n'.format(count, e))
    count += 1
    f.write('load "{0}";\n'.format(example_file))
