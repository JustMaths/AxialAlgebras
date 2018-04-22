#########################
#
# Python script to extract the results from the directory of results
# It prints in the form of a latex table Group & num & shape & dim & dim
#
# It should be run:
#
# python listresults.py 'library/RationalField()'
#
import re
import os
import os.path
import sys

dirname = sys.argv[1]

all_results = []

groups = os.listdir(dirname)
groups.remove('basic_algebras')
groups.sort()
for group in groups:
  nums = os.listdir(os.path.join(dirname, group))
  nums.sort()
  for num in nums:
    shapes = os.listdir(os.path.join(dirname, group, num))
    shapes.sort()
    for shape in shapes:
      realshape = re.sub('(5A)*(6A)*(_partial)*(.json)*','',shape)
      if "_partial" in shape:
        dim = "N/A"
      else:
        dim=""
      all_results.append("%s & %s & %s & %s & %s\\\\"%(group, num, realshape, dim, dim))

with open("allresults.out", "w") as f:
  for result in all_results:
    f.write(result+"\n")
