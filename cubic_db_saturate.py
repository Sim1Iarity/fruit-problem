import re, os, sys
f = open('cubic_db.txt', 'rt')
fout = open('cubic_db_saturated.txt', 'at+')
reg = re.compile(r'(\d+) \[\[(.*)\]\](.*)')
reg_null = re.compile(r'(\d+) \[\]')
start = int(input())
i = 0
for i in range(start): f.readline()
i = 0
while True:
    print("Reading line", i+start, file=sys.stderr)
    s = f.readline()
    if s == "": break
    ma = reg.match(s)
    if ma is None:
        ma = reg_null.match(s)
        fout.write(ma.group(0) + "\n")
        i += 1
        continue
    if ma.group(3) != "":
        fout.write(s)
        i += 1
        continue
    fout.write(ma.group(1) + " ")
    os.system('echo "ellsaturation(mkc(%s),[[%s]],1000)" | gp -q -s 1073741824 cubic.gp >cubic_db_saturated_temp.txt' % (ma.group(1), ma.group(2)))
    ftemp = open('cubic_db_saturated_temp.txt', 'rt')
    fout.write(ftemp.readline()[:-1])
    ftemp.close()
    fout.write(ma.group(3) + "\n")
    fout.flush()
    i += 1
f.close()
fout.close()