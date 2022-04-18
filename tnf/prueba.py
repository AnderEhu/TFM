import numpy as np
import time

start = time.time()
arr1 = np.array([{str(i) for i in range(1000000)}, np.array({str(i)} for i in range(10000))], dtype=object)
for i in range(1000):
    arr1[0].remove(str(i))
    arr1[0].add(str(i))
print(time.time()-start)

start = time.time()
arr2 = [{str(i) for i in range(1000000)}, [{str(i)} for i in range(10000)]]
for i in range(1000):
    arr2[0].remove(str(i))
    arr1[0].add(str(i))
print(time.time()-start)