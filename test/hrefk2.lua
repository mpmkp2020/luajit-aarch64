
local bit = require("bit")

t={}

for i=1,100 do

t[true] = i
t[false] = i
end

expect = 100

assert(t[true] == expect, "Expect "..expect..", get "..t[true])
assert(t[false] == expect, "Expect "..expect..", get "..t[false])

