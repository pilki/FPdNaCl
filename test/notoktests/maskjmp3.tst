;improperly masked indirect jump
%2 <- %1 and 0xffffffe0; not twice the same register
                       ; (should be accepted in a future version)
ijmp %2
