
# type of inert forms
`type/inert` := curry(funcPrefixType, '_Inert_');

# type used buy the partial evaluator's intermediate forms
`type/tag`   := curry(funcPrefixType, '_Tag_');

# type of M forms
`type/m`     := curry(funcPrefixType, 'M');


funcPrefixType := proc(prefix, f)
   if nargs = 2 then
       type(f, function) and StringTools:-RegMatch(cat("^", prefix), op(0, f));
   elif nargs = 3 then
       type(f, specfunc(anything, map2(cat, prefix, args[3])));
   else 
       error("must be called with 1 or 2 args");
   end if;
end proc;
