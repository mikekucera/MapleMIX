interface(warnlevel = 1):
with(LibraryTools):

try
    FileTools:-MakeDirectory("lib");
    lprint("lib directory created");
catch:
end try;

savelibname := "lib":

$include "gen.mpl"

Save(NameGenerator);

$include "types.mpl"

Save(`type/inert`);
Save(`type/m`);
Save(`type/tag`);
Save(funcPrefixType);

$include "m_def.mpl"

Save(M);

$include "inert.mpl"

Save(IntermediateForms);

$include "on_env.mpl"

Save(OnENV);

$include "onpe.mpl"

Save(OnPE);
