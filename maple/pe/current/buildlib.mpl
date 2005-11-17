interface(warnlevel = 1):
with(LibraryTools):

try
    FileTools:-MakeDirectory("lib");
    lprint("lib directory created");
catch:
end try;

savelibname := "lib":

$include "utils.mpl"

Save(printmod);

$include "gen.mpl"

Save(NameGenerator);

$include "types.mpl"

Save(funcPrefixType);
Save(`type/inert`);
Save(`type/m`);
Save(`type/tag`);
Save('`type/onenv`');
Save('`type/Static`');
Save('`type/Dynamic`');

Save(`index/err`);
Save(`index/deb`);

$include "m_def.mpl"

Save(M);

$include "pe_def.mpl"

Save(OnPE);