with(LibraryTools);
savelibname := "/home/mike/thesis/maple/pe/current/lib";


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
