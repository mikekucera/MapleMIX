#$Source: /u/maple/research/lib/src/RCS/Weierstrass,v $ 
################################################################ 
# 
#      weier - Weierstrass Elliptic and Related Functions 
# 
################################################################ 

################################################################ 
# 
#          Definitions 
# 
# (1)   WeierstrassP is a doubly-periodic elliptic function 
# defined by: 
# 
#      WeierstrassP(z, g2, g3) 
#      = 1/z^2+sum(1/(z-w)^2-1/w^2) 
# 
# where the sum ranges over w=2*m1*omega1+2*m2*omega2 
# such that (m1, m2) is in (Z x Z) - (0, 0). 
# (2)   WeierstrassPPrime is the derivative of WeierstrassP 
# defined by: 
# 
#      WeierstrassPPrime(z, g2, g3) 
#      = diff(WeierstrassP(z, g2, g3), z) 
#      = -2/z^3-2*sum(1/(z-w)^3) 
# 
# where the sum ranges over w=2*m1*omega1+2*m2*omega2 
# such that (m1, m2) is in (Z x Z) - (0, 0). 
# (3)   WeierstrassZeta is related to the anti-derivative of 
# WeierstrassP and is defined by: 
# 
#      WeierstrassZeta(z, g2, g3) 
#      = -int(WeierstrassP(t, g2, g3), t=0..z) 
#      = 1/z+sum(1/(z-w)+1/w+z/w^2) 
# 
# where the sum ranges over w=2*m1*omega1+2*m2*omega2 
# such that (m1, m2) is in (Z x Z) - (0, 0). 
# (4)   WeierstrassSigma is related to the anti-derivative of 
# WeierstrassZeta and is defined by: 
# 
#      WeierstrassSigma(z, g2, g3) 
#      = exp(int(WeierstrassZeta(t, g2, g3), t=0..z)) 
#      = z*product((1-z/w)*exp(z/w+z^2/(2*w^2))) 
# 
# where the product ranges over w=2*m1*omega1+2*m2*omega2 
# such that (m1, m2) is in (Z x Z) - (0, 0). 
################################################################ 

# Zero handler for most cases - not to be saved
ZeroHandler := proc(z, g2, g3)
    if hastype([z,g2,g3],'nonreal') then
	NumericEvent('division_by_zero', infinity+infinity*I);
    else
	NumericEvent('real_to_complex',
	      NumericEvent('division_by_zero', infinity+infinity*I) );
    fi;
end:

# RootOf handler for most cases - not to be saved
RootOfHandler := proc(tp, z, g2, g3)
    local s,x;
    # case input is of form RootOf(a*Weierstrass(_Z,g2,g3) - b)
    # in which case we return b/a
    s := subs(tp(_Z, g2, g3)=x,op(1,z));
    if type(s,'polynom'('anything',x)) and degree(s,x) = 1 then
       - coeff(s,x,0)/coeff(s,x,1);
    else
       'tp'(z, g2, g3);
    fi; 
end:

# RootOf handler for WeierstrassPPrime case, has 1 more simplification
RootOfHandlerWPP := proc(tp, z, g2, g3)
    local s,x;
    # case input is of form RootOf(a*WeierstrassPPrime(_Z,g2,g3) - b)
    # in which case we return b/a
    s := subs('WeierstrassPPrime'(_Z, g2, g3)=x,op(1,z));
    if type(s,'polynom'('anything',x)) and degree(s,x) = 1 then
       return - coeff(s,x,0)/coeff(s,x,1);
    end if;

    # case input is of form RootOf(a*WeierstrassPPrime(_Z,g2,g3) - b)
    # in which case we return b/a
    s := subs('WeierstrassP'(_Z, g2, g3)=x,op(1,z));
    if type(s,'polynom'('anything',x)) and degree(s,x) = 1 then
       s := -coeff(s,x,0)/coeff(s,x,1);
       sqrt( 4*s^3 -g2*s -g3 );
    else
       'tp'(z, g2, g3);
    fi; 
end:
# This routine is *not* to be saved !
BuildWeierstrass := proc(a, zh, rh, dh)
	local zero_handler, rootof_handler, default_handler;

	zero_handler := eval(zh);
	rootof_handler := eval(rh);
	default_handler := eval(dh);

	unprotect(a);
	assign(a,
	proc(z::algebraic, g2::algebraic, g3::algebraic)
	local res;
	option `Copyright (c) 2001 by Waterloo Maple Inc. All rights reserved.`;

	if nargs <> 3 then
		error "expecting 3 arguments but got %1", nargs;
	elif type(z,'complex(float)') or type(g2,'complex(float)') or type(g3, 'complex(float)') then
		res := evalf('procname'(z, g2, g3));
		if type(res,'complex(float)') then
			return res;
		fi;
	elif type([z,g2,g3],'list(complex(extended_numeric))') and
		hastype([z,g2,g3],'undefined') then
		NumericTools:-ThrowUndefined(z*g2*g3,'preserve'='real');
	elif ormap('type',[z,g2,g3],'infinity') then
		return('procname'(args));
	end if;

# Some simplifications

	if z = 0 then
		zero_handler(z, g2, g3)
	elif op(0,z) = 'RootOf' then
		rootof_handler(procname, z, g2, g3)
	else
		default_handler(z, g2, g3)
	end if;
	end);
	protect(a);
end:

BuildWeierstrass('WeierstrassP', ZeroHandler, RootOfHandler,
	(z,g2,g3) -> 'WeierstrassP'(`tools/sign`(z)*z, g2, g3) );
#savelib( 'WeierstrassP' ):

BuildWeierstrass('WeierstrassPPrime', ZeroHandler, RootOfHandlerWPP,
	(z,g2,g3) -> `tools/sign`(z)*'WeierstrassPPrime'(`tools/sign`(z)*z, g2, g3) );
#savelib( 'WeierstrassPPrime' ):

BuildWeierstrass('WeierstrassZeta', ZeroHandler, RootOfHandler,
	(z,g2,g3) -> `tools/sign`(z)*'WeierstrassZeta'(`tools/sign`(z)*z, g2, g3) );
#savelib( 'WeierstrassZeta' ):

BuildWeierstrass('WeierstrassSigma', 0, RootOfHandler,
	(z,g2,g3) -> `tools/sign`(z)*'WeierstrassSigma'(`tools/sign`(z)*z, g2, g3) );
#savelib( 'WeierstrassSigma' ):
