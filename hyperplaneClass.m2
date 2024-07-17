-- equivariant class of hyperplane given by some character can be easily computed
-- using the method "equivChernRoot"

-- suppose that a hyperplane in some affine space is given by f=0
-- where f is a linear form
-- with an action of T on f given by a character \chi
-- i.e. zf = \chi(z)^{-1}f

affHyperplaneClass = method();
affHyperplaneClass(ZZ, List, PolynomialRing) := (n, W, R) -> (
    return equivChernRoot(n, W, R);
)

-- the projective case is the Lemma 2.4 from Edidin-Fulghesu

projHyperplaneClass = method();
projHyperplaneClass(ZZ, List, PolynomialRing) := (n, W, R) -> (
    t := symbol t; -- hyperplane class
    R1 := R[t];
    return t + equivChernRoot(n, W, R);    
)


-- Moreover we could get the formula for the equivariant chern class of
-- degree d hypersurface in PP^n given by the vanishing locus of a degree d
-- homogeneous polynomial in terms of coordinates of PP^n
-- This is based on the result from Lemma 2.4 of Edidin-Fulghesu

projHypersurfaceClass = method();
projHypersurfaceClass(ZZ, ZZ, ZZ, List, PolynomialRing) := (n, d, W, R) -> (
    -- we denote by d the degree of hypersurface
    -- n is the dim of torus = number of vars of R
    -- W is the weights given by the action of Tn on the polynomial
    -- R is the Chow ring of the classifying space of Tn
    t := symbol t; -- hyperplane class
    L := first entries vars R; -- classes of characters of Tn
    return d*t + equivChernRoot(n, W, R);
)