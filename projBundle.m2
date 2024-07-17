needsPackage "SpechtModule"

-- start with the defining rep E of GLn (of rank n)
-- ch(E) decomposes into sum of linearly indep characters \lambda_k
-- denote by the first Chern class c1(\lambda_k) = t_k
-- we have the Tn-equiv Chow ring of a point to be the polynomial ring in t_k
-- and the GLn-equiv Chow ring of a point to be the polynomial ring in c_k
-- where c_k = ck(E) = e_k(t_1,\ldots,t_k) the kth elementary symmetric poly

-- in general, take a representation V of GLn of rank r
-- viewing V as a Tn-module allows us to decompose V = \sum \mu_k into characters
-- denote l_k = c1(\mu_k) the top chern of character, called the chern root of V
-- there is a formula for the chow ring of PP(V) called the projective bundle theorem

equivChernRoot = method();
equivChernRoot(ZZ, List, PolynomialRing) := (n, W, R) -> (
    -- length of list W is n
    -- number of variables in R should be n too
    L := first entries vars R;
    if (length W == n) and (length L == n) then (
        equivCh1 = 0;
        for i from 0 to (n - 1) do (
            equivCh1 = equivCh1 + W#i * L#i;
        )
    );
    return equivCh1;
)

-- An example
-- Consider a character \mu of T3 given by the lattice point (2*a,3*b,4*c)
-- note: we can make the weights to be symbolic as this example shows
-- we compute c1(\mu) as follow

T = ZZ[a,b,c]; -- define a ring with symbols a,b,c
R = T[l_1..l_3]; -- l_k are basis for A(BT)
W = {2*a, 3*b, 4*c}; -- input the weights
equivChernRoot(3,W,R) -- with output the corresponding Chern root



-- Projective bundle theorem

chowProjBundleTorus = method();
chowProjBundleTorus(ZZ, ZZ, List, PolynomialRing) := (n, r, W, R) -> (
    -- length of W is r i.e. rank r vector bundle
    -- W has r sublists each of which has length n corresponding to n-D torus
    -- and each sublist represents the weight on the corresponding coordinate
    -- ring R = ZZ[l_1..l_n] is the Chow ring of T_n

    -- add one if..do.. for length W == r

    t := symbol t; -- hyperplane class
    R1 := R[t];
    L := first entries vars R;
    coordinateChern := apply(W, i -> t + equivChernRoot(n, i, R)); 
    relationTorus := product(coordinateChern);
    return R1/ideal(relationTorus);
)

-- In particular, the polynomial relation from the projective bundle formula
-- can be obtained as following

chowPolyRelationTn = method();
chowPolyRelationTn(ZZ, ZZ, List, PolynomialRing) := (n, r, W, R) -> (
    t := symbol t;
    R1 := R[t];
    L := first entries vars R;
    coordinateChern := apply(W, i -> t + equivChernRoot(n, i, R));
    return product(coordinateChern);
)


chowProjBundleGLn = method();
chowProjBundleGLn(ZZ, ZZ, List, PolynomialRing) := (n, r, W, R) -> (
    -- this is simply coming from torus action
    -- together with Weyl group Sn acting on A(BT) by permuting factors
    t := symbol t; -- hyperplane class
    R1 := R[t];
    L := first entries vars R;
    coordinateChern := apply(W, i -> equivChernRoot(n, i, R)); 
    T := ZZ[a_1..a_r];
    elsympoly := elementarySymmetricPolynomials(T);
    chernCharacter := apply(elsympoly, i -> sub(i, apply(first entries vars T, j -> (j => coordinateChern#(index j)))));
    relationGLn := t^(r);
    for i from 0 to (r - 1) do (
        relationGLn = relationGLn + chernCharacter#i * t^(r - i - 1);
    );
    return R1/ideal(relationGLn);
)

-- in particular, the following function returns the Chern characters
-- as elementary symmetric polynomials of Chern roots

equivChernCharacter = method();
equivChernCharacter(ZZ, ZZ, List, PolynomialRing) := (n, r, W, R) -> (
    -- recall that let V be a r-dimensional representation of GLn
    -- Tn is a maximal torus in GLn with Chow ring of classifying space R
    -- thus the variables of polynomial ring R are the class of characters of Tn
    -- W is the list of weights of the torus actions
    -- which has r sublists, each of which has length n
    L := first entries vars R;
    coordinateChern := apply(W, i -> equivChernRoot(n, i, R));
    T := ZZ[a_1..a_r];
    elsympoly := elementarySymmetricPolynomials(T);
    chernCharacter := apply(elsympoly, i -> sub(i, apply(first entries vars T, j -> (j => coordinateChern#(index j)))));
    return chernCharacter;
)
