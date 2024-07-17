-- the goal of this file is to compute the T2-equivariant integral Chow ring
-- of AA(2,N)\D where AA(2,N) represents the affine space of binary forms of degree N
-- while D is the discriminant locus consisting of form of at least double roots
-- with a general T2 action specified in Edidin-Hu, Proposition 5.1

load "projBundle.m2"
load "hyperplaneClass.m2"

chowSmoothBinaryForms = method();
chowSmoothBinaryForms(ZZ, List, List, PolynomialRing) := (N, L, W, R) -> (
    -- N denotes the degree of binary forms
    -- L is a list representing the global weights of T2-action
    -- W is a list consisting of two sublist each of which has length two
    -- separately representing weights on x0 and x1 -- variables of binary forms
    -- R is the chow ring of classifying space of T2
    -- with generators l1, l2 as classes of standard 1-d characters of T2
    t := symbol t;
    R1 := R[t];
    V := first entries vars R;
    gRelation := L#0 * V#0 + L#1 * V#1 - t;
    T1 := equivChernRoot(2, W#0, R);
    T2 := equivChernRoot(2, W#1, R);
    push10 := 2*(N - 1)*t - N*(N - 1)*(T1 + T2);
    push11 := t^2 - (T1 + T2)*t - N*(N - 2)*T1*T2;
    polyRelation := product(apply(W, i -> t + equivChernRoot(2, i, R)));
    return R1/ideal(gRelation, push10, push11, polyRelation);
)

-- test for exact numbers
chowSmoothBinaryForms(6, {1,2}, {{2,3},{4,5}}, ZZ[l_1..l_2])

-- test for symbolic computation

