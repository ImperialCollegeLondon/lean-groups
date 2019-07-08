-- bundled subgroups

-- We're going to make one object which is all the subgroups of G.

-- first let's do some tests

import group_theory.subgroup
import algebra.group.hom

example (G1 G2 : Type*) [group G1] [group G2]
  (f : G1 → G2) [is_group_hom f] (H1 : set G1) [is_subgroup H1] :
  is_subgroup (f '' H1) :=
{ one_mem := _,
  mul_mem := _,
  inv_mem := _ }
