-- bundled subgroups

-- We're going to make one object which is all the subgroups of G.

-- first let's do some tests

import group_theory.subgroup
import algebra.group.hom

--#print notation '' 
 

example (G1 G2 : Type*) [group G1] [group G2]
  (f : G1 → G2) [is_group_hom f] (H1 : set G1) [is_subgroup H1] :
  is_subgroup (f '' H1) :=
{ one_mem := 
begin
show (1:G2) ∈ f '' H1,
unfold set.image,
use (1),
split,
{exact is_submonoid.one_mem H1},
{exact is_group_hom.map_one f}    
end,
  mul_mem := 
  begin
  intro j,
  intro k,
  intro n,
  intro m,
  --this is true because f is a group homomorphism
  --I need to get the preimage of j and k, then this is true by is_group_hom.map_mul
   sorry 
  end,
  
  inv_mem := 
  begin
  intro j,
  intro k,
  --I need the preimage of j, this is then true by is_group_hom.map_inv
  
  sorry
  end
   }
