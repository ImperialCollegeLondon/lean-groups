-- bundled subgroups

-- We're going to make one object which is all the subgroups of G.

-- first let's do some tests

import group_theory.subgroup
import algebra.group.hom


 --#print notation ↥ 
 --coe_sort #0
 --#print notation ↑
 --coe

example (G1 G2 : Type*) [group G1] [group G2]
  (f : G1 → G2) [is_group_hom f] (H1 : set G1) [is_subgroup H1] (a b : H1) :
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
 -- intro j,
 -- intro k,
 -- intro n,
 -- change j ∈ f '' H1 at n,
 -- intro m,
 -- change k ∈ f '' H1 at m,
 -- show j*k ∈ f '' H1,
 -- cases n with j' hj',
 -- cases m with k' hk',
  
  rintro j k ⟨j', hj', rfl⟩ ⟨k', hk', rfl⟩,
  show (f j') * (f k') ∈ f '' H1,
  rw [← is_group_hom.map_mul f j' k'],
 
-- need to get rid of the fs
  --apply is_submonoid.mul_mem,
  end,
  
  inv_mem := 
  begin
  --intro j,
  --intro n,
  --change j ∈ f '' H1 at n,
  --show j⁻¹ ∈ f '' H1,
 

 rintro j ⟨j', hj', rfl⟩,
 show (f j')⁻¹ ∈ f '' H1,
 rw [← is_group_hom.map_inv f j'],
 
-- need to get rid of the fs
 --rw [is_subgroup.inv_mem_iff H1],
  end
   }

