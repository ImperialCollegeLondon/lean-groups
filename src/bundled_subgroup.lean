-- Sian's work on bundled subgroups

import group_theory.subgroup
import algebra.group.hom
import bundled_group_homs

/- functions banned from this file:

1) is_submonoid
2) is_subgroup
3) is_group_hom
4) is_monoid_hom

-/

-- we want

-- The place for easy lemmas about group homs is in the group_hom namespace
namespace group_hom

variables {G : Type*} {H : Type*} [group G] [group H]

@[extensionality] theorem ext {G : Type*} {H : Type*} [group G] [group H]
  {f f' : G →* H} (H : ∀ (x : G), f x = f' x) : f = f' :=
by cases f; cases f'; congr'; exact funext H

theorem ext_iff {f f' : G →* H} : f = f' ↔ ∀ x, f x = f' x :=
⟨by rintro rfl; simp, ext⟩

variable (f : G →* H)

@[simp] lemma map_mul : ∀ (x y : G), f (x * y) = f x * f y := f.map_mul

@[simp] lemma map_one : f 1 = 1 := f.map_one

end group_hom -- namespace

-- bundled submonoids!
set_option old_structure_cmd true
structure submonoid (M : Type*) [monoid M] :=
(carrier : set M)
(one_mem : (1 : M) ∈ carrier)
(mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)

variables {M : Type*} [monoid M]

instance submonoid.has_coe : has_coe (submonoid M) (set M) := ⟨submonoid.carrier⟩

-- bundled subgroups
structure subgroup (G : Type*) [group G] extends submonoid G :=
(inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier)

variables {G : Type*} [group G] {H : Type*} [group H]

namespace subgroup

instance has_coe : has_coe (subgroup G) (set G) := ⟨subgroup.carrier⟩

definition map (f : G →* H) (G1 : subgroup G) : subgroup H :=
{ carrier := f '' (G1 : set G),
  one_mem := begin
    use 1,
    split,
    { 
      exact G1.one_mem,
    },
    { 
      exact group_hom.map_one f,
    }
  end,
  mul_mem := begin 
    rintro j k ⟨j', hj', rfl⟩ ⟨k', hk', rfl⟩,
    rw [← group_hom.map_mul f j' k'],
    use j'*k',
    split,
      apply G1.mul_mem,
        assumption,
      assumption,
    refl,
  end,
  inv_mem := begin
    rintro j ⟨j', hj', rfl⟩,
    rw [← group_hom.map_inv f j'],
    use j'⁻¹,
    split,
      apply subgroup.inv_mem,
      assumption,
    refl,
  end
}

definition comap (f : G →* H) (H1 : subgroup H) : subgroup G :=
{ carrier := f ⁻¹' (H1 : set H),
  one_mem := begin sorry end,
  mul_mem := begin sorry end,
  inv_mem := begin sorry end
}

end subgroup
