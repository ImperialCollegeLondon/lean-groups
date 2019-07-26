-- Sian's work on bundled subgroups

import group_theory.subgroup
import algebra.group.hom

/- functions banned from this file:

1) is_submonoid
2) is_subgroup
3) is_group_hom
4) is_monoid_hom

-/

-- bundled submonoids!
structure submonoid (M : Type*) [monoid M] :=
(S : set M)
(one_mem : (1 : M) ∈ S)
(mul_mem {a b} : a ∈ S → b ∈ S → a * b ∈ S)

-- bundled subgroups
structure subgroup (G : Type*) [group G] extends submonoid G :=
(inv_mem {a} : a ∈ S → a⁻¹ ∈ S)

-- bundled group homs
structure group_hom (G : Type*) (H : Type*) [group G] [group H] :=
(f : G → H)
(mul  : ∀ x y, f (x * y) = f x * f y)

-- infixr means "define notation for group_hom G H, put it in the middle of G and H, and
-- make it right associative". The 25 is its "bidmas number", i.e. its binding power.

infixr ` →g `:25 := group_hom -- is this notation terrible? 

-- The place for easy lemmas about group homs is in the group_hom namespace
namespace group_hom

variables {G : Type*} {H : Type*} [group G] [group H]

-- This is some technical thing.
-- I want to treat a term of type `group_hom G H` as an actual function sometimes.
instance : has_coe_to_fun (G →g H) := ⟨_, f⟩

--example {G : Type*} {H : Type*} [group G] [group H] (f f' : G →ₘ H) (H : ∀ (x : G), f x = f' x) : f = f' := sorry
--#exit

@[extensionality] theorem ext {G : Type*} {H : Type*} [group G] [group H]
  {f f' : G →g H} (H : ∀ (x : G), f x = f' x) : f = f' :=
by cases f; cases f'; congr'; exact funext H

theorem ext_iff {f f' : G →g H} : f = f' ↔ ∀ x, f x = f' x :=
⟨by rintro rfl; simp, ext⟩

variable (f : G →g H)

@[simp] lemma map_mul (x y : G) : f (x * y) = f x * f y := f.mul x y

@[simp] lemma map_one : f 1 = 1 := 
mul_self_iff_eq_one.1 $ begin rw [← map_mul f, one_mul] end
--I'm not really sure how this "by" notation works
--I'm using it because I want to be able to, change the goal? and
--I'm not sure how else I could, but I don't know how to use it again.

@[simp] lemma map_inv (x : G) : f (x⁻¹) = (f x)⁻¹ := 
eq_inv_of_mul_eq_one $ by rw [← map_mul f, inv_mul_self, map_one f]

--example (g : G) : g * g = g → g = 1 := by library_search


definition map (G1 G2 : Type*) [group G1] [group G2]
  (f : G1 →g G2) (H1 : subgroup G1) : subgroup G2 :=
{ S := f '' H1.S,
  one_mem := begin
    -- ugly notation leakage -- why?
    show (1 : G2) ∈ f '' H1.S,
    use 1,
    split,
    { show (1 : G1) ∈ H1.S,
      exact H1.one_mem,
    },
    { 
      exact group_hom.map_one f,
    }
  end,
  mul_mem := begin 
   show ∀ {a b : G2}, a ∈ (⇑f '' H1.S) → b ∈ (⇑f '' H1.S) → (a*b) ∈ (⇑f '' H1.S),
   rintro j k ⟨j', hj', rfl⟩ ⟨k', hk', rfl⟩,
   rw [← group_hom.map_mul f j' k'],
   unfold set.image,
   dsimp,
   use j'*k',
   split,
    apply submonoid.mul_mem,
       assumption,
    assumption,
   refl,
  end,
  inv_mem := begin
  rintro j ⟨j', hj', rfl⟩,
  show (f j')⁻¹ ∈ f '' H1.S,
  rw [← group_hom.map_inv f j'],
  unfold set.image,
  dsimp,
  use j'⁻¹,
  split,
    apply subgroup.inv_mem,
    assumption,
  refl,
  end
}

end group_hom 

