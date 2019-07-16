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

@[simp] lemma map_one : f 1 = 1 := sorry

@[simp] lemma map_inv (x : G) : f (x⁻¹) = (f x)⁻¹ := sorry

example (g : G) : g * g = g → g = 1 := by library_search

--example (f : G →g H) (g₁ g₂ g₃ : G) : f (g₁ * g₂⁻¹ * 1) = f (g₁) * (f (g₂))⁻¹ := by simp

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
      sorry
    }
  end,
  mul_mem := sorry,
  inv_mem := sorry
}

end group_hom 
