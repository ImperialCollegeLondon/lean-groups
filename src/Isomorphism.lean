--Examples of how to work with groups in Lean

-- TODO
-- order of element
-- order of group
-- some standard theorems about finite groups
-- making a subgroup
-- making a quotient group
-- isomorphism theorems

-- relevant files:

import algebra.group.basic -- stuff like mul_self_iff_eq_one, mul_inv_eq_iff_eq_mul etc
import algebra.group.hom -- unbundled group homs
import data.equiv.basic
import bundled_group_homs
import group_theory.quotient_group

/- e.g.

class is_group_hom [group α] [group β] (f : α → β) : Prop :=
(map_mul : ∀ a b : α, f (a * b) = f a * f b)
-/

import group_theory.perm.sign -- signature of a permutation

import group_theory.subgroup -- subgroups


/-
/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
class is_subgroup (s : set α) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)

class normal_subgroup [group α] (s : set α) extends is_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)

-/

import group_theory.quotient_group -- quotient groups

import bundled_subgroup

-- This gives us four functions subgroup.carrier, subgroup.one_mem,
-- subgroup.mul_mem and subgroup.inv_mem. They each eat a term
-- of type `subgroup <something>` and spit out the relevant set or proof.

-- a variable G, plus proof it's a group.

-- Subsets of a type are already bundled: they're called `set G`.
-- There's a map from `subgroup G` to `set G` which just sends
-- a subgroup `H` to its carrier set `H.carrier`; this is
-- subgroup.carrier. Let's make Lean apply it by default whenever
-- it's expecting a set and we give it a subgroup.


namespace subgroup
variables {G : Type*} [group G]

-- Two subgroups with same underlying subset are the same subgroup. 
@[extensionality] def ext (H K : subgroup G) (h : (H : set G) = K) : H = K := by cases H; cases K; cases h; refl 

-- Do you know what a partial order is? You can look it up on Wikipedia.
-- It's not hard to check that the set of subsets of a set is a partial order.
-- Because `set G` is already well-established in mathlib, it is unsurprising to
-- see that it has already been given the structure of a partial order.

example : partial_order (set G) := by apply_instance 

-- that proof works because `partial_order` is like `group`, it's a typeclass,
-- so we expect Lean to keep track of the proofs. This example just gets the proof
-- that `set G` is a partial order from its big database of proofs.

-- We would like a partial order on the sub*groups* of G, not just the subsets.
-- So we have a map `subgroup G` -> `set G` and we would like to "pull back" the
-- structure of a partial order on the target of that map, of partial order on the source.

-- Can this be done? "pullback" in Lean is called `comap` -- the computer science name for it.
-- Can you put a partial order on `subgroup G` by pulling it back from the one on `set G`?
-- Or can you do it directly? You'll have to prove the axioms for a partial order.

theorem carrier_injective : function.injective (subgroup.carrier : subgroup G → set G) := by ext

instance : partial_order (subgroup G) := 
{ le := λ H K, (H : set G) ⊆ K, 
  le_refl := begin
  intro,
  simp,
  end,
  le_trans := λ _ _ _, set.subset.trans,
  le_antisymm := λ H K h1 h2, ext H K $ set.subset.antisymm h1 h2
  }

-- If you do it directly you'll have to define the inequality you want, which will look something like this:
-- λ H K, H.carrier ⊆ K.carrier ; and then you'll have to prove all the theorems. If you pull it back you
-- won't need to prove the theorems.

open lattice

-- so let's work up to lattices. "inf H K" is just H intersect K -- but we need to check it's a subgroup. 

protected def inf (H K : subgroup G) : subgroup G :=
{ carrier := H.carrier ∩ K.carrier,
  one_mem := begin
--  unfold has_inter.inter,
--  unfold set.inter,
  split,
    apply subgroup.one_mem,
  apply subgroup.one_mem,
  end,
  mul_mem := begin
  intros,
  split,
    apply subgroup.mul_mem,
      unfold has_inter.inter at a_1,
      unfold set.inter at a_1,
      cases a_1 with Hh Hk,
      assumption,
    cases a_2 with Hh Hk,
    assumption,
  apply subgroup.mul_mem,
    cases a_1 with Hh Hk,
    assumption,
  cases a_2 with Hh Hk,
  assumption,
  end,
  inv_mem := begin
  intros,
  cases a_1 with Hh Hk,
  split,
    apply subgroup.inv_mem,
    assumption,
  apply subgroup.inv_mem,
  assumption,
  end
  }

-- notation for inf is ⊓ (\glb) and as you can see from the definition of "carrier" above (the carrier
-- is the underlying set), it's just the intersection. `inf` stands for "infimum" and "glb" for "greatest lower bound",
-- both rather pretentious names for the intersection.

instance : has_inf (subgroup G) := ⟨subgroup.inf⟩

-- half way to a lattice is a semilattice_inf: there are some axioms you need to check though.

instance : semilattice_inf (subgroup G) :=
{ inf := (⊓),
  inf_le_left := begin
  intros,
  unfold lattice.has_inf.inf,
  unfold subgroup.inf,
  --I don't really understand what I'm trying to prove
  sorry
  end,
  inf_le_right := sorry,
  le_inf := sorry,
  ..subgroup.partial_order}

-- Lean has quotients by normal subgroups.

example (G : Type*) [group G] (N : set G) [normal_subgroup N] := quotient_group.quotient N 
-- This is G/N. Lean guesses G from N.

-- We want to make a term of type `equiv X Y` where X and Y are two collections of subgroups and the `equiv` is this
-- strong kind of bijection -- a map from X to Y, and a map from Y to X, and two proofs,
-- namely that the composite maps X->Y->X and Y->X->Y are the relevant identity maps.

-- To do this we need to make the two sets. First the variables we're going to have:

variables (N : set G) [normal_subgroup N]

-- Now notation for the quotient: 

local notation `Q` := quotient_group.quotient N

-- Now the first set (or "type", as Nicola Gambino would say). 

example := subgroup Q 

-- That's the subgroups of G/N. The other set is the subgroups of G which contain N.

example := {H : subgroup G // N ≤ H.carrier}

-- Those two sets biject with each other in the stong way which I showed you today: you can construct maps
-- in both directions. Do you know how do to this in maths?

end subgroup

variables {G : Type*} [group G] {H : Type*} [group H] 

namespace monoid_hom

def map (f : G →* H) (K : subgroup G) : subgroup H :=
{ carrier := f '' K,
  one_mem := begin 
  use 1,
  split,
    apply subgroup.one_mem,
  apply monoid_hom.map_one,
  end,
  mul_mem := begin
  rintro j k ⟨j', hj', rfl⟩ ⟨k', hk', rfl⟩,
  rw [← monoid_hom.map_mul f j' k'],
  unfold set.image,
  dsimp,
  use j'*k',
  split,
    apply subgroup.mul_mem,
      assumption,
    assumption,
  refl,
  end,
  inv_mem := begin
  rintro j ⟨j', hj', rfl⟩,
  unfold set.image,
  dsimp,
  use j'⁻¹,
  split,
    apply subgroup.inv_mem,
    assumption,
  apply f.map_inv,
  end
}

def comap (f : G →* H) (K : subgroup H) : subgroup G :=
{ carrier := f ⁻¹' K,
  one_mem := begin
  unfold set.preimage,
  dsimp,
  rw monoid_hom.map_one f,
  apply subgroup.one_mem,
  end,
  mul_mem := begin
  intros,
  unfold set.preimage,
  dsimp,
  rw monoid_hom.map_mul f,
  apply subgroup.mul_mem,
    assumption,
  assumption,
  end,
  inv_mem := begin
  intros,
  unfold set.preimage,
  dsimp,
  rw f.map_inv,
  apply subgroup.inv_mem,
  assumption,
  end
}

-- We haven't make the kernel of a bundled hom into a bundled subgroup!
def ker (f : G →* H) : subgroup G :=
{ carrier := {g : G | f g = 1},
  one_mem := begin
  dsimp,
  apply monoid_hom.map_one,
  end,
  mul_mem := begin
  dsimp,
  intros,
  rw [monoid_hom.map_mul, a_1, a_2],
  simp,
  end,
  inv_mem := begin
  dsimp,
  intros,
  rw [f.map_inv, a_1],
  simp,
  end }

-- one lemma you'll need to prove that your map in the correspondence below is well-defined. 
lemma ker_sub_comap (f : G →* H) (X : subgroup H): f.ker ≤ f.comap X := begin  
sorry
end

end monoid_hom

-- OK here is the main theorem. First variables.

variables {N : subgroup G} [normal_subgroup (N : set G)]

-- notation Q for the quotient group G/N

local notation `Q` := quotient_group.quotient (N : set G)

-- definition pr for the bundled map G →* Q

def pr : G →* Q := group_hom.mk (quotient_group.mk : G → Q)

-- the kernel of the projection is N

lemma ker_pr : (pr : G →* Q).ker = N :=
begin
  apply subgroup.ext,
  convert ←quotient_group.ker_mk (↑N : set G),
  ext x,
  exact is_subgroup.mem_trivial,
end

open quotient_group monoid_hom

-- hey this Wikipedia page is great:
-- https://en.wikipedia.org/wiki/Correspondence_theorem_(group_theory)

/-- Correspondence theorem for group theory -- first version -/
def correspondence : {H : subgroup G // N ≤ H} ≃ (subgroup Q) :=
{ to_fun := λ HN, pr.map HN.1,
  inv_fun := λ K, ⟨pr.comap K, begin 
  -- same issue as semilattice_inf where I don't know how to prove the multiple things in curly brackets on one side of an equation
  end⟩,
  left_inv := sorry,
  right_inv := sorry
}

-- That theorem above (I know it says definition, that's because the functions are data) is a first
-- version of the correspondence theorem. It says that there's a bijection of sets:
-- subgroups of G containing N <-> subgroups of Q=G/N

-- The next thing to do is to check that the correspondence respects ⊓, but I haven't quite decided
-- the best way to formalise that...