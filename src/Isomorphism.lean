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
import data.set.basic 
import slice_lattice

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

import bundled_quotients

namespace subgroup
variables {G : Type*} [group G]

-- Two subgroups with same underlying subset are the same subgroup. 
@[extensionality] def ext (H K : subgroup G) (h : (H : set G) = K) : H = K :=
by cases H; cases K; cases h; refl 

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

theorem le {G : Type*} [group G] {H K : subgroup G} : H ≤ K ↔ ∀ x: G, x ∈ H → x ∈ K :=
iff.rfl

open lattice

-- so let's work up to lattices. "inf H K" is just H intersect K -- but we need to check it's a subgroup. 

example (X : Type) (A B : set X) : A ∩ B ⊆ A := set.inter_subset_left A B

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
-- is the underlying set), it's just the intersection. `inf` stands for "infimum" and
-- "glb" for "greatest lower bound",
-- both rather pretentious names for the intersection.

instance : has_inf (subgroup G) := ⟨subgroup.inf⟩

-- half way to a lattice is a semilattice_inf: there are some axioms you need to check though.

instance subgroup.semilattice_inf : semilattice_inf (subgroup G) :=
{ inf := (⊓),
  inf_le_left := begin
  intros,
  show a.carrier ∩ b.carrier ⊆ a.carrier,
  simp,
  --exact set.inter_subset_left _ _,
  --unfold lattice.has_inf.inf,
  --unfold subgroup.inf,
  end,
  inf_le_right := begin
  intros,
  show a.carrier ∩ b.carrier ⊆ b.carrier,
  simp,
  end,
  le_inf := begin
  intros a b c,
  intros hab hac,
  change a.carrier ⊆ b.carrier at hab,
  change a.carrier ⊆ c.carrier at hac,
  show a.carrier ⊆ b.carrier ∩ c.carrier,
  simp,
  split,
    assumption,
  assumption,
  end,
  ..subgroup.partial_order}

 

def top : subgroup G :=
{ carrier := set.univ,
  one_mem := set.mem_univ _,
  mul_mem := λ _ _ _ _, set.mem_univ _,
  inv_mem := λ _ _, set.mem_univ _
}

instance subgroup.has_top : has_top (subgroup G) := ⟨top⟩

def bot : subgroup G :=
{ carrier := {1},
  one_mem := begin 
    apply set.mem_singleton
  end,
  mul_mem := begin
    intros a b ha hb,
    rw set.mem_singleton_iff at ha hb ⊢,
    rw [ha, hb, mul_one],
  end,
  inv_mem := begin
    intros a ha,
    rw set.mem_singleton_iff at ha ⊢,
    rw ha,
    simp,
  end
}

instance subgroup.has_bot : has_bot (subgroup G) := ⟨bot⟩

-- Lean has quotients by normal subgroups.

-- old style method
example (G : Type*) [group G] (N : set G) [normal_subgroup N] := quotient_group.quotient N 
-- This is G/N. Lean guesses G from N.

-- We want to make a term of type `equiv X Y` where X and Y are two collections of
--  subgroups and the `equiv` is this
-- strong kind of bijection -- a map from X to Y, and a map from Y to X, and two proofs,
-- namely that the composite maps X->Y->X and Y->X->Y are the relevant identity maps.

-- To do this we need to make the two sets. First the variables we're going to have:

variables {N : subgroup G} (h : is_normal_subgroup N)

-- Now notation for the quotient: 

local notation `Q` := quotient_group.quotient' h

-- Now the first set (or "type", as Nicola Gambino would say). 

example := subgroup Q 

-- That's the subgroups of G/N. The other set is the subgroups of G which contain N.

instance subtype.has_bot : has_bot {H : subgroup G // N ≤ H} :=
⟨⟨N, le_refl N⟩⟩

def Inf (X : set (subgroup G)) : subgroup G :=
{ carrier := Inf (set.image subgroup.carrier X),
  one_mem := begin
  unfold Inf,
  unfold has_Inf.Inf,
  unfold complete_lattice.Inf,
  intro t,
  intro ht,
  rcases ht with ⟨J, hJ, rfl⟩,
  exact J.one_mem,
  end,
  mul_mem := begin
    intros a b ha hb,
    -- unfolding to find out what goal meant now all deleted
    intros H hH,
    replace ha := ha H hH,
    replace hb := hb H hH,
    rcases hH with ⟨J, hJ, rfl⟩,
    exact J.mul_mem ha hb
  end,
  inv_mem := begin 
  intros a ha H hH,
  replace ha := ha H hH,
  rcases hH with ⟨J, hJ, rfl⟩,
  exact J.inv_mem ha,
  end }

instance subgroup.has_Inf : has_Inf (subgroup G) := ⟨Inf⟩

def sup (H K : subgroup G) : subgroup G := Inf {X | H ≤ X ∧ K ≤ X}

instance : has_sup (subgroup G) := ⟨sup⟩

def Sup (X : set (subgroup G)) : subgroup G := Inf {K | ∀ H : X, H.val ≤ K}

instance subgroup.has_Sup : has_Sup (subgroup G) := ⟨Sup⟩

instance subgroup.semilattice_sup : semilattice_sup (subgroup G) := 
{ sup := sup,
  le_sup_left := begin
  intros a b,
  rw le,
  intros x hx xX xXh,
  rcases xXh with ⟨J, hJ, rfl⟩,
  cases hJ with aJ bJ,
  change a.carrier ⊆ J.carrier at aJ,
  change x ∈ a.carrier at hx,
  apply aJ,
  assumption,
  end,
  le_sup_right := begin 
  intros,
  rw le,
  intros x hx xX xXh,
  rcases xXh with ⟨J, hJ, rfl⟩,
  cases hJ with aJ bJ,
  change b.carrier ⊆ J.carrier at bJ,
  change x ∈ b.carrier at hx,
  apply bJ,
  assumption,
  end,
  sup_le := begin 
  intros a b c,
  rw le,
  intro hac,
  rw le,
  intro hbc,
  rw le,
  unfold lattice.has_sup.sup,
  unfold sup,
  intros x aorb,
  
  sorry 
  end,
   ..subgroup.partial_order}

instance subgroup.lattice : lattice (subgroup G) := { ..subgroup.semilattice_sup, ..subgroup.semilattice_inf}

lemma le_top (H : subgroup G) : H ≤ ⊤ := 
begin
  rw le,
  intros x xh,
  unfold lattice.has_top.top,
end

instance subgroup.order_top : order_top (subgroup G) := {le_top := le_top, ..subgroup.partial_order, ..subgroup.has_top, }

lemma bot_le (H : subgroup G) : ⊥ ≤ H :=
begin
  rw le,
  intros x xbot,
  unfold lattice.has_bot.bot at xbot,
  

  sorry
end

instance subgroup.order_bot : order_bot (subgroup G) := {bot_le := bot_le, ..subgroup.partial_order, ..subgroup.has_bot}

instance subgroup.bounded_lattice : bounded_lattice (subgroup G) := {..subgroup.lattice, ..subgroup.order_top, ..subgroup.order_bot}

instance subtype.has_Inf : has_Inf ({H : subgroup G // N ≤ H}) := ⟨
  λ X, ⟨Inf (set.image subtype.val X), begin sorry end ⟩
⟩

instance : complete_lattice (subgroup G) :=
{ le_Sup := begin
intros s a has,
rw le,
intros x hxa,
unfold has_Sup.Sup,
unfold Sup,
intros t ht,
rcases ht with ⟨J, hJ, rfl⟩,

sorry
end,
  Sup_le := begin
  intros s a b,
  unfold has_Sup.Sup,
  unfold Sup,
  intros j hJ,
  
  sorry
  end,
  Inf_le := begin 
  intros,
  unfold has_Inf.Inf,
  
  sorry
  end,
  le_Inf := begin 
  intros s a ha,
  unfold has_Inf.Inf,

  sorry
  end,
  ..subgroup.bounded_lattice, ..subgroup.has_Sup, ..subgroup.has_Inf}

/-
class complete_lattice (α : Type u) extends bounded_lattice α, has_Sup α, has_Inf α :=
(le_Sup : ∀s, ∀a∈s, a ≤ Sup s)
(Sup_le : ∀s a, (∀b∈s, b ≤ a) → Sup s ≤ a)
(Inf_le : ∀s, ∀a∈s, Inf s ≤ a)
(le_Inf : ∀s a, (∀b∈s, a ≤ b) → a ≤ Inf s)
-/

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

def mem_ker (f : G →* H) (x : G) : x ∈ f.ker ↔ f x = 1 := iff.rfl

theorem ker_normal (f : G →* H) : is_normal_subgroup (ker f) :=
begin
   constructor,
   -- see what you can do -- might not be logically necessary but it might also be good
   -- practice :-) 
   intros n hn g,
   change n ∈ ker f at hn,
   rw mem_ker f n at hn,
   show g * n * g⁻¹ ∈ ker f,
   rw [mem_ker f (g * n * g⁻¹), mul_assoc g n g⁻¹, group_hom.map_mul f g (n * g⁻¹)],
   rw [group_hom.map_mul f n g⁻¹, hn, one_mul],
   rw [← group_hom.map_mul],
   simp,
end


theorem ker_mk' {G : Type*} [group G] {N : subgroup G} (h : is_normal_subgroup N) :
  ker (quotient_group.mk' h) = N :=
begin
  letI : normal_subgroup N.carrier := h,
  apply subgroup.ext,
  convert quotient_group.ker_mk N.carrier,
  ext,
  rw [monoid_hom.ker, is_group_hom.mem_ker],
  refl,
end



-- one lemma you'll need to prove that your map in the correspondence below is well-defined. 
lemma ker_sub_comap (f : G →* H) (X : subgroup H): f.ker ≤ f.comap X := begin  
  intro g,
  intro h,
  have h2 : f g = 1,
    exact h,
  show f g ∈ X,
  rw h2,
  exact X.one_mem,
end

end monoid_hom

-- OK here is the main theorem. First variables.

variables {N : subgroup G} (hN : is_normal_subgroup N)

-- notation Q for the quotient group G/N

local notation `Q` := quotient_group.quotient' hN

-- the kernel of the projection is N

open monoid_hom

open quotient_group

-- hey this Wikipedia page is great:
-- https://en.wikipedia.org/wiki/Correspondence_theorem_(group_theory)

lemma mem_of_map_mem {K : subgroup G} (HK : N ≤ K) (x : G)
  (hx : ⇑(mk' hN) x ∈ (quotient_group.mk' hN).map K) : x ∈ K :=
begin
cases hx with k hxk,
    cases hxk with kK hxkx,
    let f := (mk' hN),
    have hxkone : f (x*k⁻¹) = 1,
      calc f(x*k⁻¹) = f(x)*f(k⁻¹) : by apply f.map_mul 
      ...           = f(k)*f(k⁻¹) : by rw hxkx
      ...           = f(k*k⁻¹) : by rw f.map_mul
      ...           = f(1) : by rw mul_inv_self
      ...           = 1 : f.map_one,
    rw ←mem_ker at hxkone,
    rw ker_mk' at hxkone,
    have hfh : x*k⁻¹ ∈ K,
      apply HK,
      assumption,
    convert K.mul_mem hfh kK,
    rw mul_assoc,
    rw inv_mul_self k,
    rw mul_one,
end

/-- Correspondence theorem for group theory -- first version -/

def correspondence : {H : subgroup G // N ≤ H} ≃ (subgroup Q) :=
{ to_fun := λ HN, (quotient_group.mk' hN).map HN.1,
  inv_fun := λ K, ⟨(quotient_group.mk' hN).comap K, begin 
  rw subgroup.le,
  intro g,
  intro hg,
  show (quotient_group.mk' hN) g ∈ K,
  rw ←(ker_mk' hN) at hg,
  rw mem_ker at hg,
  rw hg,
  exact K.one_mem,
  end⟩,
  left_inv := begin
  rintro ⟨K, HK⟩,
  dsimp,
  apply subtype.ext.2, 
  dsimp,
  rw subgroup.ext_iff,
  intro x,
  split,
    intro hx,
    change (quotient_group.mk' hN) x ∈ (map (mk' hN)) K at hx,
    apply mem_of_map_mem hN,
      assumption,
    assumption,
      -- f is (mk' hN) 
      -- f(x) ∈ F(K) => ∃ k ∈ K st. f(x) = f(k) 
      -- K is a subgroup => k⁻¹ exists ∈ K -- K.inv_mem kK
      -- f(x) = f(k) => f(x)f(k⁻¹) = f(k)f(k⁻¹) => f(xk⁻¹) = f(1) = 1 change, group_hom.map_mul,
      -- So xk⁻¹ ∈ ker f ⊆ K 
      -- But K is closed under multiplication and xk⁻¹ * k = x, so x ∈ K.
  intro hx,
  show (quotient_group.mk' hN) x ∈ (map (mk' hN)) K,
  exact set.mem_image_of_mem (λ (a : G), ⇑(mk' hN) a) hx,
  end,
  right_inv :=
  begin
  intro K,
  dsimp, 
  rw subgroup.ext_iff,
  intro x,
  split,
    intro hx,
    cases hx with k hxk,
    cases hxk with kK hxkx,
    change (quotient_group.mk' hN) k ∈ K at kK,
    rw hxkx at kK,
    assumption,
  intro hx,
  have hxk := mk'.surjective hN x,
  cases hxk with g hxkx,
  use g,
  split,
    show (quotient_group.mk' hN) g ∈ K,
    rwa hxkx,
  assumption,
  --cases 
  -- x ∈ K => ∃ j ∈ F⁻¹(K) st. f(j)=x (surjectivity)
  -- So f(j) ∈ F(F⁻¹(K)) => x ∈ F(F⁻¹(K))
  
  end
}

-- That theorem above (I know it says definition, that's because the functions are data) is a first
-- version of the correspondence theorem. It says that there's a bijection of sets:
-- subgroups of G containing N <-> subgroups of Q=G/N

-- The next thing to do is to check that the correspondence respects ⊓, but I haven't quite decided
-- the best way to formalise that...

-- H (containing N) is a normal subgroup of G iff H/N is a normal subgroup of G/N

theorem normal_iff_normal (hN : is_normal_subgroup N) (H : subgroup G) (hH : N ≤ H) :
  is_normal_subgroup H ↔ is_normal_subgroup (correspondence hN ⟨H, hH⟩) := 
begin
  split,
    intro nsH,
    rw is_normal_subgroup_def at nsH ⊢,
    intros,
    --have NnormH : ∀ n : G, n ∈ N → ∀ h : G, h ∈ H → h * n * h⁻¹ ∈ N,
    --  exact normal_is_subgroup hN hH,
    --have hHNG : quotient' NnormH ≤ quotient' hN, error : failed to synthesize type class instance for
    have j := mk'.surjective hN g,
    cases j with t ht,
    have k := mk'.surjective hN n,
    cases k with l hl,
    have linH : l ∈ H,
      apply mem_of_map_mem hN hH, 
      rw hl,
      apply a,
    have : t * l * t⁻¹ ∈ H,
    apply nsH,
      assumption,
    rw [←ht, ←hl],
    rw [←group_hom.map_mul, ←group_hom.map_inv, ←group_hom.map_mul],
    use t * l * t⁻¹,
    split,
      assumption,
    refl,
    -- hN : N is a normal subgroup of G, hsH : H is a normal subgroup of G
    -- Then H/N is a subgroup of G/N : hHNG
    -- So gN*hN*g⁻¹N=ghg⁻¹N : by the group rule for quoitients
    -- ghg⁻¹N ∈ H/N : nsH
    -- note H/N = ⇑(correspondence hN) ⟨H, hH⟩
  intro nscH,
  rw is_normal_subgroup_def at nscH ⊢,
  intros,
  have that : ⇑(mk' hN) n ∈ (correspondence hN) ⟨H, hH⟩,
    use n,
    split,
      assumption,
    refl,
  have := nscH (mk' hN n) that (mk' hN g),
  rw [←group_hom.map_mul, ←group_hom.map_inv, ←group_hom.map_mul] at this,
  apply mem_of_map_mem hN hH,
  assumption,
end



lemma mem_mem_inf (H₁ H₂ : subgroup G) (t : G): t ∈ H₁ ⊓ H₂ → t ∈ H₁ :=
begin
  intro tH,
  change t ∈ H₁.carrier,
  cases tH,
  assumption,
end

lemma mem_inf_mem (H₁ H₂ : subgroup G) (t : G): t ∈ H₁ ⊓ H₂ → t ∈ H₂ :=
begin
  intro tH,
  change t ∈ H₂.carrier,
  cases tH,
  assumption,
end
 




theorem correspondence.le_iff (hN : is_normal_subgroup N) (H₁ H₂ : subgroup G)
(h1 : N ≤ H₁) (h2 : N ≤ H₂) : correspondence hN ⟨H₁, h1⟩ ⊓ correspondence hN ⟨H₂, h2⟩ = 
  correspondence hN ⟨H₁ ⊓ H₂, lattice.le_inf h1 h2⟩ :=
begin
  rw subgroup.ext_iff,
  intros,
  have j := mk'.surjective hN x,
  cases j with t ht,
  rw ←ht,
  have : N ≤ H₁ ⊓ H₂,
    change N.carrier ⊆ H₁.carrier ∩ H₂.carrier,
    simp,
    split,
      assumption,
    assumption,
  split,
    intro xh,
    cases xh with xh1 xh2,
    use t,
    split,
      apply mem_of_map_mem hN this,
      use t,
      split,
        split,
          apply mem_of_map_mem hN h1,
          assumption,
        apply mem_of_map_mem hN h2,
        assumption,
      refl,
    refl,
  intro xh,
  have htt : t ∈ H₁ ⊓ H₂,
    apply mem_of_map_mem hN this,
    apply xh,
  split,
    have htt1 : t ∈ H₁,
      apply mem_mem_inf H₁ H₂,
      assumption,  
    use t,
    split,
      assumption,
    refl,
  have htt1 : t ∈ H₂,
      apply mem_inf_mem H₁ H₂,
      assumption,  
    use t,
    split,
      assumption,
    refl,
end

theorem correspondence.inf_iff (hN : is_normal_subgroup N) (H₁ H₂ : subgroup G)
(h1 : N ≤ H₁) (h2 : N ≤ H₂) : correspondence hN ⟨H₁, h1⟩ ≤ correspondence hN ⟨H₂, h2⟩ ↔ H₁ ≤ H₂ :=
begin
  split,
    intro hh,
    rw subgroup.le at hh ⊢,
    intros x xh,
    have that : ⇑(mk' hN) x ∈ (correspondence hN) ⟨H₁, h1⟩,
      use x,
      split,
        assumption,
      refl,
    have := hh (mk' hN x) that,
    apply mem_of_map_mem hN h2,
    assumption,
  intro hh,
  rw subgroup.le at hh ⊢,
  intros x xh,
  have j := mk'.surjective hN x,
  cases j with t ht,
  rw ←ht at xh,
  have xhh : t ∈ H₁,
    apply mem_of_map_mem hN h1,
    assumption,
  have := hh t xhh,
  rw ←ht,
  use t,
  split,
    assumption,
  refl,
end

theorem correspondence.top (hN : is_normal_subgroup N) :
  correspondence hN ⟨⊤, λ _ _, set.mem_univ _⟩ = ⊤ :=
begin
  rw subgroup.ext_iff,
  intro,
  have hT : N ≤ ⊤,
    apply subgroup.le_top,
  have j := mk'.surjective hN x,
  cases j with t ht,
  rw ← ht,
  split,
    intro hx,
    apply mem_of_map_mem hN hT t,
    apply hx,
  intro hx,
  use t,
  split,
    assumption,
  refl,
end  
--int.coe_nat_inj' : ∀ {m n : ℕ}, ↑m = ↑n ↔ m = n

