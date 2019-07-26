import data.quot -- equivalence relations and equivalence classes
import tactic.interactive -- for "choose" tactic

-- Sian's definition of an equivalence relation on X corresponding to a function f : X → Y

-- X and Y and f are fixed once and for all in this story, so let's make them parameters
-- in a section.

section -- in this section X and Y and the surjection f will be fixed once and for all

open function -- so I can write "surjective" instead of "function.surjective"

parameters {X : Type} {Y : Type} (f : X → Y) (hf : surjective f)

-- now let's define the binary relation that Sian came up with

def R (x₁ x₂ : X) : Prop := f x₁ = f x₂

-- top tip -- sometimes "unfold R" doesn't work. I don't know why. Try the tactic "delta R"? This always works.

theorem R.equivalence : equivalence R :=
begin
  split,
    delta R,
    unfold reflexive,
    intro,
    refl, 
  split,
    delta R,
    unfold symmetric,
    intros,
    rw a,
  delta R,
  unfold transitive,
  intros,
  rw a,
  assumption,    
end

-- A "setoid" is Lean's rather pretentious term for
-- the data of a type and an equivalence relation on the type.
-- More precisely, a term of type `setoid X` is a *pair*
-- consisting of
-- 1) a binary relation R on X
-- 2) a proof that R is an equivalence relation.

-- We just proved R was an equivalence relation on X so we can make a setoid.
-- Note that we have to give both the relation and the proof that it's an equivalence relation.

def s : setoid X := ⟨R, R.equivalence⟩ -- pointy brackets is often a constructor for a type which is a pair.

-- let's define Q to be the set of equivalence classes for this equivalence relation.

-- Lean takes the "quotient of the setoid".
def Q := quotient s
-- Now Q is the set of equivalence classes.

-- when you left the office today Friday, I had challenged you to give maps from Q to Y
-- You said "Let S be an equivalence class. Define F(S) = f(x) where x is any element of S."

-- I said "yeah but you need to check that that is well-defined, because what if your definition
-- of F(S) depends on the choice of x?"

-- If you try to make this definition in Lean, as below, then Lean makes precisely the
-- same objection. It wants to know why two things in the same equivalence class give the same answer.

def F : Q → Y := λ q, quotient.lift_on' q (λ (x : X), f x) begin
  show ∀ a b : X, R a b → f a = f b,
  delta R,
  intros,
  assumption,
end

theorem commutes' (x : X) : f x = F (quotient.mk' x) :=
begin
  refl
end

-- technical note: I managed to define a function from Q to somewhere because I knew
-- an "eliminator" for Q, namely quotient.lift_on'

-- def G : Y → Q := sorry -- you never did that bit. How will you do it?

-- you will need to know a "constructor" for Q, namely a way to make elements of Q.
-- Here is a function from X to Q.

example : X → Q := quotient.mk'

-- Using that function, can you make a function from Y to Q? Here's a hint.

include hf -- need surjectivity for this one
noncomputable def G : Y → Q := λ y, quotient.mk' (classical.some (hf y))

-- What shall we do next?

lemma commutes (x : X) : G (f x) = quotient.mk' x :=
begin
  let x' := classical.some (hf (f x)),
  have xh' := classical.some_spec (hf (f x)),
  change f x' = f x at xh',
  change quotient.mk' (x') = _,
  rw quotient.eq',
  show R _ x,
  exact xh',
end


end -- section