import algebra.group.to_additive algebra.group.basic

/-- bundled monoid homomorphisms; use this for bundled group homomorphisms too -/
structure monoid_hom (M : Type*) (N : Type*) [monoid M] [monoid N] :=
(to_fun : M → N)
(map_one' : to_fun 1 = 1)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infixr ` →* `:25 := monoid_hom

instance {M : Type*} {N : Type*} [monoid M] [monoid N] : has_coe_to_fun (M →* N) :=
⟨_, monoid_hom.to_fun⟩

/-- bundled add_monoid homomorphisms; use this for bundled add_group homomorphisms too-/
structure add_monoid_hom (M : Type*) (N : Type*) [add_monoid M] [add_monoid N] :=
(to_fun : M → N)
(map_zero' : to_fun 0 = 0)
(map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

infixr ` →+ `:25 := add_monoid_hom

instance {A : Type*} {B : Type*} [add_monoid A] [add_monoid B] : has_coe_to_fun (A →+ B) :=
⟨_, add_monoid_hom.to_fun⟩

attribute [to_additive add_monoid_hom] monoid_hom
attribute [to_additive add_monoid_hom.has_sizeof_inst] monoid_hom.has_sizeof_inst
attribute [to_additive add_monoid_hom.map_zero'] monoid_hom.map_one'
attribute [to_additive add_monoid_hom.map_add'] monoid_hom.map_mul'
attribute [to_additive add_monoid_hom.mk] monoid_hom.mk
attribute [to_additive add_monoid_hom.mk.inj] monoid_hom.mk.inj
attribute [to_additive add_monoid_hom.mk.inj_arrow] monoid_hom.mk.inj_arrow
attribute [to_additive add_monoid_hom.mk.inj_eq] monoid_hom.mk.inj_eq
attribute [to_additive add_monoid_hom.mk.sizeof_spec] monoid_hom.mk.sizeof_spec
attribute [to_additive add_monoid_hom.no_confusion] monoid_hom.no_confusion
attribute [to_additive add_monoid_hom.no_confusion_type] monoid_hom.no_confusion_type
attribute [to_additive add_monoid_hom.rec] monoid_hom.rec
attribute [to_additive add_monoid_hom.rec_on] monoid_hom.rec_on
attribute [to_additive add_monoid_hom.sizeof] monoid_hom.sizeof
attribute [to_additive add_monoid_hom.to_fun] monoid_hom.to_fun

namespace monoid_hom
variables {M : Type*} {N : Type*} {P : Type*} [monoid M] [monoid N] [monoid P]

@[extensionality] def ext (f g : M →* N) (h : (f : M → N) = g) : f = g :=
by cases f; cases g; cases h; refl

/-- if f is a monoid homomorphism then f 1 = 1-/
@[simp] lemma map_one (f : M →* N) : f 1 = 1 := f.map_one'

/-- if f is a monoid homomorphism then f (a * b) = f a * f b -/
@[simp] lemma map_mul (f : M →* N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b

/-- the identity map from a monoid to itself-/
def id (M : Type*) [monoid M] : M →* M :=
{ to_fun := id,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

/-- composition of monoid morphisms is a monoid morphism -/
def comp (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ to_fun := hnp ∘ hmn,
  map_one' := by simp,
  map_mul' := by simp,
}

/-- The product of two monoids morphisms is a monoid morphism if the target is commutative-/
def mul {M N} [monoid M] [comm_monoid N] (f g : M →* N) : M →* N :=
{ to_fun := λ m, f m * g m,
  map_one' := show f 1 * g 1 = 1, by simp,
  map_mul' := begin intros, show f (x * y) * g (x * y) = f x * g x * (f y * g y),
    rw [f.map_mul, g.map_mul, ←mul_assoc, ←mul_assoc, mul_right_comm (f x)], end
}

end monoid_hom

namespace group_hom
variables {G : Type*} [group G] {H : Type*} [group H]

/-- makes a group homomomorphism from a proof that the map preserves multiplication -/
def mk {f : G → H} (map_mul : ∀ a b : G, f (a * b) = f a * f b) : G →* H :=
{ to_fun := f,
  map_mul' := map_mul,
  map_one' := mul_self_iff_eq_one.1 $ by rw [←map_mul, mul_one]
}

/-- makes a group homomorphism from a map and a proof that it preserves multiplication -/
def mk' (f : G → H) (map_mul : ∀ a b : G, f (a * b) = f a * f b) : G →* H := mk map_mul

/-- group homomorphisms preserve inverse -/
theorem map_inv (f : G →* H) (g : G) : f g⁻¹ = (f g)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [←f.map_mul, inv_mul_self, f.map_one]

--@[to_additive add_group_hom.neg]
/-- the inverse of a group homomorphism is a group homomorphism if the target is commutative-/
def inv {G H} [group G] [comm_group H] (f : G →* H) : G →* H :=
mk' (λ g, (f g)⁻¹) $ λ a b, by rw [←mul_inv, f.map_mul]

end group_hom

namespace add_monoid_hom
variables {A : Type*} {B : Type*} {C : Type*} [add_monoid A] [add_monoid B] [add_monoid C]

/-- two additive monoid homomorphisms with equal underlying maps are equal-/
@[extensionality] def ext (f g : A →+ B) (h : (f : A → B) = g) : f = g :=
by cases f; cases g; cases h; refl

attribute [to_additive add_monoid_hom.ext] monoid_hom.ext
attribute [to_additive add_monoid_hom.ext.equations._eqn_1] monoid_hom.ext.equations._eqn_1

/-- if f is a additive monoid homomorphism then f 0 = 0-/
@[simp] def map_zero (f : A →+ B) : f 0 = 0 := f.map_zero'

attribute [to_additive add_monoid_hom.map_zero] monoid_hom.map_one

/-- if f is an additive monoid homomorphism then f (a + b) = f a + f b -/
@[simp] def map_add (f : A →+ B) : ∀ a b : A, f (a + b) = f a + f b := f.map_add'

attribute [to_additive add_monoid_hom.map_add] monoid_hom.map_mul

/-- the identity map from an add_monoid to itself -/
def id (A : Type*) [add_monoid A] : A →+ A :=
{ to_fun := id,
  map_zero' := rfl,
  map_add' := λ _ _, rfl}

attribute [to_additive add_monoid_hom.id._proof_1] monoid_hom.id._proof_1
attribute [to_additive add_monoid_hom.id._proof_2] monoid_hom.id._proof_2
attribute [to_additive add_monoid_hom.id.equations._eqn_1] monoid_hom.id.equations._eqn_1

/-- composition of additive monoid morphisms is an additive monoid morphism -/
def comp (fbc : B →+ C) (fab : A →+ B) : A →+ C :=
{ to_fun := fbc ∘ fab,
  map_zero' := by simp,
  map_add' := by simp,
}

attribute [to_additive add_monoid_hom.comp] monoid_hom.comp
attribute [to_additive add_monoid_hom.comp._proof_1] monoid_hom.comp._proof_1
attribute [to_additive add_monoid_hom.comp._proof_2] monoid_hom.comp._proof_2
attribute [to_additive add_monoid_hom.comp.equations._eqn_1] monoid_hom.comp.equations._eqn_1

/-- The sum of two additive monoid morphisms is an additive monoid morphism if the
target is commutative-/
def add {A B} [add_monoid A] [add_comm_monoid B] (f g : A →+ B) : A →+ B :=
{ to_fun := λ a, f a + g a,
  map_zero' := show f 0 + g 0 = 0, by simp,
  map_add' := begin intros, show f (x + y) + g (x + y) = f x + g x + (f y + g y),
    rw [f.map_add, g.map_add, ←add_assoc, ←add_assoc, add_right_comm (f x)], end
}

attribute [to_additive add_monoid_hom.add] monoid_hom.mul
attribute [to_additive add_monoid_hom.add._proof_1] monoid_hom.mul._proof_1
attribute [to_additive add_monoid_hom.add._proof_2] monoid_hom.mul._proof_2
attribute [to_additive add_monoid_hom.add.equations._eqn_1] monoid_hom.mul.equations._eqn_1

end add_monoid_hom

namespace add_group_hom
variables {A : Type*} {B : Type*} {C : Type*} [add_group A] [add_group B] [add_group C]

/-- makes an additive group homomomorphism from a proof that the map preserves addition -/
def mk {f : A → B} (map_add : ∀ x y : A, f (x + y) = f x + f y) : A →+ B :=
{ to_fun := f,
  map_add' := map_add,
  map_zero' := add_self_iff_eq_zero.1 $ by rw [←map_add, add_zero]
}
attribute [to_additive add_group_hom.mk] group_hom.mk
attribute [to_additive add_group_hom.mk._proof_1] group_hom.mk._proof_1
attribute [to_additive add_group_hom.mk.equations._eqn_1] group_hom.mk.equations._eqn_1

def mk' (f : A → B) (map_add : ∀ x y : A, f (x + y) = f x + f y) : A →+ B := mk map_add

attribute [to_additive add_group_hom.mk'] group_hom.mk'
attribute [to_additive add_group_hom.mk'.equations._eqn_1] group_hom.mk'.equations._eqn_1

/-- additive group homomorphisms preserve additive inverse -/
theorem map_neg (f : A →+ B) (a : A) : f (-a) = -(f a) :=
eq_neg_of_add_eq_zero $ by rw [←f.map_add, neg_add_self, f.map_zero]

attribute [to_additive add_group_hom.map_neg] group_hom.map_inv

-- NEEDS TO ADDITIVE
/-
add_group_hom.neg : Π {A : Type u_1} {B : Type u_2} [_inst_4 : add_group A] [_inst_5 : add_comm_group B], (A →+ B) → A →+ B
add_group_hom.neg._proof_1 : ∀ {A : Type u_1} {B : Type u_2} [_inst_4 : add_group A] [_inst_5 : add_comm_group B] (f : A →+ B) (a b : A),
  -⇑f (a + b) = -⇑f a + -⇑f b
add_group_hom.neg.equations._eqn_1 : ∀ {A : Type u_1} {B : Type u_2} [_inst_4 : add_group A] [_inst_5 : add_comm_group B] (f : A →+ B),
  neg f = mk' (λ (g : A), -⇑f g) _
  -/
--@[to_additive add_group_hom.neg]
/-- the additive inverse of an additive group homomorphism is an additive group homomorphism if the
target is commutative-/
def neg {A B} [add_group A] [add_comm_group B] (f : A →+ B) : A →+ B :=
mk' (λ g, -(f g)) $ λ a b, by rw [←neg_add, f.map_add]

attribute [to_additive add_group_hom.neg] group_hom.inv
attribute [to_additive add_group_hom.neg._proof_1] group_hom.inv._proof_1
attribute [to_additive add_group_hom.neg.equations._eqn_1] group_hom.inv.equations._eqn_1

end add_group_hom
