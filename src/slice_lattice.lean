import order.complete_lattice

open lattice

example {α : Type*} [partial_order α] (b : α) : partial_order {x // b ≤ x} := by apply_instance

-- why is subtype.ext an iff?

instance slice.semilattice_sup {α : Type*} [semilattice_sup α] (b : α) : semilattice_sup {x // b ≤ x} :=
{ sup := λ x y, ⟨x.val ⊔ y.val, le_sup_left_of_le x.2⟩,
  le_sup_left := λ _ _, le_sup_left,
  le_sup_right := λ _ _, le_sup_right,
  sup_le := λ _ _ _, sup_le,
  ..subtype.partial_order _}

instance slice.semilattice_inf {α : Type*} [semilattice_inf α] (b : α) : semilattice_inf {x // b ≤ x} :=
{ inf := λ x y, ⟨x.val ⊓ y.val, le_inf x.2 y.2⟩,
  inf_le_left := λ _ _, inf_le_left,
  inf_le_right := λ _ _, inf_le_right,
  le_inf := λ _ _ _, le_inf,
  ..subtype.partial_order _}

instance slice.lattice {α : Type*} [lattice α] (b : α) : lattice {x // b ≤ x} :=
{ ..slice.semilattice_inf b, ..slice.semilattice_sup b}

instance slice.order_top {α : Type*} [order_top α] (b : α) : order_top {x // b ≤ x} :=
{ top := ⟨⊤, le_top⟩,
  le_top := λ _, le_top,
  ..subtype.partial_order _ }

instance slice.order_bot {α : Type*} [partial_order α] (b : α) : order_bot {x // b ≤ x} :=
{ bot := ⟨b, le_refl b⟩,
  bot_le := subtype.property,
  ..subtype.partial_order _ }

instance slice.bounded_lattice {α : Type*} [bounded_lattice α] (b : α) : bounded_lattice {x // b ≤ x} :=
{ ..slice.order_top b, ..slice.order_bot b, ..slice.lattice b}

instance slice.has_Sup {α : Type*} [complete_lattice α] (b : α) : has_Sup {x // b ≤ x} :=
⟨λ X, ⟨Sup $ set.insert b (set.image subtype.val X), le_Sup $ set.mem_insert b _⟩⟩

instance slice.has_Inf {α : Type*} [complete_lattice α] (b : α) : has_Inf {x // b ≤ x} :=
⟨λ X, ⟨Inf $ set.image subtype.val X, le_Inf $ by {rintro _ ⟨y, _, rfl⟩, exact y.2}⟩⟩

instance slice.complete_lattice {α : Type*} [complete_lattice α] (b : α) : complete_lattice {x // b ≤ x} :=
{ le_Sup := λ X y h, le_Sup $ set.mem_insert_of_mem _ ⟨y, h, rfl⟩,
  Sup_le := λ X y h, Sup_le $ λ x h2, begin
    change x ∈ insert b _ at h2,
    rw set.mem_insert_iff at h2,
    rcases h2 with ⟨rfl, h2⟩, exact y.2,
    rcases h2 with ⟨_, h2, rfl⟩,
    exact h _ h2,
  end,
  Inf_le := λ X y h, Inf_le ⟨y, h, rfl⟩,
  le_Inf := λ X y h, le_Inf $ by {rintro _ ⟨x, hx, rfl⟩, exact h _ hx},
  ..slice.bounded_lattice b,
  ..slice.has_Sup b,
  ..slice.has_Inf b }