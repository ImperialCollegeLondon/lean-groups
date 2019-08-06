import algebra.group.to_additive algebra.group.basic algebra.group.hom group_theory.quotient_group

namespace group_hom
variables {G : Type*} [group G] {H : Type*} [group H]

def mk {G H} [group G] [group H] (f : G → H) [is_group_hom f] : G →* H :=
{ to_fun := f,
  map_one' := is_group_hom.map_one f,
  map_mul' := (is_group_hom.to_is_mul_hom f).map_mul }


end group_hom


