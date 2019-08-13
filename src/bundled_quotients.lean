import group_theory.quotient_group bundled_subgroup

namespace quotient_group

variables {G : Type*} [group G] {N : subgroup G} (h : is_normal_subgroup N)

open function

def quotient' {G : Type*} [group G] {N : subgroup G} (h : is_normal_subgroup N) := quotient N.carrier

instance quotient'_is_group {G : Type*} [group G] {N : subgroup G} (h : is_normal_subgroup N) :
group (quotient' h) := by unfold quotient'; letI : normal_subgroup (N.carrier) := h; apply_instance

def mk' {G : Type*} [group G] {N : subgroup G} (h : is_normal_subgroup N) : G →* quotient' h :=
by letI : normal_subgroup (N.carrier) := h; exact group_hom.mk (quotient_group.mk)

theorem mk'.surjective : surjective (mk' h) := begin
  intro q,
  use quotient.out' q,
  apply quotient.out_eq' 
end

end quotient_group
