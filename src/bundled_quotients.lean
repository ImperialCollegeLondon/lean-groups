import group_theory.quotient_group bundled_subgroup

namespace quotient_group

def quotient' {G : Type*} [group G] (N : normal_subgroup' G) := quotient N.carrier

instance quotient'_is_group {G : Type*} [group G] (N : normal_subgroup' G) : group (quotient' N) :=
by unfold quotient'; apply_instance

def mk' {G : Type*} [group G] (N : normal_subgroup' G) : G →* quotient' N :=
group_hom.mk (quotient_group.mk)

end quotient_group
