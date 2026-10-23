/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Quotients of ultrametric seminormed groups

The quotient seminorm `‖x‖ = inf {‖m‖ | m ↦ x}` of an ultrametric seminormed commutative group
by a subgroup is again ultrametric. Each class has representatives whose norms approximate its
quotient norm, and the ultrametric inequality for a product of such representatives descends to
the quotient. The additive form covers quotients of modules by submodules and of commutative
seminormed rings by ideals, so residue norms of nonarchimedean Banach algebras are again
nonarchimedean.
-/

public section

namespace QuotientGroup

variable {M : Type*} [SeminormedCommGroup M] [IsUltrametricDist M]

/-- The quotient of an ultrametric seminormed commutative group by a subgroup is ultrametric. -/
@[to_additive /-- The quotient of an ultrametric seminormed additive commutative group by an
additive subgroup is ultrametric. -/]
instance instIsUltrametricDist (S : Subgroup M) : IsUltrametricDist (M ⧸ S) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_mul_le_max_norm fun x y ↦ by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt x hε
    obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt y hε
    rw [← QuotientGroup.mk_mul]
    calc ‖((a * b : M) : M ⧸ S)‖ ≤ ‖a * b‖ := norm_mk_le_norm
      _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_mul_le_max a b
      _ ≤ max ‖(a : M ⧸ S)‖ ‖(b : M ⧸ S)‖ + ε :=
        (max_le_max ha.le hb.le).trans (max_add_add_right _ _ _).le

end QuotientGroup

/-- The quotient of an ultrametric seminormed module by a submodule is ultrametric. -/
instance Submodule.Quotient.instIsUltrametricDist {R M : Type*} [Ring R]
    [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module R M] (S : Submodule R M) :
    IsUltrametricDist (M ⧸ S) :=
  inferInstanceAs <| IsUltrametricDist (M ⧸ S.toAddSubgroup)
