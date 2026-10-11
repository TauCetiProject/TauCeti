/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Subquotients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Subrepresentations and quotients of smooth discrete representations

An invariant submodule of a smooth discrete representation inherits its topology and action, and
the quotient by an invariant submodule carries the quotient topology and descended action. Both
remain smooth discrete representations. These constructions supply the subgroup and quotient
coefficient modules used with continuous cohomology.
-/

public section

namespace TauCeti

open TopRep

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {G : Type*} [Group G] [TopologicalSpace G] {X : TopRep R G}

/-- Smoothness is inherited by the representation on an invariant submodule. -/
theorem IsSmoothDiscrete.subrepresentation (hX : IsSmoothDiscrete R X)
    (W : Submodule R X.V) (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    IsSmoothDiscrete R (TopRep.subrepresentation X W hW) := by
  exact hX.of_injective (TopRep.subrepresentationι X W hW)
    (TopRep.subrepresentationι_injective X W hW)

/-- The quotient by an invariant submodule of a smooth discrete representation is smooth discrete.
The quotient topology is discrete, and the descended action is continuous when multiplication in
the group is separately continuous. -/
theorem IsSmoothDiscrete.quotient [SeparatelyContinuousMul G]
    (hX : IsSmoothDiscrete R X) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    IsSmoothDiscrete R (TopRep.quotient X W hW) := by
  have : DiscreteTopology X.V := hX.discreteTopology
  have : DiscreteTopology (X.V ⧸ W) :=
    QuotientAddGroup.discreteTopology (N := W.toAddSubgroup) (isOpen_discrete _)
  let := X.distribMulAction
  let := (TopRep.quotient X W hW).distribMulAction
  refine ⟨‹DiscreteTopology (X.V ⧸ W)›, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W y
  have hstab : IsOpen (MulAction.stabilizer G (W.mkQ x) : Set G) := by
    apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G x)
    · intro g hg
      simp only [MulAction.mem_stabilizer_iff] at hg ⊢
      have hg' : X.ρ g x = x := by simpa [TopRep.distribMulAction_smul] using hg
      -- Stabilizer membership is written through the derived action, while the quotient formula
      -- is stated for the `TopRep` operators.
      change (TopRep.quotient X W hW).ρ g (W.mkQ x) = _
      rw [Submodule.mkQ_apply, TopRep.quotient_ρ,
        ContRepresentation.quotient_apply_mk]
      rw [hg']
    · simpa only [← TopRep.coe_stabilizer] using hX.stabilizer_isOpen x
  simpa only [← TopRep.coe_stabilizer (TopRep.quotient X W hW) (W.mkQ x),
    TopRep.quotient_ρ] using hstab

end TauCeti
