/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Subrepresentation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Subrepresentations and quotients of smooth discrete representations

An invariant submodule of a smooth discrete representation inherits its topology and action, and
the quotient by an invariant submodule carries the quotient topology and descended action. Both
remain smooth discrete representations. These constructions supply the subgroup and quotient
coefficient modules used with continuous cohomology.
-/

public section

namespace TopRep

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {G : Type*} [Monoid G] {X : TopRep R G}

/-- Restrict a continuous representation to an invariant submodule, with the induced topology. -/
abbrev subrepresentation (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : TopRep R G :=
  .of (X.ρ.subrepresentation W hW)

/-- The action on a subrepresentation is the ambient action with its membership proof. -/
@[simp]
theorem subrepresentation_ρ_apply (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (g : G)
    (x : subrepresentation X W hW) :
    (subrepresentation X W hW).ρ g x = ⟨X.ρ g x.1, hW g x.1 x.2⟩ := by
  apply Subtype.ext
  exact ContRepresentation.coe_subrepresentation_apply g x

/-- The inclusion of an invariant subrepresentation into its ambient representation. -/
noncomputable def subrepresentationι (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : subrepresentation X W hW ⟶ X :=
  ofHom (X.ρ.subrepresentationInclusion ⟨W, fun g x hx ↦ hW g x hx⟩)

/-- The inclusion of a subrepresentation is the subtype map. -/
@[simp]
theorem subrepresentationι_apply (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (x : subrepresentation X W hW) :
    (subrepresentationι X W hW).hom x = x.1 :=
  by simpa [subrepresentationι] using
    ContRepresentation.subrepresentationInclusion_apply X.ρ
      ⟨W, fun g x hx ↦ hW g x hx⟩ x

/-- The inclusion of a subrepresentation is injective. -/
theorem subrepresentationι_injective (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
  Function.Injective (subrepresentationι X W hW).hom :=
  fun x y h ↦ Subtype.ext <| calc
    x.1 = (subrepresentationι X W hW).hom x := (subrepresentationι_apply X W hW x).symm
    _ = (subrepresentationι X W hW).hom y := h
    _ = y.1 := subrepresentationι_apply X W hW y

/-- Descend a continuous representation to the quotient by an invariant submodule. -/
abbrev quotient (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : TopRep R G :=
  .of (X.ρ.quotient W hW)

/-- The operators of a quotient representation are the descended operators. -/
@[simp]
theorem quotient_ρ (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    (quotient X W hW).ρ = X.ρ.quotient W hW :=
  rfl

/-- The quotient action on a class is the class of the ambient action. -/
@[simp]
theorem quotient_ρ_apply_mk (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (g : G) (x : X.V) :
    (quotient X W hW).ρ g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (X.ρ g x) := by
  rw [quotient_ρ, ContRepresentation.quotient_apply_mk]

/-- The projection from a representation to its quotient by an invariant submodule. -/
def quotientπ (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) : X ⟶ quotient X W hW :=
  ofHom
    { toContinuousLinearMap := W.mkQL
      isIntertwining' g := by
        ext x
        simp [ContRepresentation.quotient_apply_mk] }

/-- The quotient projection sends a vector to its class. -/
@[simp]
theorem quotientπ_apply (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) (x : X) :
    (quotientπ X W hW).hom x = Submodule.Quotient.mk x :=
  by
    -- `ofHom` hides the continuous linear map, so expose it before applying `mkQL`'s formula.
    change W.mkQL x = _
    simp [Submodule.mkQL_apply, Submodule.mkQ_apply]

/-- The quotient projection is surjective. -/
theorem quotientπ_surjective (X : TopRep R G) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    Function.Surjective (quotientπ X W hW).hom :=
  Submodule.mkQ_surjective W

end TopRep

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
      rw [Submodule.mkQ_apply, TopRep.quotient_ρ_apply_mk]
      rw [hg']
    · simpa only [← TopRep.coe_stabilizer] using hX.stabilizer_isOpen x
  simpa only [← TopRep.coe_stabilizer (TopRep.quotient X W hW) (W.mkQ x),
    TopRep.quotient_ρ] using hstab

end TauCeti
