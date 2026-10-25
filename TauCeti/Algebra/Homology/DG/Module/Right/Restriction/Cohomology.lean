/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Basic

/-!
# The cohomology of a restricted differential graded right module

Let `f : A ⟶ B` be a morphism of differential graded algebras and `M` a right DG `B`-module.
Restriction of scalars along `f` keeps the underlying module and differential of `M`, so the
restricted module has the same cycles, boundaries and cohomology: the cohomology `H(f^* M)` is
`H(M)` as an `R`-module (`TauCeti.IsDGRightModule.restrictScalarsCohomologyEquiv`). Under this
identification, the action of `H(A)` on `H(f^* M)` is the action of `H(B)` on `H(M)` restricted
along the induced map `H(f) : H(A) → H(B)`
(`TauCeti.IsDGRightModule.restrictScalarsCohomologyEquiv_cohomologyAction`). The identification
preserves degrees (`TauCeti.IsDGRightModule.map_restrictScalarsCohomologyEquiv_cohomologyGrading`).

This is the form in which a change of coefficients by a DG algebra morphism, such as the twist of a
DG local system by a rank-one local system, is read off on cohomology.

## Main definitions

* `TauCeti.IsDGRightModule.restrictScalarsCohomologyEquiv`: the identification
  `H(f^* M) ≃ₗ[R] H(M)`.
* `TauCeti.IsDGRightModule.restrictScalarsCohomologyGradingEquiv`: its restriction
  `H^p(f^* M) ≃ₗ[R] H^p(M)` to a single degree.

## Main results

* `TauCeti.IsDGRightModule.mem_restrictScalars_cycles_iff`,
  `TauCeti.IsDGRightModule.mem_restrictScalars_boundaries_iff`: the cycles and boundaries of
  `f^* M` are those of `M`.
* `TauCeti.IsDGRightModule.restrictScalarsCohomologyEquiv_cohomologyAction`: the identification
  intertwines the action of a class `c` of `H(A)` with the action of `H(f) c`.
* `TauCeti.IsDGRightModule.map_restrictScalarsCohomologyEquiv_cohomologyGrading`: the
  identification carries `H^p(f^* M)` onto `H^p(M)`.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.
-/

public section

namespace TauCeti

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {M : Type uM} [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  {dM : M →ₗ[R] M} (f : DGAlgHom hA hB) (hM : IsDGRightModule hB ℳ dM)

namespace IsDGRightModule

/-- An element of a restricted module is a cycle exactly when its underlying element is. -/
theorem mem_restrictScalars_cycles_iff {x : DGRightModule.RestrictScalars f M} :
    x ∈ (hM.restrictScalars f).cycles ↔ x.val ∈ hM.cycles := by
  rw [mem_cycles, mem_cycles, ← val_restrictScalarsDifferential f x]
  exact ⟨congrArg DGRightModule.RestrictScalars.val, DGRightModule.RestrictScalars.ext⟩

/-- A cycle of a restricted module is a boundary exactly when its underlying cycle is. -/
theorem mem_restrictScalars_boundaries_iff {z : (hM.restrictScalars f).cycles} :
    z ∈ (hM.restrictScalars f).boundaries ↔
      (⟨(z : DGRightModule.RestrictScalars f M).val,
        (hM.mem_restrictScalars_cycles_iff f).mp z.2⟩ : hM.cycles) ∈ hM.boundaries := by
  rw [mem_boundaries, mem_boundaries]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.val, (val_restrictScalarsDifferential f x).symm.trans
      (congrArg DGRightModule.RestrictScalars.val hx)⟩,
    fun ⟨x, hx⟩ ↦ ⟨⟨x⟩, DGRightModule.RestrictScalars.ext
      ((val_restrictScalarsDifferential f _).trans hx)⟩⟩

/-- The cycles of a restricted module are the cycles of the original module. -/
private def restrictScalarsCyclesEquiv : (hM.restrictScalars f).cycles ≃ₗ[R] hM.cycles where
  toFun z := ⟨z.1.val, (hM.mem_restrictScalars_cycles_iff f).mp z.2⟩
  invFun z := ⟨⟨z.1⟩, (hM.mem_restrictScalars_cycles_iff f).mpr z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem map_restrictScalarsCyclesEquiv_boundaries :
    ((hM.restrictScalars f).boundaries.restrictScalars R).map
        (restrictScalarsCyclesEquiv f hM).toLinearMap =
      hM.boundaries.restrictScalars R := by
  ext z
  rw [Submodule.mem_map_equiv, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem,
    mem_restrictScalars_boundaries_iff]
  rfl

/-- **Restriction of scalars does not change module cohomology**: the cohomology of a module
restricted along a DG algebra morphism is that of the original module, as an `R`-module. A class
is sent to the class of the same underlying cycle
(`TauCeti.IsDGRightModule.restrictScalarsCohomologyEquiv_mk`). -/
noncomputable def restrictScalarsCohomologyEquiv :
    (hM.restrictScalars f).Cohomology ≃ₗ[R] hM.Cohomology :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm ≪≫ₗ
    Submodule.Quotient.equiv _ _ (restrictScalarsCyclesEquiv f hM)
      (map_restrictScalarsCyclesEquiv_boundaries f hM) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R _

/-- The class of a cycle of the restricted module is the class of the underlying cycle. -/
@[simp]
theorem restrictScalarsCohomologyEquiv_mk (z : (hM.restrictScalars f).cycles) :
    hM.restrictScalarsCohomologyEquiv f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨z.1.val, (hM.mem_restrictScalars_cycles_iff f).mp z.2⟩ :=
  (rfl)

/-- The class of the underlying cycle comes from the class of the cycle of the restricted
module. -/
@[simp]
theorem restrictScalarsCohomologyEquiv_symm_mk (z : hM.cycles) :
    (hM.restrictScalarsCohomologyEquiv f).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨⟨z.1⟩, (hM.mem_restrictScalars_cycles_iff f).mpr z.2⟩ :=
  (rfl)

/-- **The cohomology of a restricted module is restricted along the map on cohomology**: a class
`c` of the source algebra acts on the cohomology of the restricted module as its image under the
cohomology map of `f` acts on the cohomology of the original module. -/
theorem restrictScalarsCohomologyEquiv_cohomologyAction (c : hA.Cohomology)
    (x : (hM.restrictScalars f).Cohomology) :
    hM.restrictScalarsCohomologyEquiv f (((hM.restrictScalars f).cohomologyAction c).unop x) =
      (hM.cohomologyAction (f.cohomologyMap c)).unop (hM.restrictScalarsCohomologyEquiv f x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [cohomologyAction_mk, DGAlgHom.cohomologyMap_mk, cohomologyAction_mk,
      ← Submodule.Quotient.mk_smul, restrictScalarsCohomologyEquiv_mk,
      restrictScalarsCohomologyEquiv_mk, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    -- Cycles of the algebra act on module cycles through `Module.compHom` along the inclusion.
    simp [MulAction.compHom_smul_def]

/-- The identification `H(f^* M) ≃ H(M)` preserves degrees: a class of the restricted module has
degree `p` exactly when its image does. -/
theorem restrictScalarsCohomologyEquiv_mem_cohomologyGrading_iff {p : ℤ}
    {x : (hM.restrictScalars f).Cohomology} :
    hM.restrictScalarsCohomologyEquiv f x ∈ hM.cohomologyGrading p ↔
      x ∈ (hM.restrictScalars f).cohomologyGrading p := by
  rw [mem_cohomologyGrading, mem_cohomologyGrading]
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨⟨⟨z.1⟩, (hM.mem_restrictScalars_cycles_iff f).mpr z.2⟩, ?_, ?_⟩
    · rwa [mem_restrictScalarsGrading_iff, DGRightModule.RestrictScalars.linearEquiv_apply]
    · rw [← restrictScalarsCohomologyEquiv_symm_mk, hzx, LinearEquiv.symm_apply_apply]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_restrictScalarsGrading_iff, DGRightModule.RestrictScalars.linearEquiv_apply] at hz
    exact ⟨_, hz, (restrictScalarsCohomologyEquiv_mk f hM z).symm⟩

/-- The identification `H(f^* M) ≃ H(M)` carries `H^p(f^* M)` onto `H^p(M)`. -/
theorem map_restrictScalarsCohomologyEquiv_cohomologyGrading (p : ℤ) :
    ((hM.restrictScalars f).cohomologyGrading p).map
        (hM.restrictScalarsCohomologyEquiv f).toLinearMap =
      hM.cohomologyGrading p := by
  ext x
  rw [Submodule.mem_map_equiv, ← restrictScalarsCohomologyEquiv_mem_cohomologyGrading_iff,
    LinearEquiv.apply_symm_apply]

/-- **Restriction of scalars does not change module cohomology in a single degree**: the
identification `H(f^* M) ≃ H(M)` restricts to `H^p(f^* M) ≃ H^p(M)`. -/
noncomputable def restrictScalarsCohomologyGradingEquiv (p : ℤ) :
    (hM.restrictScalars f).cohomologyGrading p ≃ₗ[R] hM.cohomologyGrading p :=
  (hM.restrictScalarsCohomologyEquiv f).ofSubmodules _ _
    (hM.map_restrictScalarsCohomologyEquiv_cohomologyGrading f p)

/-- The identification `H^p(f^* M) ≃ H^p(M)` is the restriction of `H(f^* M) ≃ H(M)`. -/
@[simp]
theorem coe_restrictScalarsCohomologyGradingEquiv_apply (p : ℤ)
    (x : (hM.restrictScalars f).cohomologyGrading p) :
    (hM.restrictScalarsCohomologyGradingEquiv f p x : hM.Cohomology) =
      hM.restrictScalarsCohomologyEquiv f x :=
  (rfl)

end IsDGRightModule

end TauCeti
