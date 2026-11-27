/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Reductive
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Datum

/-!
# Full-cocharacter checks for the Chevalley central/derived decomposition

For a root-free datum the entire rational algebra is central and the derived ideal vanishes.
For the diagonal datum of `GL₂`, the cocharacter `(1,0)` splits as one half of `(1,1)` plus one
half of `(1,-1)`. The first summand is central and the second is a coroot. These checks use a
supplied Chevalley table, just as the general splitting does.
-/

public section

open scoped TensorProduct
open RootPairing RootPairing.ChevalleyLieAlgebra

namespace TauCeti.Examples.ChevalleyReductive

noncomputable section

section RootFree

variable {ι X Y : Type*} [IsEmpty ι] [AddCommGroup X] [AddCommGroup Y]
  [Module.Free ℤ Y] [Module.Finite ℤ Y] (P : RootPairing ι ℤ X Y)

example (x : ℚ ⊗[ℤ] ChevalleyLieAlgebra (ChevalleyConstants.ofIsEmpty P)) :
    x ∈ LieAlgebra.center ℚ (ℚ ⊗[ℤ] ChevalleyLieAlgebra (ChevalleyConstants.ofIsEmpty P)) := by
  apply (mem_center_baseChange_iff _ ℚ x).mpr
  exact ⟨by ext i; exact isEmptyElim i, RootPairing.mem_corootKer.mpr isEmptyElim⟩

example : LieAlgebra.derivedSeries ℚ
    (ℚ ⊗[ℤ] ChevalleyLieAlgebra (ChevalleyConstants.ofIsEmpty P)) 1 = ⊥ := by
  let : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  apply LieSubmodule.toSubmodule_injective
  rw [derivedSeries_one_eq_span]
  simp

end RootFree

/-- The root-free rank-one datum gives a one-dimensional rational toral Lie algebra. -/
theorem finrank_root_free_rank_one (P : RootPairing Empty ℤ ℤ ℤ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] ChevalleyLieAlgebra (ChevalleyConstants.ofIsEmpty P)) = 1 := by
  let e := LinearEquiv.baseChange ℤ ℚ _ _
    (cartanEquivOfIsEmpty (ChevalleyConstants.ofIsEmpty P))
  rw [← e.finrank_eq, Module.finrank_baseChange]
  simp

section GeneralLinearTwo

private abbrev glTwoDatum := GeneralLinear.diagonalRootDatum.{0} 2

private def positiveRoot : GeneralLinear.DiagonalRootIndex.{0} 2 :=
  ⟨(ULift.up 0, ULift.up 1), by decide⟩

private def firstCocharacter : ULift (Fin 2) → ℤ := fun i ↦ if i.down = 0 then 1 else 0

private theorem root_eval (i : GeneralLinear.DiagonalRootIndex 2) (y : ULift (Fin 2) → ℤ) :
    glTwoDatum.root' i y = y i.val.1 - y i.val.2 := by
  classical
  simp [RootPairing.root', GeneralLinear.diagonalRootDatum_toLinearMap,
    GeneralLinear.diagonalRootDatum_root, GeneralLinear.diagonalRoot_eq_coordinateRoot,
    SplitTorus.coordinateRoot_def]

private theorem central_mem (c : glTwoDatum.ChevalleyConstants) :
    (cartan c).baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] (fun _ : ULift (Fin 2) ↦ (1 : ℤ))) ∈
      LieAlgebra.center ℚ (ℚ ⊗[ℤ] ChevalleyLieAlgebra c) := by
  apply (baseChange_cartan_mem_center_iff c ℚ _).mpr
  apply RootPairing.mem_corootKer.mpr
  intro i
  have h : glTwoDatum.root' i (fun _ ↦ (1 : ℤ)) = 0 := by rw [root_eval]; simp
  have hi : (glTwoDatum.baseChange ℚ).root' i ((1 : ℚ) ⊗ₜ[ℤ] (fun _ ↦ (1 : ℤ))) = 0 := by
    rw [RootPairing.baseChange_root'_tmul, h]
    simp
  exact hi

private theorem coroot_mem (c : glTwoDatum.ChevalleyConstants) :
    (1 : ℚ) ⊗ₜ[ℤ] cartan c (glTwoDatum.coroot positiveRoot) ∈
      LieAlgebra.derivedSeries ℚ (ℚ ⊗[ℤ] ChevalleyLieAlgebra c) 1 :=
  tmul_cartan_coroot_mem_derivedSeries_one c ℚ positiveRoot

-- The full cocharacter (1,0) acts on the positive root line with weight one.
example (c : glTwoDatum.ChevalleyConstants) :
    ⁅(1 : ℚ) ⊗ₜ[ℤ] cartan c firstCocharacter, (1 : ℚ) ⊗ₜ[ℤ] root c positiveRoot⁆ =
    (1 : ℚ) ⊗ₜ[ℤ] root c positiveRoot := by
  rw [LieAlgebra.ExtendScalars.bracket_tmul, cartan_lie_root]
  have h : glTwoDatum.root' positiveRoot firstCocharacter = 1 := by
    rw [root_eval]
    rfl
  rw [h]
  simp

-- The splitting has two nonzero toral components, each with coefficient one half.
example (c : glTwoDatum.ChevalleyConstants) :
    (centerDerivedEquiv c ℚ).symm ((1 : ℚ) ⊗ₜ[ℤ] cartan c firstCocharacter) =
      ((1 / 2 : ℚ) • ⟨_, central_mem c⟩, (1 / 2 : ℚ) • ⟨_, coroot_mem c⟩) := by
  apply (centerDerivedEquiv c ℚ).symm_apply_eq.mpr
  rw [centerDerivedEquiv_apply]
  simp only [LieSubmodule.coe_smul, LinearMap.baseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h : (2 : ℤ) • firstCocharacter =
      (fun _ : ULift (Fin 2) ↦ (1 : ℤ)) + glTwoDatum.coroot positiveRoot := by
    ext i
    rcases i with ⟨i⟩
    fin_cases i <;> simp [firstCocharacter, positiveRoot, glTwoDatum]
  have ht := congrArg (fun y ↦ (1 / 2 : ℚ) ⊗ₜ[ℤ] cartan c y) h
  rw [map_smul, map_add, TensorProduct.tmul_smul, TensorProduct.tmul_add] at ht
  norm_num [two_smul ℤ] at ht
  rw [← TensorProduct.add_tmul] at ht
  norm_num at ht
  simpa only [glTwoDatum, GeneralLinear.diagonalRootDatum_coroot] using ht

end GeneralLinearTwo

end

end TauCeti.Examples.ChevalleyReductive
