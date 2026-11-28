/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval

import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.LinearSubst
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Eval
import TauCeti.RingTheory.Trace.EmbeddingsMatrix.Normed

/-!
# Coefficient recovery in the coordinates of local field embeddings

Let `F/ℚ_p` have degree `k` and let `σ₁, …, σ_k : F → K` be distinct embeddings over
`ℚ_p`. Evaluating a restricted series at `(σᵢ(y))ᵢ` for `y` in any sufficiently small
ball about zero determines all its coefficients when bounded `ℚ_p`-linear maps into
normed fields jointly separate the points of the Banach coefficient algebra. This
includes coefficient algebras with nilpotents that admit such a family.

The linear change from a small `ℚ_p`-basis of `F` to the embedding coordinates is
invertible by linear independence of embeddings (Mathlib's
`linearIndependent_algHom_toLinearMap`). Coefficient recovery then uses the
identity theorem on `ℤ_pⁿ` for module-valued restricted families.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Matrix

variable {K R : Type*} [NormedField K] [NormedCommRing R] [NormedAlgebra K R]
  [IsUltrametricDist R] [CompleteSpace R] {k : ℕ} {r : Fin k → ℝ}

variable {p : ℕ} [Fact p.Prime] {F : Type*} [NormedField F]
  [NormedAlgebra ℚ_[p] F] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] F] [NormedSpace ℚ_[p] R] [IsScalarTower ℚ_[p] K R]

/-- A restricted series over `R` is zero if its values in the coordinates of a full family
of distinct embeddings of `F/ℚ_p` vanish on a positive-radius ball about zero in `F`.
The bounded `ℚ_p`-linear maps `φ j : R → L j` must jointly separate the points of `R`. -/
theorem eq_zero_of_restrictedEval₂_algHom_eq_zero [NormOneClass R] [hr : ∀ i, Fact (0 < r i)]
    (σ : Fin k → F →ₐ[ℚ_[p]] K) (hσ : Function.Injective σ)
    (hk : Module.finrank ℚ_[p] F = k) {ε : ℝ} (hε : 0 < ε)
    {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)] [∀ j, NormedAlgebra ℚ_[p] (L j)]
    (φ : ∀ j, R →L[ℚ_[p]] L j) (hφ : ∀ a, (∀ j, φ j a = 0) → a = 0)
    (f : IsRestricted.subring (R := R) r)
    (hbound : ∀ (y : F), ‖y‖ ≤ ε → ∀ i, ‖algebraMap K R (σ i y)‖ ≤ r i)
    (h : ∀ (y : F) (hy : ‖y‖ ≤ ε),
      restrictedEval₂ (RingHom.id R) (fun i ↦ algebraMap K R (σ i y))
        (fun _ ↦ le_rfl) (hbound y hy) f = 0) :
    f = 0 := by
  obtain ⟨b, hb, hu₀⟩ := exists_norm_lt_isUnit_embeddingsMatrix σ hσ hk hε
  have : IsUltrametricDist F := .of_normedAlgebra ℚ_[p]
  let : ∀ i, Fact (0 ≤ r i) := fun i ↦ ⟨(hr i).out.le⟩
  let A₀ : Matrix (Fin k) (Fin k) K := ((Algebra.embeddingsMatrix ℚ_[p] K b).submatrix id σ)ᵀ
  have hA₀ (i j : Fin k) : A₀ i j = σ i (b j) := by
    simp only [A₀, transpose_apply, submatrix_apply, Algebra.embeddingsMatrix_apply, id_eq]
  let A : Matrix (Fin k) (Fin k) R := (algebraMap K R).mapMatrix A₀
  have hA : ∀ i j, ‖A i j‖ * (1 : ℝ) ≤ r i := by
    simpa [A, hA₀] using fun i j ↦ hbound (b j) (hb j).le i
  have hu : IsUnit A := (A₀.isUnit_iff_isUnit_det.mpr (by
    simpa only [A₀, det_transpose] using (isUnit_iff_isUnit_det _).mp hu₀)).map
      (algebraMap K R).mapMatrix
  let g := restrictedLinearSubst A hA f
  have hg : g = 0 := by
    apply Subtype.ext
    ext d
    have hgR := (isRestrictedFamily_coeff_iff _).mpr (IsRestricted.mem_subring.mp g.property)
    suffices hzero : (fun d ↦ coeff d (g : MvPowerSeries (Fin k) R)) = 0 by
      simpa using congrFun hzero d
    refine hgR.eq_zero_of_familyEval_padicInt_eq_zero (K := K) φ hφ fun x ↦ ?_
    let z (j : Fin k) := algebraMap ℚ_[p] K (x j : ℚ_[p])
    have hzR (j : Fin k) : ‖algebraMap K R (z j)‖ ≤ 1 := by
      simpa [z] using PadicInt.norm_le_one (x j)
    let y := ∑ j, (x j : ℚ_[p]) • b j
    have hy : ‖y‖ ≤ ε := by
      exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le fun j _ ↦ by
        rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one (x j))).trans
          (hb j).le
    have harg : A.map (RingHom.id R) *ᵥ (fun j ↦ algebraMap K R (z j)) =
        fun i ↦ algebraMap K R (σ i y) := by
      funext i
      simp [A, hA₀, mulVec_apply_eq_sum, y, z, Algebra.smul_def, mul_comm]
    rw [← restrictedEval₂_algebraMap_arg_eq_familyEval g z hzR]
    dsimp only [g]
    rw [restrictedEval₂_restrictedLinearSubst (RingHom.id R) A hA]
    simp only [restrictedEval₂_apply, harg] at h ⊢
    exact h y hy
  exact restrictedLinearSubst_injective A hA hu (by simpa [g] using hg)

end TauCeti.MvPowerSeries
