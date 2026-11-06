/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.WholeSpace
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# A global Schauder estimate on the complex plane

For smooth compactly supported real functions on the complex plane, the Hölder constant and
supremum of the Hessian are controlled by the Hölder constant of the Laplacian and the supremum
of the function. This transports the whole-space estimate through the orthonormal coordinates
`1, I`; the resulting constant is independent of higher derivatives of the function.
-/

public noncomputable section

open Metric Set InnerProductSpace Laplacian
open scoped NNReal ContDiff

namespace TauCeti.PDE

/-- A global Schauder estimate on `ℂ` for smooth compactly supported real functions. -/
theorem exists_holderWith_iteratedFDeriv_two_and_norm_le_of_laplacian_complex
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ {u : ℂ → ℝ} {N K : ℝ≥0}, ContDiff ℝ ∞ u →
      HasCompactSupport u → (∀ x, |u x| ≤ N) → HolderWith K α (Δ u) →
      HolderWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) ∧
        ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ C * (K + N) := by
  obtain ⟨C, hC⟩ :=
    exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv
      (n := 1) hα hα1 1 1 0
  refine ⟨C, fun {u N K} hu hc hN hK ↦ ?_⟩
  let e := Complex.orthonormalBasisOneI.repr.symm
  let v := u ∘ e
  have hv : ContDiff ℝ ∞ v := hu.comp e.contDiff
  have hcv : HasCompactSupport v := hc.comp_homeomorph e.toHomeomorph
  have hDv : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 v) :=
    hv.iteratedFDeriv_right (by simp)
  obtain ⟨B, hB, hBN⟩ := hDv.exists_holderWith_and_norm_le_of_hasCompactSupport
    (hcv.iteratedFDeriv 2) hα1.le
  have hΔv : HolderWith K α (Δ v) := by
    rw [show v = u ∘ e from rfl, laplacian_comp_linearIsometryEquiv_right]
    simpa using hK.comp e.lipschitzWith.holderWith
  have hLv : HolderWith K α (fun x ↦ ∑ i : Fin 2, ∑ j : Fin 2,
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j • fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    convert hΔv using 1
    funext x
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis v (EuclideanSpace.basisFun (Fin 2) ℝ)]
    simp [Matrix.one_apply, iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  obtain ⟨hH, -, hD⟩ := hC (uniformlyEllipticOn_const_one_one univ)
    (fun _ _ ↦ HolderWith.const) (hv.of_le (by simp)) (fun x ↦ hN (e x))
    ⟨B, by rintro _ ⟨x, rfl⟩; exact hBN x⟩ ⟨B, hB⟩ hLv
  have heN : ‖(e.toContinuousLinearEquiv.symm : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2))‖₊ = 1 := by
    apply NNReal.coe_injective
    exact e.symm.norm_toContinuousLinearMap
  have hH' := e.toContinuousLinearEquiv.holderOnWith_iteratedFDeriv_of_comp_right
    (s := univ) (f := u) (i := 2) (by simpa [v, e] using hH.holderOnWith univ)
  refine ⟨?_, fun x ↦ ?_⟩
  · simpa only [heN, one_pow, NNReal.one_rpow, mul_one, holderOnWith_univ] using hH'
  · have hnorm := e.norm_iteratedFDeriv_comp_right u (e.symm x) 2
    have hh := hD (e.symm x)
    dsimp only [v] at hh
    rw [hnorm, e.apply_symm_apply] at hh
    exact hh

end TauCeti.PDE
