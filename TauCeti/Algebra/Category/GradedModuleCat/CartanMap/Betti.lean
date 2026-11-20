/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Betti

/-!
# The graded Cartan matrix and the Betti Poincaré matrix

Let `A` be a finite-dimensional nonnegatively graded algebra over a field `k`, let `Sᵢ` be an
exhaustive family of finite-dimensional graded simples concentrated in internal degree zero, and
let `C(q)` be the graded Cartan matrix in a projective basis of classes `[A eᵢ]` and the
simple-class basis `[Sⱼ]`, with rows `Sᵢ` and columns `Pⱼ`. Choose minimal graded projective
resolutions of the `Sⱼ` by finitely generated terms, and let `B(q, t)` be their Betti Poincaré
matrix, with rows `Pᵢ` and columns `Sⱼ` (`TauCeti.bettiPoincarePowerSeriesMatrix`).

Each Betti Poincaré series vanishes below the diagonal, so its specialization at `t = -1` is a
formal power series in `q` whose coefficients are finite alternating sums
(`TauCeti.Bigraded.eulerPowerSeries`). With `C(q)` embedded in formal power series, this file
proves the **Cartan–Betti identity**

`C(q) · B(q, -1) = I`.

The resolutions may be infinite, so the identity holds coefficientwise in `q`; no finite global
dimension is assumed. Unlike the Ext form
`TauCeti.gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal`, the right-hand side
carries no factors `dim_k End_A(Sᵢ)`: those factors relate Ext dimensions to Betti numbers and
cancel. When the resolutions are linear, `B(q, t)` is supported on the diagonal and the identity
becomes the one-variable identity `C(q) · P(-q) = I` for the Poincaré matrix `P(q) = B(q, 1)`.

## Main results

* `TauCeti.gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix_eq_one`:
  `C(q) · B(q, -1) = I` for minimal resolutions.
* `TauCeti.gradedCartanMatrix_trunc_mul_diagonal_bettiPoincarePowerSeriesMatrix_eq_one`:
  `C(q) · P(-q) = I` for linear resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11, for minimal and linear resolutions
  and the matrix identity between the Hilbert series of a Koszul ring and the Poincaré series of
  its simples.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hbP in
/-- **The Cartan–Betti identity `C(q) · B(q, -1) = I`.** Over a finite-dimensional nonnegatively
graded algebra, let `Sᵢ` be an exhaustive degree-zero simple family with chosen minimal
resolutions `rⱼ` by finitely generated terms. Let `C_ps` truncate each entry of the graded Cartan
matrix into `PowerSeries ℤ`, and let the `(i, j)` entry of the second factor be the Betti
Poincaré series of `rⱼ` at `Pᵢ` evaluated at `t = -1`, the formal power series in `q` whose
coefficient of `qᵃ` is `∑ₙ (-1)ⁿ βⁿ_{i,a}(Sⱼ)`. Then their product is the identity matrix. The
resolutions may be infinite. -/
theorem gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix_eq_one
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        (fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries
        ((hr j).hasEulerPowerSeries_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc
          (fun p hp ↦ hconc j p hp.ne) i (hself i))) = 1 := by
  have (j : I) (n : ℕ) : Module.Finite k ((r j).X n) := Module.Finite.trans A ((r j).X n)
  set Cps := (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
    fun p ↦ (p.trunc : PowerSeries ℤ)
  set B := Matrix.of fun i j ↦ Bigraded.eulerPowerSeries
    ((hr j).hasEulerPowerSeries_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc
      (fun p hp ↦ hconc j p hp.ne) i (hself i)) with hB
  set d : I → PowerSeries ℤ := fun i ↦
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) with hd
  have key := gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc
  -- The Euler series of `Ext(Sₗ, Sⱼ)` is `dⱼ` times that of the Betti series of `Sₗ` at `Pⱼ`.
  have hE : Matrix.of (fun l j ↦ Bigraded.eulerPowerSeries
      ((hr l).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
        (fun p hp ↦ hconc l p hp.ne) (hconc j)
        (GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S l).obj (S j).obj))) =
      Bᵀ * Matrix.diagonal d := by
    refine Matrix.ext fun l j ↦ ?_
    have hC := (hr l).C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP
      hconc j (GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S l).obj (S j).obj)
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc j)] at hC
    simp only [hB, hd, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]
    rw [Bigraded.eulerPowerSeries_congr _
      (hC ▸ (hr l).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
        (fun p hp ↦ hconc l p hp.ne) (hconc j) _) hC.symm,
      Bigraded.eulerPowerSeries_C_mul, mul_comm]
  rw [hE, ← Matrix.mul_assoc, ← Matrix.transpose_mul] at key
  -- Cancel the nonzero constants `dⱼ` from `(B · C_ps)ᵀ · diagonal d = diagonal d`.
  have hBC : (B * Cps)ᵀ = 1 := by
    refine Matrix.ext fun i j ↦ mul_right_cancel₀ (b := d j) ?_ ?_
    · have hpos := (S j).obj.finrank_smul_piece_zero_pos_of_concentrated (e j) (hconc j)
        (hself j)
      exact (map_ne_zero_iff _ PowerSeries.C_injective).mpr (by omega)
    · have hij := congrFun (congrFun key i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_apply] at hij
      rw [hij, Matrix.one_apply]
      split_ifs with h
      · rw [h, one_mul]
      · rw [zero_mul]
  exact mul_eq_one_comm.mp (Matrix.transpose_eq_one.mp hBC)

include hbP in
/-- **The Cartan–Poincaré identity `C(q) · P(-q) = I` for linear resolutions.** Over a
finite-dimensional nonnegatively graded algebra, let `Sᵢ` be an exhaustive degree-zero simple
family with chosen linear resolutions `rⱼ` by finitely generated terms. Their Betti Poincaré
series are supported on the diagonal, so they are recorded by the one-variable Poincaré matrix
`P(q) = B(q, 1)`, whose `(i, j)` entry is `∑ₙ βⁿ_{i,n}(Sⱼ) qⁿ`. With `C_ps` the graded Cartan
matrix truncated into `PowerSeries ℤ`, `C_ps · P(-q) = I`. The resolutions may be infinite. -/
theorem gradedCartanMatrix_trunc_mul_diagonal_bettiPoincarePowerSeriesMatrix_eq_one
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        (fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ PowerSeries.rescale (-1 : ℤ) (PowerSeries.mk fun n ↦
        (PowerSeries.coeff n ((r j).bettiPoincarePowerSeries bP i)).coeff n)) = 1 := by
  have hmin (j : I) : (r j).IsMinimal := (hr j).isMinimal hneg
  rw [← gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeriesMatrix_eq_one
    S he he₀ hI hne hself hS bP hbP r hmin hneg hconc]
  congr 1
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.of_apply, Matrix.of_apply, Bigraded.eulerPowerSeries_of_diagonal _
    (((hmin j).isLinear_iff_diagonal_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc hneg
      hS hself).1 (hr j) i)]

end TauCeti
