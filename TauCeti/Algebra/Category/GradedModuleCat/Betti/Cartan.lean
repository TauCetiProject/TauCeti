/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Ext
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.PowerSeries
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Unbounded Cartan–Betti identities

This file proves the unbounded formal-power-series graded Cartan–Betti identity
`C(q) · B(q, -1) = I` (with neither finite global dimension nor a splitting field assumption)
and its one-variable diagonal specialization `C_ps · P(-q) = I` for linear minimal resolutions.

Over a finite-dimensional nonnegatively graded algebra `A`, let `Sᵢ` be an exhaustive degree-zero
simple family cut out by degree-zero idempotents `eᵢ` whose projective covers `A eᵢ` form a
Laurent basis `bP` of `K₀^gr(proj A)`:

* `TauCeti.eulerPowerSeriesBettiPoincareMatrix`: the formal-power-series matrix obtained by
  evaluating each entry of the Betti Poincaré matrix at `t = -1` via `Bigraded.eulerPowerSeries`.
* `TauCeti.diagonalBettiPowerSeriesMatrix`: the one-variable diagonal Betti power-series matrix
  evaluated at `-q`.
* `TauCeti.gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one` and
  `TauCeti.eulerPowerSeries_bettiPoincareMatrix_eq_inv_gradedCartanMatrix_trunc`: for minimal
  resolutions of an exhaustive degree-zero simple family, `C_ps · B_euler = 1` and
  `B_euler = C_ps⁻¹` in `Matrix I I (PowerSeries ℤ)`. Both the transpose and the division-ring
  diagonal factor `dim_k(eᵢ • (Sᵢ)₀)` from the Ext form cancel out completely.
* `TauCeti.coeff_gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix`: explicit
  coefficientwise `qᵖ` form of `C(q) · B(q, -1) = I` as a finite double sum.
* `TauCeti.forall_isLinear_iff_cartan_betti_maslovEulerPowerSeries`,
  `TauCeti.gradedCartanMatrix_trunc_mul_diagonalBettiPowerSeries_eq_one`, and
  `TauCeti.diagonalBettiPowerSeries_eq_inv_gradedCartanMatrix_trunc`: linearity of all minimal
  resolutions of the simples is equivalent to `C_ps · B_maslov = 1`, giving the one-variable
  identity `C_ps · P(-q) = 1` and `P(-q) = C_ps⁻¹`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *Journal of Combinatorial Theory,
  Series A* **185** (2022), Sections 2.2 and 3.1--3.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI uJ

/-! ### Derived Betti formal power-series matrices -/

section DerivedMatrices

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI} {J : Type uJ}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  {M : J → GradedModuleCat.{uA} 𝒜}
  (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
  [∀ j n, Module.Finite A ((r j).X n)]

/-- The matrix of Alexander-graded Euler formal power series of the Betti Poincaré matrix `B(q, t)`
evaluated at `t = -1`. -/
def eulerPowerSeriesBettiPoincareMatrix
    (h : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j)) :
    Matrix I J (PowerSeries ℤ) :=
  Matrix.of fun i j => Bigraded.eulerPowerSeries (h i j)

/-- The `(i, j)` entry of `eulerPowerSeriesBettiPoincareMatrix` is the Alexander-graded Euler
power series of `bettiPoincareMatrix bP r i j`. -/
@[simp]
theorem eulerPowerSeriesBettiPoincareMatrix_apply
    (h : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j)) (i : I) (j : J) :
    eulerPowerSeriesBettiPoincareMatrix bP r h i j = Bigraded.eulerPowerSeries (h i j) :=
  Matrix.of_apply _ i j

/-- The `a`-th coefficient of the `(i, j)` entry of `eulerPowerSeriesBettiPoincareMatrix` is the
alternating sum over the finite Maslov support in internal degree `a`. -/
theorem coeff_eulerPowerSeriesBettiPoincareMatrix
    (h : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j))
    (i : I) (j : J) (a : ℕ) :
    PowerSeries.coeff a (eulerPowerSeriesBettiPoincareMatrix bP r h i j) =
      ((h i j).finite_support a).toFinset.sum fun n =>
        (-1 : ℤ) ^ n * (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff (a : ℤ) := by
  simp

/-- The one-variable diagonal Betti formal power-series matrix `P(-q)`, whose `(i, j)` entry has
`n`-th coefficient `(-1)ⁿ [qⁿ][tⁿ] Bᵢⱼ(q, t)`. -/
def diagonalBettiPowerSeriesMatrix : Matrix I J (PowerSeries ℤ) :=
  Matrix.of fun i j =>
    PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.mk fun n =>
        (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff (n : ℤ))

/-- The `(i, j)` entry of `diagonalBettiPowerSeriesMatrix` is the `-1`-rescaled diagonal series of
`bettiPoincareMatrix bP r i j`. -/
@[simp]
theorem diagonalBettiPowerSeriesMatrix_apply (i : I) (j : J) :
    diagonalBettiPowerSeriesMatrix bP r i j =
      PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.mk fun n =>
          (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff (n : ℤ)) :=
  Matrix.of_apply _ i j

/-- The `n`-th coefficient of the `(i, j)` entry of `diagonalBettiPowerSeriesMatrix` is
`(-1)ⁿ [qⁿ][tⁿ] Bᵢⱼ(q, t)`. -/
theorem coeff_diagonalBettiPowerSeriesMatrix (i : I) (j : J) (n : ℕ) :
    PowerSeries.coeff n (diagonalBettiPowerSeriesMatrix bP r i j) =
      (-1 : ℤ) ^ n * (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff (n : ℤ) := by
  simp

end DerivedMatrices

/-! ### Unbounded formal-power-series Cartan–Betti identities -/

section UnboundedCartanBetti

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
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

omit [GradedAlgebra 𝒜] [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)] [Fintype I] [DecidableEq I] in
include hself in
private theorem C_finrank_smul_piece_zero_ne_zero
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (i : I) :
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 := by
  intro h0
  have hpos : (0 : ℤ) < Module.finrank k ↥(e i • (S i).obj.grading.piece 0) :=
    Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i))
  have hc0 := congrArg PowerSeries.constantCoeff h0
  simp only [PowerSeries.constantCoeff_C, map_zero] at hc0
  omega

include hbP in
/-- **Unbounded formal-power-series Cartan–Betti identity `C_ps · B_euler = I`.** Over a
finite-dimensional nonnegatively graded algebra, let `Sᵢ` be an exhaustive degree-zero simple
family with chosen minimal resolutions `rᵢ` having finitely generated terms. Evaluating the Betti
Poincaré matrix at `t = -1` via `Bigraded.eulerPowerSeries` yields a formal-power-series right (and
left) inverse to the truncated graded Cartan matrix `C_ps`, with neither finite global dimension
nor a splitting field assumption. -/
theorem gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) :=
      fun i j => (bettiPoincareMatrix_apply bP r i j).symm ▸
        (hr j).hasEulerPowerSeries_bettiPoincareSeries
          S he he₀ hI hne bP hbP hself hconc (fun p hp => hconc j p hp.ne) i) :
    ((gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p => (p.trunc : PowerSeries ℤ)) *
      eulerPowerSeriesBettiPoincareMatrix bP r hB = 1 := by
  let _ : ∀ j n, Module.Finite k ((r j).X n) := fun j n => Module.Finite.trans A ((r j).X n)
  let hExt : ∀ i j,
      IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
    fun i j => GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj
  refine (mul_eq_one_iff_transpose_mul_eq_diagonal
    (fun i => mul_right_injective₀ (C_finrank_smul_piece_zero_ne_zero S hself hconc i)) ?_).mpr
    (gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
      S he he₀ hI hne hself hS bP hbP r hr hneg hconc hExt)
  refine Matrix.ext fun i j => ?_
  rw [Matrix.diagonal_mul, Matrix.transpose_apply, eulerPowerSeriesBettiPoincareMatrix_apply,
    Matrix.of_apply, Bigraded.eulerPowerSeries_congr (hB i j)
      ((hr j).hasEulerPowerSeries_bettiPoincareSeries
        S he he₀ hI hne bP hbP hself hconc (fun p hp => hconc j p hp.ne) i)
      (bettiPoincareMatrix_apply bP r i j)]
  exact (hr j).finrank_smul_piece_zero_mul_eulerPowerSeries_bettiPoincareSeries
    S he he₀ hI hne bP hbP hself hconc (fun p hp => hconc j p hp.ne) i (hExt j i)

include hbP in
/-- **Matrix-inverse form of the unbounded Cartan–Betti identity:** `B_euler = C_ps⁻¹` in
`Matrix I I (PowerSeries ℤ)`. -/
theorem eulerPowerSeries_bettiPoincareMatrix_eq_inv_gradedCartanMatrix_trunc
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) :=
      fun i j => (bettiPoincareMatrix_apply bP r i j).symm ▸
        (hr j).hasEulerPowerSeries_bettiPoincareSeries
          S he he₀ hI hne bP hbP hself hconc (fun p hp => hconc j p hp.ne) i) :
    eulerPowerSeriesBettiPoincareMatrix bP r hB =
      ((gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p => (p.trunc : PowerSeries ℤ))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
      S he he₀ hI hne hself hS bP hbP r hr hneg hconc hB)).symm

include hbP in
/-- **Coefficientwise `qᵖ` form of `C(q) · B(q, -1) = I`.** For every internal degree `p : ℕ`
and every pair `(i, j)`, the `qᵖ`-coefficient of the product is a finite double sum equal to
`1` if `i = j` and `p = 0`, and `0` otherwise. -/
theorem coeff_gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (i j : I) (p : ℕ) :
    ∑ l, ∑ m ∈ Finset.range (p + 1),
        (gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS) i l).coeff (m : ℤ) *
        ∑ n ∈ Finset.range (p - m + 1),
          (-1 : ℤ) ^ n *
            (PowerSeries.coeff n (bettiPoincareMatrix bP r l j)).coeff ((p - m : ℕ) : ℤ) =
      if i = j ∧ p = 0 then 1 else 0 := by
  have h := congrArg (fun M => PowerSeries.coeff p (M i j))
    (gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
      S he he₀ hI hne hself hS bP hbP r hr hneg hconc)
  rw [Matrix.mul_apply, map_sum, Matrix.one_apply] at h
  have hrhs : PowerSeries.coeff p (if i = j then (1 : PowerSeries ℤ) else 0) =
      if i = j ∧ p = 0 then 1 else 0 := by
    by_cases hij : i = j <;> by_cases hp : p = 0 <;> simp [hij, hp, PowerSeries.coeff_one]
  rw [hrhs] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.map_apply, eulerPowerSeriesBettiPoincareMatrix_apply, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun m _ => ?_
  dsimp only
  rw [Polynomial.coeff_coe, coeff_trunc,
    Bigraded.coeff_eulerPowerSeries_of_lowerTriangular _
      (fun n d hdn => by
        rw [bettiPoincareMatrix_apply]
        exact (hr j).coeff_coeff_bettiPoincareSeries_eq_zero_of_lt
          S he he₀ hI hne bP hbP hself hconc (fun q hq => hconc j q hq.ne) l (by omega)),
    bettiPoincareMatrix_apply]

include hbP in
/-- **Linearity is the unbounded Cartan–Betti identity for the Maslov-graded Euler series.** Chosen
minimal resolutions with finitely generated terms of an exhaustive degree-zero simple family are
all linear if and only if `C_ps · B_maslov = 1` in `Matrix I I (PowerSeries ℤ)`. -/
theorem forall_isLinear_iff_cartan_betti_maslovEulerPowerSeries
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ j, (r j).IsLinear) ↔
      ((gradedCartanMatrix 𝒜 bP
            (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
          fun p => (p.trunc : PowerSeries ℤ)) *
        (bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries = 1 := by
  let _ : ∀ j n, Module.Finite k ((r j).X n) := fun j n => Module.Finite.trans A ((r j).X n)
  let hExt : ∀ i j,
      IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
    fun i j => GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj
  rw [forall_isLinear_iff_cartan_poincare_maslovEulerPowerSeries
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc hExt]
  symm
  refine mul_eq_one_iff_transpose_mul_eq_diagonal
    (fun i => mul_right_injective₀ (C_finrank_smul_piece_zero_ne_zero S hself hconc i)) ?_
  refine Matrix.ext fun i j => ?_
  rw [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.map_apply, Matrix.map_apply,
    bettiPoincareMatrix_apply, bigradedExtPoincarePowerSeriesMatrix_apply]
  exact (hr j).finrank_smul_piece_zero_mul_maslovEulerPowerSeries_bettiPoincareSeries
    S he he₀ hI hne bP hbP hconc i (hExt j i)

include hbP in
/-- **One-variable Cartan–Betti identity `C_ps · P(-q) = I` for linear resolutions.** When all
chosen minimal resolutions of the exhaustive simple family are linear, the diagonal Betti
one-variable matrix `P(-q)` satisfies `C_ps · P(-q) = 1` in `Matrix I I (PowerSeries ℤ)`. -/
theorem gradedCartanMatrix_trunc_mul_diagonalBettiPowerSeries_eq_one
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hlin : ∀ j, (r j).IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    ((gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p => (p.trunc : PowerSeries ℤ)) *
      diagonalBettiPowerSeriesMatrix bP r = 1 := by
  have hr : ∀ j, (r j).IsMinimal := fun j => (hlin j).isMinimal hneg
  have hdiag := (forall_isLinear_iff_diagonal_bettiPoincareMatrix
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc).mp hlin
  have hmaslov := (forall_isLinear_iff_cartan_betti_maslovEulerPowerSeries
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc).mp hlin
  rw [← hmaslov]
  congr 1
  refine Matrix.ext fun i j => PowerSeries.ext fun n => ?_
  rw [coeff_diagonalBettiPowerSeriesMatrix, Matrix.map_apply,
    Bigraded.coeff_maslovEulerPowerSeries_of_diagonal (hdiag i j) n]

include hbP in
/-- For linear minimal resolutions of an exhaustive degree-zero simple family, the one-variable
diagonal Betti power-series matrix at `-q` is the inverse of the truncated graded Cartan matrix:
`P(-q) = C_ps⁻¹`. -/
theorem diagonalBettiPowerSeries_eq_inv_gradedCartanMatrix_trunc
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hlin : ∀ j, (r j).IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    diagonalBettiPowerSeriesMatrix bP r =
      ((gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p => (p.trunc : PowerSeries ℤ))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_trunc_mul_diagonalBettiPowerSeries_eq_one
      S he he₀ hI hne hself hS bP hbP r hlin hneg hconc)).symm

end UnboundedCartanBetti

end TauCeti
