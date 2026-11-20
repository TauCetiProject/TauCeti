/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Betti

/-!
# The Cartan matrix times the Betti Poincaré matrix at `t = -1`

Let `A` be a finite-dimensional nonnegatively graded algebra over a field `k`, let `Sᵢ` be an
exhaustive family of finite-dimensional graded simples concentrated in internal degree zero, and
let `C(q)` be the graded Cartan matrix, with rows the simple classes `[Sᵢ]` and columns the
idempotent projective classes `[A eⱼ]`. Choose minimal graded projective resolutions of the `Sⱼ` by
finitely generated terms, and let `B(q, t)` be their Betti Poincaré matrix, with rows the
projectives `A eᵢ` and columns the simples `Sⱼ`.

Each resolution writes `[Sⱼ]` as the alternating sum of the classes of its terms, which is the
column `B(q, -1) eⱼ` in projective coordinates; applying the Cartan map gives the alternating
Euler identity

`C(q) · B(q, -1) = I`.

The resolutions may be infinite (over the dual numbers they are), so `B(q, -1)` is read
coefficientwise in `q`: a minimal resolution of a module concentrated in degree zero has its
`n`th term generated in degrees at least `n`, so the coefficient of `qᵃ` in `B(q, -1)` is the finite
alternating sum over `n ≤ a`
(`TauCeti.GradedProjectiveResolution.IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries`). This
is `TauCeti.Bigraded.eulerPowerSeries`, and since `C(q)` is supported in nonnegative degrees, the
identity holds in `Matrix I I (PowerSeries ℤ)`.

The proof compares with the Ext form of the identity: `dᵢ` times the Betti series at `A eᵢ` is
the Ext Poincaré series against `Sᵢ`, where `dᵢ = dim_k(eᵢ • Sᵢ)`, so the transpose of the Ext
Euler matrix is `D · B(q, -1)` with `D` the diagonal matrix of the `dᵢ`, and
`TauCeti.gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal` gives
`D · B(q, -1) · C(q) = D`.

When the resolutions are linear the Betti series are supported on the diagonal, and the identity
becomes `C(q) · P(-q) = I` for the one-variable Poincaré matrix `P(q) = B(q, 1)`. It is stated with
`TauCeti.Bigraded.maslovEulerPowerSeries`, the specialisation `q = 1`, `t ↦ -t` read as a power
series in the homological degree, which gives `B(1, -q)`; this agrees with `P(-q)` only for linear
resolutions. Conversely the identity `C(q) · B(1, -q) = I`, stated with the Betti series of minimal
resolutions, forces those resolutions to be linear.

## Main results

* `TauCeti.gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeries_eq_one`: the
  identity `C(q) · B(q, -1) = I` for minimal resolutions of the simples, possibly infinite.
* `TauCeti.forall_isLinear_iff_cartan_betti_maslovEulerPowerSeries`: minimal resolutions of the
  simples are all linear exactly when `C(q) · B(1, -q) = I`, which is `C(q) · P(-q) = I` with
  `P(q) = B(q, 1)` once the resolutions are linear.
* `gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_bettiPoincarePowerSeriesMatrix_eq_one`, in
  the namespace `TauCeti`: the identity `C(q) · P(-q) = I` for linear resolutions of the simples.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI

section BettiExtComparison

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
  (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)

include he he₀ hne hbP hconc in
/-- At `t = -1`, `dᵢ = dim_k(eᵢ • Sᵢ)` times the Betti Poincaré series of a minimal resolution at
`Pᵢ` is the Alexander-graded Euler power series of Ext against `Sᵢ`, for any finiteness
witnesses. -/
private theorem GradedProjectiveResolution.IsMinimal.C_finrank_mul_eulerPowerSeries_betti
    {M : GradedModuleCat.{uA} 𝒜}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading} [∀ n, Module.Finite A (r.X n)]
    (hr : r.IsMinimal) (i : I) (hB : Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i))
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj)
    (hE : Bigraded.HasEulerPowerSeries
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h)) :
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        Bigraded.eulerPowerSeries hB =
      Bigraded.eulerPowerSeries hE := by
  have (m : ℕ) : Module.Finite k (r.X m) := Module.Finite.trans A (r.X m)
  let _ : Module.Finite A (S i).obj := gradedFiniteModules_iff.mp (S i).property
  let _ : Module.Finite k (S i).obj := Module.Finite.trans A _
  have hEq : PowerSeries.C (C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ)) *
      r.bettiPoincarePowerSeries bP i =
        bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
    rw [← GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i)]
    exact hr.C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc i h
  rw [← Bigraded.eulerPowerSeries_C_mul hB _ (hB.C_mul _)]
  exact Bigraded.eulerPowerSeries_congr _ _ hEq

end BettiExtComparison

section CartanBetti

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

include he he₀ hne hbP in
/-- The Ext Euler matrix of minimal resolutions of the `Sᵢ` is the transpose of `D · B(q, -1)`,
where `D` is the diagonal matrix of the `dᵢ = dim_k(eᵢ • Sᵢ)`, for any finiteness witnesses. -/
private theorem ext_eulerPowerSeries_matrix_eq_transpose_diagonal_mul_betti
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj)
    (hE : ∀ i j, Bigraded.HasEulerPowerSeries
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) (h i j)))
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i)) :
    Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hE i j)) =
      (Matrix.diagonal (fun i ↦
          PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ)) *
        Matrix.of fun i j ↦ Bigraded.eulerPowerSeries (hB i j))ᵀ :=
  Matrix.ext fun i j ↦ by
    rw [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply]
    exact ((hr i).C_finrank_mul_eulerPowerSeries_betti S he he₀ hI hne bP hbP hconc j _ _ _).symm

include hbP in
/-- **The alternating Euler identity `C(q) · B(q, -1) = I`.** Over a finite-dimensional
nonnegatively graded algebra, let `Sᵢ` be an exhaustive degree-zero simple family with chosen
minimal graded projective resolutions `rᵢ` by finitely generated terms, possibly infinite. Then the
graded Cartan matrix, truncated into `PowerSeries ℤ`, times the matrix whose `(i, j)` entry is the
Betti Poincaré series of `rⱼ` at `A eᵢ` evaluated at `t = -1` coefficientwise in `q`, is the
identity. No cohomological global-dimension bound is assumed. -/
theorem gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeries_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        (fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries
        ((hr j).hasEulerPowerSeries_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc
          (fun p hp ↦ hconc j p hp.ne) i (hself i))) = 1 := by
  have (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := Module.Finite.trans A ((r i).X n)
  set Cps := (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
    fun p ↦ (p.trunc : PowerSeries ℤ)
  -- Prove `Eb * Cps = 1` for any finiteness witnesses of the Betti series.
  suffices ∀ hB : ∀ i j, Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i),
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) * Cps = 1 from
    mul_eq_one_comm.mp (this _)
  intro hB
  set Eb : Matrix I I (PowerSeries ℤ) := Matrix.of fun i j ↦ Bigraded.eulerPowerSeries (hB i j)
  set d : I → PowerSeries ℤ := fun i ↦
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ)
  -- The Ext form `Cpsᵀ * E = D`, with `E` the transpose of `D * Eb`.
  have key := gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc
  rw [ext_eulerPowerSeries_matrix_eq_transpose_diagonal_mul_betti S he he₀ hI hne bP hbP r hr hconc
    _ _ hB, ← Matrix.transpose_mul, Matrix.mul_assoc] at key
  have hD := congrArg Matrix.transpose key
  rw [Matrix.transpose_transpose, Matrix.diagonal_transpose] at hD
  -- Cancel the diagonal matrix `D`, whose entries are nonzero constants.
  refine Matrix.ext fun i j ↦ ?_
  have hij := congrFun (congrFun hD i) j
  rw [Matrix.diagonal_mul, Matrix.diagonal_apply] at hij
  have hdi : d i ≠ 0 := fun h0 ↦ by
    have hpos := (S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i)
    have hc := congrArg PowerSeries.constantCoeff h0
    simp only [d, PowerSeries.constantCoeff_C, map_zero] at hc
    omega
  rw [Matrix.one_apply]
  split_ifs at hij ⊢ with h
  · exact mul_left_cancel₀ hdi (hij.trans (mul_one _).symm)
  · exact mul_left_cancel₀ hdi (hij.trans (mul_zero _).symm)

include hbP in
/-- **Linearity is the Cartan–Betti identity `C(q) · B(1, -q) = I`.** Over a finite-dimensional
nonnegatively graded algebra, let `Sᵢ` be an exhaustive degree-zero simple family with chosen
minimal graded projective resolutions `rᵢ` by finitely generated terms. The resolutions are all
linear if and only if the graded Cartan matrix, truncated into `PowerSeries ℤ`, times the Betti
Poincaré matrix with `q = 1` and `t` replaced by `-t` (`TauCeti.Bigraded.maslovEulerPowerSeries`),
read as a power series in the homological degree, is the identity. That matrix is `P(-q)` for
`P(q) = B(q, 1)` only when the resolutions are linear. No cohomological global-dimension bound is
assumed. -/
theorem forall_isLinear_iff_cartan_betti_maslovEulerPowerSeries
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ i, (r i).IsLinear) ↔
      (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
          (fun p ↦ (p.trunc : PowerSeries ℤ)) *
        (bettiPoincarePowerSeriesMatrix r bP).map Bigraded.maslovEulerPowerSeries = 1 := by
  set Cps := (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
    fun p ↦ (p.trunc : PowerSeries ℤ)
  have key := gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincarePowerSeries_eq_one
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc
  have hiff (i j : I) (hB : Bigraded.HasEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i)) :
      Bigraded.eulerPowerSeries hB =
        Bigraded.maslovEulerPowerSeries ((r j).bettiPoincarePowerSeries bP i) ↔
      ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
        (PowerSeries.coeff n ((r j).bettiPoincarePowerSeries bP i)).coeff p = 0 := by
    exact Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff hB
      ((hr j).coeff_coeff_bettiPoincarePowerSeries_nonneg S he he₀ hI hne bP hbP hconc i (hself i))
      (fun n p hpn ↦ (hr j).coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt S he he₀ hI hne bP
        hbP hconc (fun q hq ↦ hconc j q hq.ne) i (hself i) (by omega))
  rw [forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix S he he₀ hI hne bP hbP hconc r
    hr hneg hS hself]
  simp only [bettiPoincarePowerSeriesMatrix_apply]
  constructor
  · intro hdiag
    rw [← key]
    refine congrArg (Cps * ·) (Matrix.ext fun i j ↦ ?_)
    rw [Matrix.map_apply, Matrix.of_apply, bettiPoincarePowerSeriesMatrix_apply]
    exact ((hiff i j _).2 (hdiag i j)).symm
  · intro hid i j
    -- Both matrices are right inverses of `Cps`, hence equal.
    have heq := left_inv_eq_right_inv (mul_eq_one_comm.mp key) hid
    have hij := congrFun (congrFun heq i) j
    rw [Matrix.map_apply, Matrix.of_apply, bettiPoincarePowerSeriesMatrix_apply] at hij
    exact (hiff i j _).1 hij

include hbP in
/-- **The one-variable Cartan–Poincaré identity for linear resolutions.** Over a finite-dimensional
nonnegatively graded algebra, if every member of an exhaustive degree-zero simple family `Sᵢ` has a
chosen linear graded projective resolution `rᵢ` by finitely generated terms, possibly infinite,
then `C(q) · P(-q) = I`, where `P(q) = B(q, 1)` is the Betti Poincaré matrix at `t = 1`, its
entries read as power series in `q`. For linear resolutions this is the specialisation `q = 1`,
`t ↦ -t` (`TauCeti.Bigraded.maslovEulerPowerSeries`), read in the homological degree. -/
theorem gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_bettiPoincarePowerSeriesMatrix_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        (fun p ↦ (p.trunc : PowerSeries ℤ)) *
      (bettiPoincarePowerSeriesMatrix r bP).map Bigraded.maslovEulerPowerSeries = 1 :=
  (forall_isLinear_iff_cartan_betti_maslovEulerPowerSeries S he he₀ hI hne hself hS bP hbP r
    (fun i ↦ (hr i).isMinimal hneg) hneg hconc).mp hr

end CartanBetti

end TauCeti
