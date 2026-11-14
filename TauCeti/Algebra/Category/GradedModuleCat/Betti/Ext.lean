/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Ext.EulerAdmissible
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries

/-!
# Comparison of graded Betti Poincaré series with bigraded Ext Poincaré series

Let `A` be a finite-dimensional graded algebra over a field `k`, `bP` a basis of `K₀^gr(proj A)`
given by degree-zero idempotent projectives `[A eᵢ]`, and `Sᵢ` finite graded modules concentrated in
degree `0` with `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`. By projective/simple duality
(`TauCeti.coeff_smulGradedDimension_mul_repr`) and `r.extLinearEquiv`, for any **minimal** graded
projective resolution `r` of `M` with finitely generated terms:

1. `PowerSeries.C (gdim(eᵢ • Sᵢ)) * r.bettiPoincareSeries bP i` equals
   `bigradedExtPoincarePowerSeries M Sᵢ` over arbitrary (possibly non-splitting) fields; when
   `gdim(eᵢ • Sᵢ) = 1` for all `i`, `bettiPoincareMatrix bP r` is the transpose of
   `bigradedExtPoincarePowerSeriesMatrix S`.
2. Whenever `gdim(eᵢ • Sᵢ) ≠ 0`, Betti coefficients are nonnegative, minimal Betti series are
   lower-triangular (`Bigraded.HasEulerPowerSeries` when `M` is nonnegatively graded), and
   **linearity of minimal resolutions is equivalent to diagonal Betti support**.

## Main results

* `TauCeti.coeff_repr_laurentK0_nonneg` and
  `TauCeti.GradedProjectiveResolution.coeff_coeff_bettiPoincareSeries_nonneg`: nonnegativity of
  projective coordinates and graded Betti coefficients.
* `TauCeti.GradedProjectiveResolution.IsMinimal.C_smulGradedDimension_mul_bettiPoincareSeries`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_extPoincarePowerSeries`,
  and `TauCeti.bettiPoincareMatrix_eq_transpose_bigradedExtPoincarePowerSeriesMatrix`: Betti–Ext
  Poincaré series and matrix comparison.
* `TauCeti.GradedProjectiveResolution.IsMinimal.hasEulerPowerSeries_bettiPoincareSeries` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.C_finrank_mul_eulerPowerSeries_bettiPoincareSeries`:
  Euler formal power-series specialization at `t = -1`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_diagonal_bettiPoincareSeries`,
  `TauCeti.forall_isLinear_iff_diagonal_bettiPoincareMatrix`, and
  `TauCeti.forall_exists_isLinear_iff_diagonal_bettiPoincareMatrix`: diagonal Betti criterion for
  linear resolutions over arbitrary fields.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)] {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include he₀ hne hbP in
/-- Every finite graded projective has nonnegative Laurent coefficients along `[A eᵢ]` whenever
`gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem coeff_repr_laurentK0_nonneg (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    {i : I} (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (d : ℤ) :
    0 ≤ (bP.repr (LaurentK0.of.{uA} _ P) i).coeff d := by
  have hpos : (0 : ℤ) < Module.finrank k ↥(e i • (S i).obj.grading.piece 0) :=
    Int.natCast_pos.mpr ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc hself)
  have hmul := coeff_smulGradedDimension_mul_repr S he he₀ hI hne bP hbP P hconc d
  rw [(S i).obj.smulGradedDimension_eq_C_of_concentrated (e i) hconc, coeff_C_mul] at hmul
  exact nonneg_of_mul_nonneg_right (hmul.symm ▸ Int.natCast_nonneg _) hpos

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜} {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}

include he₀ hne hbP in
/-- Every Betti coefficient of `r` along `i` is nonnegative whenever `gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem coeff_coeff_bettiPoincareSeries_nonneg [∀ n, Module.Finite A (r.X n)] {i : I}
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (n : ℕ) (d : ℤ) :
    0 ≤ (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d := by
  rw [coeff_bettiPoincareSeries]
  exact coeff_repr_laurentK0_nonneg S he he₀ hI hne bP hbP (r.finiteProjectiveTerm n)
    hself hconc d

include he₀ hne hbP in
/-- Multiplying the `(n, d)` Betti coefficient of a minimal resolution `r` by `dim_k(eᵢ • (Sᵢ)₀)`
recovers `dim_k Extⁿ_gr(M, Sᵢ)_d`. -/
theorem IsMinimal.finrank_mul_coeff_coeff_bettiPoincareSeries
    [∀ m, Module.Finite A (r.X m)] (hr : r.IsMinimal) {i : I}
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (n : ℕ) (d : ℤ) :
    (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d =
      (Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) : ℤ) := by
  have hmul := coeff_smulGradedDimension_mul_repr S he he₀ hI hne bP hbP
    (r.finiteProjectiveTerm n) hconc d
  rw [(S i).obj.smulGradedDimension_eq_C_of_concentrated (e i) hconc, coeff_C_mul,
    finiteProjectiveTerm_obj, ← coeff_bettiPoincareSeries] at hmul
  have hshift : ∀ q, q ≠ d → ((S i).obj.shiftObj d).grading.piece q = ⊥ := fun q hqd ↦ by
    simpa [sub_eq_add_neg] using hconc (q - d) (sub_ne_zero.mpr hqd)
  have hann := ((S i).obj.shiftObj d).positive_smul_top_eq_bot_of_concentrated d hshift
  exact hmul.trans <| congrArg Nat.cast ((hr.extLinearEquiv hann n).trans
    (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 d).app (S i).obj).symm n)).finrank_eq

include he₀ hne hbP in
/-- **Comparison of graded Betti and bigraded Ext Poincaré formal power series.** Multiplying
`r.bettiPoincareSeries bP i` by `gdim(eᵢ • Sᵢ)` yields `bigradedExtPoincarePowerSeries M Sᵢ`, with
no splitting or cohomological boundedness hypothesis. -/
theorem IsMinimal.C_smulGradedDimension_mul_bettiPoincareSeries
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) {i : I}
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      have := r.finite
      GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite M (S i).obj) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * r.bettiPoincareSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h :=
  PowerSeries.ext fun n ↦ LaurentPolynomial.ext fun d ↦ by
    rw [PowerSeries.coeff_C_mul, (S i).obj.smulGradedDimension_eq_C_of_concentrated (e i) hconc,
      coeff_C_mul, coeff_coeff_bigradedExtPoincarePowerSeries]
    exact hr.finrank_mul_coeff_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hconc n d

include he₀ hne hbP in
/-- When `gdim(eᵢ • Sᵢ) = 1`, `r.bettiPoincareSeries bP i` equals the bigraded Ext Poincaré power
series of `(M, Sᵢ)`. -/
theorem IsMinimal.bettiPoincareSeries_eq_extPoincarePowerSeries
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) {i : I}
    (hself : (S i).obj.smulGradedDimension (e i) = 1)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      have := r.finite
      GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite M (S i).obj) :
    r.bettiPoincareSeries bP i = bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  simpa only [hself, map_one, one_mul] using
    hr.C_smulGradedDimension_mul_bettiPoincareSeries S he he₀ hI hne bP hbP hconc h

include he₀ hne hbP in
/-- **Lower-triangularity of minimal Betti Poincaré series.** If `M` vanishes below degree `c`, then
`r.bettiPoincareSeries bP i` vanishes strictly below `d = c + n` whenever `gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem IsMinimal.coeff_coeff_bettiPoincareSeries_eq_zero_of_lt
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) {i : I}
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    {n : ℕ} {d : ℤ} (hdn : d < c + n) :
    (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 := by
  let _ (m : ℕ) : Module.Finite k (r.X m) := Module.Finite.trans A (r.X m)
  let _ := hr.subsingleton_gradedExt_of_lt hM hconc hdn
  have hne0 : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc hself).ne'
  rw [← mul_eq_zero_iff_left hne0,
    hr.finrank_mul_coeff_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hconc n d,
    Module.finrank_zero_of_subsingleton, Nat.cast_zero]

include he₀ hne hbP in
/-- Every minimal resolution `r` of a nonnegatively graded module `M` with finitely generated terms
has a well-defined Euler formal power series `B_i(M; q, -1)` whenever `gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincareSeries
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) {i : I}
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) (hM : ∀ p < 0, M.grading.piece p = ⊥)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    Bigraded.HasEulerPowerSeries (r.bettiPoincareSeries bP i) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun n d hdn ↦
    hr.coeff_coeff_bettiPoincareSeries_eq_zero_of_lt S he he₀ hI hne bP hbP hself hM hconc
      (by simpa using hdn)

include he₀ hne hbP in
/-- Evaluating `t = -1` (`Bigraded.eulerPowerSeries`) commutes with the division-endomorphism factor
`dim_k(eᵢ • (Sᵢ)₀)` relating `r.bettiPoincareSeries` and `bigradedExtPoincarePowerSeries`. -/
theorem IsMinimal.C_finrank_mul_eulerPowerSeries_bettiPoincareSeries
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) {i : I}
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) (hM : ∀ p < 0, M.grading.piece p = ⊥)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : Bigraded.HasEulerPowerSeries (r.bettiPoincareSeries bP i))
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      have := r.finite
      GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite M (S i).obj) :
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        Bigraded.eulerPowerSeries hB =
      Bigraded.eulerPowerSeries
        (have _ (m : ℕ) : Module.Finite k (r.X m) := Module.Finite.trans A (r.X m)
        hr.hasEulerPowerSeries_bigradedExtPoincarePowerSeries hM hconc h) := by
  let _ (m : ℕ) : Module.Finite k (r.X m) := Module.Finite.trans A (r.X m)
  refine PowerSeries.ext fun a ↦ ?_
  rw [PowerSeries.coeff_C_mul,
    Bigraded.coeff_eulerPowerSeries_of_lowerTriangular hB (fun n d hdn ↦
      hr.coeff_coeff_bettiPoincareSeries_eq_zero_of_lt S he he₀ hI hne bP hbP hself hM hconc
        (by simpa using hdn)) a,
    Bigraded.coeff_eulerPowerSeries_of_lowerTriangular
      (hr.hasEulerPowerSeries_bigradedExtPoincarePowerSeries hM hconc h)
      (fun n d hdn ↦ hr.coeff_coeff_bigradedExtPoincarePowerSeries_eq_zero_of_lt hM hconc h
        (by simpa using hdn)) a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [coeff_coeff_bigradedExtPoincarePowerSeries,
    ← hr.finrank_mul_coeff_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hconc n a]
  ring

include he₀ hne hbP in
/-- **Diagonal Betti support characterizes linear resolutions** for minimal resolutions over a
finite-dimensional nonnegatively graded algebra. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincareSeries
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    r.IsLinear ↔ ∀ (i : I) (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
      (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 := by
  let _ (m : ℕ) : Module.Finite k (r.X m) := Module.Finite.trans A (r.X m)
  have := r.finite
  have hcell (i : I) (n : ℕ) (d : ℤ) :
      (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 ↔
        Subsingleton (Ext.{uA} M ((S i).obj.shiftObj d) n) := by
    let h := GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite M (S i).obj
    have hne0 : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 :=
      Int.natCast_ne_zero.mpr
        ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i)).ne'
    let _ := (h.finiteLaurentSupport n).finiteDimensional d
    rw [← mul_eq_zero_iff_left hne0,
      hr.finrank_mul_coeff_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP (hconc i) n d,
      Nat.cast_eq_zero, Module.finrank_zero_iff]
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 d).app (S i).obj) n).toEquiv.subsingleton_congr
  refine ⟨fun hlin i n d hnd ↦
    (hcell i n d).mpr (hlin.subsingleton_ext_shiftObj_of_ne (hconc i) n d hnd), fun hdiag ↦ ?_⟩
  refine (hr.isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    fun N hNfinite hNsimple hNzero n d hnd ↦ ?_
  let _ : Module.Finite k N := hNfinite
  let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  obtain ⟨i, ⟨eN : N ≅ (S i).obj⟩⟩ := hS.exists_iso_of_concentrated S hconc
    ⟨N, gradedFiniteModules_iff.2 inferInstance⟩ hNsimple hNzero
  have hSi : Subsingleton (Ext.{uA} M ((S i).obj.shiftObj d) n) :=
    (hcell i n d).mp (hdiag i n d hnd)
  rw [← GradedModuleCat.shiftFunctor_obj] at hSi ⊢
  exact (extLinearEquivOfIso k (Iso.refl M)
    ((GradedModuleCat.shiftFunctor (𝒜 := 𝒜) d).mapIso eN) n).injective.subsingleton

end GradedProjectiveResolution

include he₀ hne hbP in
/-- **Transpose comparison of Betti and bigraded Ext Poincaré matrices** when
`gdim(eᵢ • Sᵢ) = 1`. -/
theorem bettiPoincareMatrix_eq_transpose_bigradedExtPoincarePowerSeriesMatrix
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
      fun i j ↦ GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj) :
    bettiPoincareMatrix bP r =
      (bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj) h)ᵀ :=
  Matrix.ext fun i j ↦ by
    rw [bettiPoincareMatrix_apply, Matrix.transpose_apply,
      bigradedExtPoincarePowerSeriesMatrix_apply]
    exact (hr j).bettiPoincareSeries_eq_extPoincarePowerSeries S he he₀ hI hne bP hbP (hself i)
      (hconc i) (h j i)

include he₀ hne hbP in
/-- **Diagonal Betti matrix characterizes simultaneous linearity** of minimal resolutions of `S`. -/
theorem forall_isLinear_iff_diagonal_bettiPoincareMatrix
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    (∀ j, (r j).IsLinear) ↔ ∀ i j (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
      (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff d = 0 := by
  simp only [fun j ↦ (hr j).isLinear_iff_diagonal_bettiPoincareSeries S he he₀ hI hne bP hbP
    hself hS hconc hneg, bettiPoincareMatrix_apply]
  exact ⟨fun h i j ↦ h j i, fun h j i ↦ h i j⟩

include he₀ hne hbP in
/-- Every member of `S` admits a linear graded projective resolution iff `bettiPoincareMatrix bP r`
is diagonally supported. -/
theorem forall_exists_isLinear_iff_diagonal_bettiPoincareMatrix
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    (∀ j, ∃ r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading, r'.IsLinear) ↔
      ∀ i j (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff d = 0 := by
  let _ (j : I) (m : ℕ) : Module.Finite k ((r j).X m) := Module.Finite.trans A ((r j).X m)
  rw [← forall_isLinear_iff_diagonal_bettiPoincareMatrix S he he₀ hI hne bP hbP r hr hself hS
    hconc hneg]
  refine ⟨fun hlin j ↦ (hr j).isLinear_iff_subsingleton_ext_shiftObj_simple hneg |>.2
    fun N _ _ hNzero n d hnd ↦ ?_, fun hlin j ↦ ⟨r j, hlin j⟩⟩
  obtain ⟨r', hr'⟩ := hlin j
  exact hr'.subsingleton_ext_shiftObj_of_ne hNzero n d hnd

end TauCeti
