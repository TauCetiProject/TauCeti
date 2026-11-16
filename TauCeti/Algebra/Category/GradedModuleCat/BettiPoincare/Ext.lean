/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Ext.EulerAdmissible
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates

/-!
# Comparison of Betti Poincaré series with bigraded Ext and linearity criteria

Let `A` be a graded algebra over a field `k` (possibly infinite-dimensional over `k`), let `bP` be
a basis of `K₀^gr(proj A)` represented by degree-zero idempotent projectives `[A eᵢ]`, and let `Sᵢ`
be finite-dimensional degree-zero graded targets with `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`.

For **any** minimal graded projective resolution `r` of `M` whose terms are finitely generated over
`A`, pairing `[Pₙ]` against `Sᵢ` via `TauCeti.gradedProjectiveExtEulerTarget_eq_mul_invert_repr`
(the single-target counterpart of `TauCeti.gradedProjectiveExtEuler_simple_eq_mul_invert_repr`) and
computing graded Hom out of `r` via `TauCeti.GradedProjectiveResolution.IsMinimal.extLinearEquiv`
identifies the `i`th Betti Poincaré series with the full unbounded bigraded Ext Poincaré power
series up to the nonsplitting-field factor `gdim(eᵢ • Sᵢ)`:

```text
gdim(eᵢ • Sᵢ) · r.bettiPoincarePowerSeries bP i = bigradedExtPoincarePowerSeries k (shift 𝒜) h.
```

This generalizes the linear-resolution coordinate formula
`TauCeti.GradedProjectiveResolution.IsLinear.smulGradedDimension_mul_repr_finiteProjectiveTerm` to
arbitrary minimal resolutions: neither linearity, finite-dimensionality of `A`, cohomological
boundedness, a nonnegative algebra grading, nor exhaustiveness of the family `S` is needed. When
`gdim(eᵢ • Sᵢ) = 1`, the `i`th Betti Poincaré series equals `bigradedExtPoincarePowerSeries`
directly, and for minimal resolutions `rⱼ` of the `Sⱼ` the transposed Betti Poincaré matrix equals
`bigradedExtPoincarePowerSeriesMatrix`.

When `gdim(eᵢ • Sᵢ) ≠ 0` (which holds over an arbitrary, possibly nonsplitting ground field), every
bidegree coefficient `[qᵖ][tⁿ]` of a minimal resolution's Betti Poincaré series is nonnegative,
vanishes strictly below `p = c + n` when `M` vanishes below `c` and the resolution terms are bounded
below, and defines an Alexander-graded Euler formal power series `Bigraded.eulerPowerSeries` when
`M` is supported in nonnegative internal degrees.

Over a nonnegatively graded algebra whose degree-zero piece `𝒜 0` is finite-dimensional over `k`
(including infinite-dimensional algebras such as `k[x]`), adapting the Ext-diagonal linearity
characterizations
`TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_diagonal_bigradedExtPoincarePowerSeries`,
`TauCeti.forall_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix`, and
`TauCeti.forall_exists_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix` shows that
diagonal support (`[qᵖ][tⁿ] = 0` for `n ≠ p`) of the Betti Poincaré series or matrix characterizes
linearity of minimal resolutions against an exhaustive degree-zero simple family `S`, with no
cohomological global-dimension bound.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.smulGradedDimension_mul_repr_finiteProjectiveTerm`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries`:
  the general minimal-resolution Betti–Ext identity, retaining `gdim(eᵢ • Sᵢ)`.
* `GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries`,
  `TauCeti.bettiPoincarePowerSeriesMatrix_transpose_eq_bigradedExtPoincarePowerSeriesMatrix`:
  the normalized (`gdim(eᵢ • Sᵢ) = 1`) Betti–Ext equality and matrix-transpose law.
* `TauCeti.GradedProjectiveResolution.IsMinimal.coeff_coeff_bettiPoincarePowerSeries_nonneg`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.C_finrank_mul_eulerPowerSeries`:
  positivity, lower-triangular vanishing, and Euler formal-power-series comparison over an arbitrary
  field with `gdim(eᵢ • Sᵢ) ≠ 0`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries`,
  `TauCeti.forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix`, and
  `TauCeti.forall_exists_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix`: diagonal-support
  characterizations of linear resolutions via Betti Poincaré series and matrices when `𝒜 0` is
  finite-dimensional over `k`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the
  division-endomorphism factor `dim_k End_A(Sᵢ)` over a nonsplitting field.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj]
  {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

/-! ### Minimal-resolution Betti–Ext comparison -/

section Comparison

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}

include he₀ hne hbP in
/-- **Bigraded Ext computes the projective coordinates of every minimal resolution term.** For any
minimal graded projective resolution `r` of `M` and finite-dimensional degree-zero targets `Sᵢ`,
multiplying the `i`th projective coordinate of `[Pₙ]` by `gdim(eᵢ • Sᵢ)` recovers the `tⁿ`
coefficient of `bigradedExtPoincarePowerSeries`. Neither linearity, finite-dimensionality of `A`, a
nonnegative algebra grading, nor cohomological boundedness is assumed. -/
theorem IsMinimal.smulGradedDimension_mul_repr_finiteProjectiveTerm (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (n : ℕ)
    [Module.Finite A (r.X n)]
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    (S i).obj.smulGradedDimension (e i) *
        bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm n)) i =
      PowerSeries.coeff n
        (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h) := by
  have hpair := gradedProjectiveExtEulerTarget_eq_mul_invert_repr S he he₀ hI hne bP hbP
    (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n)) i
  rw [gradedProjectiveExtEulerTarget_of, gradedExtEuler_projective] at hpair
  have hinv := congrArg (LaurentPolynomial.invert (R := ℤ)) hpair.symm
  have hfixed : invert ((S i).obj.smulGradedDimension (e i)) =
      (S i).obj.smulGradedDimension (e i) := by
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc, invert_C]
  rw [map_mul, hfixed, involutive_invert (R := ℤ)] at hinv
  rw [hinv]
  ext p
  rw [invert_apply, coeff_targetShiftGradedDimension, neg_neg,
    coeff_coeff_bigradedExtPoincarePowerSeries, r.finiteProjectiveTerm_obj n,
    (GradedModuleCat.homShiftPowEquiv 𝒜 (r.termObj n) (S i).obj p).finrank_eq]
  have hconc_p : ∀ q, q ≠ p → ((S i).obj.shiftObj p).grading.piece q = ⊥ := fun q hq ↦ by
    simpa [sub_eq_add_neg] using hconc (q - p) (sub_ne_zero.mpr hq)
  have hann := ((S i).obj.shiftObj p).positive_smul_top_eq_bot_of_concentrated p hconc_p
  rw [(hr.extLinearEquiv hann n).finrank_eq, ← GradedModuleCat.shiftFunctor_obj,
    ← (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 p).app (S i).obj) n).finrank_eq]

variable [∀ n, Module.Finite A (r.X n)]

include he₀ hne hbP in
/-- **Minimal-resolution Betti–Ext formal power-series identity**: multiplying the `i`th Betti
Poincaré power series of a minimal resolution by `gdim(eᵢ • Sᵢ)` gives the full bigraded Ext
Poincaré power series against `Sᵢ`. -/
theorem IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      hr.isGradedExtInternallyFinite hconc) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_C_mul, coeff_bettiPoincarePowerSeries,
    hr.smulGradedDimension_mul_repr_finiteProjectiveTerm S he he₀ hI hne bP hbP i hconc n h]

include he₀ hne hbP in
/-- Scalar bidegree form of the Betti–Ext comparison: for any minimal resolution `r`,
`dim_k(eᵢ • (Sᵢ)₀) · [qᵖ][tⁿ] (r.bettiPoincarePowerSeries bP i) = dim_k Extⁿ(M, Sᵢ{p})`. -/
theorem IsMinimal.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincarePowerSeries
    (hr : r.IsMinimal) (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (n : ℕ) (p : ℤ) :
    (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p =
      Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n p) := by
  let h := hr.isGradedExtInternallyFinite hconc
  have hcoeff := congrArg (fun f : LaurentPolynomial ℤ ↦ f.coeff p)
    (hr.smulGradedDimension_mul_repr_finiteProjectiveTerm S he he₀ hI hne bP hbP i hconc n h)
  rwa [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc, coeff_C_mul,
    ← coeff_bettiPoincarePowerSeries, coeff_coeff_bigradedExtPoincarePowerSeries] at hcoeff

include he₀ hne hbP in
/-- When `gdim(eᵢ • Sᵢ) = 1`, the `i`th Betti Poincaré series of a minimal resolution equals the
full bigraded Ext Poincaré power series against `Sᵢ`. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) = 1)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      hr.isGradedExtInternallyFinite hconc) :
    r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  simpa only [hself, map_one, one_mul] using
    hr.C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP i hconc h

end GradedProjectiveResolution

include he₀ hne hbP in
/-- **Matrix Betti–Ext comparison**: when `gdim(eᵢ • Sᵢ) = 1` for all `i`, the transpose of the
Betti Poincaré power-series matrix of minimal resolutions `rⱼ` of finite-dimensional `Sⱼ` equals
the full bigraded Ext Poincaré power-series matrix of `S`. -/
theorem bettiPoincarePowerSeriesMatrix_transpose_eq_bigradedExtPoincarePowerSeriesMatrix
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜)
      (S i).obj (S j).obj :=
      fun i j ↦ (hr i).isGradedExtInternallyFinite (hconc j)) :
    (bettiPoincarePowerSeriesMatrix bP r)ᵀ =
      bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj) h :=
  Matrix.ext fun j i ↦ by
    rw [Matrix.transpose_apply, bettiPoincarePowerSeriesMatrix_apply,
      bigradedExtPoincarePowerSeriesMatrix_apply]
    exact (hr j).bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries
      S he he₀ hI hne bP hbP i (hconc i) (hself i) (h j i)

end Comparison

/-! ### Positivity, lower-triangular vanishing, and Euler power series -/

section NeZero

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r.X n)]

include he₀ hne hbP in
/-- Every bidegree coefficient `[qᵖ][tⁿ]` of the Betti Poincaré series of a minimal resolution at
coordinate `i` with `gdim(eᵢ • Sᵢ) ≠ 0` is nonnegative, even over a nonsplitting ground field. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_nonneg (hr : r.IsMinimal)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (n : ℕ) (p : ℤ) :
    0 ≤ (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p := by
  have hpos : (0 : ℤ) < Module.finrank k ↥(e i • (S i).obj.grading.piece 0) :=
    Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc hself)
  have hmul := hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincarePowerSeries
    S he he₀ hI hne bP hbP i hconc n p
  have hnn : (0 : ℤ) ≤
      (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p := by
    rw [hmul]
    exact Int.natCast_nonneg _
  exact nonneg_of_mul_nonneg_right hnn hpos

include he₀ hne hbP in
/-- For a minimal resolution `r` of `M`, the bidegree `(n, p)` Betti coefficient at `i` vanishes if
and only if `GradedExt (shift 𝒜) M (S i).obj n p` is a subsingleton. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff (hr : r.IsMinimal)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (n : ℕ) (p : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p = 0 ↔
      Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n p) := by
  let hfin := hr.isGradedExtInternallyFinite hconc
  let _ := (hfin.finiteLaurentSupport n).finiteDimensional p
  have hd0 : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 :=
    ne_of_gt <| Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc hself)
  have hmul := hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincarePowerSeries
    S he he₀ hI hne bP hbP i hconc n p
  rw [← mul_eq_zero_iff_left hd0, hmul, Nat.cast_eq_zero, Module.finrank_zero_iff]

include he₀ hne hbP in
/-- If `M` vanishes in internal degrees below `c` and the terms of a minimal resolution `r` are
bounded below, the `i`th Betti Poincaré series of `r` vanishes for `p < c + n`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt (hr : r.IsMinimal)
    {c : ℤ} (hM : ∀ q < c, M.grading.piece q = ⊥)
    (hb : ∀ m, ∃ b : ℤ, ∀ q < b, (r.grading m).piece q = ⊥)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    {n : ℕ} {p : ℤ} (hpn : p < c + n) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p = 0 :=
  (hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff
    S he he₀ hI hne bP hbP i hself hconc n p).mpr
      (hr.subsingleton_gradedExt_of_lt_of_bddBelow hM hb hconc hpn)

include he₀ hne hbP in
/-- For a bounded-below minimally resolved module supported in nonnegative internal degrees, the
`i`th Betti Poincaré formal power series satisfies `Bigraded.HasEulerPowerSeries`, with no
cohomological bound. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (hM : ∀ q < 0, M.grading.piece q = ⊥)
    (hb : ∀ m, ∃ b : ℤ, ∀ q < b, (r.grading m).piece q = ⊥)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun _ _ han ↦
    hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt S he he₀ hI hne bP hbP hM hb i hself hconc
      (by omega)

include he₀ hne hbP in
/-- Multiplying the Alexander-graded Euler formal power series of `r.bettiPoincarePowerSeries bP i`
by `dim_k(eᵢ • (Sᵢ)₀)` recovers the Alexander-graded Euler formal power series of
`bigradedExtPoincarePowerSeries`, for any `HasEulerPowerSeries` witnesses. -/
theorem IsMinimal.C_finrank_mul_eulerPowerSeries
    (hr : r.IsMinimal) (hM : ∀ q < 0, M.grading.piece q = ⊥)
    (hb : ∀ m, ∃ b : ℤ, ∀ q < b, (r.grading m).piece q = ⊥)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      hr.isGradedExtInternallyFinite hconc)
    (hB : Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i) :=
      hr.hasEulerPowerSeries_bettiPoincarePowerSeries
        S he he₀ hI hne bP hbP hM hb i hself hconc)
    (hE : Bigraded.HasEulerPowerSeries
        (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h) :=
      hr.hasEulerPowerSeries_bigradedExtPoincarePowerSeries_of_bddBelow hM hb hconc h) :
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        Bigraded.eulerPowerSeries hB =
      Bigraded.eulerPowerSeries hE := by
  ext a
  rw [PowerSeries.coeff_C_mul,
    Bigraded.coeff_eulerPowerSeries_of_lowerTriangular hB
      (fun _ _ han ↦ hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt
        S he he₀ hI hne bP hbP hM hb i hself hconc (by omega)) a,
    Bigraded.coeff_eulerPowerSeries_of_lowerTriangular hE
      (fun _ _ han ↦ hr.coeff_coeff_bigradedExtPoincarePowerSeries_eq_zero_of_lt_of_bddBelow
        hM hb hconc h (by omega)) a,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [mul_left_comm,
    hr.finrank_smul_piece_zero_mul_coeff_coeff_bettiPoincarePowerSeries
      S he he₀ hI hne bP hbP i hconc n (a : ℤ),
    coeff_coeff_bigradedExtPoincarePowerSeries]

include he₀ hne hbP in
/-- For any linear resolution `r` (without assuming minimality, finite-dimensionality of `A`, or a
nonnegative algebra grading), all off-diagonal coefficients of `r.bettiPoincarePowerSeries bP i`
vanish when `gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem IsLinear.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_ne (hr : r.IsLinear)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (n : ℕ) (p : ℤ) (hnp : (n : ℤ) ≠ p) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p = 0 := by
  have hd0 : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 :=
    ne_of_gt <| Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc hself)
  have hmul := congrArg (fun f : LaurentPolynomial ℤ ↦ f.coeff p)
    (hr.smulGradedDimension_mul_repr_finiteProjectiveTerm S he he₀ hI hne bP hbP i hconc n)
  rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc, coeff_C_mul,
    ← coeff_bettiPoincarePowerSeries, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, ite_eq_right hnp] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hd0

end GradedProjectiveResolution

end NeZero

/-! ### Diagonal-support characterizations of linear resolutions -/

section Linearity

variable [Module.Finite k (𝒜 0)]
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r.X n)]

include he₀ hne hself hS hbP in
/-- **A minimal resolution is linear if and only if its Betti Poincaré series are diagonally
supported.** Over a nonnegatively graded algebra with finite-dimensional degree-zero part `𝒜 0`, an
exhaustive degree-zero simple family `S`, and `gdim(eᵢ • Sᵢ) ≠ 0`, `r.IsLinear` holds exactly when
`[qᵖ][tⁿ] = 0` for all `n ≠ p` across every projective coordinate `i : I`. Neither
finite-dimensionality of `A` nor a cohomological bound is assumed. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    r.IsLinear ↔ ∀ (i : I) (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p = 0 := by
  constructor
  · exact fun hlin i n p hnp ↦
      hlin.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_ne S he he₀ hI hne bP hbP i
        (hself i) (hconc i) n p hnp
  · intro hdiag
    apply (hr.isLinear_iff_subsingleton_ext_shiftObj_simple_of_moduleFinite hneg).2
    intro N hNfinite hNsimple hNzero n p hnp
    let _ : Module.Finite k N := hNfinite
    let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    let N' : (gradedFiniteModules 𝒜).FullSubcategory :=
      ⟨N, gradedFiniteModules_iff.2 inferInstance⟩
    obtain ⟨i, ⟨eN : N'.obj ≅ (S i).obj⟩⟩ :=
      hS.exists_iso_of_concentrated S hconc N' hNsimple hNzero
    have hExt : Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n p) :=
      (hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff
        S he he₀ hI hne bP hbP i (hself i) (hconc i) n p).mp (hdiag i n p hnp)
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftFunctor (𝒜 := 𝒜) p).mapIso eN ≪≫
        ((GradedModuleCat.shiftPowIso 𝒜 p).app (S i).obj).symm) n).injective.subsingleton

end GradedProjectiveResolution

include he₀ hne hself hS hbP in
/-- **Chosen minimal resolutions of an exhaustive degree-zero simple family are simultaneously
linear if and only if the Betti Poincaré power-series matrix is diagonally supported.** -/
theorem forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ j, (r j).IsLinear) ↔ ∀ i j (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      (PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix bP r i j)).coeff p = 0 := by
  simp only [fun j ↦ (hr j).isLinear_iff_diagonal_bettiPoincarePowerSeries
    S he he₀ hI hne bP hbP hself hS hneg hconc, bettiPoincarePowerSeriesMatrix_apply]
  exact ⟨fun h i j ↦ h j i, fun h j i ↦ h i j⟩

include he₀ hne hself hS hbP in
/-- Given any minimal resolutions `r j` of an exhaustive degree-zero simple family `S` with finitely
generated terms over a nonnegatively graded algebra with `Module.Finite k (𝒜 0)`, every `S j` admits
**some** linear resolution if and only if `bettiPoincarePowerSeriesMatrix bP r` is diagonally
supported. -/
theorem forall_exists_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ j, ∃ r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading, r'.IsLinear) ↔
      ∀ i j (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
        (PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix bP r i j)).coeff p = 0 := by
  rw [← forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    S he he₀ hI hne bP hbP hself hS r hr hneg hconc]
  constructor
  · intro hlin j
    apply ((hr j).isLinear_iff_subsingleton_ext_shiftObj_simple_of_moduleFinite hneg).2
    intro N _ _ hNzero n p hnp
    obtain ⟨r', hr'⟩ := hlin j
    exact hr'.subsingleton_ext_shiftObj_of_ne hNzero n p hnp
  · exact fun hlin j ↦ ⟨r j, hlin j⟩

end Linearity

end TauCeti
