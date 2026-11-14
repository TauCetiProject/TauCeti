/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BettiPoincare.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Concentrated
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries

/-!
# Ext comparison and diagonal-support linearity for Betti Poincaré series

Let `A` be a finite-dimensional graded `k`-algebra with degree-zero idempotents `eᵢ`, projective
basis `bP` with `bP i = [A eᵢ]`, and degree-zero targets `Sᵢ` whose off-diagonal idempotent graded
dimensions vanish (`gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`).

For any finite graded projective `P`, pairing `[P]` against `[Sᵢ]` via the q-Euler form and
conjugating by `LaurentPolynomial.invert` identifies every internal coefficient of the `i`th
projective coordinate of `[P]` (weighted by `dᵢ = gdim(eᵢ • Sᵢ)`) with the dimension of graded Hom
`P ⟶ Sᵢ{d}` (`TauCeti.coeff_smulGradedDimension_mul_repr_projective_of`).

When `r` is a minimal graded projective resolution of `M`, positive-degree scalars annihilate every
shift `Sᵢ{d}`, so `r.termObj n ⟶ Sᵢ{d}` computes `Extⁿ(M, Sᵢ{d})`. Assembling all homological and
internal degrees yields the power-series identity

```text
dᵢ · B_i(M; q, t) = P_Ext(M, Sᵢ; q, t)
```

(`TauCeti.GradedProjectiveResolution.IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries`),
where `dᵢ = gdim(eᵢ • Sᵢ)` is the constant endomorphism/idempotent multiplicity factor over a
general field. In the normalized (splitting-field) case `dᵢ = 1`, the Betti Poincaré matrix of
minimal resolutions of `Sⱼ` is the transpose of the bigraded Ext Poincaré matrix:

```text
B(q, t) = P_Ext(q, t)ᵀ.
```

Because each nonzero constant `dᵢ` is a non-zero-divisor in `ℤ`, diagonal support `(n : ℤ) ≠ d →
coeff = 0` of the Betti Poincaré series (or of the Betti Poincaré matrix of an exhaustive simple
family) is equivalent to linearity of the resolution over *every* field `k`, with no splitting
assumption.

## Main results

* `TauCeti.coeff_smulGradedDimension_mul_repr_projective_of`: weighted projective coordinates of
  any finite graded projective equal graded Hom dimensions into shifted degree-zero targets.
* `TauCeti.GradedProjectiveResolution.IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries`:
  `C(gdim(eᵢ • Sᵢ)) * B_i(M; q, t) = P_Ext(M, Sᵢ; q, t)` for any minimal resolution `r`.
* `TauCeti.bettiPoincarePowerSeriesMatrix_eq_transpose_bigradedExtPoincarePowerSeriesMatrix`:
  in normalized bases (`gdim(eᵢ • Sᵢ) = 1`), `B(q, t) = P_Ext(q, t)ᵀ`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries`,
  `TauCeti.forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix`, and
  `TauCeti.forall_exists_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix`: diagonal-support
  characterizations of linear resolutions via the Betti Poincaré series over an arbitrary field.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for bigraded Ext, minimal resolutions, and diagonal-support linearity.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the
  nonsplitting-field factor `gdim(eᵢ • Sᵢ)` in projective/simple pairings.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [Module.Finite k A] [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
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

include he he₀ hI hne hbP in
/-- **Weighted projective coordinates via graded Hom.** For any finite graded projective `P` and
degree-zero target family `S`, the `d`th Laurent coefficient of `gdim(eᵢ • Sᵢ) · coord_i([P])` is
`dim_k Hom(P, Sᵢ{d})`. Neither generation in a single degree nor nonnegative grading is needed. -/
theorem coeff_smulGradedDimension_mul_repr_projective_of
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (i : I) (d : ℤ) :
    ((S i).obj.smulGradedDimension (e i) * bP.repr (LaurentK0.of.{uA} _ P) i).coeff d =
      Module.finrank k (P.obj ⟶ (S i).obj.shiftObj d) := by
  let _ : Module.Projective A P.obj := (gradedFiniteProjectiveModules_iff.mp P.property).2
  have hpair := gradedProjectiveExtEuler_simple_eq_mul_invert_repr
    S he he₀ hI hne bP hbP (LaurentK0.of.{uA} _ P) i
  rw [gradedProjectiveExtEuler_of_of] at hpair
  have hinv := congrArg (LaurentPolynomial.invert (R := ℤ)) hpair
  have hfixed : invert ((S i).obj.smulGradedDimension (e i)) =
      (S i).obj.smulGradedDimension (e i) := by
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i), invert_C]
  simp only [map_mul, hfixed,
    involutive_invert (R := ℤ) (bP.repr (LaurentK0.of.{uA} _ P) i)] at hinv
  rw [← hinv, invert_apply, gradedExtEuler_projective, coeff_targetShiftGradedDimension,
    neg_neg, (GradedModuleCat.homShiftPowEquiv 𝒜 P.obj (S i).obj d).finrank_eq]

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r.X n)]

omit [GradedAlgebra 𝒜] [Module.Finite k A] [HasExt (GradedModuleCat 𝒜)] in
/-- Positive-degree scalars annihilate every internal shift of a degree-zero concentrated graded
module. -/
private theorem positive_smul_top_shiftObj_eq_bot {N : GradedModuleCat.{uA} 𝒜}
    (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (d : ℤ) :
    (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (N.shiftObj d)) = ⊥ :=
  GradedModuleCat.positive_smul_top_eq_bot_of_concentrated (N.shiftObj d) d fun q hq ↦ by
    rw [InternalGrading.shift_piece]
    exact hN (q - d) (sub_ne_zero.mpr hq)

include he he₀ hI hne hbP in
/-- **Weighted Betti coefficients equal bigraded Ext dimensions.** For a minimal resolution `r`
with finitely generated terms, multiplying the `i`th Betti coordinate in bidegree `(n, d)` by
`gdim(eᵢ • Sᵢ)` gives `dim_k Extⁿ(M, Sᵢ{d})`. -/
theorem IsMinimal.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries
    (hr : r.IsMinimal) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (i : I) (n : ℕ) (d : ℤ) :
    ((S i).obj.smulGradedDimension (e i) *
        PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d =
      Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) := by
  rw [coeff_bettiPoincarePowerSeries,
    coeff_smulGradedDimension_mul_repr_projective_of S he he₀ hI hne bP hbP
      (r.finiteProjectiveTerm n) hconc i d,
    finiteProjectiveTerm_obj]
  have hbot := positive_smul_top_shiftObj_eq_bot (𝒜 := 𝒜) (hconc i) d
  have eExt : (r.termObj n ⟶ (S i).obj.shiftObj d) ≃ₗ[k]
      GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d :=
    (hr.extLinearEquiv hbot n).trans <|
      extLinearEquivOfIso k (Iso.refl M) ((GradedModuleCat.shiftPowIso 𝒜 d).app (S i).obj).symm n
  exact congrArg Nat.cast eExt.finrank_eq

include he he₀ hI hne hbP in
/-- **Weighted Betti–Ext Poincaré series identity.** Over any field `k`, multiplying the `i`th
Betti Poincaré power series of a minimal resolution `r` of `M` by the constant `gdim(eᵢ • Sᵢ)`
produces the bigraded Ext Poincaré power series of `(M, Sᵢ)`. -/
theorem IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries
    (hr : r.IsMinimal) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    {i : I} (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  ext n d
  rw [PowerSeries.coeff_C_mul,
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc
      i n d,
    coeff_coeff_bigradedExtPoincarePowerSeries]

include he he₀ hI hne hbP in
/-- **Normalized Betti–Ext Poincaré series identity.** When `gdim(eᵢ • Sᵢ) = 1` (for instance over
a splitting field), the `i`th Betti Poincaré series of a minimal resolution of `M` equals the
bigraded Ext Poincaré series of `(M, Sᵢ)`. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries
    (hr : r.IsMinimal) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    {i : I} (hself : (S i).obj.smulGradedDimension (e i) = 1)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  simpa only [hself, map_one, one_mul] using
    hr.C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc h

include he he₀ hI hne hbP in
/-- When `gdim(eᵢ • Sᵢ) ≠ 0`, a bidegree coefficient of `r.bettiPoincarePowerSeries bP i` vanishes
if and only if the corresponding bidegree coefficient of `bigradedExtPoincarePowerSeries` vanishes.
No splitting-field hypothesis is needed. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff
    (hr : r.IsMinimal) (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    {i : I} (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj)
    (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0 ↔
      (PowerSeries.coeff n
        (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h)).coeff d = 0 := by
  have hid := congrArg (fun f ↦ (PowerSeries.coeff n f).coeff d)
    (hr.C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc h)
  rw [PowerSeries.coeff_C_mul,
    GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i),
    C_eq_algebraMap, ← Algebra.smul_def, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hid
  have hpos := GradedModuleCat.finrank_smul_piece_zero_pos_of_concentrated (e i) (S i).obj
    (hconc i) hself
  have hcz := (Nat.cast_ne_zero (R := ℤ)).mpr hpos.ne'
  rw [← hid, mul_eq_zero]
  exact ⟨fun h0 ↦ Or.inr h0, fun h0 ↦ h0.resolve_left hcz⟩

include he he₀ hI hne hbP in
/-- **Diagonal-support linearity criterion for the Betti Poincaré series.** Over a
finite-dimensional nonnegatively graded algebra over an arbitrary field `k`, a finite-term minimal
resolution `r` of `M` is linear if and only if its Betti Poincaré series is supported on the
diagonal `d = n` in every coordinate of an exhaustive degree-zero simple family with
`gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries
    (hr : r.IsMinimal) (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) :
    r.IsLinear ↔
      ∀ i (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff d = 0 := by
  let _ (n : ℕ) : Module.Finite k (r.X n) := Module.Finite.trans A (r.X n)
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have hM : Module.Finite A M := Module.Finite.of_surjective r.π r.surjective_π
  have hfin (N : GradedModuleCat.{uA} 𝒜) (hNk : Module.Finite k N) :
      IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M N := by
    let _ : Module.Finite k N := hNk
    let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    exact GradedModuleCat.isGradedExtInternallyFinite_of_finite M N
  constructor
  · intro hlin i n d hnd
    have hSi : Module.Finite k (S i).obj := inferInstance
    rw [hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff S he he₀ hI hne bP hbP hconc
      (hself i) (hfin (S i).obj hSi) n d, coeff_coeff_bigradedExtPoincarePowerSeries]
    have hshift : Subsingleton (Ext.{uA} M ((S i).obj.shiftObj d) n) :=
      hlin.subsingleton_ext_shiftObj_of_ne (hconc i) n d hnd
    rw [← GradedModuleCat.shiftFunctor_obj] at hshift
    have : Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) :=
      (extLinearEquivOfIso k (Iso.refl M)
        ((GradedModuleCat.shiftPowIso 𝒜 d).app (S i).obj) n).injective.subsingleton
    exact_mod_cast Module.finrank_zero_of_subsingleton
  · intro hdiag
    rw [hr.isLinear_iff_diagonal_bigradedExtPoincarePowerSeries hneg
      (fun N hNk _ _ ↦ hfin N hNk)]
    intro N hNk hNsimple hNzero n d hnd
    let _ : Module.Finite k N := hNk
    let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    let N' : (gradedFiniteModules 𝒜).FullSubcategory :=
      ⟨N, gradedFiniteModules_iff.2 inferInstance⟩
    obtain ⟨i, ⟨eN : N'.obj ≅ (S i).obj⟩⟩ :=
      hS.exists_iso_of_concentrated S hconc N' hNsimple hNzero
    have hSi : Module.Finite k (S i).obj := inferInstance
    have hzero_i : (PowerSeries.coeff n
        (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜)
          (hfin (S i).obj hSi))).coeff d = 0 :=
      (hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff S he he₀ hI hne bP hbP hconc
        (hself i) (hfin (S i).obj hSi) n d).mp (hdiag i n d hnd)
    have hsub_i : Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) := by
      let _ := ((hfin (S i).obj hSi).finiteLaurentSupport n).finiteDimensional d
      rw [← Module.finrank_zero_iff (R := k)]
      exact_mod_cast (by simpa using hzero_i :
        (Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) : ℤ) = 0)
    have hsub_N : Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M N n d) :=
      (extLinearEquivOfIso k (Iso.refl M)
        (((GradedModuleCat.shift 𝒜) ^ d).functor.mapIso eN) n).injective.subsingleton
    rw [coeff_coeff_bigradedExtPoincarePowerSeries]
    exact_mod_cast Module.finrank_zero_of_subsingleton

end GradedProjectiveResolution

/-! ### Matrix transpose comparison and family linearity criteria -/

include he he₀ hI hne hbP in
/-- **Weighted matrix comparison between the Betti and Ext Poincaré matrices.** Multiplying on the
left by the diagonal matrix of constants `gdim(eᵢ • Sᵢ)` sends the Betti Poincaré matrix of minimal
resolutions of `Sⱼ` to the transpose of the bigraded Ext Poincaré matrix. -/
theorem diagonal_smulGradedDimension_mul_bettiPoincarePowerSeriesMatrix [Fintype I] [DecidableEq I]
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜)
      (S i).obj (S j).obj)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal) :
    Matrix.diagonal (fun i ↦ PowerSeries.C ((S i).obj.smulGradedDimension (e i))) *
        bettiPoincarePowerSeriesMatrix bP (fun j ↦ (S j).obj) r =
      (bigradedExtPoincarePowerSeriesMatrix (fun j ↦ (S j).obj) h)ᵀ := by
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.diagonal_mul, bettiPoincarePowerSeriesMatrix_apply, Matrix.transpose_apply,
    bigradedExtPoincarePowerSeriesMatrix_apply]
  exact (hr j).C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc
    (h j i)

include he he₀ hI hne hbP in
/-- **Normalized Betti–Ext matrix transpose identity (`B(q, t) = P_Ext(q, t)ᵀ`).** When
`gdim(eᵢ • Sᵢ) = 1` for every `i`, the Betti Poincaré matrix of minimal resolutions of `S` equals
the transpose of the bigraded Ext Poincaré matrix of `S`. -/
theorem bettiPoincarePowerSeriesMatrix_eq_transpose_bigradedExtPoincarePowerSeriesMatrix
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜)
      (S i).obj (S j).obj)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal) :
    bettiPoincarePowerSeriesMatrix bP (fun j ↦ (S j).obj) r =
      (bigradedExtPoincarePowerSeriesMatrix (fun j ↦ (S j).obj) h)ᵀ := by
  refine Matrix.ext fun i j ↦ ?_
  rw [bettiPoincarePowerSeriesMatrix_apply, Matrix.transpose_apply,
    bigradedExtPoincarePowerSeriesMatrix_apply]
  exact (hr j).bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries
    S he he₀ hI hne bP hbP hconc (hself i) (h j i)

include he he₀ hI hne hbP in
/-- **Chosen minimal resolutions of an exhaustive simple family are all linear if and only if the
Betti Poincaré matrix is supported on the diagonal `d = n`.** Valid over any field `k` as long as
`gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    (∀ j, (r j).IsLinear) ↔
      ∀ i j (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n
          (bettiPoincarePowerSeriesMatrix bP (fun j ↦ (S j).obj) r i j)).coeff d = 0 := by
  simp only [bettiPoincarePowerSeriesMatrix_apply]
  rw [forall_congr' fun j ↦
    (hr j).isLinear_iff_diagonal_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hneg hS hconc
      hself]
  exact ⟨fun h i j ↦ h j i, fun h j i ↦ h i j⟩

include he he₀ hI hne hbP in
/-- **Existence of linear resolutions for an exhaustive simple family is equivalent to diagonal
support of any minimal Betti Poincaré matrix.** Over a finite-dimensional nonnegatively graded
algebra, any family of finite-term minimal resolutions `r` of `S` tests whether all members of `S`
admit linear resolutions. -/
theorem forall_exists_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    (∀ j, ∃ r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading,
      r'.IsLinear) ↔
      ∀ i j (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
        (PowerSeries.coeff n
          (bettiPoincarePowerSeriesMatrix bP (fun j ↦ (S j).obj) r i j)).coeff d = 0 := by
  rw [← forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix S he he₀ hI hne bP hbP hS
    hconc hself r hr hneg]
  refine forall_congr' fun j ↦ ⟨fun ⟨r', hr'⟩ ↦ ?_, fun hj ↦ ⟨r j, hj⟩⟩
  let _ (n : ℕ) : Module.Finite k ((r j).X n) := Module.Finite.trans A ((r j).X n)
  apply ((hr j).isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
  intro N _ _ hNzero n p hnp
  exact hr'.subsingleton_ext_shiftObj_of_ne hNzero n p hnp

end TauCeti
