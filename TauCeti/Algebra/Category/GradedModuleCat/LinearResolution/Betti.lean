/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Betti Poincaré series of graded projective resolutions

Let `bP` be a `ℤ[q,q⁻¹]`-basis of the graded projective Grothendieck group, for instance the
classes `[Pᵢ] = [A eᵢ]` of the indecomposable graded projectives. For a graded projective
resolution `P` of `M` by finitely generated terms, the **Betti Poincaré series** of `P` at `i` is

`Bᵢ(q,t) = ∑ₙ coordᵢ([Pₙ]) tⁿ`.

Since `[Pᵢ{d}] = qᵈ [Pᵢ]` (`TauCeti.laurentK0_projective_of_shiftObj`), a decomposition
`Pₙ ≅ ⊕ Pᵢ{d}^{β^n_{i,d}}` gives `Bᵢ(q,t) = ∑_{n,d} β^n_{i,d} qᵈ tⁿ`, which retains both the
homological degree `t` and the internal degree `q`. For resolutions `rⱼ` of a family of modules
`Sⱼ`, the series form the **Betti Poincaré matrix**, with rows `Pᵢ` and columns `Sⱼ`. Each
coefficient is a finite sum, also when the resolution is infinite.

Suppose that degree-zero idempotents `eᵢ` cut out finite targets `Sᵢ` concentrated in degree zero,
with `gdim(eᵢ Sⱼ) = 0` for `i ≠ j`, and write `dᵢ = gdim(eᵢ Sᵢ)`. For a minimal resolution, every
differential vanishes against `Sᵢ{j}`, so `Extⁿ(M, Sᵢ{j}) = Hom(Pₙ, Sᵢ{j})`. Pairing `[Pₙ]`
against `[Sᵢ]` then gives

`dᵢ · Bᵢ(q,t) = ∑_{n,j} dim_k Extⁿ(M, Sᵢ{j}) qʲ tⁿ`,

the bigraded Ext Poincaré power series of `(M,Sᵢ)`. When every `dᵢ` is nonzero, as for the heads
of primitive idempotents where `dᵢ = dim_k End_A(Sᵢ)`, this has three consequences:

* the series does not depend on the choice of minimal resolution;
* the series of `M{1}` is `q` times the series of `M`;
* over a nonnegatively graded algebra, when the `Sᵢ` exhaust the graded simples up to shift, a
  minimal resolution is linear exactly when every entry of its series is supported on the
  diagonal `d = n`.

## Main definitions

* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries`: the Betti Poincaré series of a
  resolution at a projective basis vector.
* `TauCeti.bettiPoincareMatrix`: the Betti Poincaré matrix of a family of resolutions.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.C_mul_bettiPoincareSeries`: for a minimal
  resolution, `dᵢ · Bᵢ` is the bigraded Ext Poincaré power series against `Sᵢ`.
* `TauCeti.diagonal_mul_bettiPoincareMatrix`: the matrix form `diag(d) · B = Eᵀ`, where `E` is the
  bigraded Ext Poincaré matrix of the family.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq`: independence of the
  minimal resolution.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_shiftObj_one`: the shift law
  `B(M{1}) = q · B(M)`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.isLinear_iff_diagonal_bettiPoincareSeries`: the
  diagonal-support criterion for linearity.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for minimal and linear resolutions and their Poincaré series.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the
  division-endomorphism factor `dim_k End_A(Sᵢ)` in projective/simple pairings.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe uk uA uI uJ

section Definitions

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- The **Betti Poincaré series** of a resolution by finitely generated terms at the `i`th basis
class of the graded projective Grothendieck group: the coefficient of `tⁿ` is the `i`th
coordinate of the class of the term `Pₙ`. -/
def bettiPoincareSeries (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦ bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i

/-- The coefficient of `tⁿ` in the Betti Poincaré series is the coordinate of `[Pₙ]`. -/
@[simp]
theorem coeff_bettiPoincareSeries (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincareSeries bP i) =
      bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincareSeries]

end GradedProjectiveResolution

/-- The **Betti Poincaré matrix** of a family of resolutions `rⱼ` of modules `Mⱼ`: rows are
indexed by the projective basis and columns by the family. -/
def bettiPoincareMatrix {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] : Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  Matrix.of fun i j ↦ (r j).bettiPoincareSeries bP i

@[simp]
theorem bettiPoincareMatrix_apply {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) :
    bettiPoincareMatrix bP r i j = (r j).bettiPoincareSeries bP i :=
  (rfl)

end Definitions

section Comparison

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
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
  (hSzero : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

include he₀ hne hbP hSzero in
/-- **Betti numbers are Ext dimensions.** For a minimal resolution, the coefficient of `qʲ tⁿ`
in `dᵢ · Bᵢ` is `dim_k Extⁿ(M, Sᵢ{j})`. Homological degree zero is included. -/
theorem IsMinimal.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) (i : I) (n : ℕ) (j : ℤ) :
    ((S i).obj.smulGradedDimension (e i) * PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff
        j = Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n j) := by
  obtain ⟨j, rfl⟩ : ∃ j' : ℤ, j = -j' := ⟨-j, (neg_neg j).symm⟩
  let P := r.finiteProjectiveTerm n
  let _ : Module.Projective A P.obj := (gradedFiniteProjectiveModules_iff.mp P.property).2
  have hpair := gradedProjectiveExtEuler_simple_eq_mul_invert_repr
    S he he₀ hI hne bP hbP (LaurentK0.of.{uA} _ P) i
  rw [gradedProjectiveExtEuler_of_of, gradedExtEuler_projective] at hpair
  have hcoeff := congrArg (fun f : LaurentPolynomial ℤ ↦ f.coeff j) hpair
  rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hSzero i)] at hcoeff ⊢
  simp only [coeff_targetShiftGradedDimension, coeff_C_mul, invert_apply] at hcoeff
  rw [coeff_C_mul, coeff_bettiPoincareSeries, ← hcoeff, finiteProjectiveTerm_obj]
  have hN : (⨆ (p : ℤ) (_ : 0 < p), 𝒜 p) • (⊤ : Submodule k ((S i).obj.shiftObj (-j))) = ⊥ :=
    GradedModuleCat.positive_smul_top_eq_bot_of_concentrated _ (-j) fun p hp ↦ by
      simpa [sub_eq_add_neg] using hSzero i (p + j) (by omega)
  exact_mod_cast ((GradedModuleCat.homShiftPowEquiv 𝒜 (r.termObj n) (S i).obj (-j)).trans
    ((hr.extLinearEquiv hN n).trans (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 (-j)).app (S i).obj).symm n))).finrank_eq

include he₀ hne hbP hSzero in
/-- **The Betti series computes the Ext Poincaré series.** For a minimal resolution of `M`,
`dᵢ · Bᵢ(q,t)` is the bigraded Ext Poincaré power series of `(M,Sᵢ)`. -/
theorem IsMinimal.C_mul_bettiPoincareSeries
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) (i : I)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * r.bettiPoincareSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  ext n j
  rw [PowerSeries.coeff_C_mul, coeff_coeff_bigradedExtPoincarePowerSeries,
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero]

section NeZero

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)

include he₀ hne hbP hSzero hself in
/-- **Independence of the minimal resolution.** Two minimal resolutions of the same module by
finitely generated terms have the same Betti Poincaré series. -/
theorem IsMinimal.bettiPoincareSeries_eq
    {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    r.bettiPoincareSeries bP i = r'.bettiPoincareSeries bP i := by
  ext n : 1
  apply mul_left_cancel₀ (hself i)
  ext j
  rw [hr.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero,
    hr'.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero]

include he₀ hne hbP hSzero hself in
/-- **The shift law** `B(M{1}) = q · B(M)`, for minimal resolutions of `M` and of `M{1}`. -/
theorem IsMinimal.bettiPoincareSeries_shiftObj_one
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj 1).grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    r'.bettiPoincareSeries bP i = PowerSeries.C (T 1) * r.bettiPoincareSeries bP i := by
  ext n : 1
  apply mul_left_cancel₀ (hself i)
  ext j
  rw [hr'.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero,
    PowerSeries.coeff_C_mul, mul_left_comm, coeff_T_mul,
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero,
    ← GradedModuleCat.shift_functor_obj,
    (gradedExtShiftSourceEquiv k (GradedModuleCat.shift 𝒜) M (S i).obj n j).finrank_eq]

open scoped Pointwise in
include he₀ hne hbP hSzero hself in
/-- **Diagonal support detects linearity.** Over a nonnegatively graded finite-dimensional
algebra, for a family `Sᵢ` concentrated in degree zero that exhausts the graded simples up to
shift, a minimal resolution by finitely generated terms is linear exactly when the coefficient
of `qᵈ tⁿ` in every Betti Poincaré series vanishes for `d ≠ n`. The resolution may be
infinite. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincareSeries
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) (hS : IsExhaustiveGradedSimpleFamily S)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    r.IsLinear ↔ ∀ i (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
      (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 := by
  have hconst (i : I) := GradedModuleCat.smulGradedDimension_eq_C_of_concentrated
    (M := (S i).obj) (e i) (hSzero i)
  have hcoeff (i : I) (n : ℕ) (d : ℤ) := by
    have h := hr.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries
      S he he₀ hI hne bP hbP hSzero i n d
    rw [hconst i, coeff_C_mul] at h
    exact h
  have hc (i : I) : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 := by
    intro h0
    apply hself i
    rw [hconst i, h0, map_zero]
  have hfin (i : I) (n : ℕ) (d : ℤ) :
      FiniteDimensional k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) := by
    let _ : IsNoetherianRing A := IsNoetherianRing.of_finite k A
    let _ : Module.Finite A M := Module.Finite.of_surjective _ r.surjective_π
    exact ((GradedModuleCat.isGradedExtInternallyFinite_of_finite M (S i).obj).finiteLaurentSupport
      n).finiteDimensional d
  constructor
  · intro hlin i n d hnd
    have hsub : Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) :=
      GradedModuleCat.subsingleton_gradedExt_iff_subsingleton_ext_shiftObj.mpr
        (hlin.subsingleton_ext_shiftObj_of_ne (hSzero i) n d hnd)
    have h := hcoeff i n d
    rw [Module.finrank_zero_of_subsingleton
      (M := GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d), Nat.cast_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hc i)
  · intro hdiag
    let _ (n : ℕ) : Module.Finite k (r.X n) := Module.Finite.trans A (r.X n)
    apply (hr.isLinear_iff_subsingleton_ext_shiftObj_simple hneg).mpr
    intro N hNfinite hNsimple hNzero n d hnd
    let _ : Module.Finite k N := hNfinite
    let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    let N' : (gradedFiniteModules 𝒜).FullSubcategory :=
      ⟨N, gradedFiniteModules_iff.2 inferInstance⟩
    obtain ⟨i, ⟨eN : N'.obj ≅ (S i).obj⟩⟩ :=
      hS.exists_iso_of_concentrated S hSzero N' hNsimple hNzero
    have h := (hcoeff i n d).symm
    rw [hdiag i n d hnd, mul_zero, Nat.cast_eq_zero] at h
    let _ := hfin i n d
    have hsub : Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) :=
      Module.finrank_zero_iff.mp h
    have hsub' : Subsingleton (Ext.{uA} M ((S i).obj.shiftObj d) n) :=
      GradedModuleCat.subsingleton_gradedExt_iff_subsingleton_ext_shiftObj.mp hsub
    rw [← GradedModuleCat.shiftFunctor_obj] at hsub'
    exact (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftFunctor (𝒜 := 𝒜) d).mapIso eN) n).injective.subsingleton

end NeZero

end GradedProjectiveResolution

include he₀ hne hbP hSzero in
/-- **Matrix form of the Ext comparison.** For minimal resolutions `rⱼ` of the family members
`Sⱼ`, the Betti Poincaré matrix `B`, scaled on the left by `diag(dᵢ)`, is the transpose of the
bigraded Ext Poincaré matrix of the family. -/
theorem diagonal_mul_bettiPoincareMatrix [Fintype I] [DecidableEq I]
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜)
      (S i).obj (S j).obj) :
    Matrix.diagonal (fun i ↦ PowerSeries.C ((S i).obj.smulGradedDimension (e i))) *
        bettiPoincareMatrix bP r =
      (bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj) h).transpose := by
  ext i j : 1
  rw [Matrix.diagonal_mul, bettiPoincareMatrix_apply, Matrix.transpose_apply,
    bigradedExtPoincarePowerSeriesMatrix_apply,
    (hr j).C_mul_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero i (h j i)]

end Comparison

end TauCeti
