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

The comparison with Ext takes `A` to be a finite-dimensional graded algebra over a field `k`, as
for the projective/module q-Euler pairing it uses, and `bP` to be the basis `bP i = [A eᵢ]` of
degree-zero idempotents `eᵢ`. Suppose that the `eᵢ` cut out finite targets `Sᵢ` concentrated in
degree zero, with `gdim(eᵢ Sⱼ) = 0` for `i ≠ j`, and write `dᵢ = gdim(eᵢ Sᵢ)`. For a minimal
resolution, every differential vanishes against `Sᵢ{j}`, so `Extⁿ(M, Sᵢ{j}) = Hom(Pₙ, Sᵢ{j})`.
Pairing `[Pₙ]` against `[Sᵢ]` then gives

`dᵢ · Bᵢ(q,t) = ∑_{n,j} dim_k Extⁿ(M, Sᵢ{j}) qʲ tⁿ`,

the bigraded Ext Poincaré power series of `(M,Sᵢ)`. When every `dᵢ` is nonzero, as for the heads
of primitive idempotents where `dᵢ = dim_k End_A(Sᵢ)`, this has three consequences:

* the series does not depend on the choice of minimal resolution, nor on the module up to
  isomorphism;
* the series of `M{d}` is `qᵈ` times the series of `M`;
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
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_iso`: independence of
  the minimal resolution and of the module up to isomorphism.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_shiftObj`: the shift law
  `B(M{d}) = qᵈ · B(M)`.
* `TauCeti.GradedProjectiveResolution.IsLinear.coeff_bettiPoincareSeries_eq_zero_of_ne`: every
  linear resolution, minimal or not, has diagonal Betti series.
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

/-- The constant coefficient of the Betti Poincaré series is the coordinate of `[P₀]`. -/
@[simp]
theorem constantCoeff_bettiPoincareSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) :
    PowerSeries.constantCoeff (r.bettiPoincareSeries bP i) =
      bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm 0)) i := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_bettiPoincareSeries]

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
/-- **Betti numbers are Ext dimensions.** Let `A` be finite-dimensional over `k`, let
`bP i = [A eᵢ]` for degree-zero idempotents `eᵢ`, and let the `Sᵢ` be concentrated in degree
zero with `gdim(eᵢ Sⱼ) = 0` for `i ≠ j`. For a minimal resolution, the coefficient of `qʲ tⁿ` in
`dᵢ · Bᵢ`, where `dᵢ = gdim(eᵢ Sᵢ)`, is `dim_k Extⁿ(M, Sᵢ{j})`. Homological degree zero is
included. -/
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
/-- **The Betti series computes the Ext Poincaré series.** Let `A` be finite-dimensional over
`k`, let `bP i = [A eᵢ]` for degree-zero idempotents `eᵢ`, and let the `Sᵢ` be concentrated in
degree zero with `gdim(eᵢ Sⱼ) = 0` for `i ≠ j`. For a minimal resolution of `M`, `dᵢ · Bᵢ(q,t)`,
where `dᵢ = gdim(eᵢ Sᵢ)`, is the bigraded Ext Poincaré power series of `(M,Sᵢ)`. -/
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

open scoped Pointwise in
include he₀ hne hbP hSzero hself in
/-- **Vanishing Betti numbers are vanishing Ext.** Let `A` be finite-dimensional over `k`, let
`bP i = [A eᵢ]`, and let the degree-zero targets `Sᵢ` satisfy `gdim(eᵢ Sⱼ) = 0` for `i ≠ j` and
`gdim(eᵢ Sᵢ) ≠ 0`. For a minimal resolution, the coefficient of `qᵈ tⁿ` in `Bᵢ` vanishes exactly
when `Extⁿ(M, Sᵢ{d})` does. -/
theorem IsMinimal.coeff_coeff_bettiPoincareSeries_eq_zero_iff
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) (i : I) (n : ℕ) (d : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 ↔
      Subsingleton (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n d) := by
  have h := hr.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries
    S he he₀ hI hne bP hbP hSzero i n d
  rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hSzero i), coeff_C_mul] at h
  have hc : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 := by
    exact_mod_cast (GradedModuleCat.finrank_smul_piece_zero_pos_of_concentrated
      (e i) (S i).obj (hSzero i) (hself i)).ne'
  let _ : Module.Finite A M := Module.Finite.of_surjective _ r.surjective_π
  let _ := ((GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite M
    (S i).obj).finiteLaurentSupport n).finiteDimensional d
  rw [← Module.finrank_zero_iff (R := k), ← Nat.cast_eq_zero (R := ℤ), ← h,
    mul_eq_zero_iff_left hc]

include he₀ hne hbP hSzero hself in
/-- **Independence of the minimal resolution.** Let `A` be finite-dimensional over `k`, let
`bP i = [A eᵢ]`, and let the degree-zero targets `Sᵢ` satisfy `gdim(eᵢ Sⱼ) = 0` for `i ≠ j` and
`gdim(eᵢ Sᵢ) ≠ 0`. Then minimal resolutions by finitely generated terms of isomorphic modules have
the same Betti Poincaré series. -/
theorem IsMinimal.bettiPoincareSeries_eq_of_iso {M' : GradedModuleCat.{uA} 𝒜} (eM : M ≅ M')
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M'.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    r.bettiPoincareSeries bP i = r'.bettiPoincareSeries bP i := by
  ext n : 1
  apply mul_left_cancel₀ (hself i)
  ext j
  rw [hr.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero,
    hr'.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero]
  exact_mod_cast (extLinearEquivOfIso k eM (Iso.refl _) n).finrank_eq

include he₀ hne hbP hSzero hself in
/-- **Independence of the minimal resolution.** Under the hypotheses of
`TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_iso`, two minimal
resolutions of the same module by finitely generated terms have the same Betti Poincaré
series. -/
theorem IsMinimal.bettiPoincareSeries_eq
    {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    r.bettiPoincareSeries bP i = r'.bettiPoincareSeries bP i :=
  hr.bettiPoincareSeries_eq_of_iso S he he₀ hI hne bP hbP hSzero hself (Iso.refl M) hr' i

include he₀ hne hbP hSzero hself in
/-- **The shift law** `B(M{d}) = qᵈ · B(M)`, for minimal resolutions of `M` and of `M{d}`. As in
`TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_iso`, `A` is
finite-dimensional over `k`, `bP i = [A eᵢ]`, and the degree-zero targets `Sᵢ` satisfy
`gdim(eᵢ Sⱼ) = 0` for `i ≠ j` and `gdim(eᵢ Sᵢ) ≠ 0`. -/
theorem IsMinimal.bettiPoincareSeries_shiftObj {d : ℤ}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    r'.bettiPoincareSeries bP i = PowerSeries.C (T d) * r.bettiPoincareSeries bP i := by
  have hshift (n : ℕ) (d' j : ℤ) :
      Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) (M.shiftObj d') (S i).obj n j) =
        Module.finrank k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n (j - d')) := by
    induction d' using Int.induction_on generalizing j with
    | zero =>
      rw [sub_zero]
      exact (extLinearEquivOfIso k ((GradedModuleCat.shiftFunctorZeroIso 𝒜).app M)
        (Iso.refl _) n).finrank_eq
    | succ d' ih =>
      rw [show j - (d' + 1) = j - 1 - d' by ring, ← ih]
      exact ((extLinearEquivOfIso k ((GradedModuleCat.shiftFunctorAddIso 𝒜 d' 1).app M).symm
        (Iso.refl _) n).trans
          (gradedExtShiftSourceEquiv k (GradedModuleCat.shift 𝒜) _ _ n j)).finrank_eq
    | pred d' ih =>
      rw [show j - (-d' - 1) = j + 1 - -d' by ring, ← ih]
      exact ((extLinearEquivOfIso k
        ((GradedModuleCat.shiftFunctorAddIso 𝒜 (-d') (-1)).app M).symm (Iso.refl _) n).trans
          (gradedExtShiftSourceInverseEquiv k (GradedModuleCat.shift 𝒜) _ _ n j)).finrank_eq
  ext n : 1
  apply mul_left_cancel₀ (hself i)
  ext j
  rw [hr'.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero,
    PowerSeries.coeff_C_mul, mul_left_comm, coeff_T_mul,
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincareSeries S he he₀ hI hne bP hbP hSzero,
    hshift]

include he₀ hne hbP hSzero hself in
/-- **Linear resolutions have diagonal Betti series.** Let `A` be finite-dimensional over `k`,
let `bP i = [A eᵢ]`, and let the degree-zero targets `Sᵢ` satisfy `gdim(eᵢ Sⱼ) = 0` for `i ≠ j`
and `gdim(eᵢ Sᵢ) ≠ 0`. For a linear resolution by finitely generated terms, minimal or not, the
coefficient of `qᵈ tⁿ` in `Bᵢ` vanishes for `d ≠ n`. -/
theorem IsLinear.coeff_bettiPoincareSeries_eq_zero_of_ne
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsLinear) (i : I) {n : ℕ} {d : ℤ}
    (hnd : (n : ℤ) ≠ d) :
    (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 := by
  have h := congrArg (fun f : LaurentPolynomial ℤ ↦ f.coeff d)
    (hr.smulGradedDimension_mul_repr_finiteProjectiveTerm S he he₀ hI hne bP hbP hSzero n i)
  simp only [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hSzero i),
    coeff_C_mul, T_apply, hnd, ↓reduceIte, mul_zero] at h
  rw [coeff_bettiPoincareSeries]
  refine (mul_eq_zero_iff_left ?_).mp h
  exact_mod_cast (GradedModuleCat.finrank_smul_piece_zero_pos_of_concentrated
    (e i) (S i).obj (hSzero i) (hself i)).ne'

include he₀ hne hbP hSzero hself in
/-- **Diagonal support detects linearity.** Let `A` be a nonnegatively graded finite-dimensional
algebra, let `bP i = [A eᵢ]`, and let the family `Sᵢ` be concentrated in degree zero, exhaust the
graded simples up to shift, and satisfy `gdim(eᵢ Sⱼ) = 0` for `i ≠ j` and `gdim(eᵢ Sᵢ) ≠ 0`.
Then a minimal resolution by finitely generated terms is linear exactly when the coefficient
of `qᵈ tⁿ` in every Betti Poincaré series vanishes for `d ≠ n`. The resolution may be
infinite. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincareSeries
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] (hr : r.IsMinimal) (hS : IsExhaustiveGradedSimpleFamily S)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) :
    r.IsLinear ↔ ∀ i (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
      (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff d = 0 := by
  refine ⟨fun hlin i n d hnd ↦
    hlin.coeff_bettiPoincareSeries_eq_zero_of_ne S he he₀ hI hne bP hbP hSzero hself i hnd,
    fun hdiag ↦ ?_⟩
  let _ (n : ℕ) : Module.Finite k (r.X n) := Module.Finite.trans A (r.X n)
  exact (hr.isLinear_iff_subsingleton_gradedExt_of_exhaustive S hS hSzero hneg).2
    fun i n d hnd ↦ (hr.coeff_coeff_bettiPoincareSeries_eq_zero_iff
      S he he₀ hI hne bP hbP hSzero hself i n d).1 (hdiag i n d hnd)

end NeZero

end GradedProjectiveResolution

include he₀ hne hbP hSzero in
/-- **Matrix form of the Ext comparison.** Let `A` be finite-dimensional over `k`, let
`bP i = [A eᵢ]` for degree-zero idempotents `eᵢ`, and let the `Sᵢ` be concentrated in degree
zero with `gdim(eᵢ Sⱼ) = 0` for `i ≠ j`. For minimal resolutions `rⱼ` of the family members
`Sⱼ`, the Betti Poincaré matrix `B`, scaled on the left by `diag(dᵢ)` with
`dᵢ = gdim(eᵢ Sᵢ)`, is the transpose of the bigraded Ext Poincaré matrix of the family. -/
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
