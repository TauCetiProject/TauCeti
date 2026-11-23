/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Ext.EulerAdmissible
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift
public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Betti Poincaré series of graded modules

Let `A` be a finite-dimensional graded algebra and `P` a graded projective resolution of a graded
module `M` by finitely generated terms. Given a Laurent basis `[Pᵢ]` of the graded Grothendieck
group of finite graded projectives, write `[Pₙ] = ∑ᵢ βⁿᵢ(q) [Pᵢ]`. When
`Pₙ ≅ ⨁_{i,d} Pᵢ{d}^{βⁿ_{i,d}}`, the coordinate `βⁿᵢ(q)` is `∑_d βⁿ_{i,d} qᵈ` because
`[Pᵢ{d}] = qᵈ [Pᵢ]`. The **Betti Poincaré series** of `M` at `Pᵢ` is the formal power series
`∑ₙ βⁿᵢ(q) tⁿ`, which records both the homological degree `t` and the internal degree `q`. For a
family of modules, such as the graded simples, the series form the **Betti Poincaré matrix**, with
rows indexed by the projective basis and columns by the family.

The basis is that of the idempotent projectives `Pᵢ = A eᵢ`, paired with finite graded modules
`Sᵢ` concentrated in degree zero with `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`. When the resolution is
minimal, the differentials vanish on maps to the targets `Sᵢ{j}`, so `Extⁿ(M, Sᵢ{j})` is the space
of graded maps `Pₙ ⟶ Sᵢ{j}`; its dimension is the coefficient of `qʲ` in `dᵢ βⁿᵢ(q)`, where
`dᵢ = dim_k(eᵢ • Sᵢ)`. When the `Sᵢ` are the graded simples and `A eᵢ ⟶ Sᵢ` their projective
covers, `dᵢ = dim_k End_A(Sᵢ)`. Hence:

* `dᵢ` times the Betti series is the bigraded Ext Poincaré series of `M` against `Sᵢ`;
* when every `dᵢ ≠ 0`, the Betti series does not depend on the minimal resolution;
* over a nonnegatively graded algebra, a minimal resolution is linear exactly when the Betti
  series are supported on the diagonal `d = n`, provided every `dᵢ ≠ 0` and the `Sᵢ` represent
  every finite simple graded module concentrated in degree zero;
* the Betti series of `M{1}` is `q` times the Betti series of `M`;
* when `M` vanishes below degree `c`, the Betti series at each `Pᵢ` with `dᵢ ≠ 0` vanishes below
  the shifted diagonal `j = c + n`; for `M` vanishing in negative degrees, its value at `t = -1`
  is therefore defined coefficientwise in `q`.

The resolution may be infinite: each coefficient of the series is a coordinate of the class of a
single term, so no finite projective dimension is needed.

## Main definitions

* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries`: the Betti Poincaré series of a
  resolution at a projective basis vector.
* `TauCeti.bettiPoincarePowerSeriesMatrix`: the Betti Poincaré series of a family of resolutions,
  as a matrix.

## Main results

In the namespace `TauCeti.GradedProjectiveResolution`:

* `IsMinimal.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries`: the coefficient of
  `qʲ tⁿ` in `dᵢ` times the Betti series is `dim_k Extⁿ(M, Sᵢ{j})`.
* `IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries`: `dᵢ` times the Betti series is
  the bigraded Ext Poincaré series against `Sᵢ`.
* `IsMinimal.bettiPoincarePowerSeries_eq`: the Betti series does not depend on the minimal
  resolution.
* `IsMinimal.coeff_coeff_bettiPoincarePowerSeries_nonneg`: at each `Pᵢ` with `dᵢ ≠ 0`, the Betti
  series of a minimal resolution has nonnegative coefficients.
* `IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt` and
  `IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries`: at each `Pᵢ` with `dᵢ ≠ 0`, the Betti
  series of a minimal resolution vanishes below a shifted diagonal; for `M` vanishing in negative
  degrees it has a well-defined value at `t = -1` coefficientwise in `q`.
* `IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries`: a minimal resolution is linear
  exactly when its Betti series have diagonal support.
* `IsMinimal.bettiPoincarePowerSeries_shiftObj_one`: the Betti series of `M{1}` is `q` times that
  of `M`.

In the namespace `TauCeti`:

* `forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix`: minimal resolutions of the
  members of a family are all linear exactly when the Betti Poincaré matrix has diagonal support.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for minimal and linear resolutions and their Poincaré series.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the factor
  `dim_k End_A(Sᵢ)` in the pairing of projective covers with simples over a general field.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe uk uA uI uJ

section Definition

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- The **Betti Poincaré series** of a graded projective resolution `P` by finitely generated
terms at the `i`th vector of a Laurent basis `bP` of graded projective `K₀`: the power series whose
coefficient of `tⁿ` is the `i`th coordinate of `[Pₙ]`. For the basis of indecomposable graded
projectives `Pᵢ` and `Pₙ ≅ ⨁_{i,d} Pᵢ{d}^{βⁿ_{i,d}}`, this is `∑_{n,d} βⁿ_{i,d} qᵈ tⁿ`. The
series is defined for any such resolution. For minimal resolutions and the basis of idempotent
projectives `A eᵢ`, at each `i` with `dᵢ = gdim(eᵢ • Sᵢ) ≠ 0`, it depends only on the resolved
module (`TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq`). -/
def bettiPoincarePowerSeries (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) :
    PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦ bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i

/-- The coefficient of `tⁿ` in the Betti Poincaré series is the `i`th coordinate of `[Pₙ]`. -/
@[simp]
theorem coeff_bettiPoincarePowerSeries (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincarePowerSeries]

end GradedProjectiveResolution

/-- The **Betti Poincaré matrix** of a family of graded projective resolutions by finitely
generated terms: the `(i, j)` entry is the Betti Poincaré series of the `j`th resolution at the
`i`th projective basis vector. Rows are indexed by the projective basis, columns by the family. -/
def bettiPoincarePowerSeriesMatrix {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) :
    Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  fun i j ↦ (r j).bettiPoincarePowerSeries bP i

/-- An entry of the Betti Poincaré matrix is a Betti Poincaré series. -/
@[simp]
theorem bettiPoincarePowerSeriesMatrix_apply {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) (j : J) :
    bettiPoincarePowerSeriesMatrix r bP i j = (r j).bettiPoincarePowerSeries bP i :=
  (rfl)

end Definition

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
  (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]

include he he₀ hne hbP hconc in
/-- **Betti numbers are Ext dimensions.** For a minimal resolution of `M`, the coefficient of
`qʲ tⁿ` in `dᵢ` times the Betti Poincaré series at `Pᵢ` is `dim_k Extⁿ(M, Sᵢ{j})`, where
`dᵢ = gdim(eᵢ • Sᵢ)`. -/
theorem IsMinimal.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (n : ℕ) (j : ℤ) :
    ((S i).obj.smulGradedDimension (e i) *
        PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j =
      Module.finrank k (Ext.{uA} M ((S i).obj.shiftObj j) n) := by
  have hN := GradedModuleCat.shiftObj_piece_eq_bot_of_concentrated (hconc i) j
  have hinv : invert ((S i).obj.smulGradedDimension (e i)) =
      (S i).obj.smulGradedDimension (e i) := by
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i), invert_C]
  rw [coeff_bettiPoincarePowerSeries, ← hinv,
    coeff_invert_smulGradedDimension_mul_repr S he he₀ hI hne bP hbP, finiteProjectiveTerm_obj]
  exact congrArg _ (hr.extLinearEquiv
    (((S i).obj.shiftObj j).positive_smul_top_eq_bot_of_concentrated _ hN) n).finrank_eq

include he he₀ hne hbP hconc in
/-- With normalized diagonal dimensions `dᵢ = 1`, the coefficient of `qʲ tⁿ` in the Betti Poincaré
series of a minimal resolution at `Pᵢ` is `dim_k Extⁿ(M, Sᵢ{j})`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries (hr : r.IsMinimal) (i : I)
    (hself : (S i).obj.smulGradedDimension (e i) = 1) (n : ℕ) (j : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j =
      Module.finrank k (Ext.{uA} M ((S i).obj.shiftObj j) n) := by
  simpa only [hself, one_mul] using
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc
      i n j

include he he₀ hne hbP hconc in
/-- **The Betti series computes the Ext Poincaré series against `Sᵢ`.** For a minimal resolution
of `M`, the constant `dᵢ = gdim(eᵢ • Sᵢ)` times the Betti Poincaré series at `Pᵢ` is the bigraded
Ext Poincaré series of `M` against `Sᵢ`. -/
theorem IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries (hr : r.IsMinimal) (i : I)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  ext n j
  rw [PowerSeries.coeff_C_mul,
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc,
    coeff_coeff_bigradedExtPoincarePowerSeries]
  exact congrArg _ (extLinearEquivOfIso k (Iso.refl M)
    ((GradedModuleCat.shiftPowIso 𝒜 j).app (S i).obj) n).finrank_eq.symm

include he he₀ hne hbP hconc in
/-- With normalized diagonal dimensions `dᵢ = 1`, the Betti Poincaré series of a minimal resolution
at `Pᵢ` is the bigraded Ext Poincaré series of `M` against `Sᵢ`. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (hself : (S i).obj.smulGradedDimension (e i) = 1)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj) :
    r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  simpa only [hself, map_one, one_mul] using
    hr.C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc i h

include he he₀ hne hbP hconc in
/-- **The Betti Poincaré series does not depend on the minimal resolution**: two minimal
resolutions of the same module have the same Betti Poincaré series at every `Pᵢ` with
`dᵢ = gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) :
    r.bettiPoincarePowerSeries bP i = r'.bettiPoincarePowerSeries bP i := by
  ext n : 1
  refine mul_left_cancel₀ hself (LaurentPolynomial.ext fun j ↦ ?_)
  rw [hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc,
    hr'.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc]

include he he₀ hne hbP hconc in
/-- A coefficient of the Betti Poincaré series of a minimal resolution at `Pᵢ` with `dᵢ ≠ 0`
vanishes exactly when the corresponding Ext group into the shifted target vanishes. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff (hr : r.IsMinimal) (i : I)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) (n : ℕ) (j : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 ↔
      Subsingleton (Ext.{uA} M ((S i).obj.shiftObj j) n) := by
  have hN := GradedModuleCat.shiftObj_piece_eq_bot_of_concentrated (hconc i) j
  let _ : Module.Finite A (S i).obj := gradedFiniteModules_iff.mp (S i).property
  let _ : Module.Finite k (S i).obj := Module.Finite.trans A _
  let _ : Module.Finite k (r.termObj n) := Module.Finite.trans A (r.X n)
  obtain ⟨c, hd⟩ : ∃ c : ℤ, (S i).obj.smulGradedDimension (e i) = C c :=
    ⟨_, GradedModuleCat.smulGradedDimension_eq_C_of_concentrated (e := e i) _ (hconc i)⟩
  have hcoeff := hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne
    bP hbP hconc i n j
  rw [hd, coeff_C_mul] at hcoeff
  have hc : c ≠ 0 := fun h0 ↦ hself (by rw [hd, h0, map_zero])
  have : FiniteDimensional k (Ext.{uA} M ((S i).obj.shiftObj j) n) :=
    Module.Finite.equiv
      (hr.extLinearEquiv (((S i).obj.shiftObj j).positive_smul_top_eq_bot_of_concentrated _ hN) n)
  rw [← Module.finrank_zero_iff (R := k), ← Int.natCast_eq_zero, ← hcoeff, mul_eq_zero,
    or_iff_right hc]

include he he₀ hne hbP hconc in
/-- The coefficients of the Betti Poincaré series of a minimal resolution at `Pᵢ` with
`dᵢ = gdim(eᵢ • Sᵢ) ≠ 0` are nonnegative. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_nonneg (hr : r.IsMinimal) (i : I)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) (n : ℕ) (j : ℤ) :
    0 ≤ (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j := by
  -- `dᵢ` times the coefficient is an Ext dimension, and `dᵢ > 0`.
  let _ : Module.Finite A (S i).obj := gradedFiniteModules_iff.mp (S i).property
  let _ : Module.Finite k (S i).obj := Module.Finite.trans A _
  have hcoeff := hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne
    bP hbP hconc i n j
  rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i), coeff_C_mul]
    at hcoeff
  exact nonneg_of_mul_nonneg_right (hcoeff ▸ Int.natCast_nonneg _)
    (Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) hself))

include he he₀ hne hbP hconc in
/-- **The Betti Poincaré series of a minimal resolution vanishes below a shifted diagonal.** If `M`
vanishes in internal degrees below `c`, then at every `Pᵢ` with `dᵢ = gdim(eᵢ • Sᵢ) ≠ 0` the
coefficient of `qʲ tⁿ` vanishes whenever `j < c + n`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) (i : I)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) {n : ℕ} {j : ℤ} (hjn : j < c + n) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 := by
  have (m : ℕ) : Module.Finite k (r.X m) := Module.Finite.trans A (r.X m)
  rw [hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff S he he₀ hI hne bP hbP hconc i hself]
  exact GradedModuleCat.subsingleton_gradedExt_iff_subsingleton_ext_shiftObj.1
    (hr.subsingleton_gradedExt_of_lt hM (hconc i) hjn)

include he he₀ hne hbP hconc in
/-- The Betti Poincaré series of a minimal resolution of a module vanishing in negative internal
degrees, at every `Pᵢ` with `dᵢ = gdim(eᵢ • Sᵢ) ≠ 0`, has an Alexander-graded Euler power series:
its value at `t = -1` is defined coefficientwise in `q`. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (hM : ∀ p < 0, M.grading.piece p = ⊥) (i : I)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) :
    Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun _ _ han ↦
    hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt S he he₀ hI hne bP hbP hconc hM i hself
      (by omega)

include he he₀ hne hbP hconc in
/-- **A minimal resolution is linear exactly when its Betti Poincaré series are supported on the
diagonal.** Over a nonnegatively graded algebra, let the `Sᵢ` represent every finite simple graded
module concentrated in degree zero, with every `dᵢ = gdim(eᵢ • Sᵢ)` nonzero. Then a minimal
resolution is linear exactly when the coefficient of `qʲ tⁿ` in each Betti Poincaré series vanishes
for `j ≠ n`. The resolution may be infinite. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hS : IsExhaustiveGradedSimpleFamily S)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) :
    r.IsLinear ↔ ∀ i (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
      (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 := by
  have (n : ℕ) : Module.Finite k (r.X n) := Module.Finite.trans A (r.X n)
  simp_rw [hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff S he he₀ hI hne bP hbP hconc _
    (hself _)]
  exact hr.isLinear_iff_subsingleton_ext_shiftObj_family hneg hS hconc

include he he₀ hne hbP hconc in
/-- **The Betti Poincaré series of `M{1}` is `q` times that of `M`**, for minimal resolutions of
`M` and of `M{1}`, at every `Pᵢ` with `dᵢ = gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem IsMinimal.bettiPoincarePowerSeries_shiftObj_one
    {r₁ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj 1).grading}
    [∀ n, Module.Finite A (r₁.X n)] (hr : r.IsMinimal) (hr₁ : r₁.IsMinimal) (i : I)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) :
    r₁.bettiPoincarePowerSeries bP i = PowerSeries.C (T 1) * r.bettiPoincarePowerSeries bP i := by
  ext n : 1
  rw [PowerSeries.coeff_C_mul]
  refine mul_left_cancel₀ hself (LaurentPolynomial.ext fun j ↦ ?_)
  rw [hr₁.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc,
    mul_left_comm, coeff_T_mul,
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc]
  -- `Ext(M{1}, Sᵢ{j})` is the bigraded `Ext^{n,j}(M{1}, Sᵢ)`, which is `Ext^{n,j-1}(M, Sᵢ)`.
  rw [← GradedModuleCat.shift_functor_obj]
  exact congrArg _ (((extLinearEquivOfIso k (Iso.refl _)
    ((GradedModuleCat.shiftPowIso 𝒜 j).app (S i).obj).symm n).trans
      (gradedExtShiftSourceEquiv k (GradedModuleCat.shift 𝒜) M (S i).obj n j)).trans
        (extLinearEquivOfIso k (Iso.refl M)
          ((GradedModuleCat.shiftPowIso 𝒜 (j - 1)).app (S i).obj) n)).finrank_eq

end GradedProjectiveResolution

include he he₀ hne hbP hconc in
/-- **Linearity of a family of minimal resolutions is diagonal support of the Betti Poincaré
matrix.** Over a nonnegatively graded algebra, let the `Sᵢ` represent every finite simple graded
module concentrated in degree zero, with every `dᵢ = gdim(eᵢ • Sᵢ)` nonzero. Minimal resolutions
of a family of graded modules are all linear exactly when every entry of their Betti Poincaré
matrix has its coefficient of `qᵖ tⁿ` vanish for `p ≠ n`. -/
theorem forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hS : IsExhaustiveGradedSimpleFamily S)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) :
    (∀ j, (r j).IsLinear) ↔ ∀ i j (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
      (PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix r bP i j)).coeff p = 0 := by
  simp only [bettiPoincarePowerSeriesMatrix_apply]
  rw [forall_comm]
  exact forall_congr' fun j ↦
    (hr j).isLinear_iff_diagonal_bettiPoincarePowerSeries S he he₀ hI hne bP hbP hconc hneg hS hself

end TauCeti
