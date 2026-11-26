/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Ext.EulerAdmissible
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Betti Poincaré series of graded modules

Let `A` be a graded `k`-algebra with grading `𝒜 : ℤ → Submodule k A`, and let `P` be a graded
projective resolution of a graded module `M` by finitely generated `A`-modules. Given a Laurent
basis `[Pᵢ]` of the graded Grothendieck group `K₀^gr(proj A)` of finite graded projectives, write
`[Pₙ] = ∑ᵢ βⁿᵢ(q) [Pᵢ]`. When `Pₙ ≅ ⨁_{i,d} Pᵢ{d}^{βⁿ_{i,d}}`, the coordinate `βⁿᵢ(q)` is
`∑_d βⁿ_{i,d} qᵈ` because `[Pᵢ{d}] = qᵈ [Pᵢ]`. The **Betti Poincaré series** of `P` at `[Pᵢ]` is
the formal power series `∑ₙ βⁿᵢ(q) tⁿ`, recording both the homological degree `t` and the internal
degree `q`. For an indexed family of resolved modules, the series form the **Betti Poincaré
matrix**, with rows indexed by the projective basis and columns by the family.

Without assuming a field, `Ext`, or finite-dimensionality of `A`:

* shifting a resolution from `M` to `M{d}` (`GradedProjectiveResolution.shiftObj`) multiplies every
  Betti Poincaré series by `qᵈ` (`bettiPoincarePowerSeries_shiftObj`);
* when `𝒜` decomposes `A`, termwise uniqueness of minimal graded projective resolutions
  (`GradedProjectiveResolution.IsMinimal.termObjIso`) makes the Betti Poincaré series and matrix
  independent of the chosen minimal resolutions whenever the resolution terms have gradings bounded
  below — in particular automatically over a nonnegatively graded algebra or when terms are finite
  over `k` (`IsMinimal.bettiPoincarePowerSeries_eq`,
  `IsMinimal.bettiPoincarePowerSeries_eq_of_nonneg`,
  `IsMinimal.bettiPoincarePowerSeries_eq_of_finite`).

Over a field `k` (with `A` possibly infinite-dimensional over `k`, such as `k[x]`), let `[Pᵢ]` be
the basis of degree-zero idempotent projectives `[A eᵢ]` paired with degree-zero targets `Sᵢ` that
are finite-dimensional over `k` and satisfy `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`. When `P` is minimal,
differentials vanish on graded maps into `Sᵢ{j}`, so `Extⁿ(M, Sᵢ{j})` is isomorphic to
`Pₙ ⟶ Sᵢ{j}`, whose `k`-dimension is the coefficient of `qʲ` in `dᵢ βⁿᵢ(q)` with
`dᵢ = dim_k(eᵢ • (Sᵢ)₀)`. Hence:

* `dᵢ` times the Betti Poincaré series is the bigraded Ext Poincaré power series of `M` against
  `Sᵢ` (`IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries`), and when `dᵢ = 1` for all
  `i` the transposed Betti Poincaré matrix of minimal resolutions of `S` equals
  `bigradedExtPoincarePowerSeriesMatrix`;
* at each `Pᵢ` with `dᵢ ≠ 0`, the Betti Poincaré series of a minimal resolution has nonnegative
  coefficients and, when `M` vanishes below degree `c` and resolution terms are bounded below,
  vanishes strictly below `j = c + n`, giving `Bigraded.HasEulerPowerSeries` when `c = 0`;
* over a nonnegatively graded algebra whose degree-zero piece `𝒜 0` is finite-dimensional over `k`,
  a minimal resolution is linear if and only if its Betti Poincaré series against an exhaustive
  degree-zero simple family are supported on the diagonal `j = n`
  (`IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries`).

The resolution may be infinite: each coefficient of the series is a coordinate of the class of a
single term, so no finite projective dimension is needed.

## Main definitions

* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries`: the Betti Poincaré series of a
  resolution at a projective basis vector.
* `TauCeti.bettiPoincarePowerSeriesMatrix`: the Betti Poincaré series of a family of resolutions,
  as a matrix.

## Main results

In the namespace `TauCeti.GradedProjectiveResolution`:

* `coeff_bettiPoincarePowerSeries_eq_zero_of_subsingleton`, `trunc_bettiPoincarePowerSeries`, and
  `eval_trunc_bettiPoincarePowerSeries`: vanishing terms, polynomial truncation for finite
  resolutions, and evaluation at `t = -1`.
* `of_finiteProjectiveTerm_shiftObj` and `bettiPoincarePowerSeries_shiftObj`: regrading `M` to
  `M{d}` multiplies each term class and Betti Poincaré series by `qᵈ`.
* `IsMinimal.finiteProjectiveTermIso`, `IsMinimal.bettiPoincarePowerSeries_eq`,
  `IsMinimal.bettiPoincarePowerSeries_eq_of_nonneg`, and
  `IsMinimal.bettiPoincarePowerSeries_shiftObj_eq`: unconditional minimal-resolution independence
  and shift laws via uniqueness of minimal resolutions.
* `IsMinimal.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries`,
  `IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries`, and
  `IsMinimal.C_finrank_mul_eulerPowerSeries`: Betti–Ext comparisons without assuming `A` is
  finite-dimensional over `k`.
* `IsMinimal.coeff_coeff_bettiPoincarePowerSeries_nonneg`,
  `IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt_of_bddBelow`, and
  `IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries_of_bddBelow`: nonnegativity,
  lower-triangular vanishing, and `Bigraded.HasEulerPowerSeries` at `Pᵢ` with `dᵢ ≠ 0`.
* `IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries`: diagonal-support characterization of
  linear resolutions when `𝒜 0` is finite-dimensional over `k`.

In the namespace `TauCeti`:

* `bettiPoincarePowerSeriesMatrix_eq` and `bettiPoincarePowerSeriesMatrix_eq_of_nonneg`:
  independence of the Betti Poincaré matrix from the chosen minimal resolutions.
* `bettiPoincarePowerSeriesMatrix_transpose_eq_bigradedExtPoincarePowerSeriesMatrix`: transposed
  Betti–Ext matrix identity when `dᵢ = 1`.
* `forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix` and
  `forall_exists_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix`: diagonal-support
  characterizations of linear resolutions for families.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for minimal and linear resolutions and their Poincaré series.
* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Section 20, for
  uniqueness of minimal projective resolutions.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the factor
  `dim_k End_A(Sᵢ)` in the pairing of projective covers with simples over a general field.

The Betti–Ext comparison generalizes
`TauCeti.GradedProjectiveResolution.IsLinear.smulGradedDimension_mul_repr_finiteProjectiveTerm` via
`TauCeti.gradedProjectiveExtEulerTarget_eq_mul_invert_repr` and
`TauCeti.coeff_invert_smulGradedDimension_mul_repr`, and the diagonal linearity criteria adapt
`TauCeti.forall_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix` and its siblings in
`TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI uJ

/-! ### Definition, truncation, and internal shifts -/

section Definition

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- The **Betti Poincaré series** of a graded projective resolution `P` by finitely generated
terms at the `i`th vector of a Laurent basis `bP` of graded projective `K₀`: the power series whose
coefficient of `tⁿ` is the `i`th coordinate of `[Pₙ]`. For the basis of indecomposable graded
projectives `Pᵢ` and `Pₙ ≅ ⨁_{i,d} Pᵢ{d}^{βⁿ_{i,d}}`, this is `∑_{n,d} βⁿ_{i,d} qᵈ tⁿ`. The
series is defined for any such resolution; for minimal resolutions with bounded-below terms over a
decomposed grading it depends only on the resolved module
(`TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq`). -/
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

/-- The constant term (`n = 0`) of `r.bettiPoincarePowerSeries bP i` is the `i`th coordinate of
`[P₀]`. -/
@[simp]
theorem constantCoeff_bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) :
    PowerSeries.constantCoeff (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm 0)) i := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_bettiPoincarePowerSeries]

/-- Over a finite index type, the `tⁿ` coefficients of `r.bettiPoincarePowerSeries bP` reconstruct
the class `[Pₙ]` in `K₀^gr(proj A)`. -/
theorem of_finiteProjectiveTerm_eq_sum_bettiPoincarePowerSeries [Fintype I]
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (n : ℕ) :
    LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n) =
      ∑ i, PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) • bP i := by
  conv_lhs => rw [← bP.sum_repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))]
  simp only [coeff_bettiPoincarePowerSeries]

/-- A vanishing term of a resolution contributes nothing to its Betti Poincaré series. -/
theorem coeff_bettiPoincarePowerSeries_eq_zero_of_subsingleton
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) {n : ℕ}
    (hn : Subsingleton (r.X n)) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) = 0 := by
  have hZ : Limits.IsZero (r.finiteProjectiveTerm n) :=
    Limits.IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
      (by simpa using GradedModuleCat.isZero_of_subsingleton (r.termObj n))
  rw [coeff_bettiPoincarePowerSeries, ← LaurentK0.ofExactK0_exactK0_of.{uA},
    ExactK0.of_eq_zero_of_isZero.{uA} hZ, map_zero, map_zero, Finsupp.zero_apply]

/-- **The Betti Poincaré series of a finite resolution is a polynomial.** If the terms of the
resolution vanish above homological degree `N`, its Betti Poincaré series agrees with its
truncation below `t^(N + 1)`. -/
theorem trunc_bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) {N : ℕ}
    (hN : ∀ n, N < n → Subsingleton (r.X n)) :
    (PowerSeries.trunc (N + 1) (r.bettiPoincarePowerSeries bP i) : PowerSeries _) =
      r.bettiPoincarePowerSeries bP i := by
  ext n : 1
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · exact (r.coeff_bettiPoincarePowerSeries_eq_zero_of_subsingleton bP i (hN n (by omega))).symm

/-- The Betti Poincaré series truncated below `t^(N + 1)` and evaluated at `t = -1` is the
coordinate of the alternating class `∑_{n ≤ N} (-1)ⁿ [P_n]` of the terms. -/
theorem eval_trunc_bettiPoincarePowerSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (i : I) (N : ℕ) :
    (PowerSeries.trunc (N + 1) (r.bettiPoincarePowerSeries bP i)).eval (-1) =
      bP.repr (∑ n ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ n • LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i := by
  rw [← Polynomial.eval₂_id, PowerSeries.eval₂_trunc_eq_sum_range, map_sum,
    Finset.sum_apply']
  exact Finset.sum_congr rfl fun n _ ↦ by simp [coeff_bettiPoincarePowerSeries, mul_comm]

/-- If `Pₙ` is graded-isomorphic to an internal shift `P{d}` of a projective representing `bP j`,
the `n`th Betti coefficient at `i` is `qᵈ` for `i = j` and `0` otherwise. -/
theorem coeff_bettiPoincarePowerSeries_of_iso_shiftObj [DecidableEq I]
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    {n : ℕ} {P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory} {j : I}
    (hbP : bP j = LaurentK0.of.{uA} _ P) {d : ℤ} (e : r.termObj n ≅ P.obj.shiftObj d) (i : I) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) =
      if i = j then T d else 0 := by
  have hiso : r.finiteProjectiveTerm n ≅
      ⟨P.obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj P.property d⟩ :=
    (gradedFiniteProjectiveModules 𝒜).fullyFaithfulι.preimageIso
      (eqToIso (r.finiteProjectiveTerm_obj n) ≪≫ e)
  rw [coeff_bettiPoincarePowerSeries, LaurentK0.of_congr.{uA} _ hiso,
    laurentK0_projective_of_shiftObj P d, ← hbP, map_smul, bP.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
  simp [eq_comm]

/-- Shifting a resolution to `M{d}` multiplies the class of each resolution term by `qᵈ`. -/
@[simp]
theorem of_finiteProjectiveTerm_shiftObj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    (d : ℤ) (n : ℕ) [Module.Finite A (r.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ((r.shiftObj d).finiteProjectiveTerm n) =
      (T d : LaurentPolynomial ℤ) •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm n) := by
  have hterm : (r.shiftObj d).finiteProjectiveTerm n =
      ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
        gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩ :=
    ObjectProperty.FullSubcategory.ext (by simp)
  rw [hterm]
  exact laurentK0_projective_of_shiftObj (r.finiteProjectiveTerm n) d

/-- **Internal-shift law for Betti Poincaré series**: shifting a resolution of `M` to `M{d}`
multiplies each Betti Poincaré power series by `qᵈ`. -/
@[simp]
theorem bettiPoincarePowerSeries_shiftObj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))) (d : ℤ) (i : I) :
    (r.shiftObj d).bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d) * r.bettiPoincarePowerSeries bP i := by
  ext n : 1
  rw [coeff_bettiPoincarePowerSeries, of_finiteProjectiveTerm_shiftObj, map_smul,
    Finsupp.smul_apply, smul_eq_mul, PowerSeries.coeff_C_mul, coeff_bettiPoincarePowerSeries]

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

/-- Shifting each resolved module `M j` by `d j` multiplies the `j`th column of the Betti Poincaré
matrix by `q^{d j}`. -/
theorem bettiPoincarePowerSeriesMatrix_shiftObj {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (d : J → ℤ) (i : I) (j : J) :
    bettiPoincarePowerSeriesMatrix (fun j ↦ (r j).shiftObj (d j)) bP i j =
      PowerSeries.C (T (d j)) * bettiPoincarePowerSeriesMatrix r bP i j :=
  (r j).bettiPoincarePowerSeries_shiftObj bP (d j) i

end Definition

/-! ### Minimal-resolution independence and shift laws -/

section MinimalUniqueness

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜]
  {I : Type uI}

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}

/-- Any two minimal graded projective resolutions of `M` with bounded-below terms have isomorphic
finite-projective terms in any homological degree `n` where both `n`th terms are finitely
generated. -/
def IsMinimal.finiteProjectiveTermIso
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₁.grading m).piece p = ⊥)
    (hb₂ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₂.grading m).piece p = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    r₁.finiteProjectiveTerm n ≅ r₂.finiteProjectiveTerm n :=
  (gradedFiniteProjectiveModules 𝒜).fullyFaithfulι.preimageIso <|
    eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫
      hr₁.termObjIso hr₂ hb₁ hb₂ n ≪≫
      eqToIso (r₂.finiteProjectiveTerm_obj n).symm

/-- The underlying morphism of `(finiteProjectiveTermIso ...).hom` is `(termObjIso ...).hom`
conjugated by `eqToHom` along `finiteProjectiveTerm_obj`. -/
@[simp]
theorem IsMinimal.finiteProjectiveTermIso_hom_hom
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₁.grading m).piece p = ⊥)
    (hb₂ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₂.grading m).piece p = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    (hr₁.finiteProjectiveTermIso hr₂ hb₁ hb₂ n).hom.hom =
      eqToHom (r₁.finiteProjectiveTerm_obj n) ≫
        (hr₁.termObjIso hr₂ hb₁ hb₂ n).hom ≫
        eqToHom (r₂.finiteProjectiveTerm_obj n).symm := by
  rw [← ObjectProperty.ι_map]
  exact ((gradedFiniteProjectiveModules 𝒜).fullyFaithfulι.map_preimage _).trans
    (by simp only [Iso.trans_hom, eqToIso.hom])

/-- Including `finiteProjectiveTermIso` into `GradedModuleCat 𝒜` recovers `termObjIso`
conjugated by `eqToIso` along `finiteProjectiveTerm_obj`. -/
@[simp]
theorem IsMinimal.mapIso_finiteProjectiveTermIso
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₁.grading m).piece p = ⊥)
    (hb₂ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₂.grading m).piece p = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    (gradedFiniteProjectiveModules 𝒜).ι.mapIso
        (hr₁.finiteProjectiveTermIso hr₂ hb₁ hb₂ n) =
      eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫
        hr₁.termObjIso hr₂ hb₁ hb₂ n ≪≫
        eqToIso (r₂.finiteProjectiveTerm_obj n).symm :=
  Iso.ext <| by
    rw [Functor.mapIso_hom, ObjectProperty.ι_map, finiteProjectiveTermIso_hom_hom]
    simp only [Iso.trans_hom, eqToIso.hom]

/-- The underlying morphism of `(finiteProjectiveTermIso ...).inv` is `(termObjIso ...).inv`
conjugated by `eqToHom` along `finiteProjectiveTerm_obj`. -/
@[simp]
theorem IsMinimal.finiteProjectiveTermIso_inv_hom
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₁.grading m).piece p = ⊥)
    (hb₂ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₂.grading m).piece p = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    (hr₁.finiteProjectiveTermIso hr₂ hb₁ hb₂ n).inv.hom =
      eqToHom (r₂.finiteProjectiveTerm_obj n) ≫
        (hr₁.termObjIso hr₂ hb₁ hb₂ n).inv ≫
        eqToHom (r₁.finiteProjectiveTerm_obj n).symm := by
  rw [← ObjectProperty.ι_map]
  exact (congrArg Iso.inv (hr₁.mapIso_finiteProjectiveTermIso hr₂ hb₁ hb₂ n)).trans
    (by simp only [Iso.trans_inv, eqToIso.inv, Category.assoc])

/-- Any two minimal graded projective resolutions of `M` with bounded-below terms have equal term
classes in `K₀^gr(proj A)` in any homological degree `n` where both `n`th terms are finitely
generated. -/
theorem IsMinimal.of_finiteProjectiveTerm_eq
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₁.grading m).piece p = ⊥)
    (hb₂ : ∀ m, ∃ b : ℤ, ∀ p < b, (r₂.grading m).piece p = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  LaurentK0.of_congr.{uA} _ (hr₁.finiteProjectiveTermIso hr₂ hb₁ hb₂ n)

variable [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions of `M` with
finitely generated terms have isomorphic finite-projective terms in every homological degree. -/
def IsMinimal.finiteProjectiveTermIsoOfNonneg
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (n : ℕ) :
    r₁.finiteProjectiveTerm n ≅ r₂.finiteProjectiveTerm n :=
  hr₁.finiteProjectiveTermIso hr₂
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg)
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg) n

/-- `finiteProjectiveTermIsoOfNonneg` specializes `finiteProjectiveTermIso` using the automatic
lower bounds on finitely generated modules over a nonnegatively graded algebra. -/
@[simp]
theorem IsMinimal.finiteProjectiveTermIsoOfNonneg_eq_finiteProjectiveTermIso
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (n : ℕ) :
    hr₁.finiteProjectiveTermIsoOfNonneg hneg hr₂ n =
      hr₁.finiteProjectiveTermIso hr₂
        (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg)
        (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg) n :=
  (rfl)

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions of `M` with
finitely generated terms have equal term classes in `K₀^gr(proj A)` in every homological degree. -/
theorem IsMinimal.of_finiteProjectiveTerm_eq_of_nonneg
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  LaurentK0.of_congr.{uA} _ (hr₁.finiteProjectiveTermIsoOfNonneg hneg hr₂ n)

/-- **The Betti Poincaré series does not depend on the minimal resolution**: any two minimal graded
projective resolutions of `M` with finitely generated bounded-below terms define the same Betti
Poincaré series at every basis vector. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) (i : I) :
    r₁.bettiPoincarePowerSeries bP i = r₂.bettiPoincarePowerSeries bP i := by
  ext n : 1
  simp only [coeff_bettiPoincarePowerSeries, hr₁.of_finiteProjectiveTerm_eq hr₂ hb₁ hb₂ n]

/-- **Minimal-resolution independence over a nonnegatively graded algebra**: any two minimal graded
projective resolutions of `M` with finitely generated terms define the same Betti Poincaré
series. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_of_nonneg
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (i : I) :
    r₁.bettiPoincarePowerSeries bP i = r₂.bettiPoincarePowerSeries bP i :=
  hr₁.bettiPoincarePowerSeries_eq bP hr₂
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg)
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg) i

/-- **Minimal-resolution independence for `k`-finite resolution terms**, without assuming the
algebra grading is nonnegative. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_of_finite
    [∀ n, Module.Finite k (r₁.X n)] [∀ n, Module.Finite k (r₂.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (i : I) :
    r₁.bettiPoincarePowerSeries bP i = r₂.bettiPoincarePowerSeries bP i :=
  hr₁.bettiPoincarePowerSeries_eq bP hr₂
    (fun n ↦
      let ⟨b, hb⟩ := (r₁.grading n).finite_piece_ne_bot.bddBelow
      ⟨b, fun _ hp ↦ by by_contra hne; exact absurd (hb hne) (not_le.mpr hp)⟩)
    (fun n ↦
      let ⟨b, hb⟩ := (r₂.grading n).finite_piece_ne_bot.bddBelow
      ⟨b, fun _ hp ↦ by by_contra hne; exact absurd (hb hne) (not_le.mpr hp)⟩) i

/-- **The Betti Poincaré series of `M{d}` is `qᵈ` times that of `M`**, for any minimal resolutions
`r'` of `M{d}` and `r₁` of `M` with finitely generated bounded-below terms. -/
theorem IsMinimal.bettiPoincarePowerSeries_shiftObj_eq {d : ℤ}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r'.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hr' : r'.IsMinimal) (hr₁ : r₁.IsMinimal)
    (hb' : ∀ n, ∃ b : ℤ, ∀ p < b, (r'.grading n).piece p = ⊥)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥) (i : I) :
    r'.bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d) * r₁.bettiPoincarePowerSeries bP i := by
  have hb₁' : ∀ n, ∃ b : ℤ, ∀ p < b, ((r₁.shiftObj d).grading n).piece p = ⊥ := fun n ↦ by
    obtain ⟨b, hbn⟩ := hb₁ n
    refine ⟨b + d, fun p hp ↦ ?_⟩
    simpa [sub_eq_add_neg] using hbn (p - d) (by omega)
  exact (hr'.bettiPoincarePowerSeries_eq bP ((r₁.isMinimal_shiftObj_iff d).mpr hr₁)
    hb' hb₁' i).trans (r₁.bettiPoincarePowerSeries_shiftObj bP d i)

/-- Over a nonnegatively graded algebra, the Betti Poincaré series of any minimal resolution `r'`
of `M{d}` with finitely generated terms is `qᵈ` times that of any minimal resolution `r₁` of `M`
with finitely generated terms. -/
theorem IsMinimal.bettiPoincarePowerSeries_shiftObj_eq_of_nonneg {d : ℤ}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r'.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr' : r'.IsMinimal) (hr₁ : r₁.IsMinimal) (i : I) :
    r'.bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d) * r₁.bettiPoincarePowerSeries bP i :=
  hr'.bettiPoincarePowerSeries_shiftObj_eq bP hr₁
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg)
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg) i

/-- For minimal resolutions of `M{d}` and `M` with `k`-finite terms, the Betti Poincaré series of
`M{d}` is `qᵈ` times that of `M`, without assuming the algebra grading is nonnegative. -/
theorem IsMinimal.bettiPoincarePowerSeries_shiftObj_eq_of_finite {d : ℤ}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r'.X n)]
    [∀ n, Module.Finite k (r'.X n)] [∀ n, Module.Finite k (r₁.X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hr' : r'.IsMinimal) (hr₁ : r₁.IsMinimal) (i : I) :
    r'.bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d) * r₁.bettiPoincarePowerSeries bP i :=
  hr'.bettiPoincarePowerSeries_shiftObj_eq bP hr₁
    (fun n ↦
      let ⟨b, hb⟩ := (r'.grading n).finite_piece_ne_bot.bddBelow
      ⟨b, fun _ hp ↦ by by_contra hne; exact absurd (hb hne) (not_le.mpr hp)⟩)
    (fun n ↦
      let ⟨b, hb⟩ := (r₁.grading n).finite_piece_ne_bot.bddBelow
      ⟨b, fun _ hp ↦ by by_contra hne; exact absurd (hb hne) (not_le.mpr hp)⟩) i

end GradedProjectiveResolution

/-- Any two families of minimal graded projective resolutions with finitely generated bounded-below
terms define the same Betti Poincaré matrix. -/
theorem bettiPoincarePowerSeriesMatrix_eq {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    {r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal)
    (hb₁ : ∀ j n, ∃ b : ℤ, ∀ p < b, ((r₁ j).grading n).piece p = ⊥)
    (hb₂ : ∀ j n, ∃ b : ℤ, ∀ p < b, ((r₂ j).grading n).piece p = ⊥) :
    bettiPoincarePowerSeriesMatrix r₁ bP = bettiPoincarePowerSeriesMatrix r₂ bP :=
  Matrix.ext fun i j ↦ (hr₁ j).bettiPoincarePowerSeries_eq bP (hr₂ j) (hb₁ j) (hb₂ j) i

/-- Over a nonnegatively graded algebra, any two families of minimal graded projective resolutions
with finitely generated terms define the same Betti Poincaré matrix. -/
theorem bettiPoincarePowerSeriesMatrix_eq_of_nonneg {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    {r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal) :
    bettiPoincarePowerSeriesMatrix r₁ bP = bettiPoincarePowerSeriesMatrix r₂ bP :=
  Matrix.ext fun i j ↦ (hr₁ j).bettiPoincarePowerSeries_eq_of_nonneg bP hneg (hr₂ j) i

end MinimalUniqueness

/-! ### Comparison with bigraded Ext, nonnegativity, and lower-triangularity -/

section BettiExtComparison

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj] {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r.X n)]

include he he₀ hne hbP in
/-- **Betti numbers are Ext dimensions.** For a minimal resolution of `M`, the coefficient of
`qʲ tⁿ` in `dᵢ` times the Betti Poincaré series at `Pᵢ` is `dim_k Extⁿ(M, Sᵢ{j})`, where
`dᵢ = gdim(eᵢ • Sᵢ)`. Neither finite-dimensionality of `A` nor a nonnegative grading is assumed. -/
theorem IsMinimal.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (n : ℕ) (j : ℤ) :
    ((S i).obj.smulGradedDimension (e i) *
        PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j =
      Module.finrank k (Ext.{uA} M ((S i).obj.shiftObj j) n) := by
  have hN := GradedModuleCat.shiftObj_piece_eq_bot_of_concentrated hconc j
  have hinv : invert ((S i).obj.smulGradedDimension (e i)) =
      (S i).obj.smulGradedDimension (e i) := by
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc, invert_C]
  rw [coeff_bettiPoincarePowerSeries, ← hinv,
    coeff_invert_smulGradedDimension_mul_repr S he he₀ hI hne bP hbP, finiteProjectiveTerm_obj]
  exact congrArg _ (hr.extLinearEquiv
    (((S i).obj.shiftObj j).positive_smul_top_eq_bot_of_concentrated _ hN) n).finrank_eq

include he he₀ hne hbP in
/-- With normalized diagonal dimension `dᵢ = 1`, the coefficient of `qʲ tⁿ` in the Betti Poincaré
series of a minimal resolution at `Pᵢ` is `dim_k Extⁿ(M, Sᵢ{j})`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) = 1) (n : ℕ) (j : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j =
      Module.finrank k (Ext.{uA} M ((S i).obj.shiftObj j) n) := by
  simpa only [hself, one_mul] using
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP i hconc
      n j

include he he₀ hne hbP in
/-- **The Betti series computes the Ext Poincaré series against `Sᵢ`.** For a minimal resolution
of `M`, the constant `dᵢ = gdim(eᵢ • Sᵢ)` times the Betti Poincaré series at `Pᵢ` is the bigraded
Ext Poincaré series of `M` against `Sᵢ`, without assuming `A` is finite-dimensional over `k`. -/
theorem IsMinimal.C_smulGradedDimension_mul_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      hr.isGradedExtInternallyFinite hconc) :
    PowerSeries.C ((S i).obj.smulGradedDimension (e i)) * r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  ext n j
  rw [PowerSeries.coeff_C_mul,
    hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne bP hbP i hconc,
    coeff_coeff_bigradedExtPoincarePowerSeries]
  exact congrArg _ (extLinearEquivOfIso k (Iso.refl M)
    ((GradedModuleCat.shiftPowIso 𝒜 j).app (S i).obj) n).finrank_eq.symm

include he he₀ hne hbP in
/-- With normalized diagonal dimension `dᵢ = 1`, the Betti Poincaré series of a minimal resolution
at `Pᵢ` is the bigraded Ext Poincaré series of `M` against `Sᵢ`. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) = 1)
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      hr.isGradedExtInternallyFinite hconc) :
    r.bettiPoincarePowerSeries bP i =
      bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
  simpa only [hself, map_one, one_mul] using
    hr.C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP i hconc h

include he he₀ hne hbP in
/-- A coefficient of the Betti Poincaré series of a minimal resolution at `Pᵢ` with `dᵢ ≠ 0`
vanishes exactly when the corresponding Ext group into the shifted target vanishes. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) (n : ℕ) (j : ℤ) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 ↔
      Subsingleton (Ext.{uA} M ((S i).obj.shiftObj j) n) := by
  let hfin := hr.isGradedExtInternallyFinite hconc
  have : FiniteDimensional k (GradedExt.{uA} (GradedModuleCat.shift 𝒜) M (S i).obj n j) :=
    (hfin.finiteLaurentSupport n).finiteDimensional j
  have : FiniteDimensional k (Ext.{uA} M ((S i).obj.shiftObj j) n) :=
    Module.Finite.equiv (extLinearEquivOfIso k (Iso.refl M)
      ((GradedModuleCat.shiftPowIso 𝒜 j).app (S i).obj) n)
  obtain ⟨c, hd⟩ : ∃ c : ℤ, (S i).obj.smulGradedDimension (e i) = C c :=
    ⟨_, GradedModuleCat.smulGradedDimension_eq_C_of_concentrated (e := e i) _ hconc⟩
  have hcoeff := hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne
    bP hbP i hconc n j
  rw [hd, coeff_C_mul] at hcoeff
  have hc : c ≠ 0 := fun h0 ↦ hself (by rw [hd, h0, map_zero])
  rw [← Module.finrank_zero_iff (R := k), ← Int.natCast_eq_zero, ← hcoeff, mul_eq_zero,
    or_iff_right hc]

include he he₀ hne hbP in
/-- The coefficients of the Betti Poincaré series of a minimal resolution at `Pᵢ` with
`dᵢ = gdim(eᵢ • Sᵢ) ≠ 0` are nonnegative. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_nonneg (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) (n : ℕ) (j : ℤ) :
    0 ≤ (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j := by
  have hcoeff := hr.coeff_smulGradedDimension_mul_coeff_bettiPoincarePowerSeries S he he₀ hI hne
    bP hbP i hconc n j
  rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc, coeff_C_mul]
    at hcoeff
  exact nonneg_of_mul_nonneg_right (hcoeff ▸ Int.natCast_nonneg _)
    (Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc hself))

include he he₀ hne hbP in
/-- **The Betti Poincaré series of a bounded-below minimal resolution vanishes below a shifted
diagonal.** If `M` vanishes in internal degrees below `c` and the terms of `r` have gradings bounded
below, then at every `Pᵢ` with `dᵢ ≠ 0` the coefficient of `qʲ tⁿ` vanishes whenever `j < c + n`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt_of_bddBelow (hr : r.IsMinimal)
    {c : ℤ} (hM : ∀ p < c, M.grading.piece p = ⊥)
    (hb : ∀ m, ∃ b : ℤ, ∀ p < b, (r.grading m).piece p = ⊥)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) {n : ℕ} {j : ℤ} (hjn : j < c + n) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 := by
  rw [hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff S he he₀ hI hne bP hbP i hconc hself]
  exact GradedModuleCat.subsingleton_gradedExt_iff_subsingleton_ext_shiftObj.mp
    (hr.subsingleton_gradedExt_of_lt_of_bddBelow hM hb hconc hjn)

include he he₀ hne hbP in
/-- Over a nonnegatively graded algebra, if `M` vanishes in internal degrees below `c`, then at
every `Pᵢ` with `dᵢ ≠ 0` the coefficient of `qʲ tⁿ` in the Betti Poincaré series of `r` vanishes
whenever `j < c + n`, without assuming `A` is finite-dimensional over `k`. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt_of_nonneg (hr : r.IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {c : ℤ} (hM : ∀ p < c, M.grading.piece p = ⊥)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) {n : ℕ} {j : ℤ} (hjn : j < c + n) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 :=
  hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt_of_bddBelow S he he₀ hI hne bP hbP hM
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg) i hconc hself hjn

include he he₀ hne hbP in
/-- **The Betti Poincaré series of a minimal resolution with `k`-finite terms vanishes below a
shifted diagonal**, without assuming the algebra grading is nonnegative. -/
theorem IsMinimal.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt
    [∀ n, Module.Finite k (r.X n)] (hr : r.IsMinimal) {c : ℤ}
    (hM : ∀ p < c, M.grading.piece p = ⊥) (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) {n : ℕ} {j : ℤ} (hjn : j < c + n) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 :=
  hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt_of_bddBelow S he he₀ hI hne bP hbP hM
    (fun m ↦
      let ⟨b, hb⟩ := (r.grading m).finite_piece_ne_bot.bddBelow
      ⟨b, fun _ hp ↦ by by_contra hne; exact absurd (hb hne) (not_le.mpr hp)⟩)
    i hconc hself hjn

include he he₀ hne hbP in
/-- For a bounded-below minimal resolution of a module vanishing in negative internal degrees, the
Betti Poincaré series at every `Pᵢ` with `dᵢ ≠ 0` satisfies `Bigraded.HasEulerPowerSeries`. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries_of_bddBelow (hr : r.IsMinimal)
    (hM : ∀ p < 0, M.grading.piece p = ⊥)
    (hb : ∀ m, ∃ b : ℤ, ∀ p < b, (r.grading m).piece p = ⊥)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) :
    Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun _ _ han ↦
    hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt_of_bddBelow S he he₀ hI hne bP hbP hM hb
      i hconc hself (by omega)

include he he₀ hne hbP in
/-- Over a nonnegatively graded algebra, the Betti Poincaré series of a minimal resolution of a
module vanishing in negative internal degrees satisfies `Bigraded.HasEulerPowerSeries` at every
`Pᵢ` with `dᵢ ≠ 0`, without assuming `A` is finite-dimensional over `k`. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries_of_nonneg (hr : r.IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hM : ∀ p < 0, M.grading.piece p = ⊥)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) :
    Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i) :=
  hr.hasEulerPowerSeries_bettiPoincarePowerSeries_of_bddBelow S he he₀ hI hne bP hbP hM
    (fun _ ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg) i hconc hself

include he he₀ hne hbP in
/-- The Betti Poincaré series of a minimal resolution with `k`-finite terms of a module vanishing in
negative internal degrees, at every `Pᵢ` with `dᵢ = gdim(eᵢ • Sᵢ) ≠ 0`, has an Alexander-graded
Euler power series: its value at `t = -1` is defined coefficientwise in `q`. -/
theorem IsMinimal.hasEulerPowerSeries_bettiPoincarePowerSeries
    [∀ n, Module.Finite k (r.X n)] (hr : r.IsMinimal)
    (hM : ∀ p < 0, M.grading.piece p = ⊥) (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0) :
    Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i) :=
  Bigraded.HasEulerPowerSeries.of_lowerTriangular fun _ _ han ↦
    hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_lt S he he₀ hI hne bP hbP hM i hconc hself
      (by omega)

include he he₀ hne hbP in
/-- At `t = -1`, `dᵢ = dim_k(eᵢ • (Sᵢ)₀)` times the Alexander-graded Euler power series of
`r.bettiPoincarePowerSeries bP i` equals the Alexander-graded Euler power series of
`bigradedExtPoincarePowerSeries`, for any `HasEulerPowerSeries` witnesses. -/
theorem IsMinimal.C_finrank_mul_eulerPowerSeries (hr : r.IsMinimal)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : Bigraded.HasEulerPowerSeries (r.bettiPoincarePowerSeries bP i))
    (h : IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) M (S i).obj :=
      hr.isGradedExtInternallyFinite hconc)
    (hE : Bigraded.HasEulerPowerSeries
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h)) :
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        Bigraded.eulerPowerSeries hB =
      Bigraded.eulerPowerSeries hE := by
  have hEq : PowerSeries.C (C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ)) *
      r.bettiPoincarePowerSeries bP i =
        bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) h := by
    rw [← GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc]
    exact hr.C_smulGradedDimension_mul_bettiPoincarePowerSeries S he he₀ hI hne bP hbP i hconc h
  rw [← Bigraded.eulerPowerSeries_C_mul hB _ (hB.C_mul _)]
  exact Bigraded.eulerPowerSeries_congr _ _ hEq

include he₀ hne hbP in
/-- For any linear resolution `r` (without assuming minimality, finite-dimensionality of `A`, or a
nonnegative algebra grading), all off-diagonal coefficients of `r.bettiPoincarePowerSeries bP i`
vanish when `gdim(eᵢ • Sᵢ) ≠ 0`. -/
theorem IsLinear.coeff_coeff_bettiPoincarePowerSeries_eq_zero_of_ne (hr : r.IsLinear)
    (i : I) (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : (S i).obj.smulGradedDimension (e i) ≠ 0)
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

include he he₀ hne hbP in
/-- **Matrix Betti–Ext comparison**: when `gdim(eᵢ • Sᵢ) = 1` for all `i`, the transpose of the
Betti Poincaré matrix of minimal resolutions `rⱼ` of finite-dimensional degree-zero `Sⱼ` equals
`bigradedExtPoincarePowerSeriesMatrix`. -/
theorem bettiPoincarePowerSeriesMatrix_transpose_eq_bigradedExtPoincarePowerSeriesMatrix
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜)
      (S i).obj (S j).obj :=
      fun i j ↦ (hr i).isGradedExtInternallyFinite (hconc j)) :
    (bettiPoincarePowerSeriesMatrix r bP)ᵀ =
      bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj) h :=
  Matrix.ext fun j i ↦ by
    rw [Matrix.transpose_apply, bettiPoincarePowerSeriesMatrix_apply,
      bigradedExtPoincarePowerSeriesMatrix_apply]
    exact (hr j).bettiPoincarePowerSeries_eq_bigradedExtPoincarePowerSeries
      S he he₀ hI hne bP hbP i (hconc i) (hself i) (h j i)

end BettiExtComparison

/-! ### Diagonal-support characterizations of linear resolutions -/

section Linearity

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k (𝒜 0)]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) [∀ i, Module.Finite k (S i).obj] {e : I → A}
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
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r.X n)]

include he he₀ hne hbP hconc in
/-- **A minimal resolution is linear exactly when its Betti Poincaré series are supported on the
diagonal.** Over a nonnegatively graded algebra with finite-dimensional degree-zero part `𝒜 0`, let
the `Sᵢ` represent every finite simple graded module concentrated in degree zero, with every
`dᵢ = gdim(eᵢ • Sᵢ)` nonzero. Then a minimal resolution with finitely generated `A`-module terms is
linear if and only if the coefficient of `qʲ tⁿ` in each Betti Poincaré series vanishes for
`n ≠ j`. Neither finite-dimensionality of `A` nor a cohomological bound is assumed. -/
theorem IsMinimal.isLinear_iff_diagonal_bettiPoincarePowerSeries (hr : r.IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hS : IsExhaustiveGradedSimpleFamily S)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) :
    r.IsLinear ↔ ∀ i (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
      (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff j = 0 := by
  simp_rw [hr.coeff_coeff_bettiPoincarePowerSeries_eq_zero_iff S he he₀ hI hne bP hbP _
    (hconc _) (hself _)]
  exact hr.isLinear_iff_subsingleton_ext_shiftObj_family_of_moduleFinite hneg hS hconc

end GradedProjectiveResolution

include he he₀ hne hbP hconc in
/-- **Linearity of a family of minimal resolutions is diagonal support of the Betti Poincaré
matrix.** Over a nonnegatively graded algebra with finite-dimensional degree-zero part `𝒜 0`, let
the `Sᵢ` represent every finite simple graded module concentrated in degree zero, with every
`dᵢ = gdim(eᵢ • Sᵢ)` nonzero. Minimal resolutions with finitely generated terms of a family of
graded modules are all linear if and only if every entry of their Betti Poincaré matrix has its
coefficient of `qᵖ tⁿ` vanish for `n ≠ p`. -/
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

include he he₀ hne hbP hconc in
/-- Given any minimal resolutions `r j` of an exhaustive degree-zero simple family `S` with finitely
generated terms over a nonnegatively graded algebra with `Module.Finite k (𝒜 0)` and
`gdim(eᵢ • Sᵢ) ≠ 0`, every `S j` admits **some** linear resolution if and only if
`bettiPoincarePowerSeriesMatrix r bP` is diagonally supported. -/
theorem forall_exists_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)] (hr : ∀ j, (r j).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hS : IsExhaustiveGradedSimpleFamily S)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) :
    (∀ j, ∃ r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S j).obj.grading, r'.IsLinear) ↔
      ∀ i j (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
        (PowerSeries.coeff n (bettiPoincarePowerSeriesMatrix r bP i j)).coeff p = 0 := by
  rw [← forall_isLinear_iff_diagonal_bettiPoincarePowerSeriesMatrix
    S he he₀ hI hne bP hbP hconc r hr hneg hS hself]
  refine ⟨fun hlin j ↦ ?_, fun hlin j ↦ ⟨r j, hlin j⟩⟩
  apply ((hr j).isLinear_iff_subsingleton_ext_shiftObj_simple_of_moduleFinite hneg).mpr
  intro N _ _ hNzero n p hnp
  obtain ⟨r', hr'⟩ := hlin j
  exact hr'.subsingleton_ext_shiftObj_of_ne hNzero n p hnp

end Linearity

end TauCeti
