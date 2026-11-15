/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution

/-!
# Betti Poincaré series and matrices of graded projective resolutions

Let `A` be a graded `k`-algebra with grading `𝒜 : ℤ → Submodule k A`, and let `bP` be a basis of
the graded projective Grothendieck group `K₀^gr(proj A)` over `ℤ[q,q⁻¹]`. For a graded `A`-module
`M` equipped with a concrete graded projective resolution `r` whose terms are finitely generated
over `A`, each term `Pₙ` determines a class `[Pₙ] ∈ K₀^gr(proj A)` and hence coordinate Laurent
polynomials `bP.repr [Pₙ] i ∈ ℤ[q,q⁻¹]`.

This file packages these projective coordinates into:

* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries`: for each `i : I`, the formal
  power series `∑ n ≥ 0, (bP.repr [Pₙ] i) tⁿ ∈ (ℤ[q,q⁻¹])⟦t⟧` recording the graded multiplicities
  of the `i`th projective basis element across all homological degrees.
* `TauCeti.bettiPoincarePowerSeriesMatrix`: for an indexed family of resolved modules `Mⱼ`, the
  matrix with rows indexed by the projective basis `bP` and columns indexed by `j`, whose `(i, j)`
  entry is `(r j).bettiPoincarePowerSeries bP i`.

The definition itself uses neither a field, a grading decomposition, nor minimality, and requires
no cohomological vanishing bound. Under the shift normalization `[P{d}] = qᵈ [P]` of
`TauCeti.LaurentK0`, shifting a resolution to `M{d}` multiplies every Betti Poincaré series by `qᵈ`
(and shifting to `M{1}` multiplies it by `q`). When `𝒜` decomposes `A`, termwise uniqueness of
bounded-below minimal resolutions (`TauCeti.GradedProjectiveResolution.IsMinimal.termObjIso`) makes
the Betti Poincaré series and matrix independent of the chosen minimal resolutions — unconditionally
for finitely generated terms when `𝒜` is nonnegatively graded.

## Main definitions

* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries`: projective-coordinate formal power
  series of a graded projective resolution with finitely generated terms.
* `TauCeti.bettiPoincarePowerSeriesMatrix`: matrix of Betti Poincaré formal power series of a
  family of resolved graded modules.

## Main results

* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries_shiftObj` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_shiftObj_eq_of_neg`:
  shifting `M` to `M{d}` multiplies the Betti Poincaré series by `qᵈ`.
* `TauCeti.GradedProjectiveResolution.bettiPoincarePowerSeries_eq_coe_trunc`: for a resolution
  whose terms vanish from homological degree `N` onward, the Betti Poincaré power series equals its
  polynomial truncation.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincarePowerSeries_eq_of_neg`, and
  `TauCeti.bettiPoincarePowerSeriesMatrix_eq_of_neg`: minimal graded projective resolutions yield
  the same Betti Poincaré series and matrix.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI uJ

section Basic

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
  [∀ n, Module.Finite A (r.X n)]

/-- The **Betti Poincaré formal power series** of a graded projective resolution `r` with finitely
generated terms, relative to a basis `bP` of `K₀^gr(proj A)`: for `i : I`, the coefficient of `tⁿ`
is the `i`th `ℤ[q,q⁻¹]`-coordinate of `[Pₙ]`. No cohomological bound or minimality is assumed. -/
def bettiPoincarePowerSeries (i : I) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦
    bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n)) i

/-- The coefficient of `tⁿ` in `r.bettiPoincarePowerSeries bP i` is the `i`th projective-basis
coordinate of `[Pₙ]`. -/
@[simp]
theorem coeff_bettiPoincarePowerSeries (n : ℕ) (i : I) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincarePowerSeries]

/-- The bidegree `(n, p)` integer coefficient `[qᵖ][tⁿ]` of `r.bettiPoincarePowerSeries bP i`. -/
theorem coeff_coeff_bettiPoincarePowerSeries (n : ℕ) (p : ℤ) (i : I) :
    (PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i)).coeff p =
      (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)) i).coeff p := by
  rw [coeff_bettiPoincarePowerSeries]

/-- The constant term (`n = 0`) of `r.bettiPoincarePowerSeries bP i` is the `i`th projective-basis
coordinate of `[P₀]`. -/
@[simp]
theorem constantCoeff_bettiPoincarePowerSeries (i : I) :
    PowerSeries.constantCoeff (r.bettiPoincarePowerSeries bP i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm 0)) i := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_bettiPoincarePowerSeries]

/-- Over a finite index type, the `tⁿ` coefficients of `r.bettiPoincarePowerSeries bP` reconstruct
the Grothendieck class of the `n`th resolution term in `K₀^gr(proj A)`. -/
theorem of_finiteProjectiveTerm_eq_sum_bettiPoincarePowerSeries [Fintype I] (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n) =
      ∑ i, PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) • bP i := by
  conv_lhs =>
    rw [← bP.sum_repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n))]
  simp only [coeff_bettiPoincarePowerSeries]

/-- A subsingleton resolution term vanishes in `K₀^gr(proj A)`. -/
theorem of_finiteProjectiveTerm_eq_zero_of_subsingleton (n : ℕ) [Subsingleton (r.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n) = 0 := by
  have : Subsingleton (r.finiteProjectiveTerm n).obj := by
    rw [finiteProjectiveTerm_obj]
    exact ‹Subsingleton (r.X n)›
  have hzero : Limits.IsZero (r.finiteProjectiveTerm n) :=
    (Limits.IsZero.iff_id_eq_zero _).mpr <|
      ObjectProperty.hom_ext _ (GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦
        Subsingleton.elim _ _))
  rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hzero, map_zero]

/-- If the `n`th term of `r` is a subsingleton, the `n`th coefficient of every Betti Poincaré
series vanishes. -/
theorem coeff_bettiPoincarePowerSeries_eq_zero_of_subsingleton (n : ℕ) [Subsingleton (r.X n)]
    (i : I) :
    PowerSeries.coeff n (r.bettiPoincarePowerSeries bP i) = 0 := by
  rw [coeff_bettiPoincarePowerSeries, r.of_finiteProjectiveTerm_eq_zero_of_subsingleton n,
    map_zero, Finsupp.zero_apply]

/-- If the terms of `r` vanish from homological degree `N` onward, each Betti Poincaré power series
coincides with its polynomial truncation below `N`. -/
theorem bettiPoincarePowerSeries_eq_coe_trunc {N : ℕ}
    (hN : ∀ n ≥ N, Subsingleton (r.X n)) (i : I) :
    r.bettiPoincarePowerSeries bP i =
      (PowerSeries.trunc N (r.bettiPoincarePowerSeries bP i) :
        PowerSeries (LaurentPolynomial ℤ)) := by
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · have := hN n (Nat.le_of_not_lt hn)
    exact r.coeff_bettiPoincarePowerSeries_eq_zero_of_subsingleton bP n i

/-- If `Pₙ` is graded-isomorphic to an internal shift `P{d}` of a projective representing `bP j`,
the `n`th Betti coefficient at `i` is `qᵈ` for `i = j` and `0` otherwise. -/
theorem coeff_bettiPoincarePowerSeries_of_iso_shiftObj [DecidableEq I] {n : ℕ}
    {P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory} {j : I}
    (hbP : bP j = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P)
    {d : ℤ} (e : r.termObj n ≅ P.obj.shiftObj d) (i : I) :
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
theorem of_finiteProjectiveTerm_shiftObj (d : ℤ) (n : ℕ) :
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
theorem bettiPoincarePowerSeries_shiftObj (d : ℤ) (i : I) :
    (r.shiftObj d).bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d : LaurentPolynomial ℤ) * r.bettiPoincarePowerSeries bP i := by
  apply PowerSeries.ext
  intro n
  rw [coeff_bettiPoincarePowerSeries, of_finiteProjectiveTerm_shiftObj, map_smul,
    Finsupp.smul_apply, smul_eq_mul, PowerSeries.coeff_C_mul, coeff_bettiPoincarePowerSeries]

/-- Shifting a resolution of `M` by one internal degree (`M{1}`) multiplies each Betti Poincaré
power series by `q`. -/
theorem bettiPoincarePowerSeries_shiftObj_one (i : I) :
    (r.shiftObj 1).bettiPoincarePowerSeries bP i =
      PowerSeries.C (T 1 : LaurentPolynomial ℤ) * r.bettiPoincarePowerSeries bP i :=
  r.bettiPoincarePowerSeries_shiftObj bP 1 i

end GradedProjectiveResolution

/-- The **Betti Poincaré power-series matrix** of a family of graded modules `M : J → ...` equipped
with graded projective resolutions `r j` having finitely generated terms, relative to a projective
basis `bP` indexed by `I`. Rows are indexed by `bP` and columns by `J`, so the `(i, j)` entry is
`(r j).bettiPoincarePowerSeries bP i`. -/
def bettiPoincarePowerSeriesMatrix {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] :
    Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  fun i j ↦ (r j).bettiPoincarePowerSeries bP i

/-- The `(i, j)` entry of `bettiPoincarePowerSeriesMatrix bP r` is the `i`th Betti Poincaré series
of `r j`. -/
@[simp]
theorem bettiPoincarePowerSeriesMatrix_apply {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) :
    bettiPoincarePowerSeriesMatrix bP r i j = (r j).bettiPoincarePowerSeries bP i :=
  (rfl)

/-- Shifting each resolved module `M j` by `d j` multiplies the `j`th column of the Betti Poincaré
matrix by `q^{d j}`. -/
theorem bettiPoincarePowerSeriesMatrix_shiftObj {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (d : J → ℤ) (i : I) (j : J) :
    bettiPoincarePowerSeriesMatrix bP (fun j ↦ (r j).shiftObj (d j)) i j =
      PowerSeries.C (T (d j) : LaurentPolynomial ℤ) *
        bettiPoincarePowerSeriesMatrix bP r i j :=
  (r j).bettiPoincarePowerSeries_shiftObj bP (d j) i

end Basic

/-! ### Independence of chosen minimal resolutions -/

section Minimal

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜]
  {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
  [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]

/-- Any two minimal graded projective resolutions of `M` with finitely generated bounded-below terms
have isomorphic finite-projective terms in every homological degree. -/
def IsMinimal.finiteProjectiveTermIso
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) (n : ℕ) :
    r₁.finiteProjectiveTerm n ≅ r₂.finiteProjectiveTerm n :=
  (gradedFiniteProjectiveModules 𝒜).fullyFaithfulι.preimageIso
    (eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫ hr₁.termObjIso hr₂ hb₁ hb₂ n ≪≫
      eqToIso (r₂.finiteProjectiveTerm_obj n).symm)

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions of `M` with
finitely generated terms have isomorphic finite-projective terms in every homological degree. -/
def IsMinimal.finiteProjectiveTermIsoOfModuleFinite
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (n : ℕ) :
    r₁.finiteProjectiveTerm n ≅ r₂.finiteProjectiveTerm n :=
  (gradedFiniteProjectiveModules 𝒜).fullyFaithfulι.preimageIso
    (eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫ hr₁.termObjIsoOfModuleFinite hneg hr₂ n ≪≫
      eqToIso (r₂.finiteProjectiveTerm_obj n).symm)

/-- Any two minimal graded projective resolutions of `M` with finitely generated bounded-below terms
have equal term classes in `K₀^gr(proj A)` in every homological degree. -/
theorem IsMinimal.of_finiteProjectiveTerm_eq
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  LaurentK0.of_congr.{uA} _ (hr₁.finiteProjectiveTermIso hr₂ hb₁ hb₂ n)

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions of `M` with
finitely generated terms have equal term classes in `K₀^gr(proj A)` in every homological degree. -/
theorem IsMinimal.of_finiteProjectiveTerm_eq_of_neg
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (n : ℕ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  LaurentK0.of_congr.{uA} _ (hr₁.finiteProjectiveTermIsoOfModuleFinite hneg hr₂ n)

/-- **Minimal-resolution independence of the Betti Poincaré series**: any two minimal graded
projective resolutions of `M` with finitely generated bounded-below terms define the same Betti
Poincaré formal power series. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) (i : I) :
    r₁.bettiPoincarePowerSeries bP i = r₂.bettiPoincarePowerSeries bP i := by
  ext n
  simp only [coeff_bettiPoincarePowerSeries, hr₁.of_finiteProjectiveTerm_eq hr₂ hb₁ hb₂ n]

/-- **Minimal-resolution independence over a nonnegatively graded algebra**: any two minimal graded
projective resolutions of `M` with finitely generated terms define the same Betti Poincaré formal
power series. -/
theorem IsMinimal.bettiPoincarePowerSeries_eq_of_neg
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (i : I) :
    r₁.bettiPoincarePowerSeries bP i = r₂.bettiPoincarePowerSeries bP i := by
  ext n
  simp only [coeff_bettiPoincarePowerSeries, hr₁.of_finiteProjectiveTerm_eq_of_neg hneg hr₂ n]

/-- Over a nonnegatively graded algebra, the Betti Poincaré series of **any** minimal resolution
`r'` of `M{d}` with finitely generated terms equals `qᵈ` times that of any minimal resolution `r₁`
of `M` with finitely generated terms. -/
theorem IsMinimal.bettiPoincarePowerSeries_shiftObj_eq_of_neg {d : ℤ}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r'.X n)]
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr' : r'.IsMinimal) (hr₁ : r₁.IsMinimal) (i : I) :
    r'.bettiPoincarePowerSeries bP i =
      PowerSeries.C (T d : LaurentPolynomial ℤ) * r₁.bettiPoincarePowerSeries bP i :=
  (hr'.bettiPoincarePowerSeries_eq_of_neg bP hneg ((r₁.isMinimal_shiftObj_iff d).mpr hr₁) i).trans
    (r₁.bettiPoincarePowerSeries_shiftObj bP d i)

end GradedProjectiveResolution

/-- Any two families of minimal graded projective resolutions with finitely generated bounded-below
terms define the same Betti Poincaré power-series matrix. -/
theorem bettiPoincarePowerSeriesMatrix_eq {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    {r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal)
    (hb₁ : ∀ j n, ∃ b : ℤ, ∀ p < b, ((r₁ j).grading n).piece p = ⊥)
    (hb₂ : ∀ j n, ∃ b : ℤ, ∀ p < b, ((r₂ j).grading n).piece p = ⊥) :
    bettiPoincarePowerSeriesMatrix bP r₁ = bettiPoincarePowerSeriesMatrix bP r₂ :=
  Matrix.ext fun i j ↦ (hr₁ j).bettiPoincarePowerSeries_eq bP (hr₂ j) (hb₁ j) (hb₂ j) i

/-- Over a nonnegatively graded algebra, any two families of minimal graded projective resolutions
with finitely generated terms define the same Betti Poincaré power-series matrix. -/
theorem bettiPoincarePowerSeriesMatrix_eq_of_neg {J : Type uJ}
    {M : J → GradedModuleCat.{uA} 𝒜}
    {r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal) :
    bettiPoincarePowerSeriesMatrix bP r₁ = bettiPoincarePowerSeriesMatrix bP r₂ :=
  Matrix.ext fun i j ↦ (hr₁ j).bettiPoincarePowerSeries_eq_of_neg bP hneg (hr₂ j) i

end Minimal

end TauCeti
