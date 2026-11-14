/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.Bigraded.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution

/-!
# Graded Betti Poincaré series and matrices of projective resolutions

Let `A` be a graded `k`-algebra and `bP` a `ℤ[q,q⁻¹]`-basis of the Laurent Grothendieck group
`K₀^gr(proj A)` of finitely generated graded projective `A`-modules. A graded projective
resolution `r` of `M` whose terms are finitely generated `A`-modules records, in each homological
degree `n : ℕ`, a class `[Pₙ] ∈ K₀^gr(proj A)`. Expanding `[Pₙ]` in the basis `bP` produces
Laurent polynomials `bP.repr [Pₙ] i = ∑_d β_{n, d}^i q^d`, which assemble into the formal power
series

`B_i(M; q, t) = ∑_{n ≥ 0} (bP.repr [Pₙ] i) tⁿ ∈ (ℤ[q,q⁻¹])⟦t⟧`.

For a family of graded modules `Mⱼ` with chosen resolutions `rⱼ`, these series form the **Betti
Poincaré matrix** `B(q, t) ∈ Matrix I J (PowerSeries (LaurentPolynomial ℤ))` with `(i, j)`
entry `B_i(Mⱼ; q, t)`.

Because minimal graded projective resolutions with bounded-below terms are unique up to termwise
graded isomorphism (`TauCeti.GradedProjectiveResolution.IsMinimal.termObjIso`), `[Pₙ]` and hence
`B_i(M; q, t)` depend only on `M` and `bP` whenever `r` is minimal — in particular whenever `A` is
nonnegatively decomposed, since finitely generated `A`-modules are then automatically bounded below.
Regrading `M` to `M{d}` shifts every resolution term to `Pₙ{d}`, multiplying `B_i(M; q, t)` by
`q^d` (`PowerSeries.C (T d)`).

## Main definitions

* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries`: the `i`th graded Betti Poincaré formal
  power series `∑_n (bP.repr [Pₙ] i) tⁿ` of a resolution with finitely generated terms.
* `TauCeti.bettiPoincareMatrix`: the `I × J` matrix of graded Betti Poincaré series of a family of
  resolutions.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_bddBelow`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq`, and
  `TauCeti.bettiPoincareMatrix_congr`: minimal graded projective resolutions have the same Betti
  series in every projective basis.
* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries_shiftObj`,
  `TauCeti.GradedProjectiveResolution.bettiPoincareSeries_shiftObj_one`, and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_shiftObj_eq`: shifting `M` to
  `M{d}` (in particular `M{1}`) multiplies its Betti Poincaré series by `q^d` (`q`).
* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries_eq_sum_of_forall_subsingleton` and
  `TauCeti.GradedProjectiveResolution.maslovEulerPowerSeries_bettiPoincareSeries_eq_sum`:
  polynomial truncation and the `q = 1, X ↦ -X` specialization for finite resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  **1836**, Springer (2004), Section 2.3.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *Journal of Combinatorial Theory,
  Series A* **185** (2022), Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe uk uA uI uJ

section Definitions

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- **The graded Betti Poincaré formal power series** of a graded projective resolution `r` with
finitely generated `A`-module terms, along the `i`th element of a projective Grothendieck basis
`bP`: its `n`th power-series coefficient is the Laurent polynomial `bP.repr [r.termObj n] i`. -/
def bettiPoincareSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) :
    PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦ bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i

/-- The `n`th coefficient of `r.bettiPoincareSeries bP i` is the `i`th projective coordinate of the
`n`th resolution term. -/
@[simp]
theorem coeff_bettiPoincareSeries
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincareSeries bP i) =
      bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincareSeries]

/-- Shifting a resolution of `M` to `M{d}` shifts each bundled finite projective term by `d`. -/
@[simp]
theorem finiteProjectiveTerm_shiftObj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (d : ℤ) (n : ℕ) :
    (r.shiftObj d).finiteProjectiveTerm n =
      ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
        gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩ :=
  ObjectProperty.FullSubcategory.ext (by simp)

/-- **Shift law for graded Betti Poincaré series.** Shifting `r` from `M` to `M{d}` multiplies its
Betti Poincaré series by `q^d` (`PowerSeries.C (T d)`). -/
@[simp]
theorem bettiPoincareSeries_shiftObj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (d : ℤ) (i : I) :
    (r.shiftObj d).bettiPoincareSeries bP i =
      PowerSeries.C (T d) * r.bettiPoincareSeries bP i := by
  apply PowerSeries.ext
  intro n
  rw [coeff_bettiPoincareSeries, PowerSeries.coeff_C_mul, coeff_bettiPoincareSeries,
    finiteProjectiveTerm_shiftObj, laurentK0_projective_of_shiftObj, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

/-- Shifting `r` from `M` to `M{1}` multiplies its Betti Poincaré series by `q`
(`PowerSeries.C (T 1)`). -/
theorem bettiPoincareSeries_shiftObj_one
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) :
    (r.shiftObj 1).bettiPoincareSeries bP i =
      PowerSeries.C (T 1) * r.bettiPoincareSeries bP i :=
  r.bettiPoincareSeries_shiftObj bP 1 i

/-- Shifting `r` to `M{d}` translates internal Betti coefficients by `d`:
`β_{n, p}^i(M{d}) = β_{n, p - d}^i(M)`. -/
theorem coeff_coeff_bettiPoincareSeries_shiftObj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (d : ℤ) (i : I) (n : ℕ) (p : ℤ) :
    (PowerSeries.coeff n ((r.shiftObj d).bettiPoincareSeries bP i)).coeff p =
      (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff (p - d) := by
  rw [bettiPoincareSeries_shiftObj, PowerSeries.coeff_C_mul, coeff_T_mul]

/-- A subsingleton resolution term contributes zero to the Betti Poincaré series. -/
theorem coeff_bettiPoincareSeries_eq_zero_of_subsingleton
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) {n : ℕ} (hn : Subsingleton (r.X n)) :
    PowerSeries.coeff n (r.bettiPoincareSeries bP i) = 0 := by
  have hsub : Subsingleton (r.finiteProjectiveTerm n).obj := by
    rw [r.finiteProjectiveTerm_obj n]
    exact hn
  have hz : IsZero (r.finiteProjectiveTerm n) :=
    (IsZero.iff_id_eq_zero _).2 <| ObjectProperty.hom_ext _ <|
      GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)
  rw [coeff_bettiPoincareSeries, ← LaurentK0.ofExactK0_exactK0_of.{uA},
    ExactK0.of_eq_zero_of_isZero.{uA} hz, map_zero, map_zero, Finsupp.zero_apply]

/-- For a resolution whose terms vanish from homological degree `b` onward, the Betti Poincaré
series is the finite polynomial sum `∑_{n < b} (bP.repr [Pₙ] i) Xⁿ`. -/
theorem bettiPoincareSeries_eq_sum_of_forall_subsingleton
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) (b : ℕ)
    (hb : ∀ n, b ≤ n → Subsingleton (r.X n)) :
    r.bettiPoincareSeries bP i =
      ∑ n ∈ Finset.range b,
        PowerSeries.C (PowerSeries.coeff n (r.bettiPoincareSeries bP i)) * PowerSeries.X ^ n := by
  apply PowerSeries.ext
  intro m
  rw [map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  by_cases hmb : m < b
  · rw [Finset.sum_ite_eq (Finset.range b) m, ite_eq_left (Finset.mem_range.mpr hmb)]
  · rw [Finset.sum_ite_eq (Finset.range b) m, ite_eq_right (Finset.mem_range.not.mpr hmb),
      r.coeff_bettiPoincareSeries_eq_zero_of_subsingleton bP i (hb m (Nat.le_of_not_lt hmb))]

/-- Applying `Bigraded.maslovEulerPowerSeries` (`q = 1`, `X ↦ -X`) to a resolution whose terms
vanish from homological degree `b` onward yields the finite polynomial sum
`∑_{n < b} (-1)ⁿ (laurentEval 1 [tⁿ] B_i) Xⁿ` in `PowerSeries ℤ`. -/
theorem maslovEulerPowerSeries_bettiPoincareSeries_eq_sum
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) (b : ℕ)
    (hb : ∀ n, b ≤ n → Subsingleton (r.X n)) :
    Bigraded.maslovEulerPowerSeries (r.bettiPoincareSeries bP i) =
      ∑ n ∈ Finset.range b,
        PowerSeries.C ((-1 : ℤ) ^ n *
          laurentEval (1 : ℤˣ) (PowerSeries.coeff n (r.bettiPoincareSeries bP i))) *
          PowerSeries.X ^ n := by
  apply PowerSeries.ext
  intro m
  rw [Bigraded.coeff_maslovEulerPowerSeries, map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  by_cases hmb : m < b
  · rw [Finset.sum_ite_eq (Finset.range b) m, ite_eq_left (Finset.mem_range.mpr hmb)]
  · rw [Finset.sum_ite_eq (Finset.range b) m, ite_eq_right (Finset.mem_range.not.mpr hmb),
      r.coeff_bettiPoincareSeries_eq_zero_of_subsingleton bP i (hb m (Nat.le_of_not_lt hmb)),
      map_zero, mul_zero]

end GradedProjectiveResolution

/-- **The Betti Poincaré matrix** of a family of graded projective resolutions `r j` of `M j` along
a projective Grothendieck basis `bP`: its `(i, j)` entry is `(r j).bettiPoincareSeries bP i`, so
rows are indexed by the projective basis `I` and columns by the resolved family `J`. -/
def bettiPoincareMatrix {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] :
    Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  Matrix.of fun i j ↦ (r j).bettiPoincareSeries bP i

/-- The `(i, j)` entry of `bettiPoincareMatrix bP r` is `(r j).bettiPoincareSeries bP i`. -/
@[simp]
theorem bettiPoincareMatrix_apply {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) :
    bettiPoincareMatrix bP r i j = (r j).bettiPoincareSeries bP i :=
  (rfl)

/-- The `n`th power-series coefficient of `(bettiPoincareMatrix bP r) i j` is the `i`th projective
coordinate of `(r j).finiteProjectiveTerm n`. -/
theorem coeff_bettiPoincareMatrix {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) (n : ℕ) :
    PowerSeries.coeff n (bettiPoincareMatrix bP r i j) =
      bP.repr (LaurentK0.of.{uA} _ ((r j).finiteProjectiveTerm n)) i := by
  simp

end Definitions

section Uniqueness

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜]
  {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- Two minimal graded projective resolutions of `M` have the same `n`th projective Grothendieck
class whenever both `n`th terms are bounded below. -/
theorem IsMinimal.laurentK0_of_finiteProjectiveTerm_eq_of_bddBelow
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) {n : ℕ}
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)]
    (b₁ b₂ : ℤ)
    (hbelow₁ : ∀ p < b₁, (r₁.grading n).piece p = ⊥)
    (hbelow₂ : ∀ p < b₂, (r₂.grading n).piece p = ⊥) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  LaurentK0.of_congr _
    (ObjectProperty.isoMk _ (eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫
      hr₁.termObjIso hr₂ b₁ b₂ hbelow₁ hbelow₂ ≪≫
      eqToIso (r₂.finiteProjectiveTerm_obj n).symm))

/-- Over a nonnegatively decomposed algebra, two minimal graded projective resolutions of `M` have
the same `n`th projective Grothendieck class whenever both `n`th terms are finitely generated
`A`-modules. -/
theorem IsMinimal.laurentK0_of_finiteProjectiveTerm_eq
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  LaurentK0.of_congr _
    (ObjectProperty.isoMk _ (eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫
      hr₁.termObjIsoOfFinite hr₂ h𝒜 n ≪≫
      eqToIso (r₂.finiteProjectiveTerm_obj n).symm))

/-- **Independence of minimal resolution (bounded-below form).** Two minimal graded projective
resolutions of `M` with bounded-below terms define the same Betti Poincaré series in every
projective basis. -/
theorem IsMinimal.bettiPoincareSeries_eq_of_bddBelow
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (b₁ b₂ : ℕ → ℤ)
    (hbelow₁ : ∀ n p, p < b₁ n → (r₁.grading n).piece p = ⊥)
    (hbelow₂ : ∀ n p, p < b₂ n → (r₂.grading n).piece p = ⊥) (i : I) :
    r₁.bettiPoincareSeries bP i = r₂.bettiPoincareSeries bP i := by
  apply PowerSeries.ext
  intro n
  rw [coeff_bettiPoincareSeries, coeff_bettiPoincareSeries,
    hr₁.laurentK0_of_finiteProjectiveTerm_eq_of_bddBelow hr₂ (b₁ n) (b₂ n)
      (hbelow₁ n) (hbelow₂ n)]

/-- **Independence of minimal resolution.** Over a nonnegatively decomposed algebra, any two
minimal graded projective resolutions of `M` with finitely generated `A`-module terms define the
same Betti Poincaré series in every projective basis. -/
theorem IsMinimal.bettiPoincareSeries_eq
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (i : I) :
    r₁.bettiPoincareSeries bP i = r₂.bettiPoincareSeries bP i := by
  apply PowerSeries.ext
  intro n
  rw [coeff_bettiPoincareSeries, coeff_bettiPoincareSeries,
    hr₁.laurentK0_of_finiteProjectiveTerm_eq hr₂ h𝒜 n]

/-- **Shift law for minimal resolutions.** Over a nonnegatively decomposed algebra, if `r` is any
minimal resolution of `M` and `r'` is any minimal resolution of `M{d}` with finitely generated
terms, then `r'.bettiPoincareSeries bP i = q^d · r.bettiPoincareSeries bP i`. -/
theorem IsMinimal.bettiPoincareSeries_shiftObj_eq
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {d : ℤ} {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (i : I) :
    r'.bettiPoincareSeries bP i = PowerSeries.C (T d) * r.bettiPoincareSeries bP i := by
  rw [hr'.bettiPoincareSeries_eq bP ((r.isMinimal_shiftObj_iff d).mpr hr) h𝒜 i,
    r.bettiPoincareSeries_shiftObj bP d i]

/-- Over a nonnegatively decomposed algebra, any minimal resolution `r'` of `M{1}` has Betti
Poincaré series `q · r.bettiPoincareSeries bP i` for any minimal resolution `r` of `M`. -/
theorem IsMinimal.bettiPoincareSeries_shiftObj_one_eq
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj 1).grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (i : I) :
    r'.bettiPoincareSeries bP i = PowerSeries.C (T 1) * r.bettiPoincareSeries bP i :=
  hr.bettiPoincareSeries_shiftObj_eq bP hr' h𝒜 i

end GradedProjectiveResolution

/-- **Independence of minimal resolutions for the Betti Poincaré matrix.** Over a nonnegatively
decomposed algebra, replacing a family of minimal resolutions by any other family of minimal
resolutions with finitely generated terms leaves `bettiPoincareMatrix` unchanged. -/
theorem bettiPoincareMatrix_congr {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    {r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal)
    (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) :
    bettiPoincareMatrix bP r₁ = bettiPoincareMatrix bP r₂ :=
  Matrix.ext fun i j ↦ (hr₁ j).bettiPoincareSeries_eq bP (hr₂ j) h𝒜 i

end Uniqueness

end TauCeti
