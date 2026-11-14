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
import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Graded Betti Poincaré series and matrices of projective resolutions

Let `A` be a graded `k`-algebra and `bP` a `ℤ[q,q⁻¹]`-basis of `K₀^gr(proj A)`. A graded projective
resolution `r` of `M` with finitely generated `A`-module terms yields classes `[Pₙ] ∈ K₀^gr(proj A)`
whose `bP`-coordinates assemble into the **graded Betti Poincaré series**
`B_i(M; q, t) = ∑_{n ≥ 0} (bP.repr [Pₙ] i) tⁿ ∈ (ℤ[q,q⁻¹])⟦t⟧`, and for a family `rⱼ` into the
**Betti Poincaré matrix** `B(q, t) ∈ Matrix I J (PowerSeries (LaurentPolynomial ℤ))`.

By `TauCeti.GradedProjectiveResolution.IsMinimal.termObjIso`, minimal resolutions with bounded-below
terms (in particular finitely generated terms over nonnegatively decomposed algebras) have the same
Betti series in every projective basis, and shifting `M` to `M{d}` multiplies `B_i` by `q^d`.

## Main definitions and results

* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries` and `TauCeti.bettiPoincareMatrix`:
  the graded Betti Poincaré formal power series and matrix along a projective basis `bP`.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_bddBelow`,
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq`, and
  `TauCeti.bettiPoincareMatrix_congr`: independence of the choice of minimal resolution.
* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries_shiftObj` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_shiftObj_eq`: `M{d}` shift laws.
* `TauCeti.GradedProjectiveResolution.bettiPoincareSeries_eq_sum_of_forall_subsingleton` and
  `TauCeti.GradedProjectiveResolution.maslovEulerPowerSeries_bettiPoincareSeries_eq_sum`:
  finite-resolution polynomial truncation and `q = 1, X ↦ -X` specialization.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, LNM **1836**, Springer (2004),
  Section 2.3.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *JCTA* **185** (2022), Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe uk uA uI uJ

section Definitions

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) [∀ n, Module.Finite A (r.X n)]

/-- **The graded Betti Poincaré formal power series** of `r` along `bP`: its `n`th coefficient is
`bP.repr [r.termObj n] i`. -/
def bettiPoincareSeries (i : I) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦ bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i

/-- The `n`th coefficient of `r.bettiPoincareSeries bP i` is the `i`th projective coordinate of the
`n`th resolution term. -/
@[simp]
theorem coeff_bettiPoincareSeries (i : I) (n : ℕ) :
    PowerSeries.coeff n (r.bettiPoincareSeries bP i) =
      bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincareSeries]

/-- Shifting a resolution of `M` to `M{d}` shifts each bundled finite projective term by `d`. -/
@[simp]
theorem finiteProjectiveTerm_shiftObj (d : ℤ) (n : ℕ) :
    (r.shiftObj d).finiteProjectiveTerm n =
      ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
        gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩ :=
  ObjectProperty.FullSubcategory.ext (by simp)

/-- **Shift law for graded Betti Poincaré series.** Shifting `r` to `M{d}` multiplies its Betti
Poincaré series by `q^d` (`PowerSeries.C (T d)`). -/
@[simp]
theorem bettiPoincareSeries_shiftObj (d : ℤ) (i : I) :
    (r.shiftObj d).bettiPoincareSeries bP i = PowerSeries.C (T d) * r.bettiPoincareSeries bP i :=
  PowerSeries.ext fun n ↦ by
    rw [coeff_bettiPoincareSeries, PowerSeries.coeff_C_mul, coeff_bettiPoincareSeries,
      finiteProjectiveTerm_shiftObj, laurentK0_projective_of_shiftObj, map_smul,
      Finsupp.smul_apply, smul_eq_mul]

/-- Shifting `r` to `M{d}` translates internal Betti coefficients by `d`. -/
theorem coeff_coeff_bettiPoincareSeries_shiftObj (d : ℤ) (i : I) (n : ℕ) (p : ℤ) :
    (PowerSeries.coeff n ((r.shiftObj d).bettiPoincareSeries bP i)).coeff p =
      (PowerSeries.coeff n (r.bettiPoincareSeries bP i)).coeff (p - d) := by
  rw [bettiPoincareSeries_shiftObj, PowerSeries.coeff_C_mul, coeff_T_mul]

/-- A subsingleton resolution term contributes zero to the Betti Poincaré series. -/
theorem coeff_bettiPoincareSeries_eq_zero_of_subsingleton (i : I) {n : ℕ}
    (hn : Subsingleton (r.X n)) :
    PowerSeries.coeff n (r.bettiPoincareSeries bP i) = 0 := by
  have : Subsingleton (r.finiteProjectiveTerm n).obj := r.finiteProjectiveTerm_obj n ▸ hn
  rw [coeff_bettiPoincareSeries, ← LaurentK0.ofExactK0_exactK0_of.{uA},
    ExactK0.of_eq_zero_of_isZero.{uA}
      (GradedModuleCat.isZero_fullSubcategory_of_subsingleton _),
    map_zero, map_zero, Finsupp.zero_apply]

/-- For a resolution whose terms vanish from homological degree `b` onward, the Betti Poincaré
series is the finite polynomial sum `∑_{n < b} (bP.repr [Pₙ] i) Xⁿ`. -/
theorem bettiPoincareSeries_eq_sum_of_forall_subsingleton (i : I) (b : ℕ)
    (hb : ∀ n, b ≤ n → Subsingleton (r.X n)) :
    r.bettiPoincareSeries bP i = ∑ n ∈ Finset.range b,
      PowerSeries.C (PowerSeries.coeff n (r.bettiPoincareSeries bP i)) * PowerSeries.X ^ n :=
  PowerSeries.ext fun m ↦ by
    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    by_cases hmb : m < b
    · rw [Finset.sum_ite_eq (Finset.range b) m, ite_eq_left (Finset.mem_range.mpr hmb)]
    · rw [Finset.sum_ite_eq (Finset.range b) m, ite_eq_right (Finset.mem_range.not.mpr hmb),
        r.coeff_bettiPoincareSeries_eq_zero_of_subsingleton bP i (hb m (Nat.le_of_not_lt hmb))]

/-- Applying `Bigraded.maslovEulerPowerSeries` (`q = 1`, `X ↦ -X`) to a resolution whose terms
vanish from degree `b` onward yields the finite sum in `PowerSeries ℤ`. -/
theorem maslovEulerPowerSeries_bettiPoincareSeries_eq_sum (i : I) (b : ℕ)
    (hb : ∀ n, b ≤ n → Subsingleton (r.X n)) :
    Bigraded.maslovEulerPowerSeries (r.bettiPoincareSeries bP i) =
      ∑ n ∈ Finset.range b, PowerSeries.C ((-1 : ℤ) ^ n *
        laurentEval (1 : ℤˣ) (PowerSeries.coeff n (r.bettiPoincareSeries bP i))) *
        PowerSeries.X ^ n := by
  conv_lhs => rw [r.bettiPoincareSeries_eq_sum_of_forall_subsingleton bP i b hb]
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ PowerSeries.ext fun m ↦ ?_
  simp only [Bigraded.coeff_maslovEulerPowerSeries, PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h <;> simp [h]

end GradedProjectiveResolution

/-- **The Betti Poincaré matrix** of resolutions `r j` of `M j` along `bP`, with `(i, j)` entry
`(r j).bettiPoincareSeries bP i`. -/
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
    bettiPoincareMatrix bP r i j = (r j).bettiPoincareSeries bP i := (rfl)

end Definitions

section Uniqueness

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜] {I : Type uI}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- Two minimal graded projective resolutions of `M` have the same `n`th projective Grothendieck
class whenever both `n`th terms are bounded below. -/
theorem IsMinimal.laurentK0_of_finiteProjectiveTerm_eq_of_bddBelow
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) {n : ℕ}
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] (b₁ b₂ : ℤ)
    (hbelow₁ : ∀ p < b₁, (r₁.grading n).piece p = ⊥)
    (hbelow₂ : ∀ p < b₂, (r₂.grading n).piece p = ⊥) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  LaurentK0.of_congr _ (ObjectProperty.isoMk _ (eqToIso (r₁.finiteProjectiveTerm_obj n) ≪≫
    hr₁.termObjIso hr₂ b₁ b₂ hbelow₁ hbelow₂ ≪≫ eqToIso (r₂.finiteProjectiveTerm_obj n).symm))

/-- Over a nonnegatively decomposed algebra, two minimal resolutions of `M` have the same `n`th
projective Grothendieck class whenever both `n`th terms are finitely generated `A`-modules. -/
theorem IsMinimal.laurentK0_of_finiteProjectiveTerm_eq
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (r₁.finiteProjectiveTerm n) =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r₂.finiteProjectiveTerm n) :=
  let hb₁ := (r₁.grading n).bddBelow_setOf_piece_ne_bot 𝒜 h𝒜
  let hb₂ := (r₂.grading n).bddBelow_setOf_piece_ne_bot 𝒜 h𝒜
  hr₁.laurentK0_of_finiteProjectiveTerm_eq_of_bddBelow hr₂ hb₁.choose hb₂.choose
    (fun _ hp ↦ Classical.not_not.mp fun hne ↦ (hb₁.choose_spec hne).not_gt hp)
    (fun _ hp ↦ Classical.not_not.mp fun hne ↦ (hb₂.choose_spec hne).not_gt hp)

/-- **Independence of minimal resolution (bounded-below form).** -/
theorem IsMinimal.bettiPoincareSeries_eq_of_bddBelow
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (b₁ b₂ : ℕ → ℤ)
    (hbelow₁ : ∀ n p, p < b₁ n → (r₁.grading n).piece p = ⊥)
    (hbelow₂ : ∀ n p, p < b₂ n → (r₂.grading n).piece p = ⊥) (i : I) :
    r₁.bettiPoincareSeries bP i = r₂.bettiPoincareSeries bP i :=
  PowerSeries.ext fun n ↦ by
    rw [coeff_bettiPoincareSeries, coeff_bettiPoincareSeries,
      hr₁.laurentK0_of_finiteProjectiveTerm_eq_of_bddBelow hr₂ (b₁ n) (b₂ n)
        (hbelow₁ n) (hbelow₂ n)]

/-- **Independence of minimal resolution** over a nonnegatively decomposed algebra. -/
theorem IsMinimal.bettiPoincareSeries_eq
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (i : I) :
    r₁.bettiPoincareSeries bP i = r₂.bettiPoincareSeries bP i := by
  choose b₁ hb₁ using fun n ↦ (r₁.grading n).bddBelow_setOf_piece_ne_bot 𝒜 h𝒜
  choose b₂ hb₂ using fun n ↦ (r₂.grading n).bddBelow_setOf_piece_ne_bot 𝒜 h𝒜
  exact hr₁.bettiPoincareSeries_eq_of_bddBelow bP hr₂ b₁ b₂
    (fun n _ hp ↦ Classical.not_not.mp fun hne ↦ (hb₁ n hne).not_gt hp)
    (fun n _ hp ↦ Classical.not_not.mp fun hne ↦ (hb₂ n hne).not_gt hp) i

/-- **Shift law for minimal resolutions.** Over a nonnegatively decomposed algebra, minimal
resolutions `r` of `M` and `r'` of `M{d}` satisfy `B_i(M{d}) = q^d · B_i(M)`. -/
theorem IsMinimal.bettiPoincareSeries_shiftObj_eq
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading} {d : ℤ}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (i : I) :
    r'.bettiPoincareSeries bP i = PowerSeries.C (T d) * r.bettiPoincareSeries bP i := by
  rw [hr'.bettiPoincareSeries_eq bP ((r.isMinimal_shiftObj_iff d).mpr hr) h𝒜 i,
    r.bettiPoincareSeries_shiftObj bP d i]

end GradedProjectiveResolution

/-- **Independence of minimal resolutions for `bettiPoincareMatrix`** over a nonnegatively
decomposed algebra. -/
theorem bettiPoincareMatrix_congr {J : Type uJ} {M : J → GradedModuleCat.{uA} 𝒜}
    {r₁ r₂ : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r₁ j).X n)] [∀ j n, Module.Finite A ((r₂ j).X n)]
    (hr₁ : ∀ j, (r₁ j).IsMinimal) (hr₂ : ∀ j, (r₂ j).IsMinimal) (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) :
    bettiPoincareMatrix bP r₁ = bettiPoincareMatrix bP r₂ :=
  Matrix.ext fun i j ↦ (hr₁ j).bettiPoincareSeries_eq bP (hr₂ j) h𝒜 i

end Uniqueness

end TauCeti
