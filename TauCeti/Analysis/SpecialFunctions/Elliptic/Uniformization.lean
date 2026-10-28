/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The Weierstrass curve of a period lattice

A period pair `L` with lattice `Λ` has the lattice invariants `g₂ = 60 ∑' λ⁻⁴` and
`g₃ = 140 ∑' λ⁻⁶` (`PeriodPair.g₂`, `PeriodPair.g₃`), and Mathlib proves the differential equation
`℘'² = 4 ℘³ - g₂ ℘ - g₃` (`PeriodPair.derivWeierstrassP_sq`). Dividing `℘'` by `2` turns this into
a Weierstrass equation with leading coefficient one, so this file attaches to `L` the Weierstrass
curve

  `y² = x³ - (g₂ / 4) x - g₃ / 4`

(`PeriodPair.weierstrassCurve`) and the map `z ↦ (℘(z), ℘'(z) / 2)` from `ℂ` to its points, sending
the lattice to the point at infinity (`PeriodPair.weierstrassPoint`). These are the first steps of
the complex uniformization `ℂ / Λ ≃ E(ℂ)`.

The discriminant of the curve is `g₂³ - 27 g₃²`. For the lattice `ℤ τ + ℤ` of a point `τ` of the
upper half-plane, the lattice sums are Eisenstein series, `g₂ = (4 π⁴ / 3) E₄(τ)` and
`g₃ = (8 π⁶ / 27) E₆(τ)` (by Mathlib's `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`), so
the identity `E₄³ - E₆² = 1728 Δ` (`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`) gives
`g₂³ - 27 g₃² = (2 π)¹² Δ(τ)`, which does not vanish. Every lattice is a nonzero multiple of such a
lattice, and rescaling a lattice by `c` multiplies `g₂` by `c⁻⁴` and `g₃` by `c⁻⁶`; so the
discriminant never vanishes and the curve is elliptic. Its `j`-invariant is
`1728 g₂³ / (g₂³ - 27 g₃²)`, which for `ℤ τ + ℤ` is the modular invariant `j(τ) = E₄(τ)³ / Δ(τ)`.

## Main definitions

* `PeriodPair.weierstrassCurve`: the Weierstrass curve `y² = x³ - (g₂ / 4) x - g₃ / 4`.
* `PeriodPair.weierstrassPoint`: the point `(℘(z), ℘'(z) / 2)`, or `0` for `z ∈ Λ`.

## Main results

* `PeriodPair.weierstrassCurve_smul`: rescaling the lattice by `c` changes the curve by the
  variable change with `u = c`.
* `UpperHalfPlane.G_periodPair`: `G k (ℤ τ + ℤ) = 2 ζ(k) E_k(τ)` for `k ≥ 3`.
* `UpperHalfPlane.weierstrassCurve_Δ_periodPair`: the discriminant of the curve of `ℤ τ + ℤ` is
  `(2 π)¹² Δ(τ)`.
* `PeriodPair.weierstrassCurve_Δ`, `PeriodPair.weierstrassCurve_Δ_ne_zero`: the discriminant is
  `g₂³ - 27 g₃²`, and it is nonzero.
* `PeriodPair.weierstrassCurve_j`, `UpperHalfPlane.weierstrassCurve_j_periodPair`: the
  `j`-invariant, and its identification with the modular invariant `TauCeti.ModularForm.j`.
* `PeriodPair.weierstrassPoint_add_coe`, `PeriodPair.weierstrassPoint_neg`,
  `PeriodPair.weierstrassPoint_eq_zero_iff`: the point map is `Λ`-periodic, odd, and vanishes
  exactly on `Λ`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.3 and §VI.5.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  §VII.2.3 and §VII.3.3.
-/

public noncomputable section

open Complex ModularForm UpperHalfPlane WeierstrassCurve

open scoped Real

/-! ### Lattice sums of `ℤ τ + ℤ` -/

namespace UpperHalfPlane

/-- For `k ≥ 3` the lattice sum `G k` of `ℤ τ + ℤ` is the Eisenstein series `2 ζ(k) E_k(τ)`. -/
lemma G_periodPair (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    τ.periodPair.G k = 2 * riemannZeta k * E hk τ := by
  have h := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  rw [PeriodPair.G,
    ← ((finTwoArrowEquiv ℤ).trans τ.periodPair.latticeEquivProd.symm.toEquiv).tsum_eq]
  -- Mathlib has no evaluation lemma for `E`, which is `(1 / 2) • eisensteinSeriesSIF` by
  -- definition; Mathlib's `EisensteinSeries.q_expansion_riemannZeta` unfolds it the same way.
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [hE, mul_comm 2, mul_assoc, ← mul_assoc 2, mul_one_div_cancel two_ne_zero, one_mul, ← h]
  refine tsum_congr fun v ↦ ?_
  simp [EisensteinSeries.eisSummand, PeriodPair.latticeEquiv_symm_apply]

/-- `g₂(ℤ τ + ℤ) = (4 π⁴ / 3) E₄(τ)`. -/
lemma g₂_periodPair (τ : ℍ) : τ.periodPair.g₂ = 4 * π ^ 4 / 3 * E₄ τ := by
  rw [PeriodPair.g₂, G_periodPair τ (by norm_num), Nat.cast_ofNat, riemannZeta_four]
  ring

/-- `g₃(ℤ τ + ℤ) = (8 π⁶ / 27) E₆(τ)`. -/
lemma g₃_periodPair (τ : ℍ) : τ.periodPair.g₃ = 8 * π ^ 6 / 27 * E₆ τ := by
  have hζ : riemannZeta 6 = π ^ 6 / 945 := by
    have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    norm_num [show bernoulli 6 = 1 / 42 by decide +kernel, Nat.factorial] at h
    rw [h]
    ring
  rw [PeriodPair.g₃, G_periodPair τ (by norm_num), Nat.cast_ofNat, hζ]
  ring

end UpperHalfPlane

/-! ### The Weierstrass curve of a period lattice -/

namespace PeriodPair

variable (L : PeriodPair)

/-- The Weierstrass curve `y² = x³ - (g₂ / 4) x - g₃ / 4` of a period lattice. The point
`(℘(z), ℘'(z) / 2)` lies on it for `z ∉ Λ` (`PeriodPair.equation_weierstrassP`). -/
def weierstrassCurve : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)

@[simp] lemma weierstrassCurve_a₁ : L.weierstrassCurve.a₁ = 0 := by unfold weierstrassCurve; rfl
@[simp] lemma weierstrassCurve_a₂ : L.weierstrassCurve.a₂ = 0 := by unfold weierstrassCurve; rfl
@[simp] lemma weierstrassCurve_a₃ : L.weierstrassCurve.a₃ = 0 := by unfold weierstrassCurve; rfl

@[simp] lemma weierstrassCurve_a₄ : L.weierstrassCurve.a₄ = -(L.g₂ / 4) := by
  unfold weierstrassCurve; rfl

@[simp] lemma weierstrassCurve_a₆ : L.weierstrassCurve.a₆ = -(L.g₃ / 4) := by
  unfold weierstrassCurve; rfl

/-- The discriminant of the Weierstrass curve of a lattice is `g₂³ - 27 g₃²`. -/
lemma weierstrassCurve_Δ : L.weierstrassCurve.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃,
    weierstrassCurve_a₄, weierstrassCurve_a₆]
  ring

/-- Rescaling the lattice by `c` changes its Weierstrass curve by the variable change
`(x, y) ↦ (c⁻² x, c⁻³ y)`, that is, with `u = c` and `r = s = t = 0`. -/
lemma weierstrassCurve_smul (c : ℂˣ) :
    (c • L).weierstrassCurve = (⟨c, 0, 0, 0⟩ : VariableChange ℂ) • L.weierstrassCurve := by
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, g₂_smul, g₃_smul] <;> ring

/-- The Weierstrass curve depends only on the lattice, not on the chosen basis. -/
lemma weierstrassCurve_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.weierstrassCurve = L'.weierstrassCurve := by
  ext <;> simp [g₂, g₃, G_eq_of_lattice_eq h]

end PeriodPair

namespace UpperHalfPlane

/-- The discriminant of the Weierstrass curve of `ℤ τ + ℤ` is `(2 π)¹² Δ(τ)`. -/
lemma weierstrassCurve_Δ_periodPair (τ : ℍ) :
    τ.periodPair.weierstrassCurve.Δ = (2 * π) ^ 12 * discriminant τ := by
  rw [PeriodPair.weierstrassCurve_Δ, g₂_periodPair, g₃_periodPair,
    discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

end UpperHalfPlane

namespace PeriodPair

variable (L : PeriodPair)

/-- **The discriminant `g₂³ - 27 g₃²` of a lattice does not vanish.** -/
lemma weierstrassCurve_Δ_ne_zero : L.weierstrassCurve.Δ ≠ 0 := by
  obtain ⟨c, τ, h⟩ := L.exists_lattice_eq_smul_periodPair
  rw [weierstrassCurve_eq_of_lattice_eq h, weierstrassCurve_smul, variableChange_Δ,
    weierstrassCurve_Δ_periodPair]
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (mul_ne_zero (by simp [Real.pi_ne_zero])
    (discriminant_ne_zero τ))

instance : L.weierstrassCurve.IsElliptic :=
  ⟨L.weierstrassCurve_Δ_ne_zero.isUnit⟩

/-- The `j`-invariant of the Weierstrass curve of a lattice is `1728 g₂³ / (g₂³ - 27 g₃²)`. -/
lemma weierstrassCurve_j :
    L.weierstrassCurve.j = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [j_eq, weierstrassCurve_Δ]
  simp only [c₄, b₂, b₄, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃,
    weierstrassCurve_a₄]
  ring

end PeriodPair

namespace UpperHalfPlane

/-- The `j`-invariant of the Weierstrass curve of `ℤ τ + ℤ` is the modular invariant
`j(τ) = E₄(τ)³ / Δ(τ)`. -/
lemma weierstrassCurve_j_periodPair (τ : ℍ) :
    τ.periodPair.weierstrassCurve.j = TauCeti.ModularForm.j τ := by
  rw [j_eq, weierstrassCurve_Δ_periodPair, TauCeti.ModularForm.j_apply]
  simp only [c₄, b₂, b₄, PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
    PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄, g₂_periodPair]
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp
  ring

end UpperHalfPlane

/-! ### The point `(℘(z), ℘'(z) / 2)` -/

namespace PeriodPair

variable (L : PeriodPair) {z : ℂ}

/-- For `z ∉ Λ` the point `(℘(z), ℘'(z) / 2)` lies on the Weierstrass curve of `L`: this is the
differential equation `℘'² = 4 ℘³ - g₂ ℘ - g₃` divided by `4`. -/
lemma equation_weierstrassP (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [Affine.equation_iff]
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆]
  linear_combination L.derivWeierstrassP_sq z hz / 4

lemma nonsingular_weierstrassP (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Nonsingular (℘[L] z) (℘'[L] z / 2) :=
  Affine.equation_iff_nonsingular.mp (L.equation_weierstrassP hz)

open Classical in
/-- The point `(℘(z), ℘'(z) / 2)` of the Weierstrass curve of `L` for `z ∉ Λ`, and the point at
infinity `0` for `z ∈ Λ`. -/
def weierstrassPoint (z : ℂ) : L.weierstrassCurve.toAffine.Point :=
  if hz : z ∈ L.lattice then 0 else .some _ _ (L.nonsingular_weierstrassP hz)

lemma weierstrassPoint_of_mem (hz : z ∈ L.lattice) : L.weierstrassPoint z = 0 := by
  simp [weierstrassPoint, hz]

lemma weierstrassPoint_of_notMem (hz : z ∉ L.lattice) :
    L.weierstrassPoint z = .some _ _ (L.nonsingular_weierstrassP hz) := by
  simp [weierstrassPoint, hz]

@[simp]
lemma weierstrassPoint_coe (l : L.lattice) : L.weierstrassPoint l = 0 :=
  L.weierstrassPoint_of_mem l.2

@[simp]
lemma weierstrassPoint_zero : L.weierstrassPoint 0 = 0 :=
  L.weierstrassPoint_of_mem (zero_mem _)

/-- The point map vanishes exactly on the lattice. -/
@[simp]
lemma weierstrassPoint_eq_zero_iff : L.weierstrassPoint z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h ↦ by_contra fun hz ↦ ?_, L.weierstrassPoint_of_mem⟩
  rw [L.weierstrassPoint_of_notMem hz] at h
  exact Affine.Point.some_ne_zero _ h

lemma weierstrassPoint_add_coe (z : ℂ) (l : L.lattice) :
    L.weierstrassPoint (z + l) = L.weierstrassPoint z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hz, L.weierstrassPoint_of_mem (add_mem hz l.2)]
  · have hzl : z + l ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h l.2)
    rw [L.weierstrassPoint_of_notMem hz, L.weierstrassPoint_of_notMem hzl]
    simp [weierstrassP_add_coe, derivWeierstrassP_add_coe]

lemma periodic_weierstrassPoint (l : L.lattice) : L.weierstrassPoint.Periodic l :=
  (L.weierstrassPoint_add_coe · l)

/-- The point map is odd: `-z` goes to `(℘(z), -℘'(z) / 2)`. -/
@[simp]
lemma weierstrassPoint_neg (z : ℂ) : L.weierstrassPoint (-z) = -L.weierstrassPoint z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hz, L.weierstrassPoint_of_mem (neg_mem hz), Affine.Point.neg_zero]
  · rw [L.weierstrassPoint_of_notMem hz, L.weierstrassPoint_of_notMem (by simpa using hz),
      Affine.Point.neg_some]
    simp [weierstrassP_neg, derivWeierstrassP_neg, Affine.negY, neg_div]

end PeriodPair
