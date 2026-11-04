/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.RadiusLiminf
public import TauCeti.RingTheory.PowerSeries.Entire.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# The radius of a power series

The *radius* of a power series `f = ∑ aₙ Xⁿ` over a normed ring is the supremum, in `ℝ≥0∞`, of
the nonnegative real radii `r` at which `f` is restricted, that is, at which `‖aₙ‖ rⁿ → 0`. It is
an invariant of the coefficient norms alone: it does not refer to points at which `f` might be
evaluated, so it does not depend on a choice of extension field, and an isometric change of
coefficients preserves it. Polynomials, including zero, have radius `∞`.

The series is restricted at every radius of absolute value strictly below its radius and at no
radius strictly above it; at the radius itself the radius alone decides nothing.
Restrictedness at `r` may be replaced by boundedness of the weighted coefficient norms
`‖aₙ‖ rⁿ`, which makes the radius agree with Mathlib's `FormalMultilinearSeries.radius` of any
formal multilinear series with the same coefficient norms. Through this comparison the
**Cauchy–Hadamard formula** `1 / radius f = limsup ‖aₙ‖ ^ (1 / n)` follows from
`FormalMultilinearSeries.radius_inv_eq_limsup`, and Mathlib's ratio tests for
`FormalMultilinearSeries.ofScalars` apply to series over a nontrivially normed field.

## Main definitions

* `PowerSeries.radius f`: the supremum of the radii `r ≥ 0` at which `f` is restricted.

## Main results

* `PowerSeries.isRestricted_of_lt_radius` and `PowerSeries.not_isRestricted_of_radius_lt`:
  `f` is restricted at every `r` with `|r| < radius f` and at no `r` with `radius f < |r|`.
* `PowerSeries.le_radius_of_bound`: bounded weighted coefficient norms at `r` give
  `r ≤ radius f`.
* `PowerSeries.radius_eq_top_iff`: the radius is infinite exactly for entire series; in
  particular `PowerSeries.radius_coe`: polynomials have infinite radius.
* `PowerSeries.radius_pos_iff`: the radius is positive exactly when the series is restricted at
  some positive radius.
* `PowerSeries.radius_eq_radius_of_norm_eq` and `PowerSeries.radius_eq_radius_ofScalars`: the
  radius is the radius of any formal multilinear series with the same coefficient norms.
* `PowerSeries.radius_eq_liminf` and `PowerSeries.radius_inv_eq_limsup`: the Cauchy–Hadamard
  formula.
* `PowerSeries.radius_map`: isometric coefficient maps preserve the radius.
* `PowerSeries.radius_mk_pow`: over a ring with multiplicative norm, the geometric series
  `∑ aⁿ Xⁿ` has radius `‖a‖⁻¹`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §1.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace PowerSeries

open Filter
open scoped NNReal ENNReal

section NormedRing

variable {R S : Type*} [NormedRing R] [NormedRing S] {f g : R⟦X⟧}

/-- The *radius* of a power series `f = ∑ aₙ Xⁿ`: the supremum of the radii `r ≥ 0` at which `f`
is restricted, that is, at which `‖aₙ‖ rⁿ → 0`. -/
noncomputable def radius (f : R⟦X⟧) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (_ : f.IsRestricted r), (r : ℝ≥0∞)

/-- The radius as the supremum of the radii of restrictedness. -/
theorem radius_def (f : R⟦X⟧) : f.radius = ⨆ (r : ℝ≥0) (_ : f.IsRestricted r), (r : ℝ≥0∞) :=
  (rfl)

/-- A series restricted at `r` has radius at least `|r|`. -/
theorem le_radius_of_isRestricted {r : ℝ} (hf : f.IsRestricted r) : ‖r‖ₑ ≤ f.radius := by
  have hr : f.IsRestricted (‖r‖₊ : ℝ) := by rwa [coe_nnnorm, Real.norm_eq_abs, isRestricted_abs_iff]
  rw [enorm_eq_nnnorm]
  exact le_iSup₂ (f := fun (s : ℝ≥0) (_ : f.IsRestricted s) ↦ (s : ℝ≥0∞)) _ hr

/-- A series is restricted at every radius of absolute value strictly below its radius. -/
theorem isRestricted_of_lt_radius {r : ℝ} (h : ‖r‖ₑ < f.radius) : f.IsRestricted r := by
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp h
  obtain ⟨hfs, hrs⟩ := lt_iSup_iff.mp hs
  rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm,
    Real.norm_eq_abs] at hrs
  exact TauCeti.PowerSeries.isRestricted_of_abs_le hfs (hrs.le.trans (le_abs_self _))

/-- A series is not restricted at any radius of absolute value strictly above its radius. -/
theorem not_isRestricted_of_radius_lt {r : ℝ} (h : f.radius < ‖r‖ₑ) : ¬f.IsRestricted r :=
  fun hf ↦ (le_radius_of_isRestricted hf).not_gt h

/-- If the weighted coefficient norms `‖aₙ‖ rⁿ` are bounded, the radius is at least `r`. -/
theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0} (h : ∀ n, ‖coeff n f‖ * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ f.radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_
  have hf : f.IsRestricted s := PowerSeries.HasGaussNorm.isRestricted_of_abs_lt
    ⟨C, by rintro _ ⟨n, rfl⟩; exact h n⟩ (by simpa using hs)
  simpa using le_radius_of_isRestricted hf

/-- The radius is infinite exactly when the series is entire. -/
@[simp]
theorem radius_eq_top_iff : f.radius = ⊤ ↔ f.IsEntire := by
  refine ⟨fun h ↦ isEntire_iff.mpr fun r ↦ isRestricted_of_lt_radius (h ▸ enorm_lt_top),
    fun h ↦ ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_⟩
  simpa using le_radius_of_isRestricted (h.isRestricted r)

/-- Polynomials have infinite radius. -/
@[simp]
theorem radius_coe (p : Polynomial R) : (p : R⟦X⟧).radius = ⊤ :=
  radius_eq_top_iff.mpr (isEntire_coe p)

/-- The zero series has infinite radius. -/
@[simp]
theorem radius_zero : (0 : R⟦X⟧).radius = ⊤ :=
  radius_eq_top_iff.mpr isEntire_zero

/-- The radius is positive exactly when the series is restricted at some positive radius. -/
theorem radius_pos_iff : 0 < f.radius ↔ ∃ r : ℝ, 0 < r ∧ f.IsRestricted r := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr, hf⟩ ↦ ?_⟩
  · obtain ⟨r, hr, hrf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    exact ⟨r, by simpa using hr, isRestricted_of_lt_radius (by simpa using hrf)⟩
  · exact (enorm_pos.mpr hr.ne').trans_le (le_radius_of_isRestricted hf)

/-- **Comparison with formal multilinear series.** The radius of `f` is the radius of any formal
multilinear series whose terms have the norms of the coefficients of `f`. -/
theorem radius_eq_radius_of_norm_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : ∀ n, ‖p n‖ = ‖coeff n f‖) :
    f.radius = p.radius := by
  refine le_antisymm (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
    (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
  · obtain ⟨A, -, hA⟩ :=
      (isRestricted_of_lt_radius (r := r) (by simpa using hr)).exists_nonneg_norm_coeff_mul_pow_le
    exact p.le_radius_of_bound A fun n ↦ by simpa [h] using hA n
  · obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
    exact le_radius_of_bound C fun n ↦ by simpa [h] using hC n

/-- The radius of `f` is the radius of the real scalar series with coefficients `‖aₙ‖`. -/
private theorem radius_eq_radius_ofScalars_norm (f : S⟦X⟧) :
    f.radius = (FormalMultilinearSeries.ofScalars ℝ fun n ↦ ‖coeff n f‖).radius :=
  radius_eq_radius_of_norm_eq _ fun n ↦ by simp

/-- **Comparison of radii.** If the coefficients of `g` are no larger in norm than those of `f`,
the radius of `g` is at least that of `f`. -/
theorem radius_le_radius_of_norm_coeff_le {g : S⟦X⟧} (h : ∀ n, ‖coeff n g‖ ≤ ‖coeff n f‖) :
    f.radius ≤ g.radius := by
  rw [radius_eq_radius_ofScalars_norm f, radius_eq_radius_ofScalars_norm g]
  exact FormalMultilinearSeries.radius_le_of_le fun n ↦ by simpa using h n

/-- Coefficient maps preserving norms preserve the radius. -/
theorem radius_map (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ = ‖x‖) :
    (f.map φ).radius = f.radius :=
  le_antisymm (radius_le_radius_of_norm_coeff_le fun n ↦ by simp [hφ])
    (radius_le_radius_of_norm_coeff_le fun n ↦ by simp [hφ])

/-- The radius of a sum is at least the smaller of the two radii. -/
theorem min_radius_le_radius_add (f g : R⟦X⟧) : min f.radius g.radius ≤ (f + g).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hf := isRestricted_of_lt_radius (f := f) (r := r) (by simpa using (lt_min_iff.mp hr).1)
  have hg := isRestricted_of_lt_radius (f := g) (r := r) (by simpa using (lt_min_iff.mp hr).2)
  simpa using le_radius_of_isRestricted (hf.add hg)

/-- The radius of a product is at least the smaller of the two radii. -/
theorem min_radius_le_radius_mul (f g : R⟦X⟧) : min f.radius g.radius ≤ (f * g).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨s, hrs, hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hf := isRestricted_of_lt_radius (f := f) (r := s) (by simpa using (lt_min_iff.mp hs).1)
  have hg := isRestricted_of_lt_radius (f := g) (r := s) (by simpa using (lt_min_iff.mp hs).2)
  have hrs' : |(r : ℝ)| < |(s : ℝ)| := by simpa using hrs
  simpa using le_radius_of_isRestricted (hf.mul_of_abs_lt hg hrs')

/-- **Cauchy–Hadamard formula**, `liminf` form: the radius of `∑ aₙ Xⁿ` is
`liminf 1 / ‖aₙ‖ ^ (1 / n)`. -/
theorem radius_eq_liminf :
    f.radius = liminf (fun n ↦ (1 / (‖coeff n f‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  rw [radius_eq_radius_ofScalars_norm, FormalMultilinearSeries.radius_eq_liminf]
  congr! 5 with n
  exact NNReal.eq (by simp)

/-- **Cauchy–Hadamard formula**: the inverse of the radius of `∑ aₙ Xⁿ` is
`limsup ‖aₙ‖ ^ (1 / n)`. -/
theorem radius_inv_eq_limsup :
    f.radius⁻¹ = limsup (fun n ↦ ((‖coeff n f‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  simpa [ENNReal.inv_liminf] using congr($(radius_eq_liminf (f := f))⁻¹)

/-- Over a ring with multiplicative norm, the geometric series `∑ aⁿ Xⁿ` has radius `‖a‖⁻¹`.
For `a ≠ 0` it is restricted at every smaller radius but not at `‖a‖⁻¹` itself; for `a = 0` it is
the constant `1` and the radius is `∞`. -/
theorem radius_mk_pow [NormMulClass R] (a : R) :
    (mk fun n ↦ a ^ n).radius = (‖a‖₊ : ℝ≥0∞)⁻¹ := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [nnnorm_zero, ENNReal.coe_zero, ENNReal.inv_zero]
    refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ le_radius_of_bound ‖(1 : R)‖ fun n ↦ ?_
    cases n <;> simp
  have : Nontrivial R := ⟨⟨a, 0, ha⟩⟩
  have : NormOneClass R := NormMulClass.toNormOneClass
  have ha' : ‖a‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr ha
  rw [← ENNReal.coe_inv ha']
  refine le_antisymm (le_of_not_gt fun h ↦ ?_) (le_radius_of_bound 1 fun n ↦ ?_)
  · refine TauCeti.PowerSeries.not_isRestricted_mk_pow ha (isRestricted_of_lt_radius ?_)
    rwa [enorm_eq_nnnorm, nnnorm_inv, nnnorm_norm]
  · rw [coeff_mk, norm_pow, NNReal.coe_inv, coe_nnnorm, ← mul_pow,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_pow]

end NormedRing

/-- Over a nontrivially normed field `K`, the radius of `f` is the radius of the scalar formal
multilinear series `FormalMultilinearSeries.ofScalars E (coeff · f)` in any normed `K`-algebra
`E` with `‖1‖ = 1`. -/
theorem radius_eq_radius_ofScalars {K : Type*} [NontriviallyNormedField K] (E : Type*)
    [NormedRing E] [NormOneClass E] [NormedAlgebra K E] (f : K⟦X⟧) :
    f.radius = (FormalMultilinearSeries.ofScalars E fun n ↦ coeff n f).radius :=
  radius_eq_radius_of_norm_eq _ fun n ↦ FormalMultilinearSeries.ofScalars_norm E _ n

end PowerSeries
