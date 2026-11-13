/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Radius
public import TauCeti.RingTheory.PowerSeries.Convergence

/-!
# Pointwise convergence radius from the Newton polygon

Fix a real additive valuation `v` on a normed division ring `K` and a base `b > 1` recovering the
norm via `‖x‖ = b ^ (-(v x).untop₀)` for `x ≠ 0`. By `PowerSeries.radius_eq_exp_linearGrowthInf`,
the intrinsic coefficient radius of `f = ∑ aₙ Xⁿ` is `b ^ λ`, where
`λ = liminf_{n → ∞} v (aₙ) / n` is `LinearGrowth.linearGrowthInf`.

This file relates `λ` and the Newton slopes of `f` to the pointwise convergence radius
`PowerSeries.convergenceRadius f L` in complete extensions `L` of `K`:

* Over *any* complete nontrivially normed field extension `L` (even discretely normed, such as
  `ℚ_[p]`), `f.convergenceRadius L = 0` if and only if the coefficient heights fail to be
  admissible (`¬IsAdmissible`), and `f.convergenceRadius L = ⊤` if and only if `λ = ⊤` (for
  admissible infinitely supported `f`, if and only if the finite Newton slopes are unbounded).
* When `L` is complete and either densely normed (such as `ℂ_[p]`) or algebraically closed and
  nontrivially normed, `f.convergenceRadius L` equals `b ^ λ`, and for admissible infinitely
  supported `f` it equals `b` raised to the supremum of the finite unit slopes of
  `f.newtonPolygon v`.
* Over a discretely normed complete ultrametric extension `A` whose nonzero norms are integer
  powers `b ^ m`, whenever `λ = t ∈ ℝ` is not an integer and `b ^ ⌊t⌋` is attained in `A`, the
  pointwise convergence radius rounds down to `b ^ ⌊t⌋`, giving the strict inequality
  `f.convergenceRadius A < f.radius`.

## Main results

* `PowerSeries.convergenceRadius_eq_zero_iff_not_isAdmissible`,
  `PowerSeries.convergenceRadius_eq_top_iff_linearGrowthInf_eq_top` and
  `PowerSeries.convergenceRadius_eq_top_iff_iSup_unitSlope_newtonPolygon_eq_top`: vanishing and
  finiteness/infinite pointwise convergence radius in any complete nontrivially normed extension.
* `PowerSeries.convergenceRadius_eq_exp_linearGrowthInf`,
  `PowerSeries.convergenceRadius_eq_ofReal_rpow`,
  `PowerSeries.convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon` and their `*_of_isAlgClosed`
  counterparts: Newton-polygon formulas for `f.convergenceRadius L` in complete densely normed or
  algebraically closed nontrivially normed extensions `L`.
* `PowerSeries.convergenceRadius_eq_ofReal_zpow_floor` and
  `PowerSeries.convergenceRadius_lt_radius_of_linearGrowthInf`: rounding down to `b ^ ⌊t⌋` and
  strict inequality `f.convergenceRadius A < f.radius` for non-integral limiting slope `t` in
  discretely normed ultrametric extensions.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open TauCeti LinearGrowth
open scoped NNReal ENNReal

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (f : K⟦X⟧)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **The vertical case in extensions.** Over any complete nontrivially normed field `L` with
isometric `K`-action, `f.convergenceRadius L = 0` if and only if the coefficient heights of `f`
have no real affine lower bound. -/
theorem convergenceRadius_eq_zero_iff_not_isAdmissible (L : Type*) [NontriviallyNormedField L]
    [SMul K L] [NormSMulClass K L] [CompleteSpace L] :
    f.convergenceRadius L = 0 ↔ ¬IsAdmissible fun n ↦ v (coeff n f) := by
  rw [convergenceRadius_eq_zero_iff_radius_eq_zero, radius_eq_zero_iff_not_isAdmissible f v hb hv]

/-- Over any complete nontrivially normed field `L` with isometric `K`-action,
`f.convergenceRadius L = ⊤` if and only if the lower linear growth of the coefficient heights is
`⊤`. -/
theorem convergenceRadius_eq_top_iff_linearGrowthInf_eq_top (L : Type*) [NontriviallyNormedField L]
    [SMul K L] [NormSMulClass K L] [CompleteSpace L] :
    f.convergenceRadius L = ⊤ ↔ (linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) = ⊤ := by
  rw [convergenceRadius_eq_top_iff, isEntire_iff_linearGrowthInf_eq_top f v hb hv]

/-- For admissible, infinitely supported `f`, its pointwise convergence radius in any complete
nontrivially normed extension `L` is `⊤` if and only if the finite unit slopes of
`f.newtonPolygon v` are unbounded. -/
theorem convergenceRadius_eq_top_iff_iSup_unitSlope_newtonPolygon_eq_top (L : Type*)
    [NontriviallyNormedField L] [SMul K L] [NormSMulClass K L] [CompleteSpace L]
    (hf : IsAdmissible fun n ↦ v (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.convergenceRadius L = ⊤ ↔ ⨆ i : finiteEdges (f.newtonPolygon v),
      (unitSlope (f.newtonPolygon v) i : EReal) = ⊤ := by
  rw [convergenceRadius_eq_top_iff, isEntire_iff_iSup_unitSlope_newtonPolygon_eq_top f v hb hv
    hf hinf]

/-- **Pointwise convergence radius from coefficient growth** in a complete densely normed extension
`L` (such as `ℂ_[p]`): `f.convergenceRadius L = b ^ λ` where `λ = liminf v (aₙ) / n`. -/
theorem convergenceRadius_eq_exp_linearGrowthInf (L : Type*) [DenselyNormedField L]
    [SMul K L] [NormSMulClass K L] [CompleteSpace L] :
    f.convergenceRadius L =
      EReal.exp ((linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) * Real.log b) := by
  rw [f.convergenceRadius_eq_radius L, radius_eq_exp_linearGrowthInf f v hb hv]

/-- **Pointwise convergence radius from coefficient growth** in a complete algebraically closed
nontrivially normed extension `L`: `f.convergenceRadius L = b ^ λ`. -/
theorem convergenceRadius_eq_exp_linearGrowthInf_of_isAlgClosed (L : Type*)
    [NontriviallyNormedField L] [IsAlgClosed L] [SMul K L] [NormSMulClass K L] [CompleteSpace L] :
    f.convergenceRadius L =
      EReal.exp ((linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) * Real.log b) := by
  rw [f.convergenceRadius_eq_radius_of_isAlgClosed L, radius_eq_exp_linearGrowthInf f v hb hv]

/-- When the lower linear growth of the coefficient heights is a finite real number `t`, the
pointwise convergence radius in a complete densely normed extension `L` is `b ^ t`. -/
theorem convergenceRadius_eq_ofReal_rpow (L : Type*) [DenselyNormedField L]
    [SMul K L] [NormSMulClass K L] [CompleteSpace L] {t : ℝ}
    (ht : (linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) = t) :
    f.convergenceRadius L = ENNReal.ofReal (b ^ t) := by
  rw [f.convergenceRadius_eq_radius L, radius_eq_ofReal_rpow f v hb hv ht]

/-- When the lower linear growth of the coefficient heights is a finite real number `t`, the
pointwise convergence radius in a complete algebraically closed nontrivially normed extension `L`
is `b ^ t`. -/
theorem convergenceRadius_eq_ofReal_rpow_of_isAlgClosed (L : Type*) [NontriviallyNormedField L]
    [IsAlgClosed L] [SMul K L] [NormSMulClass K L] [CompleteSpace L] {t : ℝ}
    (ht : (linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) = t) :
    f.convergenceRadius L = ENNReal.ofReal (b ^ t) := by
  rw [f.convergenceRadius_eq_radius_of_isAlgClosed L, radius_eq_ofReal_rpow f v hb hv ht]

/-- **Pointwise convergence radius from Newton slopes.** For admissible, infinitely supported `f`,
its pointwise convergence radius in a complete densely normed extension `L` is `b` raised to the
supremum of the finite unit slopes of `f.newtonPolygon v`. -/
theorem convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon (L : Type*) [DenselyNormedField L]
    [SMul K L] [NormSMulClass K L] [CompleteSpace L]
    (hf : IsAdmissible fun n ↦ v (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.convergenceRadius L = EReal.exp ((⨆ i : finiteEdges (f.newtonPolygon v),
      (unitSlope (f.newtonPolygon v) i : EReal)) * Real.log b) := by
  rw [f.convergenceRadius_eq_radius L, radius_eq_exp_iSup_unitSlope_newtonPolygon f v hb hv hf hinf]

/-- For admissible, infinitely supported `f`, its pointwise convergence radius in a complete
algebraically closed nontrivially normed extension `L` is `b` raised to the supremum of the finite
unit slopes of `f.newtonPolygon v`. -/
theorem convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon_of_isAlgClosed (L : Type*)
    [NontriviallyNormedField L] [IsAlgClosed L] [SMul K L] [NormSMulClass K L] [CompleteSpace L]
    (hf : IsAdmissible fun n ↦ v (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.convergenceRadius L = EReal.exp ((⨆ i : finiteEdges (f.newtonPolygon v),
      (unitSlope (f.newtonPolygon v) i : EReal)) * Real.log b) := by
  rw [f.convergenceRadius_eq_radius_of_isAlgClosed L,
    radius_eq_exp_iSup_unitSlope_newtonPolygon f v hb hv hf hinf]

/-- **Discretely normed extensions round non-integral limiting slopes down.** Let `A` be a complete
ultrametric extension whose nonzero norms are integer powers of `b`. If the lower linear growth of
`v (aₙ)` is a non-integral real number `t` (`(⌊t⌋ : ℝ) < t`) and `b ^ ⌊t⌋` is attained as a norm in
`A`, then `f.convergenceRadius A = ENNReal.ofReal (b ^ ⌊t⌋)`. -/
theorem convergenceRadius_eq_ofReal_zpow_floor (A : Type*) [SeminormedRing A] [SMul K A]
    [NormSMulClass K A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    (hdisc : ∀ y : A, ‖y‖ ≠ 0 → ∃ m : ℤ, ‖y‖ = b ^ m) {t : ℝ}
    (ht : (linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) = t) (hfloor : (⌊t⌋ : ℝ) < t)
    (hatt : ∃ x : A, ‖x‖ = b ^ ⌊t⌋) :
    f.convergenceRadius A = ENNReal.ofReal (b ^ ⌊t⌋) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hrad : f.radius = ENNReal.ofReal (b ^ t) := radius_eq_ofReal_rpow f v hb hv ht
  have hres : f.IsRestricted (b ^ ⌊t⌋) := isRestricted_of_lt_radius <| by
    rw [Real.eNorm_eq_ofReal (zpow_pos hb0 ⌊t⌋).le, hrad, ← Real.rpow_intCast]
    exact ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hb0 t) |>.mpr
      (Real.rpow_lt_rpow_left_iff hb |>.mpr hfloor)
  have hnres : ¬f.IsRestricted (b ^ (⌊t⌋ + 1)) := not_isRestricted_of_radius_lt <| by
    rw [Real.eNorm_eq_ofReal (zpow_pos hb0 (⌊t⌋ + 1)).le, hrad, ← Real.rpow_intCast]
    exact ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hb0 _) |>.mpr
      (Real.rpow_lt_rpow_left_iff hb |>.mpr (by exact_mod_cast Int.lt_floor_add_one t))
  exact convergenceRadius_eq_ofReal_zpow hb hdisc hatt hres hnres

/-- Under the hypotheses of `convergenceRadius_eq_ofReal_zpow_floor`, the pointwise convergence
radius in `A` is strictly smaller than the intrinsic radius `f.radius`. -/
theorem convergenceRadius_lt_radius_of_linearGrowthInf (A : Type*) [SeminormedRing A] [SMul K A]
    [NormSMulClass K A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    (hdisc : ∀ y : A, ‖y‖ ≠ 0 → ∃ m : ℤ, ‖y‖ = b ^ m) {t : ℝ}
    (ht : (linearGrowthInf fun n ↦ (v (coeff n f)).toEReal) = t) (hfloor : (⌊t⌋ : ℝ) < t)
    (hatt : ∃ x : A, ‖x‖ = b ^ ⌊t⌋) :
    f.convergenceRadius A < f.radius := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [convergenceRadius_eq_ofReal_zpow_floor f v hb hv A hdisc ht hfloor hatt,
    radius_eq_ofReal_rpow f v hb hv ht, ← Real.rpow_intCast]
  exact ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hb0 t) |>.mpr
    (Real.rpow_lt_rpow_left_iff hb |>.mpr hfloor)

end PowerSeries
