/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Calculus.ParametricIntegral.Primitive
public import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Normalizing an area form on the annulus strip

Let `ρ (x, y) dx ∧ dy` be a positive area form on the closed annulus `(ℝ / ℤ) × [0, 1]`, given
by a density `ρ : ℝ × ℝ → ℝ` on its universal cover that is `1`-periodic in `x` and positive on
the closed strip `ℝ × [0, 1]`; periodicity and positivity are only assumed on the strip. Put

* `s(x) = ∫₀¹ ρ(x, r) dr`, the mass of the column over `x` (`TauCeti.stripColumnMass`);
* `a = ∫₀¹ s(x) dx > 0`, the total area of the annulus (`TauCeti.stripTotalMass`);
* `u(x) = a⁻¹ ∫₀ˣ s(t) dt` (`TauCeti.stripAngle`) and `v(x, y) = s(x)⁻¹ ∫₀ʸ ρ(x, r) dr`
  (`TauCeti.stripHeight`).

The map `N (x, y) = (u(x), v(x, y))` (`TauCeti.stripNormalize`) normalizes the area form: its
Jacobian determinant is `ρ / a`, that is `a du ∧ dv = ρ dx ∧ dy`
(`TauCeti.stripTotalMass_mul_det_fderiv_stripNormalize`). It commutes with the deck translation,
`N (x + 1, y) = N (x, y) + (1, 0)`, and preserves both boundary lines, `N (x, 0) = (u(x), 0)` and
`N (x, 1) = (u(x), 1)`. The angular coordinate `u` is a strictly increasing surjection of `ℝ`
with `u(x + 1) = u(x) + 1` (`TauCeti.strictMono_stripAngle`, `TauCeti.surjective_stripAngle`,
`TauCeti.stripAngle_add_one`), that is, a continuous degree-one circle lift; being strictly
increasing, it preserves strict inequalities between boundary points, and hence the strict
boundary displacement conditions of a map of the strip.

The map `N` is a bijection of the closed strip onto itself (`TauCeti.bijOn_stripNormalize`),
`C^n` when `ρ` is, and for `n ≥ 1` its inverse on the strip (`TauCeti.stripNormalizeInv`) is
`C^n` on the closed strip as well (`TauCeti.contDiffOn_stripNormalizeInv`): the inverse function
theorem applies at every point of the strip, and near the strip the sign of `v` and of `1 - v`
detects the two boundary lines.

Consequently a map of the strip preserving `ρ dx ∧ dy`, in the sense that
`ρ(F p) · det DF_p = ρ(p)`, becomes area preserving for the standard form `dx ∧ dy` after
conjugation by `N` (`TauCeti.det_fderivWithin_eq_one_of_comp_stripNormalize`), at the points of
the boundary lines as well, where the conjugate is only defined on the strip. This reduces
fixed-point theorems for area-preserving maps of the annulus with a smooth positive area form,
such as the Poincaré–Birkhoff theorem, to the standard area form. For the constant density the
normalization is the identity (`TauCeti.stripNormalize_const`).

The smoothness statements assume that `ρ` is `C^n` on the whole plane `ℝ × ℝ`, not just on the
closed strip: the inverse function theorem is applied at the boundary points of the strip, which
needs `N` to be differentiable on a full neighbourhood of them. A density that is only known to
be smooth on the closed strip must first be extended to a smooth density on the plane; that
extension of smooth functions from a closed half-plane is not part of this file.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. 120 (1965),
  286–294.
-/

public section

noncomputable section

open Set Filter Topology MeasureTheory

namespace TauCeti

variable {ρ : ℝ × ℝ → ℝ}

/-! ### The normalizing coordinates -/

/-- The mass `s(x) = ∫₀¹ ρ(x, r) dr` of the column over `x` of the strip `ℝ × [0, 1]`. -/
def stripColumnMass (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, ρ (x, r)

/-- The total mass `a = ∫₀¹ s(x) dx` of the fundamental domain `[0, 1] × [0, 1]` of the strip,
the area of the annulus `(ℝ / ℤ) × [0, 1]` for the density `ρ`. -/
def stripTotalMass (ρ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, stripColumnMass ρ x

/-- The angular coordinate `u(x) = a⁻¹ ∫₀ˣ s(t) dt` of the area normalization of the strip. -/
def stripAngle (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  (stripTotalMass ρ)⁻¹ * ∫ t in (0 : ℝ)..x, stripColumnMass ρ t

/-- The height coordinate `v(x, y) = s(x)⁻¹ ∫₀ʸ ρ(x, r) dr` of the area normalization of the
strip. -/
def stripHeight (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (stripColumnMass ρ p.1)⁻¹ * ∫ r in (0 : ℝ)..p.2, ρ (p.1, r)

/-- The **area normalization** `N (x, y) = (u(x), v(x, y))` of the strip `ℝ × [0, 1]` for the
density `ρ`. -/
def stripNormalize (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (stripAngle ρ p.1, stripHeight ρ p)

theorem stripColumnMass_def (x : ℝ) : stripColumnMass ρ x = ∫ r in (0 : ℝ)..1, ρ (x, r) :=
  (rfl)

theorem stripTotalMass_def : stripTotalMass ρ = ∫ x in (0 : ℝ)..1, stripColumnMass ρ x :=
  (rfl)

theorem stripAngle_def (x : ℝ) :
    stripAngle ρ x = (stripTotalMass ρ)⁻¹ * ∫ t in (0 : ℝ)..x, stripColumnMass ρ t :=
  (rfl)

theorem stripHeight_def (p : ℝ × ℝ) :
    stripHeight ρ p = (stripColumnMass ρ p.1)⁻¹ * ∫ r in (0 : ℝ)..p.2, ρ (p.1, r) :=
  (rfl)

@[simp]
theorem stripNormalize_apply (p : ℝ × ℝ) :
    stripNormalize ρ p = (stripAngle ρ p.1, stripHeight ρ p) :=
  (rfl)

/-! ### Masses -/

theorem continuous_stripColumnMass (hρ : Continuous ρ) : Continuous (stripColumnMass ρ) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x r ↦ ρ (x, r)) hρ 0 1

/-- The column masses are positive when `ρ` is positive on the closed strip. -/
theorem stripColumnMass_pos (hρ : Continuous ρ) (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y))
    (x : ℝ) : 0 < stripColumnMass ρ x :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hρ.comp (Continuous.prodMk_right x)).intervalIntegrable _ _)
    (fun r hr ↦ hpos x r (Ioo_subset_Icc_self hr)) zero_lt_one

/-- The column masses of an `x`-periodic density are periodic. -/
theorem periodic_stripColumnMass
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) :
    Function.Periodic (stripColumnMass ρ) 1 := fun x ↦
  intervalIntegral.integral_congr fun r hr ↦ hper x r (by rwa [uIcc_of_le zero_le_one] at hr)

/-- The total mass is positive when `ρ` is positive on the closed strip. -/
theorem stripTotalMass_pos (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : 0 < stripTotalMass ρ :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_stripColumnMass hρ).intervalIntegrable _ _)
    (fun x _ ↦ stripColumnMass_pos hρ hpos x) zero_lt_one

/-! ### The angular coordinate -/

@[simp]
theorem stripAngle_zero : stripAngle ρ 0 = 0 := by
  simp [stripAngle_def]

/-- The derivative of the angular coordinate is `u'(x) = a⁻¹ s(x)`. -/
theorem hasDerivAt_stripAngle (hρ : Continuous ρ) (x : ℝ) :
    HasDerivAt (stripAngle ρ) ((stripTotalMass ρ)⁻¹ * stripColumnMass ρ x) x :=
  (((continuous_stripColumnMass hρ).integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul _

theorem continuous_stripAngle (hρ : Continuous ρ) : Continuous (stripAngle ρ) :=
  continuous_iff_continuousAt.2 fun x ↦ (hasDerivAt_stripAngle hρ x).continuousAt

/-- The angular coordinate of an `x`-periodic density is a degree-one lift:
`u(x + 1) = u(x) + 1`. -/
theorem stripAngle_add_one (hρ : Continuous ρ)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (x : ℝ) :
    stripAngle ρ (x + 1) = stripAngle ρ x + 1 := by
  have hs := continuous_stripColumnMass hρ
  rw [stripAngle_def, stripAngle_def,
    ← intervalIntegral.integral_add_adjacent_intervals (b := x) (hs.intervalIntegrable _ _)
      (hs.intervalIntegrable _ _),
    (periodic_stripColumnMass hper).intervalIntegral_add_eq x 0, zero_add, mul_add,
    ← stripTotalMass_def, inv_mul_cancel₀ (stripTotalMass_pos hρ hpos).ne']

theorem strictMono_stripAngle (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : StrictMono (stripAngle ρ) :=
  strictMono_of_deriv_pos fun x ↦ (hasDerivAt_stripAngle hρ x).deriv ▸
    mul_pos (inv_pos.2 (stripTotalMass_pos hρ hpos)) (stripColumnMass_pos hρ hpos x)

/-- The angular coordinate of an `x`-periodic density is a surjection of `ℝ`, since it is a
continuous degree-one circle lift. -/
theorem surjective_stripAngle (hρ : Continuous ρ)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : Function.Surjective (stripAngle ρ) :=
  let u : CircleDeg1Lift :=
    ⟨⟨stripAngle ρ, (strictMono_stripAngle hρ hpos).monotone⟩, stripAngle_add_one hρ hper hpos⟩
  u.continuous_iff_surjective.1 (continuous_stripAngle hρ)

/-! ### The height coordinate -/

@[simp]
theorem stripHeight_mk_zero (x : ℝ) : stripHeight ρ (x, 0) = 0 := by
  simp [stripHeight_def]

theorem stripHeight_mk_one (hρ : Continuous ρ) (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y))
    (x : ℝ) : stripHeight ρ (x, 1) = 1 :=
  inv_mul_cancel₀ (stripColumnMass_pos hρ hpos x).ne'

theorem stripHeight_add_one (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (x : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    stripHeight ρ (x + 1, y) = stripHeight ρ (x, y) := by
  simp only [stripHeight_def, periodic_stripColumnMass hper x]
  congr 1
  refine intervalIntegral.integral_congr fun r hr ↦ hper x r ?_
  rw [uIcc_of_le hy.1] at hr
  exact ⟨hr.1, hr.2.trans hy.2⟩

theorem continuous_stripHeight (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : Continuous (stripHeight ρ) :=
  (((continuous_stripColumnMass hρ).comp continuous_fst).inv₀ fun p ↦
    (stripColumnMass_pos hρ hpos p.1).ne').mul
    (intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun x r ↦ ρ (x, r)) hρ)

/-- On each column of the closed strip the height coordinate is strictly increasing. -/
theorem strictMonoOn_stripHeight (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (x : ℝ) :
    StrictMonoOn (fun y ↦ stripHeight ρ (x, y)) (Icc 0 1) := by
  intro y hy y' hy' hlt
  have hc : Continuous fun r ↦ ρ (x, r) := hρ.comp (Continuous.prodMk_right x)
  refine mul_lt_mul_of_pos_left ?_ (inv_pos.2 (stripColumnMass_pos hρ hpos x))
  rw [← sub_pos, intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
    (fun r hr ↦ hpos x r ⟨hy.1.trans hr.1.le, hr.2.le.trans hy'.2⟩) hlt

/-- Below the strip, the height coordinate is negative as long as `ρ` stays positive on the
segment from the point up to the lower boundary line. -/
private theorem stripHeight_neg (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {x y : ℝ} (hy : y < 0)
    (hρy : ∀ r ∈ Icc y 0, 0 < ρ (x, r)) : stripHeight ρ (x, y) < 0 := by
  have hc : Continuous fun r ↦ ρ (x, r) := hρ.comp (Continuous.prodMk_right x)
  refine mul_neg_of_pos_of_neg (inv_pos.2 (stripColumnMass_pos hρ hpos x)) ?_
  rw [intervalIntegral.integral_symm, neg_neg_iff_pos]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
    (fun r hr ↦ hρy r (Ioo_subset_Icc_self hr)) hy

/-- Above the strip, the height coordinate exceeds `1` as long as `ρ` stays positive on the
segment from the upper boundary line up to the point. -/
private theorem one_lt_stripHeight (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {x y : ℝ} (hy : 1 < y)
    (hρy : ∀ r ∈ Icc 1 y, 0 < ρ (x, r)) : 1 < stripHeight ρ (x, y) := by
  have hc : Continuous fun r ↦ ρ (x, r) := hρ.comp (Continuous.prodMk_right x)
  have hs := stripColumnMass_pos hρ hpos x
  have hI : 0 < ∫ r in (1 : ℝ)..y, ρ (x, r) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
      (fun r hr ↦ hρy r (Ioo_subset_Icc_self hr)) hy
  rw [stripHeight_def, ← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), ← stripColumnMass_def, mul_add,
    inv_mul_cancel₀ hs.ne']
  exact lt_add_of_pos_right _ (mul_pos (inv_pos.2 hs) hI)

/-! ### The normalization as a map of the strip -/

/-- The area normalization commutes with the deck translation `(x, y) ↦ (x + 1, y)`. -/
theorem stripNormalize_add_one (hρ : Continuous ρ)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (x : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    stripNormalize ρ (x + 1, y) = stripNormalize ρ (x, y) + (1, 0) := by
  simp [stripAngle_add_one hρ hper hpos, stripHeight_add_one hper x hy]

/-- The area normalization preserves the lower boundary line. -/
theorem stripNormalize_mk_zero (x : ℝ) : stripNormalize ρ (x, 0) = (stripAngle ρ x, 0) := by
  simp

/-- The area normalization preserves the upper boundary line. -/
theorem stripNormalize_mk_one (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (x : ℝ) :
    stripNormalize ρ (x, 1) = (stripAngle ρ x, 1) := by
  simp [stripHeight_mk_one hρ hpos]

theorem mapsTo_stripNormalize (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    MapsTo (stripNormalize ρ) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) := by
  rintro ⟨x, y⟩ ⟨-, hy⟩
  have hmono := (strictMonoOn_stripHeight hρ hpos x).monotoneOn
  refine ⟨mem_univ _, ?_, ?_⟩
  · simpa using hmono ⟨le_rfl, zero_le_one⟩ hy hy.1
  · simpa [stripHeight_mk_one hρ hpos] using hmono hy ⟨zero_le_one, le_rfl⟩ hy.2

theorem injOn_stripNormalize (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    InjOn (stripNormalize ρ) (univ ×ˢ Icc 0 1) := by
  rintro ⟨x, y⟩ ⟨-, hy⟩ ⟨x', y'⟩ ⟨-, hy'⟩ h
  simp only [stripNormalize_apply, Prod.mk.injEq] at h
  obtain rfl := (strictMono_stripAngle hρ hpos).injective h.1
  exact Prod.ext rfl ((strictMonoOn_stripHeight hρ hpos x).injOn hy hy' h.2)

theorem surjOn_stripNormalize (hρ : Continuous ρ)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    SurjOn (stripNormalize ρ) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) := by
  rintro ⟨ξ, η⟩ ⟨-, hη⟩
  obtain ⟨x, rfl⟩ := surjective_stripAngle hρ hper hpos ξ
  have hc : ContinuousOn (fun y ↦ stripHeight ρ (x, y)) (Icc 0 1) :=
    ((continuous_stripHeight hρ hpos).comp (Continuous.prodMk_right x)).continuousOn
  obtain ⟨y, hy, hyη⟩ := intermediate_value_Icc zero_le_one hc
    (by simpa [stripHeight_mk_one hρ hpos] using hη)
  exact ⟨(x, y), ⟨mem_univ _, hy⟩, by simp [hyη]⟩

/-- **The area normalization is a bijection of the closed strip `ℝ × [0, 1]`.** -/
theorem bijOn_stripNormalize (hρ : Continuous ρ)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    BijOn (stripNormalize ρ) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) :=
  ⟨mapsTo_stripNormalize hρ hpos, injOn_stripNormalize hρ hpos,
    surjOn_stripNormalize hρ hper hpos⟩

/-- The inverse of the area normalization on the closed strip `ℝ × [0, 1]`. Its values off the
strip carry no meaning. -/
def stripNormalizeInv (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ × ℝ :=
  Function.invFunOn (stripNormalize ρ) (univ ×ˢ Icc 0 1)

/-- On the closed strip, `TauCeti.stripNormalizeInv` is a two-sided inverse of the area
normalization. -/
theorem invOn_stripNormalizeInv (hρ : Continuous ρ)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    InvOn (stripNormalizeInv ρ) (stripNormalize ρ) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) :=
  (bijOn_stripNormalize hρ hper hpos).invOn_invFunOn

theorem bijOn_stripNormalizeInv (hρ : Continuous ρ)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    BijOn (stripNormalizeInv ρ) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) :=
  (bijOn_stripNormalize hρ hper hpos).symm (invOn_stripNormalizeInv hρ hper hpos).symm

/-! ### Smoothness and the Jacobian -/

theorem contDiff_stripColumnMass {n : ℕ∞} (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (stripColumnMass ρ) :=
  hρ.parametric_intervalIntegral

theorem contDiff_stripAngle {n : ℕ∞} (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (stripAngle ρ) :=
  contDiff_const.mul <| (contDiff_parametric_primitive_of_contDiff
    (f := fun _ : ℝ ↦ stripColumnMass ρ) ((contDiff_stripColumnMass hρ).comp contDiff_snd)
    0).comp (contDiff_id.prodMk contDiff_id)

theorem contDiff_stripHeight {n : ℕ∞} (hρ : ContDiff ℝ n ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : ContDiff ℝ n (stripHeight ρ) :=
  (((contDiff_stripColumnMass hρ).comp contDiff_fst).inv fun p ↦
    (stripColumnMass_pos hρ.continuous hpos p.1).ne').mul
    (contDiff_parametric_primitive_of_contDiff (f := fun x r ↦ ρ (x, r)) hρ 0)

/-- The area normalization is `C^n` when the density is. -/
theorem contDiff_stripNormalize {n : ℕ∞} (hρ : ContDiff ℝ n ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : ContDiff ℝ n (stripNormalize ρ) :=
  ((contDiff_stripAngle hρ).comp contDiff_fst).prodMk (contDiff_stripHeight hρ hpos)

/-- The first column of the Jacobian matrix of the area normalization has first entry
`u'(x) = a⁻¹ s(x)`. -/
private theorem fderiv_stripNormalize_apply_one_zero_fst (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (p : ℝ × ℝ) :
    (fderiv ℝ (stripNormalize ρ) p (1, 0)).1 =
      (stripTotalMass ρ)⁻¹ * stripColumnMass ρ p.1 := by
  have hN := ((contDiff_stripNormalize hρ hpos).differentiable one_ne_zero p).hasFDerivAt
  have hu := ((hasDerivAt_stripAngle hρ.continuous p.1).hasFDerivAt).comp p (hasFDerivAt_fst)
  have h := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ ↦ L (1, 0)) (hN.fst.unique hu)
  simpa using h

/-- The second column of the Jacobian matrix of the area normalization is `(0, ρ / s)`. -/
private theorem fderiv_stripNormalize_apply_zero_one (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (p : ℝ × ℝ) :
    fderiv ℝ (stripNormalize ρ) p (0, 1) = (0, (stripColumnMass ρ p.1)⁻¹ * ρ p) := by
  obtain ⟨x, y⟩ := p
  have hN := ((contDiff_stripNormalize hρ hpos).differentiable one_ne_zero (x, y)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ (x, t)) (0, 1) y :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  have hc : Continuous fun r ↦ ρ (x, r) := hρ.continuous.comp (Continuous.prodMk_right x)
  have hv : HasDerivAt (fun t ↦ stripHeight ρ (x, t)) ((stripColumnMass ρ x)⁻¹ * ρ (x, y)) y := by
    simp only [stripHeight_def]
    exact (hc.integral_hasStrictDerivAt 0 y).hasDerivAt.const_mul _
  exact (hN.comp_hasDerivAt y hline).unique ((hasDerivAt_const y (stripAngle ρ x)).prodMk hv)

/-- **The area normalization normalizes the area form**: `a du ∧ dv = ρ dx ∧ dy`, that is, the
Jacobian determinant of `N` is `ρ / a`. -/
theorem stripTotalMass_mul_det_fderiv_stripNormalize (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (p : ℝ × ℝ) :
    stripTotalMass ρ * (fderiv ℝ (stripNormalize ρ) p).det = ρ p := by
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp only [ContinuousLinearMap.coe_coe, fderiv_stripNormalize_apply_one_zero_fst hρ hpos,
    fderiv_stripNormalize_apply_zero_one hρ hpos, mul_zero, sub_zero]
  have ha := (stripTotalMass_pos hρ.continuous hpos).ne'
  have hs := (stripColumnMass_pos hρ.continuous hpos p.1).ne'
  field_simp

/-- At a point where the density does not vanish, the derivative of the area normalization is
invertible. -/
theorem det_fderiv_stripNormalize_ne_zero (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {p : ℝ × ℝ} (hp : ρ p ≠ 0) :
    (fderiv ℝ (stripNormalize ρ) p).det ≠ 0 := fun h ↦
  hp <| by rw [← stripTotalMass_mul_det_fderiv_stripNormalize hρ hpos p, h, mul_zero]

/-- Near a point of the closed strip, a point that the area normalization sends into the strip
already lies in the strip. -/
private theorem eventually_mem_strip_of_stripNormalize_mem (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ Icc 0 1) :
    ∀ᶠ p' in 𝓝 p, stripNormalize ρ p' ∈ univ ×ˢ Icc 0 1 → p' ∈ univ ×ˢ Icc 0 1 := by
  obtain ⟨x, y⟩ := p
  obtain ⟨-, hy⟩ := hp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hρ.continuousAt (x := (x, y))).eventually (lt_mem_nhds (hpos x y hy)))
  filter_upwards [Metric.ball_mem_nhds _ hδ] with ⟨x', y'⟩ hp' hN
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp'
  obtain ⟨-, hv⟩ := hN
  dsimp only at hp' hv
  refine ⟨mem_univ _, ?_, ?_⟩
  · by_contra! hy'
    -- Every point of the segment from `(x', y')` up to `(x', 0)` is `δ`-close to `(x, y)`.
    refine (stripHeight_neg hρ hpos hy' fun r hr ↦ hball ?_).not_ge hv.1
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    dsimp only at hp' hy hr ⊢
    simp only [abs_lt] at hp' ⊢
    exact ⟨hp'.1, by constructor <;> linarith [hr.1, hr.2, hy.1, hp'.2.1, hp'.2.2]⟩
  · by_contra! hy'
    -- Every point of the segment from `(x', 1)` up to `(x', y')` is `δ`-close to `(x, y)`.
    refine (one_lt_stripHeight hρ hpos hy' fun r hr ↦ hball ?_).not_ge hv.2
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    dsimp only at hp' hy hr ⊢
    simp only [abs_lt] at hp' ⊢
    exact ⟨hp'.1, by constructor <;> linarith [hr.1, hr.2, hy.2, hp'.2.1, hp'.2.2]⟩

/-- **The inverse of the area normalization is smooth on the closed strip.** For a `C^n`
density with `n ≥ 1`, the inverse `TauCeti.stripNormalizeInv` of the area normalization is `C^n`
on the closed strip `ℝ × [0, 1]`. -/
theorem contDiffOn_stripNormalizeInv {n : ℕ∞} (hρ : ContDiff ℝ n ρ) (hn : 1 ≤ n)
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    ContDiffOn ℝ n (stripNormalizeInv ρ) (univ ×ˢ Icc 0 1) := by
  intro q hq
  have hinv := invOn_stripNormalizeInv hρ.continuous hper hpos
  set p := stripNormalizeInv ρ q
  have hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1 := (bijOn_stripNormalizeInv hρ.continuous hper hpos).mapsTo hq
  have hNp : stripNormalize ρ p = q := hinv.2 hq
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast hn)
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hn).ne'
  have hN : ContDiffAt ℝ n (stripNormalize ρ) p := (contDiff_stripNormalize hρ hpos).contDiffAt
  have hdet := det_fderiv_stripNormalize_ne_zero hρ1 hpos (hpos p.1 p.2 hp.2).ne'
  have hD : HasFDerivAt (stripNormalize ρ)
      (((fderiv ℝ (stripNormalize ρ) p).toContinuousLinearEquivOfDetNeZero hdet :
        ℝ × ℝ →L[ℝ] ℝ × ℝ)) p := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact ((contDiff_stripNormalize hρ1 hpos).differentiable one_ne_zero p).hasFDerivAt
  have hstrict := hN.hasStrictFDerivAt hD hn0
  -- The local inverse `g` of `N` at `p` is `C^n` at `q = N p` and agrees with
  -- `stripNormalizeInv` on the strip near `q`.
  set g := hstrict.localInverse _ _ p
  have hg : ContDiffAt ℝ n g q := hNp ▸ hN.to_localInverse hD hn0
  have hcont : Tendsto g (𝓝 q) (𝓝 p) := hNp ▸ hstrict.localInverse_tendsto
  refine hg.contDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (hNp ▸ hstrict.eventually_right_inverse),
      nhdsWithin_le_nhds
        (hcont.eventually (eventually_mem_strip_of_stripNormalize_mem hρ.continuous hpos hp)),
      self_mem_nhdsWithin] with q' hright hmem hq'
    rw [← hinv.1 (hmem (by rwa [hright])), hright]
  · calc stripNormalizeInv ρ q = p := rfl
      _ = g (stripNormalize ρ p) := hstrict.localInverse_apply_image.symm
      _ = g q := by rw [hNp]

/-! ### Transport of area-preserving maps -/

/-- **Area-preserving maps become standard area preserving.** Let `F` preserve the area form
`ρ dx ∧ dy` at a point `p` of the closed strip, in the sense that `ρ(F p) · det DF_p = ρ(p)`, and
let `G` be the conjugate of `F` by the area normalization `N` on the strip near `p`, so that
`G ∘ N = N ∘ F` on the strip near `p`. Then `G` preserves the standard area form `dx ∧ dy` at
`N p`: the determinant of the derivative of `G` within the strip at `N p` is `1`. This covers the
points of the boundary lines, where `G` need only be defined on the strip, as for the conjugate
`N ∘ F ∘ TauCeti.stripNormalizeInv`. -/
theorem det_fderivWithin_eq_one_of_comp_stripNormalize (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {F G : ℝ × ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ Icc 0 1) (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableWithinAt ℝ G (univ ×ˢ Icc 0 1) (stripNormalize ρ p))
    (hFρ : ρ (F p) * (fderiv ℝ F p).det = ρ p)
    (hconj : G ∘ stripNormalize ρ =ᶠ[𝓝[univ ×ˢ Icc 0 1] p] stripNormalize ρ ∘ F) :
    (fderivWithin ℝ G (univ ×ˢ Icc 0 1) (stripNormalize ρ p)).det = 1 := by
  have hN := (contDiff_stripNormalize hρ hpos).differentiable one_ne_zero
  have hchain : (fderivWithin ℝ G (univ ×ˢ Icc 0 1) (stripNormalize ρ p)).comp
      (fderiv ℝ (stripNormalize ρ) p) =
      (fderiv ℝ (stripNormalize ρ) (F p)).comp (fderiv ℝ F p) :=
    ((uniqueDiffOn_univ.prod uniqueDiffOn_Icc_zero_one) p hp).eq
      (hG.hasFDerivWithinAt.comp p (hN p).hasFDerivAt.hasFDerivWithinAt
        (mapsTo_stripNormalize hρ.continuous hpos))
      ((((hN (F p)).hasFDerivAt.comp p hF.hasFDerivAt).hasFDerivWithinAt).congr_of_eventuallyEq
        hconj (hconj.eq_of_nhdsWithin hp))
  have hdet := congrArg ContinuousLinearMap.det hchain
  have ha := stripTotalMass_mul_det_fderiv_stripNormalize hρ hpos p
  have hb := stripTotalMass_mul_det_fderiv_stripNormalize hρ hpos (F p)
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, LinearMap.det_comp] at hdet
  simp only [ContinuousLinearMap.det] at ha hb hFρ ⊢
  -- `det DG · ρ(p) = a · det DG · det DN_p = a · det DN_(F p) · det DF_p = ρ(F p) · det DF_p`.
  set dG := LinearMap.det
    (fderivWithin ℝ G (univ ×ˢ Icc 0 1) (stripNormalize ρ p) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ)
  have key : (dG - 1) * ρ p = 0 := by
    linear_combination stripTotalMass ρ * hdet - dG * ha +
      LinearMap.det (fderiv ℝ F p : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) * hb + hFρ
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right (hpos p.1 p.2 hp.2).ne')

/-! ### The constant density -/

/-- For a nonzero constant density the area normalization is the identity. -/
theorem stripNormalize_const {c : ℝ} (hc : c ≠ 0) : stripNormalize (fun _ ↦ c) = id := by
  funext ⟨x, y⟩
  simp [stripAngle_def, stripHeight_def, stripTotalMass_def, stripColumnMass_def,
    mul_inv_cancel_right₀ hc, mul_comm c⁻¹]

end TauCeti
