/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.Topology.Order.ProjIcc

/-!
# Normalizing a periodic area form on the annulus strip

Let `ρ` be a function on the plane `ℝ × ℝ`, `1`-periodic in the first coordinate and positive on
the strip `ℝ × [0, 1]`, so that `ρ dx ∧ dy` is a positive area form on the strip covering the
closed annulus `(ℝ / ℤ) × [0, 1]`. This file writes down explicit coordinates in which this form
is a constant multiple of `dx ∧ dy`. With the column means and the area of the annulus

`s(x) = ∫₀¹ ρ(x, r) dr`  (`TauCeti.stripColumnMean`),
`a = ∫₀¹ s(x) dx`  (`TauCeti.annulusArea`),

put

`u(x) = a⁻¹ ∫₀ˣ s(t) dt`  (`TauCeti.stripAreaFraction`),
`v(x, y) = s(x)⁻¹ ∫₀ʸ ρ(x, r) dr`,

and `Φ(x, y) = (u(x), v(x, y))` (`TauCeti.stripDensityNormalization`). Then:

* `Φ` is triangular: when `ρ` is positive on the strip, `u` is strictly increasing
  (`TauCeti.stripAreaFraction_strictMono`), and for each `x` the map `y ↦ v(x, y)` is strictly
  increasing where `ρ(x, ·)` is positive (`TauCeti.strictMonoOn_stripDensityNormalization_snd`).
  So `Φ` preserves the order of first coordinates, and with it the sign of the horizontal
  displacement `X(x, y) - x` of a map along either boundary line.
* `Φ` fixes the boundary lines: `v(x, 0) = 0` and `v(x, 1) = 1`
  (`TauCeti.stripDensityNormalization_snd_mk_zero`, `TauCeti.stripDensityNormalization_snd_mk_one`).
  On the strip it commutes with the deck translation, `Φ(x + 1, y) = Φ(x, y) + (1, 0)`
  (`TauCeti.stripDensityNormalization_add_fst`), and it maps the strip bijectively onto itself
  (`TauCeti.bijOn_stripDensityNormalization`).
* Its Jacobian determinant is `ρ / a` (`TauCeti.det_fderiv_stripDensityNormalization`), that is,
  `Φ^*(a dx ∧ dy) = ρ dx ∧ dy`: in the coordinates `(u, v)` the form `ρ dx ∧ dy` is `a du ∧ dv`.
  The factor `a` cannot be dropped: `Φ` carries the annulus of `ρ`-area `a` to the annulus of
  standard area `1`.
* On the open set of points `(x, y)` such that `ρ(x, ·)` is positive on the segment between `0`
  and `y`, which contains the strip, `Φ` is injective, with positive Jacobian determinant
  (`TauCeti.det_fderiv_stripDensityNormalization_pos`). It is therefore an orientation-preserving
  open partial homeomorphism of the plane
  (`TauCeti.stripDensityNormalizationOpenPartialHomeomorph`), smooth with smooth inverse when `ρ`
  is smooth (`TauCeti.contDiffOn_stripDensityNormalizationOpenPartialHomeomorph_symm`).
* Conjugating by `Φ` turns a map preserving `ρ dx ∧ dy` into a map preserving `dx ∧ dy`: the
  Jacobian determinant of `Φ ∘ F ∘ Φ⁻¹` at `Φ(p)` is `ρ(F p) det DF_p / ρ(p)`
  (`TauCeti.det_fderiv_stripDensityNormalization_comp_comp_symm`).

These are the ingredients for conjugating a lift of an area-preserving diffeomorphism of the
annulus, for an arbitrary positive periodic area form, by a boundary-preserving
orientation-preserving diffeomorphism commuting with the deck translation, to one preserving the
standard form `dx ∧ dy`, which is the setting of the generating-function proof of the
Poincaré–Birkhoff theorem. For the constant density `ρ = 1` the
normalization is the identity (`TauCeti.stripDensityNormalization_one`), and for `ρ = 1 + y` it is
`(x, y) ↦ (x, (2y + y²) / 3)` (`TauCeti.stripDensityNormalization_one_add_snd`).

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. 120 (1965),
  286–294.
-/

public section

noncomputable section

open Filter Function Set intervalIntegral
open scoped Topology Interval

namespace TauCeti

/-! ### The normalized coordinates -/

/-- The mean `s(x) = ∫₀¹ ρ(x, r) dr` of a function `ρ` on the plane along the vertical segment
over `x` in the strip `ℝ × [0, 1]`. -/
def stripColumnMean (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, ρ (x, r)

/-- The area `a = ∫₀¹ s(x) dx = ∫₀¹ ∫₀¹ ρ(x, y) dy dx` of the annulus `(ℝ / ℤ) × [0, 1]` for the
form `ρ dx ∧ dy`, where `s` is `TauCeti.stripColumnMean ρ`. -/
def annulusArea (ρ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, stripColumnMean ρ x

/-- The fraction `u(x) = a⁻¹ ∫₀ˣ s(t) dt` of the area of the annulus lying over `[0, x]`, where `s`
is `TauCeti.stripColumnMean ρ` and `a` is `TauCeti.annulusArea ρ`. It is the first coordinate of
`TauCeti.stripDensityNormalization ρ`, and its restriction to either boundary line. -/
def stripAreaFraction (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  (annulusArea ρ)⁻¹ * ∫ t in (0 : ℝ)..x, stripColumnMean ρ t

/-- The **density normalization** `Φ(x, y) = (u(x), v(x, y))` of `ρ dx ∧ dy`, where
`u = TauCeti.stripAreaFraction ρ` and `v(x, y) = s(x)⁻¹ ∫₀ʸ ρ(x, r) dr` with
`s = TauCeti.stripColumnMean ρ`. When `ρ` is positive on the strip, it pulls `a dx ∧ dy` back to
`ρ dx ∧ dy` (`TauCeti.det_fderiv_stripDensityNormalization`), where `a = TauCeti.annulusArea ρ`. -/
def stripDensityNormalization (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (stripAreaFraction ρ p.1, (stripColumnMean ρ p.1)⁻¹ * ∫ r in (0 : ℝ)..p.2, ρ (p.1, r))

variable {ρ : ℝ × ℝ → ℝ} {n : ℕ∞}

theorem stripColumnMean_def (x : ℝ) : stripColumnMean ρ x = ∫ r in (0 : ℝ)..1, ρ (x, r) :=
  (rfl)

theorem annulusArea_def : annulusArea ρ = ∫ x in (0 : ℝ)..1, stripColumnMean ρ x :=
  (rfl)

theorem stripAreaFraction_def (x : ℝ) :
    stripAreaFraction ρ x = (annulusArea ρ)⁻¹ * ∫ t in (0 : ℝ)..x, stripColumnMean ρ t :=
  (rfl)

@[simp]
theorem stripDensityNormalization_fst (p : ℝ × ℝ) :
    (stripDensityNormalization ρ p).1 = stripAreaFraction ρ p.1 :=
  (rfl)

theorem stripDensityNormalization_snd (p : ℝ × ℝ) :
    (stripDensityNormalization ρ p).2 =
      (stripColumnMean ρ p.1)⁻¹ * ∫ r in (0 : ℝ)..p.2, ρ (p.1, r) :=
  (rfl)

/-! ### Boundary values and periodicity -/

@[simp]
theorem stripAreaFraction_zero : stripAreaFraction ρ 0 = 0 := by
  simp [stripAreaFraction_def]

/-- The area fraction over `[0, 1]` is `1`. -/
theorem stripAreaFraction_one (ha : annulusArea ρ ≠ 0) : stripAreaFraction ρ 1 = 1 := by
  rw [stripAreaFraction_def, ← annulusArea_def, inv_mul_cancel₀ ha]

/-- The normalization maps the lower boundary line `y = 0` into itself. -/
@[simp]
theorem stripDensityNormalization_snd_mk_zero (x : ℝ) :
    (stripDensityNormalization ρ (x, 0)).2 = 0 := by
  simp [stripDensityNormalization_snd]

/-- The normalization maps the upper boundary line `y = 1` into itself. -/
theorem stripDensityNormalization_snd_mk_one {x : ℝ} (hs : stripColumnMean ρ x ≠ 0) :
    (stripDensityNormalization ρ (x, 1)).2 = 1 := by
  rw [stripDensityNormalization_snd, ← stripColumnMean_def, inv_mul_cancel₀ hs]

/-- The column mean of a function `1`-periodic on the strip is `1`-periodic. -/
theorem stripColumnMean_periodic (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) :
    Periodic (stripColumnMean ρ) 1 := fun x ↦
  integral_congr fun y hy ↦ hper x y (by rwa [uIcc_of_le zero_le_one] at hy)

/-- The column means only read `ρ` on the strip. -/
private theorem stripColumnMean_congr {ρ' : ℝ × ℝ → ℝ} (h : EqOn ρ' ρ (univ ×ˢ Icc 0 1)) :
    stripColumnMean ρ' = stripColumnMean ρ :=
  funext fun x ↦ integral_congr fun y hy ↦
    h ⟨mem_univ _, by rwa [uIcc_of_le zero_le_one] at hy⟩

/-- On the strip, the density normalization only reads `ρ` there. -/
private theorem stripDensityNormalization_congr {ρ' : ℝ × ℝ → ℝ}
    (h : EqOn ρ' ρ (univ ×ˢ Icc 0 1)) :
    EqOn (stripDensityNormalization ρ') (stripDensityNormalization ρ) (univ ×ˢ Icc 0 1) := by
  have hcm := stripColumnMean_congr h
  refine fun p hp ↦ Prod.ext ?_ ?_
  · simp only [stripDensityNormalization_fst, stripAreaFraction_def, annulusArea_def, hcm]
  · simp only [stripDensityNormalization_snd, hcm]
    exact congrArg _ (integral_congr fun y hy ↦ h ⟨mem_univ _,
      Icc_subset_Icc_right hp.2.2 (by rwa [uIcc_of_le hp.2.1] at hy)⟩)

theorem continuous_stripColumnMean (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1)) :
    Continuous (stripColumnMean ρ) := by
  obtain ⟨ρ', hρ', h⟩ := hρ.exists_continuous_eqOn_univ_prod_Icc zero_le_one
  rw [← stripColumnMean_congr h]
  exact continuous_parametric_intervalIntegral_of_continuous' (f := fun x r ↦ ρ' (x, r)) hρ' 0 1

theorem continuous_stripAreaFraction (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1)) :
    Continuous (stripAreaFraction ρ) :=
  continuous_const.mul (continuous_primitive
    (fun _ _ ↦ (continuous_stripColumnMean hρ).intervalIntegrable _ _) 0)

/-- Along each vertical line `{x} × ℝ` the normalization is continuous. -/
theorem continuous_stripDensityNormalization_curry_right {x : ℝ}
    (hρ : Continuous fun r ↦ ρ (x, r)) :
    Continuous fun y ↦ stripDensityNormalization ρ (x, y) := by
  refine (continuous_prodMk (f := fun y ↦ (stripDensityNormalization ρ (x, y)).1)
    (g := fun y ↦ (stripDensityNormalization ρ (x, y)).2)).2
    ⟨by simpa using continuous_const, ?_⟩
  simp only [stripDensityNormalization_snd]
  exact continuous_const.mul (continuous_primitive
    (fun _ _ ↦ hρ.intervalIntegrable _ _) 0)

/-- For a density `1`-periodic on the strip, `u(x + 1) = u(x) + 1`: the area fraction is the
lift of a degree-one map of the circle. -/
theorem stripAreaFraction_add_one (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) (ha : annulusArea ρ ≠ 0) (x : ℝ) :
    stripAreaFraction ρ (x + 1) = stripAreaFraction ρ x + 1 := by
  have hc := continuous_stripColumnMean hρ
  have h : ∫ t in (0 : ℝ)..x + 1, stripColumnMean ρ t =
      (∫ t in (0 : ℝ)..x, stripColumnMean ρ t) + annulusArea ρ := by
    rw [← integral_add_adjacent_intervals (hc.intervalIntegrable 0 x)
      (hc.intervalIntegrable x (x + 1)),
      (stripColumnMean_periodic hper).intervalIntegral_add_eq x 0, zero_add, annulusArea_def]
  rw [stripAreaFraction_def, stripAreaFraction_def, h, mul_add, inv_mul_cancel₀ ha]

/-- On the strip, the normalization commutes with the deck translation `(x, y) ↦ (x + 1, y)`. -/
theorem stripDensityNormalization_add_fst (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) (ha : annulusArea ρ ≠ 0)
    {p : ℝ × ℝ} (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    stripDensityNormalization ρ (p + (1, 0)) = stripDensityNormalization ρ p + (1, 0) := by
  -- `v(x, y)` only reads `ρ` on `{x} × [0, y]`, which lies in the strip.
  have hint : ∫ r in (0 : ℝ)..p.2, ρ (p.1 + 1, r) = ∫ r in (0 : ℝ)..p.2, ρ (p.1, r) :=
    integral_congr fun y hy ↦ hper p.1 y <|
      Icc_subset_Icc_right hp.2 (by rwa [uIcc_of_le hp.1] at hy)
  ext
  · simp [stripAreaFraction_add_one hρ hper ha]
  · simp [stripDensityNormalization_snd, (stripColumnMean_periodic hper) p.1, hint]

/-- The area fraction is the identity on the integers. -/
theorem stripAreaFraction_intCast (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) (ha : annulusArea ρ ≠ 0) (m : ℤ) :
    stripAreaFraction ρ m = m := by
  have hg : Periodic (fun x ↦ stripAreaFraction ρ x - x) 1 := fun x ↦ by
    simp only [stripAreaFraction_add_one hρ hper ha]
    ring
  simpa [sub_eq_zero] using (hg.int_mul m).eq

/-- For a density `1`-periodic on the strip with nonzero area, the area fraction is onto. -/
theorem stripAreaFraction_surjective (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) (ha : annulusArea ρ ≠ 0) :
    Surjective (stripAreaFraction ρ) := by
  intro u
  have h1 : stripAreaFraction ρ ⌊u⌋ ≤ u := by
    rw [stripAreaFraction_intCast hρ hper ha]
    exact Int.floor_le u
  have h2 : u ≤ stripAreaFraction ρ (⌊u⌋ + 1) := by
    rw [stripAreaFraction_add_one hρ hper ha, stripAreaFraction_intCast hρ hper ha]
    exact (Int.lt_floor_add_one u).le
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by linarith : (⌊u⌋ : ℝ) ≤ ⌊u⌋ + 1)
    (continuous_stripAreaFraction hρ).continuousOn ⟨h1, h2⟩
  exact ⟨x, hx⟩

/-! ### Positivity and monotonicity -/

/-- The column mean is positive over `x` when `ρ` is positive on the segment `{x} × [0, 1]`. -/
theorem stripColumnMean_pos (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1)) {x : ℝ}
    (hpos : ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : 0 < stripColumnMean ρ x :=
  have hc : ContinuousOn (fun r ↦ ρ (x, r)) (Icc 0 1) :=
    hρ.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hr ↦ ⟨mem_univ x, hr⟩
  intervalIntegral_pos_of_pos_on (hc.intervalIntegrable_of_Icc zero_le_one)
    (fun y hy ↦ hpos y (Ioo_subset_Icc_self hy)) zero_lt_one

/-- Every column mean is positive when `ρ` is positive on the strip. -/
theorem stripColumnMean_pos_of_forall (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (x : ℝ) : 0 < stripColumnMean ρ x :=
  stripColumnMean_pos hρ (hpos x)

/-- The area of the annulus is positive when all column means are. -/
theorem annulusArea_pos (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hs : ∀ x ∈ Icc (0 : ℝ) 1, 0 < stripColumnMean ρ x) :
    0 < annulusArea ρ :=
  intervalIntegral_pos_of_pos_on ((continuous_stripColumnMean hρ).intervalIntegrable 0 1)
    (fun x hx ↦ hs x (Ioo_subset_Icc_self hx)) zero_lt_one

/-- The area of the annulus is positive when `ρ` is positive on the strip. -/
theorem annulusArea_pos_of_forall (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : 0 < annulusArea ρ :=
  annulusArea_pos hρ fun x _ ↦ stripColumnMean_pos_of_forall hρ hpos x

/-- The area fraction has derivative `u'(x) = s(x) / a`. -/
theorem hasDerivAt_stripAreaFraction (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1)) (x : ℝ) :
    HasDerivAt (stripAreaFraction ρ) ((annulusArea ρ)⁻¹ * stripColumnMean ρ x) x :=
  ((continuous_stripColumnMean hρ).integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul _

/-- When all column means are positive, the area fraction is strictly increasing. -/
theorem stripAreaFraction_strictMono (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hs : ∀ x, 0 < stripColumnMean ρ x) :
    StrictMono (stripAreaFraction ρ) :=
  strictMono_of_deriv_pos fun x ↦ by
    rw [(hasDerivAt_stripAreaFraction hρ x).deriv]
    exact mul_pos (inv_pos.2 (annulusArea_pos hρ fun x _ ↦ hs x)) (hs x)

/-! ### Smoothness and the Jacobian -/

theorem contDiff_stripColumnMean (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (stripColumnMean ρ) :=
  (contDiff_parametric_primitive_of_contDiff (f := fun x r ↦ ρ (x, r)) hρ 0).comp
    (contDiff_id.prodMk contDiff_const)

theorem contDiff_stripAreaFraction (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (stripAreaFraction ρ) :=
  contDiff_const.mul ((contDiff_parametric_primitive_of_contDiff
    (f := fun (_ : ℝ) t ↦ stripColumnMean ρ t) ((contDiff_stripColumnMean hρ).comp contDiff_snd)
    0).comp (contDiff_id.prodMk contDiff_id))

/-- The normalization is `C^n` at every point over which the column mean does not vanish. -/
theorem contDiffAt_stripDensityNormalization (hρ : ContDiff ℝ n ρ) {p : ℝ × ℝ}
    (hs : stripColumnMean ρ p.1 ≠ 0) : ContDiffAt ℝ n (stripDensityNormalization ρ) p :=
  ((contDiff_stripAreaFraction hρ).contDiffAt.comp p contDiffAt_fst).prodMk
    ((((contDiff_stripColumnMean hρ).contDiffAt.inv hs).comp p contDiffAt_fst).mul
      (contDiff_parametric_primitive_of_contDiff (f := fun x r ↦ ρ (x, r)) hρ 0).contDiffAt)

/-- The normalization has strict derivative `fderiv ℝ Φ p` at every point over which the column
mean does not vanish. -/
theorem hasStrictFDerivAt_stripDensityNormalization (hρ : ContDiff ℝ 1 ρ) {p : ℝ × ℝ}
    (hs : stripColumnMean ρ p.1 ≠ 0) :
    HasStrictFDerivAt (stripDensityNormalization ρ) (fderiv ℝ (stripDensityNormalization ρ) p) p :=
  have h := contDiffAt_stripDensityNormalization hρ hs
  h.hasStrictFDerivAt (h.differentiableAt one_ne_zero).hasFDerivAt one_ne_zero

theorem differentiableAt_stripDensityNormalization (hρ : ContDiff ℝ 1 ρ) {p : ℝ × ℝ}
    (hs : stripColumnMean ρ p.1 ≠ 0) : DifferentiableAt ℝ (stripDensityNormalization ρ) p :=
  (hasStrictFDerivAt_stripDensityNormalization hρ hs).differentiableAt

/-- The normalization is `C^n` when no column mean vanishes. -/
theorem contDiff_stripDensityNormalization (hρ : ContDiff ℝ n ρ)
    (hs : ∀ x, stripColumnMean ρ x ≠ 0) : ContDiff ℝ n (stripDensityNormalization ρ) :=
  contDiff_iff_contDiffAt.2 fun p ↦ contDiffAt_stripDensityNormalization hρ (hs p.1)

/-- The normalization is `C^n` when `ρ` is `C^n` and positive on the strip. -/
theorem contDiff_stripDensityNormalization_of_forall (hρ : ContDiff ℝ n ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    ContDiff ℝ n (stripDensityNormalization ρ) :=
  contDiff_stripDensityNormalization hρ fun x ↦
    (stripColumnMean_pos_of_forall hρ.continuous.continuousOn hpos x).ne'

/-- **The Jacobian of the density normalization.** Over a column of nonzero mean, the Jacobian
determinant of `Φ` is `ρ / a`, that is, `Φ` pulls `a dx ∧ dy` back to `ρ dx ∧ dy`. -/
theorem det_fderiv_stripDensityNormalization (hρ : ContDiff ℝ 1 ρ) {p : ℝ × ℝ}
    (hs : stripColumnMean ρ p.1 ≠ 0) :
    (fderiv ℝ (stripDensityNormalization ρ) p).det = (annulusArea ρ)⁻¹ * ρ p := by
  obtain ⟨x, y⟩ := p
  set A := fderiv ℝ (stripDensityNormalization ρ) (x, y)
  have hA : HasFDerivAt (stripDensityNormalization ρ) A (x, y) :=
    (hasStrictFDerivAt_stripDensityNormalization hρ hs).hasFDerivAt
  have hcρ := hρ.continuous.continuousOn (s := univ ×ˢ Icc 0 1)
  -- Along the horizontal line through `(x, y)` the first coordinate is `t ↦ u(x + t)`.
  have h10 : (A (1, 0)).1 = (annulusArea ρ)⁻¹ * stripColumnMean ρ x := by
    have h1 := hasFDerivAt_fst.comp_hasDerivAt _ (hA.hasLineDerivAt (1, 0))
    have h2 := HasDerivAt.comp_const_add x 0 (by simpa using hasDerivAt_stripAreaFraction hcρ x)
    exact h1.unique (by simpa [Function.comp_def] using h2)
  -- Along the vertical line the first coordinate is constant and the second is
  -- `t ↦ s(x)⁻¹ ∫₀^(y + t) ρ(x, r) dr`.
  have h01 : (A (0, 1)).1 = 0 := by
    have h1 := hasFDerivAt_fst.comp_hasDerivAt _ (hA.hasLineDerivAt (0, 1))
    have h2 : HasDerivAt (fun _ : ℝ ↦ stripAreaFraction ρ x) 0 0 := hasDerivAt_const _ _
    exact h1.unique (by simpa [Function.comp_def] using h2)
  have h01' : (A (0, 1)).2 = (stripColumnMean ρ x)⁻¹ * ρ (x, y) := by
    have h1 := hasFDerivAt_snd.comp_hasDerivAt _ (hA.hasLineDerivAt (0, 1))
    have h3 : HasDerivAt (fun t ↦ (stripColumnMean ρ x)⁻¹ * ∫ r in (0 : ℝ)..t, ρ (x, r))
        ((stripColumnMean ρ x)⁻¹ * ρ (x, y)) y :=
      ((by fun_prop : Continuous fun r ↦ ρ (x, r)).integral_hasStrictDerivAt 0
        y).hasDerivAt.const_mul _
    have h2 := HasDerivAt.comp_const_add y 0 (by simpa using h3)
    exact h1.unique (by simpa [Function.comp_def, stripDensityNormalization_snd] using h2)
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp only [ContinuousLinearMap.coe_coe, h10, h01, h01', mul_zero, sub_zero]
  field_simp

/-! ### The normalization as a partial homeomorphism -/

/-- The open set of points `(x, y)` of the plane such that `ρ(x, ·)` is positive on the segment
between `0` and `y`. When `ρ` is continuous and positive on the strip `ℝ × [0, 1]`, it is an open
neighbourhood of the strip (`TauCeti.isOpen_stripDensityNormalizationSource`,
`TauCeti.univ_prod_Icc_subset_stripDensityNormalizationSource`) on which the density normalization
is injective (`TauCeti.injOn_stripDensityNormalization`). -/
def stripDensityNormalizationSource (ρ : ℝ × ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ r ∈ [[0, p.2]], 0 < ρ (p.1, r)}

@[simp]
theorem mem_stripDensityNormalizationSource {p : ℝ × ℝ} :
    p ∈ stripDensityNormalizationSource ρ ↔ ∀ r ∈ [[0, p.2]], 0 < ρ (p.1, r) :=
  Iff.rfl

theorem isOpen_stripDensityNormalizationSource (hρ : Continuous ρ) :
    IsOpen (stripDensityNormalizationSource ρ) := by
  -- The segment between `0` and `y` is the image of `[0, 1]` under `t ↦ t y`.
  have hseg (p : ℝ × ℝ) :
      p ∈ stripDensityNormalizationSource ρ ↔ ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ (p.1, t * p.2) := by
    have h : (· * p.2) '' Icc (0 : ℝ) 1 = [[0, p.2]] := by
      rw [← uIcc_of_le zero_le_one, image_mul_const_uIcc, zero_mul, one_mul]
    rw [mem_stripDensityNormalizationSource, ← h, forall_mem_image]
  have hc : Continuous fun z : (ℝ × ℝ) × ℝ ↦ ρ (z.1.1, z.2 * z.1.2) := by fun_prop
  refine isOpen_iff_mem_nhds.2 fun p hp ↦ ?_
  have h := isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := p)
    (P := fun q t ↦ 0 < ρ (q.1, t * q.2)) fun t ht ↦
      (hc.tendsto (p, t)).eventually (lt_mem_nhds ((hseg p).1 hp t ht))
  filter_upwards [h] with q hq using (hseg q).2 hq

/-- The strip `ℝ × [0, 1]` lies in the domain of injectivity of the normalization. -/
theorem univ_prod_Icc_subset_stripDensityNormalizationSource
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ stripDensityNormalizationSource ρ := fun p hp r hr ↦ by
  rw [uIcc_of_le hp.2.1] at hr
  exact hpos p.1 r ⟨hr.1, hr.2.trans hp.2.2⟩

/-- On each vertical line, the second coordinate `y ↦ v(x, y)` of the density normalization is
strictly increasing on the heights `y` such that `ρ(x, ·)` is positive on the segment between `0`
and `y`, when the column mean over `x` is positive. -/
theorem strictMonoOn_stripDensityNormalization_snd {x : ℝ}
    (hρ : Continuous fun r ↦ ρ (x, r)) (hs : 0 < stripColumnMean ρ x) :
    StrictMonoOn (fun y ↦ (stripDensityNormalization ρ (x, y)).2)
      {y | (x, y) ∈ stripDensityNormalizationSource ρ} := by
  intro b hb c hc hbc
  simp only [stripDensityNormalization_snd]
  refine mul_lt_mul_of_pos_left ?_ (inv_pos.2 hs)
  -- Between two heights of the source, `ρ(x, ·)` is positive, so the primitive separates them.
  have hsub := integral_interval_sub_left (μ := MeasureTheory.volume)
    (hρ.intervalIntegrable 0 c) (hρ.intervalIntegrable 0 b)
  have hpos := intervalIntegral_pos_of_pos_on (hρ.intervalIntegrable b c) (fun t ht ↦ by
    rcases le_or_gt 0 t with h0 | h0
    · exact hc t (mem_uIcc.2 (Or.inl ⟨h0, ht.2.le⟩))
    · exact hb t (mem_uIcc.2 (Or.inr ⟨ht.1.le, h0.le⟩))) hbc
  linarith

/-- The density normalization is injective on the points `(x, y)` such that `ρ(x, ·)` is positive
on the segment between `0` and `y`, when `ρ` is positive on the strip. -/
theorem injOn_stripDensityNormalization (hρ : Continuous ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    InjOn (stripDensityNormalization ρ) (stripDensityNormalizationSource ρ) := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq h
  have hs := stripColumnMean_pos_of_forall hρ.continuousOn hpos
  obtain rfl : x = x' :=
    (stripAreaFraction_strictMono hρ.continuousOn hs).injective (congrArg Prod.fst h)
  rw [(strictMonoOn_stripDensityNormalization_snd (by fun_prop) (hs x)).injOn hp hq
    (congrArg Prod.snd h)]

/-- At a point of the domain of injectivity, the Jacobian determinant of the normalization is
positive: the normalization preserves orientation. -/
theorem det_fderiv_stripDensityNormalization_pos (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {p : ℝ × ℝ}
    (hp : p ∈ stripDensityNormalizationSource ρ) :
    0 < (fderiv ℝ (stripDensityNormalization ρ) p).det := by
  have hcρ := hρ.continuous.continuousOn (s := univ ×ˢ Icc 0 1)
  rw [det_fderiv_stripDensityNormalization hρ (stripColumnMean_pos_of_forall hcρ hpos p.1).ne']
  exact mul_pos (inv_pos.2 (annulusArea_pos_of_forall hcρ hpos)) (hp p.2 right_mem_uIcc)

/-- The density normalization is an open map on its domain of injectivity: at each of its points
it has invertible strict derivative. -/
private theorem isOpenMap_domRestrict_stripDensityNormalization (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    IsOpenMap ((stripDensityNormalizationSource ρ).domRestrict (stripDensityNormalization ρ)) := by
  refine isOpenMap_iff_nhds_le.2 fun ⟨p, hp⟩ ↦ ?_
  have hdet := (det_fderiv_stripDensityNormalization_pos hρ hpos hp).ne'
  have hΦ : HasStrictFDerivAt (stripDensityNormalization ρ)
      ((fderiv ℝ (stripDensityNormalization ρ) p).toContinuousLinearEquivOfDetNeZero hdet :
        (ℝ × ℝ) →L[ℝ] ℝ × ℝ) p := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hasStrictFDerivAt_stripDensityNormalization hρ
      (stripColumnMean_pos_of_forall hρ.continuous.continuousOn hpos p.1).ne'
  -- The source is open, so the neighbourhoods of `p` in it map onto those in the plane; the
  -- restricted map is `Φ` composed with the inclusion of the source, which closes the goal.
  have hnhds := map_nhds_subtypeVal_eq_nhds hp
    ((isOpen_stripDensityNormalizationSource hρ.continuous).mem_nhds hp)
  rw [domRestrict_apply, ← hΦ.map_nhds_eq_of_equiv, ← hnhds, Filter.map_map]
  rfl

/-- The density normalization of a `C¹` density positive on the strip, as an open partial
homeomorphism of the plane with source `TauCeti.stripDensityNormalizationSource ρ`, an open
neighbourhood of the strip. It is smooth with smooth inverse when `ρ` is
(`TauCeti.contDiffOn_stripDensityNormalizationOpenPartialHomeomorph_symm`) and, when `ρ` is moreover
`1`-periodic in `x` on the strip, maps the strip onto itself
(`TauCeti.bijOn_stripDensityNormalization`). -/
def stripDensityNormalizationOpenPartialHomeomorph (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((injOn_stripDensityNormalization hρ.continuous hpos).toPartialEquiv _ _)
    (contDiff_stripDensityNormalization_of_forall hρ hpos).continuous.continuousOn
    (isOpenMap_domRestrict_stripDensityNormalization hρ hpos)
    (isOpen_stripDensityNormalizationSource hρ.continuous)

section

variable {hρ₁ : ContDiff ℝ 1 ρ} {hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)}

@[simp]
theorem coe_stripDensityNormalizationOpenPartialHomeomorph :
    ⇑(stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos) = stripDensityNormalization ρ :=
  (rfl)

@[simp]
theorem stripDensityNormalizationOpenPartialHomeomorph_source :
    (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).source =
      stripDensityNormalizationSource ρ :=
  (rfl)

@[simp]
theorem stripDensityNormalizationOpenPartialHomeomorph_target :
    (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).target =
      stripDensityNormalization ρ '' stripDensityNormalizationSource ρ :=
  (rfl)

end

/-- **Smoothness of the inverse.** For a `C^n` density positive on the strip, the inverse of the
density normalization is `C^n` on its open domain. -/
theorem contDiffOn_stripDensityNormalizationOpenPartialHomeomorph_symm (hρ₁ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) (hρ : ContDiff ℝ n ρ) :
    ContDiffOn ℝ n (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).symm
      (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).target :=
  (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).contDiffOn_symm_of_isInvertible_fderiv
    (contDiff_stripDensityNormalization_of_forall hρ hpos).contDiffOn fun _ hp ↦
    ⟨_, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _
      (det_fderiv_stripDensityNormalization_pos hρ₁ hpos hp).ne'⟩

/-! ### The strip -/

/-- For a density continuous, positive and `1`-periodic on the strip `ℝ × [0, 1]`, the density
normalization maps the strip bijectively onto itself. -/
theorem bijOn_stripDensityNormalization (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) :
    BijOn (stripDensityNormalization ρ) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) := by
  -- On the strip the normalization only reads `ρ` there, so `ρ` may be taken continuous.
  obtain ⟨ρ', hc, hρρ'⟩ := hρ.exists_continuous_eqOn_univ_prod_Icc zero_le_one
  refine BijOn.congr (f₁ := stripDensityNormalization ρ') ?_ (stripDensityNormalization_congr hρρ')
  replace hper x y (hy : y ∈ Icc (0 : ℝ) 1) : ρ' (x + 1, y) = ρ' (x, y) := by
    rw [hρρ' ⟨mem_univ _, hy⟩, hρρ' ⟨mem_univ _, hy⟩, hper x y hy]
  replace hpos x y (hy : y ∈ Icc (0 : ℝ) 1) : 0 < ρ' (x, y) := by
    rw [hρρ' ⟨mem_univ _, hy⟩]
    exact hpos x y hy
  have hs := stripColumnMean_pos_of_forall hc.continuousOn hpos
  refine ⟨fun p hp ↦ ⟨mem_univ _, ?_⟩,
    (injOn_stripDensityNormalization hc hpos).mono
      (univ_prod_Icc_subset_stripDensityNormalizationSource hpos), fun q hq ↦ ?_⟩
  · -- `v(x, ·)` is monotone on `[0, 1]`, with `v(x, 0) = 0` and `v(x, 1) = 1`.
    have hv := (strictMonoOn_stripDensityNormalization_snd (by fun_prop) (hs p.1)).monotoneOn
    have hmem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : (p.1, y) ∈ stripDensityNormalizationSource ρ' :=
      univ_prod_Icc_subset_stripDensityNormalizationSource hpos ⟨mem_univ _, hy⟩
    have h0 := hv (hmem (left_mem_Icc.2 zero_le_one)) (hmem hp.2) hp.2.1
    have h1 := hv (hmem hp.2) (hmem (right_mem_Icc.2 zero_le_one)) hp.2.2
    simp only [stripDensityNormalization_snd_mk_zero,
      stripDensityNormalization_snd_mk_one (hs p.1).ne'] at h0 h1
    exact ⟨h0, h1⟩
  · -- Solve `u(x) = q.1` by surjectivity of `u`, then `v(x, y) = q.2` on the column over `x`.
    obtain ⟨x, hx⟩ := stripAreaFraction_surjective hc.continuousOn hper
      (annulusArea_pos_of_forall hc.continuousOn hpos).ne' q.1
    obtain ⟨y, hy, hxy⟩ := intermediate_value_Icc zero_le_one
      (continuous_stripDensityNormalization_curry_right (ρ := ρ') (x := x)
        (by fun_prop)).snd.continuousOn
      (by simpa [stripDensityNormalization_snd_mk_one (hs x).ne'] using hq.2)
    exact ⟨(x, y), ⟨mem_univ _, hy⟩, Prod.ext (by simpa using hx) hxy⟩

/-- For a density positive on the strip, the area fraction of `x` lies in `[0, 1)` exactly when `x`
does. -/
theorem stripAreaFraction_mem_Ico_iff (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {x : ℝ} :
    stripAreaFraction ρ x ∈ Ico (0 : ℝ) 1 ↔ x ∈ Ico (0 : ℝ) 1 := by
  have hu := stripAreaFraction_strictMono hρ (stripColumnMean_pos_of_forall hρ hpos)
  have h1 := stripAreaFraction_one (annulusArea_pos_of_forall hρ hpos).ne'
  rw [mem_Ico, mem_Ico]
  conv_rhs => rw [← hu.le_iff_le, ← hu.lt_iff_lt, stripAreaFraction_zero, h1]

/-- For a density positive on the strip, the normalization maps a point `(x, y)` of the strip to an
interior height, `0 < v(x, y) < 1`, exactly when `0 < y < 1`. -/
theorem stripDensityNormalization_snd_mem_Ioo_iff (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {p : ℝ × ℝ} (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    (stripDensityNormalization ρ p).2 ∈ Ioo (0 : ℝ) 1 ↔ p.2 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨x, y⟩ := p
  -- On the strip the normalization only reads `ρ` there, so `ρ` may be taken continuous.
  obtain ⟨ρ', hc, hρρ'⟩ := hρ.exists_continuous_eqOn_univ_prod_Icc zero_le_one
  replace hpos x y (hy : y ∈ Icc (0 : ℝ) 1) : 0 < ρ' (x, y) := by
    rw [hρρ' ⟨mem_univ _, hy⟩]
    exact hpos x y hy
  have hs := stripColumnMean_pos_of_forall hc.continuousOn hpos x
  have hv := strictMonoOn_stripDensityNormalization_snd (by fun_prop) hs
  have hmem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : (x, y) ∈ stripDensityNormalizationSource ρ' :=
    univ_prod_Icc_subset_stripDensityNormalizationSource hpos ⟨mem_univ _, hy⟩
  have h0 := hmem (left_mem_Icc.2 zero_le_one)
  have h1 := hmem (right_mem_Icc.2 zero_le_one)
  rw [← stripDensityNormalization_congr hρρ' ⟨mem_univ _, hp⟩, mem_Ioo, mem_Ioo,
    ← hv.lt_iff_lt h0 (hmem hp), ← hv.lt_iff_lt (hmem hp) h1]
  simp only [stripDensityNormalization_snd_mk_zero, stripDensityNormalization_snd_mk_one hs.ne']

/-- For a density positive on the strip, the normalization maps a point of the strip into the
half-open fundamental domain `[0, 1) × (0, 1)` of the interior of the annulus exactly when the
point lies there. -/
theorem stripDensityNormalization_mem_Ico_prod_Ioo_iff (hρ : ContinuousOn ρ (univ ×ˢ Icc 0 1))
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {p : ℝ × ℝ} (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    stripDensityNormalization ρ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ↔
      p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [mem_prod, mem_prod, stripDensityNormalization_fst,
    stripAreaFraction_mem_Ico_iff hρ hpos,
    stripDensityNormalization_snd_mem_Ioo_iff hρ hpos hp]

section

variable {hρ₁ : ContDiff ℝ 1 ρ} {hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)}

@[simp]
theorem stripDensityNormalizationOpenPartialHomeomorph_symm_apply_apply {p : ℝ × ℝ}
    (hp : p ∈ stripDensityNormalizationSource ρ) :
    (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).symm
      (stripDensityNormalization ρ p) = p := by
  simpa only [coe_stripDensityNormalizationOpenPartialHomeomorph] using
    (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).left_inv hp

/-- For a density positive and `1`-periodic on the strip, the strip lies in the target of the
normalization. -/
theorem univ_prod_Icc_subset_stripDensityNormalizationOpenPartialHomeomorph_target
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) :
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).target := by
  rw [stripDensityNormalizationOpenPartialHomeomorph_target]
  exact (bijOn_stripDensityNormalization hρ₁.continuous.continuousOn hper hpos).surjOn.mono
    (univ_prod_Icc_subset_stripDensityNormalizationSource hpos) subset_rfl

/-- For a density positive and `1`-periodic on the strip, the inverse of the normalization maps the
strip into itself. -/
theorem mapsTo_stripDensityNormalizationOpenPartialHomeomorph_symm
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) :
    MapsTo (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).symm
      (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ :=
    (bijOn_stripDensityNormalization hρ₁.continuous.continuousOn hper hpos).surjOn hq
  rwa [stripDensityNormalizationOpenPartialHomeomorph_symm_apply_apply
    (univ_prod_Icc_subset_stripDensityNormalizationSource hpos hp)]

/-- On the strip, the inverse of the normalization commutes with the deck translation. -/
theorem stripDensityNormalizationOpenPartialHomeomorph_symm_add_fst
    (hper : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)) {q : ℝ × ℝ}
    (hq : q.2 ∈ Icc (0 : ℝ) 1) :
    (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).symm (q + (1, 0)) =
      (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).symm q + (1, 0) := by
  have hc := hρ₁.continuous.continuousOn (s := univ ×ˢ Icc 0 1)
  obtain ⟨p, hp, rfl⟩ :=
    (bijOn_stripDensityNormalization hc hper hpos).surjOn ⟨mem_univ _, hq⟩
  have hp' : (p + (1, 0)).2 ∈ Icc (0 : ℝ) 1 := by simpa using hp.2
  rw [← stripDensityNormalization_add_fst hc hper (annulusArea_pos_of_forall hc hpos).ne' hp.2,
    stripDensityNormalizationOpenPartialHomeomorph_symm_apply_apply
      (univ_prod_Icc_subset_stripDensityNormalizationSource hpos ⟨mem_univ _, hp'⟩),
    stripDensityNormalizationOpenPartialHomeomorph_symm_apply_apply
      (univ_prod_Icc_subset_stripDensityNormalizationSource hpos hp)]

end

/-! ### Conjugating area-preserving maps -/

/-- **Conjugation by the density normalization.** Let `F` be differentiable at a point `p` of the
domain of the normalization `Φ`. Then the Jacobian determinant of `Φ ∘ F ∘ Φ⁻¹` at `Φ(p)` is
`ρ(F p) det DF_p / ρ(p)`. In particular, if `F` preserves `ρ dx ∧ dy` at `p`, that is
`ρ(F p) det DF_p = ρ(p)`, then `Φ ∘ F ∘ Φ⁻¹` preserves `dx ∧ dy` at `Φ(p)`. -/
theorem det_fderiv_stripDensityNormalization_comp_comp_symm (hρ₁ : ContDiff ℝ 1 ρ)
    (hpos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)) {F : ℝ × ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    (hp : p ∈ stripDensityNormalizationSource ρ) (hF : DifferentiableAt ℝ F p) :
    (fderiv ℝ (stripDensityNormalization ρ ∘ F ∘
        (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos).symm)
      (stripDensityNormalization ρ p)).det = ρ (F p) * (fderiv ℝ F p).det / ρ p := by
  set e := stripDensityNormalizationOpenPartialHomeomorph hρ₁ hpos
  have hs := stripColumnMean_pos_of_forall hρ₁.continuous.continuousOn hpos
  have ha : annulusArea ρ ≠ 0 := (annulusArea_pos_of_forall hρ₁.continuous.continuousOn hpos).ne'
  have hdet := (det_fderiv_stripDensityNormalization_pos hρ₁ hpos hp).ne'
  set A := (fderiv ℝ (stripDensityNormalization ρ) p).toContinuousLinearEquivOfDetNeZero hdet
  have hA : (A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) = fderiv ℝ (stripDensityNormalization ρ) p :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet
  have hsymm : e.symm (stripDensityNormalization ρ p) = p := e.left_inv hp
  have hq : stripDensityNormalization ρ p ∈ e.target := e.map_source hp
  -- The inverse has derivative `A⁻¹` at `Φ(p)`.
  have he : HasFDerivAt e.symm (A.symm : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (stripDensityNormalization ρ p) := by
    refine e.hasFDerivAt_symm hq ?_
    rw [hsymm, hA]
    exact (hasStrictFDerivAt_stripDensityNormalization hρ₁ (hs p.1).ne').hasFDerivAt
  have hΦF : HasFDerivAt (stripDensityNormalization ρ)
      (fderiv ℝ (stripDensityNormalization ρ) (F p)) (F p) :=
    (hasStrictFDerivAt_stripDensityNormalization hρ₁ (hs (F p).1).ne').hasFDerivAt
  have hF' : HasFDerivAt F (fderiv ℝ F p) (e.symm (stripDensityNormalization ρ p)) := by
    rw [hsymm]
    exact hF.hasFDerivAt
  have hΦF' : HasFDerivAt (stripDensityNormalization ρ)
      (fderiv ℝ (stripDensityNormalization ρ) (F p))
      ((F ∘ e.symm) (stripDensityNormalization ρ p)) := by
    rw [comp_apply, hsymm]
    exact hΦF
  have hcomp := hΦF'.comp _ (hF'.comp _ he)
  rw [hcomp.fderiv, ContinuousLinearMap.det_comp, ContinuousLinearMap.det_comp,
    ContinuousLinearEquiv.det_coe_symm, hA,
    det_fderiv_stripDensityNormalization hρ₁ (hs _).ne',
    det_fderiv_stripDensityNormalization hρ₁ (hs _).ne']
  have hρp : ρ p ≠ 0 := (hp p.2 right_mem_uIcc).ne'
  field_simp

/-! ### Examples -/

/-- For the constant density `ρ = 1` the normalization is the identity. -/
theorem stripDensityNormalization_one : stripDensityNormalization (fun _ ↦ (1 : ℝ)) = id := by
  have hs (x : ℝ) : stripColumnMean (fun _ ↦ (1 : ℝ)) x = 1 := by simp [stripColumnMean_def]
  have ha : annulusArea (fun _ ↦ (1 : ℝ)) = 1 := by simp [annulusArea_def, hs]
  funext p
  ext <;> simp [stripAreaFraction_def, stripDensityNormalization_snd, hs, ha]

/-- For the density `ρ = 1 + y`, with column means `s = 3 / 2` and annulus area `a = 3 / 2`, the
normalization is `(x, y) ↦ (x, (2y + y²) / 3)`. -/
theorem stripDensityNormalization_one_add_snd (x y : ℝ) :
    stripDensityNormalization (fun p ↦ 1 + p.2) (x, y) = (x, (2 * y + y ^ 2) / 3) := by
  have hs (x : ℝ) : stripColumnMean (fun p ↦ 1 + p.2) x = 3 / 2 := by
    rw [stripColumnMean_def, integral_add intervalIntegrable_const intervalIntegrable_id]
    norm_num [integral_id]
  have ha : annulusArea (fun p ↦ 1 + p.2) = 3 / 2 := by simp [annulusArea_def, hs]
  ext
  · simp [stripAreaFraction_def, hs, ha]
  · simp only [stripDensityNormalization_snd, hs,
      integral_add intervalIntegrable_const intervalIntegrable_id, integral_const, integral_id,
      smul_eq_mul]
    ring

end TauCeti
