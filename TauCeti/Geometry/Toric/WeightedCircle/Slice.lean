/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.Complex.RootsOfUnity.Circle
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Toric.WeightedCircle.Basic
import TauCeti.Analysis.Complex.Circle

/-!
# Slice charts of the weighted ellipsoid quotient

Let `a, b` be positive integers and `ε > 0`. The circle acts on `ℂ²` by the weighted rotations
`u • (z₁, z₂) = (u ^ a z₁, u ^ b z₂)` (`TauCeti.Toric.weightedRotation`), and preserves the
ellipsoid `E : a |z₁|² + b |z₂|² = 2 ε` (`TauCeti.Toric.weightedEllipsoid`), the level of the
moment map `(a |z₁|² + b |z₂|²) / 2`. For coprime weights the orbit space `E / S¹` is a sphere with
two orbifold points (`TauCeti.Toric.weightedOrbitHomeomorph`). This file gives `E / S¹` two explicit
slice charts, over `z₁ ≠ 0` and over `z₂ ≠ 0`, retaining the finite stabilizers of the axes.

* **Slices.** Over `z₁ ≠ 0` the slice is `w ↦ (√((2 ε - b |w|²) / a), w)` on the disc
  `b |w|² < 2 ε` (`TauCeti.Toric.weightedSliceFst`); over `z₂ ≠ 0` it is
  `u ↦ (u, √((2 ε - a |u|²) / b))` on the disc `a |u|² < 2 ε` (`TauCeti.Toric.weightedSliceSnd`).
  Every orbit meets the first slice by rotating `z₁` onto the nonnegative real axis
  (`TauCeti.Toric.exists_weightedRotation_eq_weightedSliceFst`).
* **Residual groups.** Two points of the first slice lie in one orbit exactly when they differ by
  the residual action of `ℤ / a`, `w ↦ exp(-2π i b k / a) w`
  (`TauCeti.Toric.exists_weightedRotation_weightedSliceFst_eq_iff`); for the second slice the
  residual group is `ℤ / b`, acting by `u ↦ exp(-2π i a k / b) u`. For coprime weights these
  actions are free away from the centre of the disc, in particular effective
  (`ZMod.toCircle_pow_mul_eq_self_iff`, applied to `-k`).
* **Change of slices.** On the overlap `w ≠ 0`, the slice point over `w` is rotated onto the second
  slice at `exp(-i a arg(w) / b) √((2 ε - b |w|²) / a)` (`TauCeti.Toric.weightedSliceTransition`),
  and the second slice meets that orbit exactly in the `ℤ / b`-orbit of this point
  (`TauCeti.Toric.exists_weightedRotation_weightedSliceFst_eq_weightedSliceSnd_iff`). So the change
  of slices is defined up to the residual group of the target.
* **Charts of the orbit space.** The maps sending a point of either disc to the orbit of its slice
  point (`TauCeti.Toric.weightedSliceChartFst`, `TauCeti.Toric.weightedSliceChartSnd`) are
  continuous and open, have as images the open sets of orbits with `z₁ ≠ 0`, respectively
  `z₂ ≠ 0`, and have as fibres the orbits of the residual groups. Together these say that each
  induces a homeomorphism from the quotient of its disc by the residual group onto an open subset
  of `E / S¹`.
* **The symplectic form.** The first coordinate of the first slice is real, so the slice pulls the
  standard symplectic form `dx₁ ∧ dy₁ + dx₂ ∧ dy₂` back to the area form `d(Re w) ∧ d(Im w)`
  of the disc (`TauCeti.Toric.stdComplexSymplecticForm_prod_fderiv_weightedSliceFst`), and
  likewise for the second slice. A reduced form on `E / S¹` pulls back along the orbit projection
  to the restriction of the symplectic form to `E`, so this is what such a form is in each chart.

## References

* E. Lerman and S. Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. **349** (1997), 4201–4230, Section 1 (weighted projective
  spaces as symplectic orbifold quotients).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (reduction by circle actions with finite stabilizers).
-/

public section

noncomputable section

open Set Filter Topology Real

namespace TauCeti.Toric

variable {a b : ℕ} {ε : ℝ}

/-! ### The slices -/

variable (a b ε) in
/-- The **slice over `z₁ ≠ 0`** of the weighted ellipsoid `a |z₁|² + b |z₂|² = 2 ε`: the map
`w ↦ (√((2 ε - b |w|²) / a), w)`, whose first coordinate is real and nonnegative. On the disc
`b |w|² < 2 ε` it meets every circle orbit through a point with `z₁ ≠ 0`, and two of its points lie
in the same orbit exactly when they differ by the residual action of the `a`-th roots of unity. -/
def weightedSliceFst (w : ℂ) : ℂ × ℂ :=
  (((√((2 * ε - b * ‖w‖ ^ 2) / a) : ℝ) : ℂ), w)

variable (a b ε) in
/-- The **slice over `z₂ ≠ 0`** of the weighted ellipsoid `a |z₁|² + b |z₂|² = 2 ε`: the map
`u ↦ (u, √((2 ε - a |u|²) / b))`, whose second coordinate is real and nonnegative. It is the slice
over `z₁ ≠ 0` for the exchanged weights, read through the exchange of coordinates
(`TauCeti.Toric.weightedSliceSnd_eq_swap`). -/
def weightedSliceSnd (u : ℂ) : ℂ × ℂ :=
  (u, ((√((2 * ε - a * ‖u‖ ^ 2) / b) : ℝ) : ℂ))

@[simp]
theorem weightedSliceFst_fst (w : ℂ) :
    (weightedSliceFst a b ε w).1 = ((√((2 * ε - b * ‖w‖ ^ 2) / a) : ℝ) : ℂ) :=
  (rfl)

@[simp]
theorem weightedSliceFst_snd (w : ℂ) : (weightedSliceFst a b ε w).2 = w :=
  (rfl)

@[simp]
theorem weightedSliceSnd_fst (u : ℂ) : (weightedSliceSnd a b ε u).1 = u :=
  (rfl)

@[simp]
theorem weightedSliceSnd_snd (u : ℂ) :
    (weightedSliceSnd a b ε u).2 = ((√((2 * ε - a * ‖u‖ ^ 2) / b) : ℝ) : ℂ) :=
  (rfl)

/-- The slice over `z₂ ≠ 0` is the slice over `z₁ ≠ 0` for the exchanged weights, with its
coordinates exchanged. -/
theorem weightedSliceSnd_eq_swap (u : ℂ) :
    weightedSliceSnd a b ε u = (weightedSliceFst b a ε u).swap :=
  (rfl)

/-- The first coordinate of the slice has norm `√((2 ε - b |w|²) / a)`. -/
theorem norm_weightedSliceFst_fst (w : ℂ) :
    ‖(weightedSliceFst a b ε w).1‖ = √((2 * ε - b * ‖w‖ ^ 2) / a) := by
  rw [weightedSliceFst_fst, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The slice over `z₁ ≠ 0` lies on the ellipsoid where `b |w|² ≤ 2 ε`. -/
theorem weightedSliceFst_mem_weightedEllipsoid (ha : 0 < a) {w : ℂ} (hw : b * ‖w‖ ^ 2 ≤ 2 * ε) :
    weightedSliceFst a b ε w ∈ weightedEllipsoid a b ε := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [mem_weightedEllipsoid, norm_weightedSliceFst_fst,
    Real.sq_sqrt (div_nonneg (by linarith) ha'.le), weightedSliceFst_snd]
  field_simp
  ring

/-- The slice over `z₂ ≠ 0` lies on the ellipsoid where `a |u|² ≤ 2 ε`. -/
theorem weightedSliceSnd_mem_weightedEllipsoid (hb : 0 < b) {u : ℂ} (hu : a * ‖u‖ ^ 2 ≤ 2 * ε) :
    weightedSliceSnd a b ε u ∈ weightedEllipsoid a b ε := by
  rw [weightedSliceSnd_eq_swap, ← swap_mem_weightedEllipsoid, Prod.swap_swap]
  exact weightedSliceFst_mem_weightedEllipsoid hb hu

/-- On the open disc `b |w|² < 2 ε` the first coordinate of the slice is positive. -/
theorem weightedSliceFst_fst_ne_zero (ha : 0 < a) {w : ℂ} (hw : b * ‖w‖ ^ 2 < 2 * ε) :
    (weightedSliceFst a b ε w).1 ≠ 0 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [← norm_ne_zero_iff, norm_weightedSliceFst_fst]
  exact (Real.sqrt_pos.2 (div_pos (by linarith) ha')).ne'

/-! ### The residual actions -/

/-- **The residual action on the slice over `z₁ ≠ 0`.** An `a`-th root of unity `u` fixes the
first coordinate of the slice, so it maps the slice to itself, acting by `w ↦ u ^ b w`. -/
theorem weightedRotation_weightedSliceFst {u : Circle} (hu : u ^ a = 1) (w : ℂ) :
    weightedRotation a b u (weightedSliceFst a b ε w) =
      weightedSliceFst a b ε ((u : ℂ) ^ b * w) := by
  have hu' : (u : ℂ) ^ a = 1 := by rw [← Circle.coe_pow, hu, Circle.coe_one]
  ext <;> simp [hu', norm_pow]

/-- **Two points of the slice over `z₁ ≠ 0` in the same orbit.** On the open disc
`b |w|² < 2 ε`, the circle element `u` maps the slice point over `w` to the slice point over `w'`
exactly when `u` is an `a`-th root of unity and `w' = u ^ b w`. -/
theorem weightedRotation_weightedSliceFst_eq_iff (ha : 0 < a) {w : ℂ} (hw : b * ‖w‖ ^ 2 < 2 * ε)
    {u : Circle} {w' : ℂ} :
    weightedRotation a b u (weightedSliceFst a b ε w) = weightedSliceFst a b ε w' ↔
      u ^ a = 1 ∧ w' = (u : ℂ) ^ b * w := by
  refine ⟨fun h ↦ ?_, fun ⟨hu, hw'⟩ ↦ by rw [hw', weightedRotation_weightedSliceFst hu]⟩
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [weightedRotation_fst, weightedRotation_snd, weightedSliceFst_snd] at h₁ h₂
  have hr := congrArg norm h₁
  simp only [norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul,
    norm_weightedSliceFst_fst] at hr
  rw [weightedSliceFst_fst, weightedSliceFst_fst, ← hr] at h₁
  refine ⟨?_, h₂.symm⟩
  have hne := weightedSliceFst_fst_ne_zero (ε := ε) ha hw
  rw [weightedSliceFst_fst] at hne
  rw [← Circle.coe_eq_one, Circle.coe_pow]
  exact (mul_eq_right₀ hne).1 h₁

/-- **The residual action on the slice over `z₂ ≠ 0`.** A `b`-th root of unity `u` maps the slice
to itself, acting by `w ↦ u ^ a w`. -/
theorem weightedRotation_weightedSliceSnd {u : Circle} (hu : u ^ b = 1) (w : ℂ) :
    weightedRotation a b u (weightedSliceSnd a b ε w) =
      weightedSliceSnd a b ε ((u : ℂ) ^ a * w) := by
  rw [weightedSliceSnd_eq_swap, weightedSliceSnd_eq_swap, ← Prod.swap_swap
    (weightedRotation a b u _), swap_weightedRotation, Prod.swap_swap,
    weightedRotation_weightedSliceFst hu]

/-- **Two points of the slice over `z₂ ≠ 0` in the same orbit.** On the open disc
`a |w|² < 2 ε`, the circle element `u` maps the slice point over `w` to the slice point over `w'`
exactly when `u` is a `b`-th root of unity and `w' = u ^ a w`. -/
theorem weightedRotation_weightedSliceSnd_eq_iff (hb : 0 < b) {w : ℂ} (hw : a * ‖w‖ ^ 2 < 2 * ε)
    {u : Circle} {w' : ℂ} :
    weightedRotation a b u (weightedSliceSnd a b ε w) = weightedSliceSnd a b ε w' ↔
      u ^ b = 1 ∧ w' = (u : ℂ) ^ a * w := by
  rw [← weightedRotation_weightedSliceFst_eq_iff hb hw, weightedSliceSnd_eq_swap,
    weightedSliceSnd_eq_swap, ← Prod.swap_inj, swap_weightedRotation, Prod.swap_swap,
    Prod.swap_swap]

/-- On the ellipsoid, for `a > 0`, a point has nonzero first coordinate exactly when its second
coordinate lies in the open disc `b |z₂|² < 2 ε` of the slice over `z₁ ≠ 0`. -/
theorem fst_ne_zero_iff_of_mem_weightedEllipsoid (ha : 0 < a) {z : ℂ × ℂ}
    (hz : z ∈ weightedEllipsoid a b ε) : z.1 ≠ 0 ↔ b * ‖z.2‖ ^ 2 < 2 * ε := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [mem_weightedEllipsoid] at hz
  rw [← norm_pos_iff]
  constructor
  · intro h
    nlinarith [pow_pos h 2]
  · intro h
    by_contra h'
    have : ‖z.1‖ = 0 := le_antisymm (not_lt.1 h') (norm_nonneg _)
    rw [this] at hz
    linarith

/-- **Every orbit meets the slice over `z₁ ≠ 0`.** For a point `z` of the ellipsoid, the circle
element `u = exp(-i arg(z₁) / a)` rotates `z₁` onto the nonnegative real axis, so it maps `z` to the
slice point over `u ^ b z₂`, whose norm is that of `z₂`. This lies in the open disc `b |w|² < 2 ε`
exactly when `z₁ ≠ 0` (`TauCeti.Toric.fst_ne_zero_iff_of_mem_weightedEllipsoid`). -/
theorem exists_weightedRotation_eq_weightedSliceFst (ha : 0 < a) {z : ℂ × ℂ}
    (hz : z ∈ weightedEllipsoid a b ε) :
    ∃ u : Circle, weightedRotation a b u z = weightedSliceFst a b ε ((u : ℂ) ^ b * z.2) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hua : Circle.exp (-(Complex.arg z.1 / a)) ^ a = Circle.exp (-Complex.arg z.1) := by
    rw [← Circle.exp_natCast_mul]
    congr 1
    field_simp
  refine ⟨Circle.exp (-(Complex.arg z.1 / a)), Prod.ext ?_ (by simp)⟩
  rw [mem_weightedEllipsoid] at hz
  have hs : (2 * ε - b * ‖((Circle.exp (-(Complex.arg z.1 / a)) : ℂ)) ^ b * z.2‖ ^ 2) / a =
      ‖z.1‖ ^ 2 := by
    rw [norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul]
    field_simp
    linarith
  rw [weightedRotation_fst, weightedSliceFst_fst, hs, Real.sqrt_sq (norm_nonneg _),
    ← Circle.coe_pow, hua, Circle.exp_neg_arg_mul_self]

/-- **Every orbit meets the slice over `z₂ ≠ 0`**, at the slice point over `u ^ a z₁` for
`u = exp(-i arg(z₂) / b)`. -/
theorem exists_weightedRotation_eq_weightedSliceSnd (hb : 0 < b) {z : ℂ × ℂ}
    (hz : z ∈ weightedEllipsoid a b ε) :
    ∃ u : Circle, weightedRotation a b u z = weightedSliceSnd a b ε ((u : ℂ) ^ a * z.1) := by
  obtain ⟨u, hu⟩ := exists_weightedRotation_eq_weightedSliceFst (a := b) (b := a) (ε := ε) hb
    (swap_mem_weightedEllipsoid.2 hz)
  refine ⟨u, ?_⟩
  have h := congrArg Prod.swap hu
  rwa [swap_weightedRotation, Prod.swap_swap, Prod.snd_swap, ← weightedSliceSnd_eq_swap] at h

/-! ### The residual cyclic groups -/

/-- **The slice over `z₁ ≠ 0` meets each orbit in an orbit of `ℤ / a`.** On the open disc
`b |w|² < 2 ε`, the slice points over `w` and `w'` lie in the same circle orbit exactly when
`w' = exp(-2π i b k / a) w` for some `k ∈ ℤ / a`. -/
theorem exists_weightedRotation_weightedSliceFst_eq_iff [NeZero a] {w : ℂ}
    (hw : b * ‖w‖ ^ 2 < 2 * ε) {w' : ℂ} :
    (∃ u : Circle,
        weightedRotation a b u (weightedSliceFst a b ε w) = weightedSliceFst a b ε w') ↔
      ∃ k : ZMod a, w' = ((ZMod.toCircle (-k) ^ b : Circle) : ℂ) * w := by
  simp_rw [weightedRotation_weightedSliceFst_eq_iff (NeZero.pos a) hw]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨j, rfl⟩ := ZMod.exists_toCircle_eq_of_pow_eq_one hu
    exact ⟨-j, by rw [neg_neg, Circle.coe_pow]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨ZMod.toCircle (-k), ZMod.toCircle_pow_eq_one (-k), by rw [Circle.coe_pow]⟩

/-- **The slice over `z₂ ≠ 0` meets each orbit in an orbit of `ℤ / b`.** On the open disc
`a |u|² < 2 ε`, the slice points over `u` and `u'` lie in the same circle orbit exactly when
`u' = exp(-2π i a k / b) u` for some `k ∈ ℤ / b`. -/
theorem exists_weightedRotation_weightedSliceSnd_eq_iff [NeZero b] {u : ℂ}
    (hu : a * ‖u‖ ^ 2 < 2 * ε) {u' : ℂ} :
    (∃ v : Circle,
        weightedRotation a b v (weightedSliceSnd a b ε u) = weightedSliceSnd a b ε u') ↔
      ∃ k : ZMod b, u' = ((ZMod.toCircle (-k) ^ a : Circle) : ℂ) * u := by
  rw [← exists_weightedRotation_weightedSliceFst_eq_iff (ε := ε) hu]
  refine exists_congr fun v ↦ ?_
  rw [weightedSliceSnd_eq_swap, weightedSliceSnd_eq_swap, ← Prod.swap_inj, swap_weightedRotation,
    Prod.swap_swap, Prod.swap_swap]

/-! ### The change of slices -/

variable (a b ε) in
/-- The **change from the slice over `z₁ ≠ 0` to the slice over `z₂ ≠ 0`**,
`w ↦ exp(-i a arg(w) / b) √((2 ε - b |w|²) / a)`. It is defined using the principal argument, so it
is a choice: the change of slices is well defined only up to the residual group `ℤ / b` of the
slice over `z₂ ≠ 0`
(`TauCeti.Toric.exists_weightedRotation_weightedSliceFst_eq_weightedSliceSnd_iff`). -/
def weightedSliceTransition (w : ℂ) : ℂ :=
  (Circle.exp (-(a * Complex.arg w / b)) : ℂ) * ((√((2 * ε - b * ‖w‖ ^ 2) / a) : ℝ) : ℂ)

/-- The change of slices has the norm `√((2 ε - b |w|²) / a)` of the first coordinate of the slice
point over `w`. -/
theorem norm_weightedSliceTransition (w : ℂ) :
    ‖weightedSliceTransition a b ε w‖ = √((2 * ε - b * ‖w‖ ^ 2) / a) := by
  rw [weightedSliceTransition, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- **The change of slices.** For `w` in the closed disc `b |w|² ≤ 2 ε`, the circle element
`exp(-i arg(w) / b)` rotates the slice point over `w` onto the slice over `z₂ ≠ 0`, at the point
over `weightedSliceTransition a b ε w`. -/
theorem weightedRotation_weightedSliceFst_eq_weightedSliceSnd (ha : 0 < a) (hb : 0 < b) {w : ℂ}
    (hw : b * ‖w‖ ^ 2 ≤ 2 * ε) :
    weightedRotation a b (Circle.exp (-(Complex.arg w / b))) (weightedSliceFst a b ε w) =
      weightedSliceSnd a b ε (weightedSliceTransition a b ε w) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  refine Prod.ext ?_ ?_
  · rw [weightedRotation_fst, weightedSliceSnd_fst, weightedSliceTransition, ← Circle.coe_pow,
      ← Circle.exp_natCast_mul, weightedSliceFst_fst]
    congr 3
    ring
  · have hs : (2 * ε - a * ‖weightedSliceTransition a b ε w‖ ^ 2) / b = ‖w‖ ^ 2 := by
      rw [norm_weightedSliceTransition, Real.sq_sqrt (div_nonneg (by linarith) ha'.le)]
      field_simp
      ring
    have hv : b * -(Complex.arg w / b) = -Complex.arg w := by field_simp
    rw [weightedRotation_snd, weightedSliceSnd_snd, hs, Real.sqrt_sq (norm_nonneg _),
      weightedSliceFst_snd, ← Circle.coe_pow, ← Circle.exp_natCast_mul, hv,
      Circle.exp_neg_arg_mul_self]

/-- **The change of slices retains the residual group `ℤ / b`.** For a nonzero `w` in the closed
disc `b |w|² ≤ 2 ε`, the slice point over `w` and the slice point over `u` of the slice over
`z₂ ≠ 0` lie in the same circle orbit exactly when `u = exp(-2π i a k / b) τ(w)` for some
`k ∈ ℤ / b`, where `τ = weightedSliceTransition a b ε`. -/
theorem exists_weightedRotation_weightedSliceFst_eq_weightedSliceSnd_iff (ha : 0 < a)
    [NeZero b] {w : ℂ} (hw₀ : w ≠ 0) (hw : b * ‖w‖ ^ 2 ≤ 2 * ε) {u : ℂ} :
    (∃ v : Circle,
        weightedRotation a b v (weightedSliceFst a b ε w) = weightedSliceSnd a b ε u) ↔
      ∃ k : ZMod b,
        u = ((ZMod.toCircle (-k) ^ a : Circle) : ℂ) * weightedSliceTransition a b ε w := by
  have hb := NeZero.pos b
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hτ : a * ‖weightedSliceTransition a b ε w‖ ^ 2 < 2 * ε := by
    rw [norm_weightedSliceTransition, Real.sq_sqrt (div_nonneg (by linarith) ha'.le)]
    field_simp
    nlinarith [pow_pos (norm_pos_iff.2 hw₀) 2]
  rw [← exists_weightedRotation_weightedSliceSnd_eq_iff hτ,
    ← weightedRotation_weightedSliceFst_eq_weightedSliceSnd ha hb hw]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v * (Circle.exp (-(Complex.arg w / b)))⁻¹, by
      rw [← weightedRotation_mul, inv_mul_cancel_right, hv]⟩
  · rintro ⟨v, hv⟩
    exact ⟨v * Circle.exp (-(Complex.arg w / b)), by rw [weightedRotation_mul, hv]⟩

/-! ### The symplectic form in the slices -/

/-- The standard area form of `ℂ` vanishes on real vectors. -/
private theorem stdComplexSymplecticForm_ofReal (x y : ℝ) :
    stdComplexSymplecticForm (x : ℂ) (y : ℂ) = 0 := by
  simp

private theorem differentiableAt_sqrt_weightedSlice {c d : ℕ} (hc : 0 < c) {w : ℂ}
    (hw : d * ‖w‖ ^ 2 < 2 * ε) :
    DifferentiableAt ℝ (fun w : ℂ ↦ √((2 * ε - d * ‖w‖ ^ 2) / c)) w := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  refine DifferentiableAt.sqrt ?_ (div_pos (by linarith) hc').ne'
  have : DifferentiableAt ℝ (fun w : ℂ ↦ ‖w‖ ^ 2) w :=
    DifferentiableAt.norm_sq ℝ (f := id) differentiableAt_id
  fun_prop

/-- **The slice over `z₁ ≠ 0` pulls the symplectic form back to the area form.** On the open disc
`b |w|² < 2 ε`, the standard symplectic form `dx₁ ∧ dy₁ + dx₂ ∧ dy₂` of `ℂ²` evaluates on the
images of `v, v'` under the derivative of the slice as the area form `d(Re w) ∧ d(Im w)` on `v, v'`:
the first coordinate of the slice is real, so it contributes nothing. A reduced form on the orbit
space pulls back along the orbit projection to the restriction of the symplectic form to the
ellipsoid, so this computes such a form in the slice chart. -/
theorem stdComplexSymplecticForm_prod_fderiv_weightedSliceFst (ha : 0 < a) {w : ℂ}
    (hw : b * ‖w‖ ^ 2 < 2 * ε) (v v' : ℂ) :
    stdComplexSymplecticForm.prod stdComplexSymplecticForm
        (fderiv ℝ (weightedSliceFst a b ε) w v) (fderiv ℝ (weightedSliceFst a b ε) w v') =
      stdComplexSymplecticForm v v' := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp w
    (differentiableAt_sqrt_weightedSlice ha hw).hasFDerivAt).prodMk (hasFDerivAt_id w)).fderiv
  -- By definition, the slice is the pair of the real square root, as a complex number, and `id`.
  rw [show weightedSliceFst a b ε = fun w ↦
    ((Complex.ofRealCLM ∘ fun w : ℂ ↦ √((2 * ε - b * ‖w‖ ^ 2) / a)) w, id w) from rfl, h]
  simp only [SymplecticForm.prod_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.coe_id', id_eq, stdComplexSymplecticForm_ofReal, zero_add]

/-- **The slice over `z₂ ≠ 0` pulls the symplectic form back to the area form** `d(Re u) ∧ d(Im u)`
on the open disc `a |u|² < 2 ε`. -/
theorem stdComplexSymplecticForm_prod_fderiv_weightedSliceSnd (hb : 0 < b) {u : ℂ}
    (hu : a * ‖u‖ ^ 2 < 2 * ε) (v v' : ℂ) :
    stdComplexSymplecticForm.prod stdComplexSymplecticForm
        (fderiv ℝ (weightedSliceSnd a b ε) u v) (fderiv ℝ (weightedSliceSnd a b ε) u v') =
      stdComplexSymplecticForm v v' := by
  have h := ((hasFDerivAt_id u).prodMk (Complex.ofRealCLM.hasFDerivAt.comp u
    (differentiableAt_sqrt_weightedSlice hb hu).hasFDerivAt)).fderiv
  -- By definition, the slice is the pair of `id` and the real square root, as a complex number.
  rw [show weightedSliceSnd a b ε = fun u ↦ (id u,
    (Complex.ofRealCLM ∘ fun u : ℂ ↦ √((2 * ε - a * ‖u‖ ^ 2) / b)) u) from rfl, h]
  simp only [SymplecticForm.prod_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.coe_id', id_eq, stdComplexSymplecticForm_ofReal, add_zero]

/-! ### The slice charts of the orbit space -/

/-- The slice over `z₁ ≠ 0` is continuous. -/
theorem continuous_weightedSliceFst : Continuous (weightedSliceFst a b ε) := by
  unfold weightedSliceFst
  fun_prop

/-- The slice over `z₂ ≠ 0` is continuous. -/
theorem continuous_weightedSliceSnd : Continuous (weightedSliceSnd a b ε) := by
  unfold weightedSliceSnd
  fun_prop

variable (a b ε) in
/-- The **slice chart over `z₁ ≠ 0`** of the orbit space `E / S¹` of the weighted ellipsoid
`E : a |z₁|² + b |z₂|² = 2 ε`: a point `w` of the open disc `b |w|² < 2 ε` goes to the orbit of the
slice point `(√((2 ε - b |w|²) / a), w)`. It is continuous and open
(`TauCeti.Toric.isOpenMap_weightedSliceChartFst`), its image is the open set of orbits with
`z₁ ≠ 0` (`TauCeti.Toric.range_weightedSliceChartFst`), and its fibres are the orbits of the
residual group `ℤ / a` acting by `w ↦ exp(-2π i b k / a) w`
(`TauCeti.Toric.weightedSliceChartFst_eq_iff`). So it induces a homeomorphism from the quotient of
the disc by `ℤ / a` onto that open set. -/
def weightedSliceChartFst [NeZero a] (w : {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε}) :
    MulAction.orbitRel.Quotient Circle (weightedEllipsoid a b ε) :=
  Quotient.mk _
    ⟨weightedSliceFst a b ε w, weightedSliceFst_mem_weightedEllipsoid (NeZero.pos a) w.2.le⟩

variable (a b ε) in
/-- The **slice chart over `z₂ ≠ 0`** of the orbit space `E / S¹` of the weighted ellipsoid
`E : a |z₁|² + b |z₂|² = 2 ε`: a point `u` of the open disc `a |u|² < 2 ε` goes to the orbit of the
slice point `(u, √((2 ε - a |u|²) / b))`. It is continuous and open
(`TauCeti.Toric.isOpenMap_weightedSliceChartSnd`), its image is the open set of orbits with
`z₂ ≠ 0` (`TauCeti.Toric.range_weightedSliceChartSnd`), and its fibres are the orbits of the
residual group `ℤ / b` acting by `u ↦ exp(-2π i a k / b) u`
(`TauCeti.Toric.weightedSliceChartSnd_eq_iff`). -/
def weightedSliceChartSnd [NeZero b] (u : {u : ℂ // a * ‖u‖ ^ 2 < 2 * ε}) :
    MulAction.orbitRel.Quotient Circle (weightedEllipsoid a b ε) :=
  Quotient.mk _
    ⟨weightedSliceSnd a b ε u, weightedSliceSnd_mem_weightedEllipsoid (NeZero.pos b) u.2.le⟩

theorem weightedSliceChartFst_apply [NeZero a] (w : {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε}) :
    weightedSliceChartFst a b ε w = Quotient.mk _
      ⟨weightedSliceFst a b ε w, weightedSliceFst_mem_weightedEllipsoid (NeZero.pos a) w.2.le⟩ :=
  (rfl)

theorem weightedSliceChartSnd_apply [NeZero b] (u : {u : ℂ // a * ‖u‖ ^ 2 < 2 * ε}) :
    weightedSliceChartSnd a b ε u = Quotient.mk _
      ⟨weightedSliceSnd a b ε u, weightedSliceSnd_mem_weightedEllipsoid (NeZero.pos b) u.2.le⟩ :=
  (rfl)

theorem continuous_weightedSliceChartFst [NeZero a] : Continuous (weightedSliceChartFst a b ε) :=
  continuous_quotient_mk'.comp
    ((continuous_weightedSliceFst.comp continuous_subtype_val).subtype_mk _)

theorem continuous_weightedSliceChartSnd [NeZero b] : Continuous (weightedSliceChartSnd a b ε) :=
  continuous_quotient_mk'.comp
    ((continuous_weightedSliceSnd.comp continuous_subtype_val).subtype_mk _)

/-- Two points of the disc have the same image under the slice chart over `z₁ ≠ 0` exactly when the
circle maps the slice point over the first to the slice point over the second. -/
private theorem weightedSliceChartFst_eq_iff_exists [NeZero a]
    {w w' : {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε}} :
    weightedSliceChartFst a b ε w = weightedSliceChartFst a b ε w' ↔
      ∃ u : Circle,
        weightedRotation a b u (weightedSliceFst a b ε w) = weightedSliceFst a b ε w' := by
  rw [eq_comm, weightedSliceChartFst_apply, weightedSliceChartFst_apply, Quotient.eq,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  simp only [← Subtype.coe_inj, coe_smul_weightedEllipsoid]

/-- **The fibres of the slice chart over `z₁ ≠ 0` are the orbits of `ℤ / a`**: two points `w, w'`
of the disc go to the same orbit exactly when `w' = exp(-2π i b k / a) w` for some `k ∈ ℤ / a`. -/
theorem weightedSliceChartFst_eq_iff [NeZero a] {w w' : {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε}} :
    weightedSliceChartFst a b ε w = weightedSliceChartFst a b ε w' ↔
      ∃ k : ZMod a, (w' : ℂ) = ((ZMod.toCircle (-k) ^ b : Circle) : ℂ) * w := by
  rw [weightedSliceChartFst_eq_iff_exists, exists_weightedRotation_weightedSliceFst_eq_iff w.2]

/-- **The fibres of the slice chart over `z₂ ≠ 0` are the orbits of `ℤ / b`**: two points `u, u'`
of the disc go to the same orbit exactly when `u' = exp(-2π i a k / b) u` for some `k ∈ ℤ / b`. -/
theorem weightedSliceChartSnd_eq_iff [NeZero b] {u u' : {u : ℂ // a * ‖u‖ ^ 2 < 2 * ε}} :
    weightedSliceChartSnd a b ε u = weightedSliceChartSnd a b ε u' ↔
      ∃ k : ZMod b, (u' : ℂ) = ((ZMod.toCircle (-k) ^ a : Circle) : ℂ) * u := by
  rw [← exists_weightedRotation_weightedSliceSnd_eq_iff u.2, eq_comm, weightedSliceChartSnd_apply,
    weightedSliceChartSnd_apply, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  simp only [← Subtype.coe_inj, coe_smul_weightedEllipsoid]

/-- **The image of the slice chart over `z₁ ≠ 0`** is the set of orbits of points with `z₁ ≠ 0`. -/
theorem range_weightedSliceChartFst [NeZero a] :
    range (weightedSliceChartFst a b ε) =
      Quotient.mk _ '' {z : weightedEllipsoid a b ε | (z : ℂ × ℂ).1 ≠ 0} := by
  have ha := NeZero.pos a
  ext q
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, weightedSliceFst_fst_ne_zero ha w.2, (weightedSliceChartFst_apply w).symm⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, hu⟩ := exists_weightedRotation_eq_weightedSliceFst (ε := ε) ha z.2
    have hw : b * ‖(u : ℂ) ^ b * (z : ℂ × ℂ).2‖ ^ 2 < 2 * ε := by
      simpa [norm_pow] using (fst_ne_zero_iff_of_mem_weightedEllipsoid ha z.2).1 hz
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [weightedSliceChartFst_apply, Quotient.eq, MulAction.orbitRel_apply,
      MulAction.mem_orbit_iff]
    exact ⟨u, Subtype.ext (by rw [coe_smul_weightedEllipsoid, hu])⟩

/-- **The image of the slice chart over `z₂ ≠ 0`** is the set of orbits of points with `z₂ ≠ 0`. -/
theorem range_weightedSliceChartSnd [NeZero b] :
    range (weightedSliceChartSnd a b ε) =
      Quotient.mk _ '' {z : weightedEllipsoid a b ε | (z : ℂ × ℂ).2 ≠ 0} := by
  have hb := NeZero.pos b
  ext q
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨_, show (weightedSliceSnd a b ε u).2 ≠ 0 from ?_, (weightedSliceChartSnd_apply u).symm⟩
    rw [weightedSliceSnd_eq_swap, Prod.snd_swap]
    exact weightedSliceFst_fst_ne_zero hb u.2
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv⟩ := exists_weightedRotation_eq_weightedSliceSnd (ε := ε) hb z.2
    have hu : a * ‖(v : ℂ) ^ a * (z : ℂ × ℂ).1‖ ^ 2 < 2 * ε := by
      simpa [norm_pow] using
        (fst_ne_zero_iff_of_mem_weightedEllipsoid hb (swap_mem_weightedEllipsoid.2 z.2)).1 hz
    refine ⟨⟨_, hu⟩, ?_⟩
    rw [weightedSliceChartSnd_apply, Quotient.eq, MulAction.orbitRel_apply,
      MulAction.mem_orbit_iff]
    exact ⟨v, Subtype.ext (by rw [coe_smul_weightedEllipsoid, hv])⟩

/-- **The saturation of an open set under the residual group is open.** For an open set `U` of the
disc `b |w|² < 2 ε`, the points of the disc with the same image under the slice chart over
`z₁ ≠ 0` as a point of `U` form an open set: it is the union of the images of `U` under the
residual action of the `a`-th roots of unity. -/
theorem isOpen_preimage_image_weightedSliceChartFst [NeZero a]
    {U : Set {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε}} (hU : IsOpen U) :
    IsOpen (weightedSliceChartFst a b ε ⁻¹' (weightedSliceChartFst a b ε '' U)) := by
  have hT : weightedSliceChartFst a b ε ⁻¹' (weightedSliceChartFst a b ε '' U) =
      ⋃ (ζ : Circle) (_ : ζ ^ a = 1), (fun w : {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε} ↦
        (⟨(ζ : ℂ) ^ b * w, by simpa [norm_pow] using w.2⟩ : {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε})) ⁻¹'
          U := by
    ext w
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨w', hw', h⟩
      obtain ⟨u, hu⟩ := weightedSliceChartFst_eq_iff_exists.1 h.symm
      obtain ⟨hua, huw⟩ := (weightedRotation_weightedSliceFst_eq_iff (NeZero.pos a) w.2).1 hu
      refine ⟨u, hua, ?_⟩
      convert hw' using 1
      exact Subtype.ext huw.symm
    · rintro ⟨ζ, hζ, hw⟩
      refine ⟨_, hw, weightedSliceChartFst_eq_iff_exists.2 ⟨ζ⁻¹, ?_⟩⟩
      rw [weightedRotation_weightedSliceFst (by rw [inv_pow, hζ, inv_one]), ← mul_assoc, ← mul_pow,
        ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_pow, one_mul]
  rw [hT]
  exact isOpen_iUnion fun ζ ↦ isOpen_iUnion fun _ ↦ hU.preimage <|
    (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- **The slice chart over `z₁ ≠ 0` is an open map**, for any positive weights (coprimality is not
needed). -/
theorem isOpenMap_weightedSliceChartFst [NeZero a] : IsOpenMap (weightedSliceChartFst a b ε) := by
  -- Fix `w₀` in an open set `U` of the disc and a radius `ρ > |w₀|` with `b ρ² < 2 ε`. The points
  -- of the closed disc of radius `ρ` outside the saturation `T` of `U` under the residual group
  -- form a compact set, whose circle saturation `F` in the ellipsoid is compact, hence closed.
  -- Every point `z` of the ellipsoid with `|z₂| < ρ` and outside `F` has its orbit through a slice
  -- point over a point of `T`. So these points form an open neighbourhood of the orbit of `w₀`
  -- inside the preimage of the image of `U`.
  have ha := NeZero.pos a
  set D := {w : ℂ // b * ‖w‖ ^ 2 < 2 * ε}
  set s : D → weightedEllipsoid a b ε := fun w ↦
    ⟨weightedSliceFst a b ε w, weightedSliceFst_mem_weightedEllipsoid ha w.2.le⟩ with hs_def
  have hs : Continuous s := (continuous_weightedSliceFst.comp continuous_subtype_val).subtype_mk _
  intro U hU
  set T := weightedSliceChartFst a b ε ⁻¹' (weightedSliceChartFst a b ε '' U)
  have hT : IsOpen T := isOpen_preimage_image_weightedSliceChartFst hU
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage, isOpen_iff_forall_mem_open]
  rintro z₀ ⟨w₀, hw₀U, hz₀⟩
  -- A radius `ρ > |w₀|` with `b ρ² < 2 ε`.
  have hev : ∀ᶠ r in 𝓝 ‖(w₀ : ℂ)‖, b * r ^ 2 < 2 * ε :=
    (continuous_const.mul (continuous_pow 2)).continuousAt.eventually_lt continuousAt_const w₀.2
  obtain ⟨ρ, hρ, hρw : ‖(w₀ : ℂ)‖ < ρ⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi ‖(w₀ : ℂ)‖))).and
      (self_mem_nhdsWithin (s := Ioi ‖(w₀ : ℂ)‖))).exists
  have hb : (0 : ℝ) ≤ b := b.cast_nonneg
  have hK : IsCompact {w : D | ‖(w : ℂ)‖ ≤ ρ} := by
    rw [Subtype.isCompact_iff]
    convert isCompact_closedBall (0 : ℂ) ρ using 1
    ext x
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      Metric.mem_closedBall, dist_zero_right]
    refine ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨?_, h⟩⟩
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) h 2) hb
    linarith
  -- The circle saturation of the slice points over the closed disc of radius `ρ`, away from `T`,
  -- is compact, hence closed in the ellipsoid.
  have hF : IsClosed
      ((fun p : Circle × D ↦ p.1 • s p.2) '' (univ ×ˢ ({w : D | ‖(w : ℂ)‖ ≤ ρ} \ T))) :=
    ((isCompact_univ.prod (hK.diff hT)).image
      (continuous_fst.smul (hs.comp continuous_snd))).isClosed
  refine ⟨{z | ‖(z : ℂ × ℂ).2‖ < ρ} ∩ ((fun p : Circle × D ↦ p.1 • s p.2) ''
    (univ ×ˢ ({w : D | ‖(w : ℂ)‖ ≤ ρ} \ T)))ᶜ, ?_, ?_, ?_⟩
  -- Every point of the neighbourhood lies over the image of `U`.
  · rintro z ⟨hzρ, hzF⟩
    have hbz : b * ‖(z : ℂ × ℂ).2‖ ^ 2 < 2 * ε := by
      have := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg (z : ℂ × ℂ).2) (le_of_lt hzρ) 2) hb
      linarith
    obtain ⟨u, hu⟩ := exists_weightedRotation_eq_weightedSliceFst (ε := ε) ha z.2
    set c : D := ⟨(u : ℂ) ^ b * (z : ℂ × ℂ).2, by simpa [norm_pow] using hbz⟩
    have hc : u • z = s c := Subtype.ext (by rw [coe_smul_weightedEllipsoid, hu])
    have hcT : c ∈ T := by
      by_contra hcT
      refine hzF ⟨(u⁻¹, c), ⟨mem_univ _, by simpa [c, norm_pow] using hzρ.le, hcT⟩, ?_⟩
      simp only [← hc, inv_smul_smul]
    obtain ⟨w, hwU, hw⟩ := hcT
    exact ⟨w, hwU, hw.trans (Quotient.sound ⟨u, hc⟩)⟩
  -- The neighbourhood is open.
  · exact (isOpen_lt (continuous_norm.comp (continuous_snd.comp continuous_subtype_val))
      continuous_const).inter hF.isOpen_compl
  -- The neighbourhood contains `z₀`.
  · obtain ⟨u, hu⟩ : ∃ u : Circle, u • s w₀ = z₀ := Quotient.exact hz₀.symm
    refine ⟨?_, ?_⟩
    · simpa [← hu, hs_def, norm_pow] using hρw
    · rintro ⟨⟨v, c⟩, ⟨-, -, hcT⟩, hc : v • s c = z₀⟩
      refine hcT ⟨w₀, hw₀U, Quotient.sound (MulAction.mem_orbit_iff.2 ⟨u⁻¹ * v, ?_⟩)⟩
      rw [mul_smul, hc, ← hu, inv_smul_smul]

/-- **The slice chart over `z₁ ≠ 0` has open image**, the set of orbits with `z₁ ≠ 0`. -/
theorem isOpen_range_weightedSliceChartFst [NeZero a] :
    IsOpen (range (weightedSliceChartFst a b ε)) :=
  isOpenMap_weightedSliceChartFst.isOpen_range

/-- The slice chart over `z₂ ≠ 0` is, by definition, the slice chart over `z₁ ≠ 0` for the exchanged
weights followed by the exchange of coordinates. -/
theorem weightedSliceChartSnd_eq_swapOrbitHomeomorph [NeZero b]
    (u : {u : ℂ // a * ‖u‖ ^ 2 < 2 * ε}) :
    weightedSliceChartSnd a b ε u = swapOrbitHomeomorph a b ε (weightedSliceChartFst b a ε u) :=
  by rw [weightedSliceChartSnd_apply, weightedSliceChartFst_apply, swapOrbitHomeomorph_mk]; rfl

/-- **The slice chart over `z₂ ≠ 0` is an open map.** It is the slice chart over `z₁ ≠ 0` for the
exchanged weights, followed by the homeomorphism of orbit spaces exchanging the coordinates. -/
theorem isOpenMap_weightedSliceChartSnd [NeZero b] : IsOpenMap (weightedSliceChartSnd a b ε) := by
  have h : weightedSliceChartSnd a b ε = swapOrbitHomeomorph a b ε ∘ weightedSliceChartFst b a ε :=
    funext weightedSliceChartSnd_eq_swapOrbitHomeomorph
  rw [h]
  exact (swapOrbitHomeomorph a b ε).isOpenMap.comp isOpenMap_weightedSliceChartFst

/-- **The slice chart over `z₂ ≠ 0` has open image**, the set of orbits with `z₂ ≠ 0`. -/
theorem isOpen_range_weightedSliceChartSnd [NeZero b] :
    IsOpen (range (weightedSliceChartSnd a b ε)) :=
  isOpenMap_weightedSliceChartSnd.isOpen_range

end TauCeti.Toric
