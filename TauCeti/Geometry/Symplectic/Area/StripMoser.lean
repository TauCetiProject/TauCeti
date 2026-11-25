/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Plane
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive
import TauCeti.Analysis.Calculus.Moser
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# An explicit Moser primitive on the annulus strip

Let `ρ = 1 + g` be a density on the plane, `1`-periodic in the first coordinate, so that
`ρ dx ∧ dy` is an area form on the strip `ℝ × [0, 1]` covering the closed annulus
`(ℝ / ℤ) × [0, 1]`. Suppose the annulus has the same area for `ρ dx ∧ dy` as for `dx ∧ dy`,
that is `∫₀¹ ∫₀¹ g(x, y) dx dy = 0`. This file writes down an explicit primitive of the
difference `ρ dx ∧ dy - dx ∧ dy = g dx ∧ dy` whose Moser vector field is tangent to both boundary
lines of the strip, and proves that this field moves `ρ dx ∧ dy` back to `dx ∧ dy`.

With the row means `m(y) = ∫₀¹ g(x, y) dx` (`TauCeti.stripRowMean`), put

`a(y) = -∫₀ʸ m(r) dr`  (`TauCeti.stripMoserDxCoeff`),
`b(x, y) = ∫₀ˣ (g(s, y) - m(y)) ds`  (`TauCeti.stripMoserDyCoeff`),

and `β = a dx + b dy` (`TauCeti.stripMoserPrimitive`). Then:

* `dβ = g dx ∧ dy` (`TauCeti.extDeriv_stripMoserPrimitive`), since `∂_x b = g - m` and
  `∂_y a = -m`;
* `a(0) = 0`, and `a(1) = 0` exactly when `∫₀¹ m = 0` (`TauCeti.stripMoserDxCoeff_one_eq_zero_iff`);
* `b` is `1`-periodic in `x` when `g` is (`TauCeti.stripMoserDyCoeff_add_one`), because each
  horizontal integral of `g - m` over a period vanishes;
* `a` and `b`, hence `β`, are `C^n` when `g` is (`TauCeti.contDiff_stripMoserPrimitive`).

For `t ∈ [0, 1]` the two-form `ω_t = (1 - t) dx ∧ dy + t ρ dx ∧ dy = (1 + t g) dx ∧ dy` is
positive where `ρ` is. Where `1 + t g ≠ 0`, the Moser vector field `X_t` defined by
`ι_(X_t) ω_t = -β` is

`X_t = (1 + t g)⁻¹ (-b, a)`  (`TauCeti.stripMoserVectorField`,
`TauCeti.curryLeft_stripMoserVectorField`).

Its second component vanishes on the boundary lines `y = 0` and `y = 1` when the total area
condition holds (`TauCeti.stripMoserVectorField_snd_mk_zero`,
`TauCeti.stripMoserVectorField_snd_mk_one`), so it is tangent to both boundary lines, and it
is invariant under the deck translation `(x, y) ↦ (x + 1, y)`
(`TauCeti.stripMoserVectorField_add_one`). It is jointly `C^n` in `(t, p)` where `1 + t g ≠ 0`
(`TauCeti.contDiffOn_stripMoserVectorField`). By Moser's identity
(`TauCeti.compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg`), a family of maps `ψ_t` moving
along `X_t` satisfies `ψ₁^* (ρ dx ∧ dy) = ψ₀^* (dx ∧ dy)`
(`TauCeti.compContinuousLinearMap_fderiv_eq_of_stripMoserVectorField`). Since every two-form on
the plane is closed, no closedness hypothesis is needed.

This is the step that turns a smooth isotopy of the annulus into an area-preserving one: if
`h^* (dx ∧ dy) = ρ dx ∧ dy` and `ψ₀ = id`, then `h ∘ ψ₁` preserves `dx ∧ dy`. The flow
`ψ` itself is not constructed here. For the density `ρ = 1 + ε sin(2π x)` the data are
`m = 0`, `a = 0` and `b = ε (1 - cos(2π x)) / (2π)` (`TauCeti.stripMoserDyCoeff_sin`); the
field then has zero second component everywhere.

## Main definitions

* `TauCeti.stripRowMean g y`: the mean `∫₀¹ g(x, y) dx` of `g` along the row at height `y`.
* `TauCeti.stripMoserPrimitive g`: the one-form `β = a dx + b dy` with `dβ = g dx ∧ dy`.
* `TauCeti.stripMoserVectorField g t`: the Moser vector field `(1 + t g)⁻¹ (-b, a)`.

## Main results

* `TauCeti.extDeriv_stripMoserPrimitive`: `dβ = g dx ∧ dy`.
* `TauCeti.curryLeft_stripMoserVectorField`: `ι_(X_t) ((1 + t g) dx ∧ dy) = -β`.
* `TauCeti.stripMoserVectorField_snd_mk_zero`, `TauCeti.stripMoserVectorField_snd_mk_one`: the
  field is tangent to both boundary lines.
* `TauCeti.compContinuousLinearMap_fderiv_eq_of_stripMoserVectorField`: the Moser flow pulls
  `ρ dx ∧ dy` back to `dx ∧ dy`.

## References

* J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. 120 (1965),
  286–294.
* Charles Conley and Eduard Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open MeasureTheory Set Filter intervalIntegral Real
open scoped Topology

namespace TauCeti

/-! ### The primitive -/

/-- The mean `m(y) = ∫₀¹ g(x, y) dx` of a function `g` on the plane along the horizontal row at
height `y`. -/
def stripRowMean (g : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, g (x, y)

/-- The `dx`-coefficient `a(y) = -∫₀ʸ m(r) dr` of the Moser primitive
`TauCeti.stripMoserPrimitive g`, where `m` is `TauCeti.stripRowMean g`. -/
def stripMoserDxCoeff (g : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  -∫ r in (0 : ℝ)..y, stripRowMean g r

/-- The `dy`-coefficient `b(x, y) = ∫₀ˣ (g(s, y) - m(y)) ds` of the Moser primitive
`TauCeti.stripMoserPrimitive g`, where `m` is `TauCeti.stripRowMean g`. -/
def stripMoserDyCoeff (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..p.1, (g (s, p.2) - stripRowMean g p.2)

/-- The **Moser primitive** `β = a dx + b dy` of `g dx ∧ dy` on the strip, with coefficients
`TauCeti.stripMoserDxCoeff g` and `TauCeti.stripMoserDyCoeff g`. For `C¹` functions `g`, its
exterior derivative is `g dx ∧ dy` (`TauCeti.extDeriv_stripMoserPrimitive`). -/
def stripMoserPrimitive (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  stripMoserDxCoeff g p.2 • Prod.realPlaneDx p + stripMoserDyCoeff g p • Prod.realPlaneDy p

variable {g : ℝ × ℝ → ℝ} {n : ℕ∞}

/-- The row mean at height `y` is `∫₀¹ g(x, y) dx`. -/
theorem stripRowMean_def (y : ℝ) : stripRowMean g y = ∫ x in (0 : ℝ)..1, g (x, y) := by
  rw [stripRowMean]

/-- The `dx`-coefficient of the Moser primitive is `a(y) = -∫₀ʸ m(r) dr`. -/
theorem stripMoserDxCoeff_def (y : ℝ) :
    stripMoserDxCoeff g y = -∫ r in (0 : ℝ)..y, stripRowMean g r := by
  rw [stripMoserDxCoeff]

/-- The `dy`-coefficient of the Moser primitive is `b(x, y) = ∫₀ˣ (g(s, y) - m(y)) ds`. -/
theorem stripMoserDyCoeff_def (p : ℝ × ℝ) :
    stripMoserDyCoeff g p = ∫ s in (0 : ℝ)..p.1, (g (s, p.2) - stripRowMean g p.2) := by
  rw [stripMoserDyCoeff]

/-- The Moser primitive `β = a dx + b dy` evaluates to `a w₁ + b w₂` on a vector `w`. -/
@[simp]
theorem stripMoserPrimitive_apply (p : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) :
    stripMoserPrimitive g p v =
      stripMoserDxCoeff g p.2 * (v 0).1 + stripMoserDyCoeff g p * (v 0).2 := by
  simp [stripMoserPrimitive]

/-- The `dx`-coefficient vanishes on the bottom boundary line `y = 0`. -/
@[simp]
theorem stripMoserDxCoeff_zero : stripMoserDxCoeff g 0 = 0 := by
  simp [stripMoserDxCoeff]

/-- The `dx`-coefficient vanishes on the top boundary line exactly when the row means of `g`
have integral zero, that is, when `∫₀¹ ∫₀¹ g(x, y) dx dy = 0`. -/
theorem stripMoserDxCoeff_one_eq_zero_iff :
    stripMoserDxCoeff g 1 = 0 ↔ ∫ y in (0 : ℝ)..1, stripRowMean g y = 0 := by
  simp [stripMoserDxCoeff]

/-- The `dy`-coefficient vanishes on the vertical line `x = 0`. -/
@[simp]
theorem stripMoserDyCoeff_mk_zero (y : ℝ) : stripMoserDyCoeff g (0, y) = 0 := by
  simp [stripMoserDyCoeff]

/-- The row means of a `C^n` function are `C^n`. -/
theorem contDiff_stripRowMean (hg : ContDiff ℝ n g) : ContDiff ℝ n (stripRowMean g) :=
  ContDiff.parametric_intervalIntegral (f := fun q : ℝ × ℝ ↦ g (q.2, q.1))
    (hg.comp (contDiff_snd.prodMk contDiff_fst))

/-- The row means of a continuous function are continuous. -/
theorem continuous_stripRowMean (hg : Continuous g) : Continuous (stripRowMean g) :=
  (contDiff_stripRowMean (n := 0) (contDiff_zero.2 hg)).continuous

/-- The `dx`-coefficient of the Moser primitive of a `C^n` function is `C^n`. -/
theorem contDiff_stripMoserDxCoeff (hg : ContDiff ℝ n g) : ContDiff ℝ n (stripMoserDxCoeff g) := by
  have h := contDiff_parametric_primitive_of_contDiff (f := fun (_ : ℝ) r ↦ stripRowMean g r)
    ((contDiff_stripRowMean hg).comp contDiff_snd) 0
  exact (h.comp (contDiff_id.prodMk contDiff_id)).neg

/-- The `dy`-coefficient of the Moser primitive of a `C^n` function is `C^n`. -/
theorem contDiff_stripMoserDyCoeff (hg : ContDiff ℝ n g) : ContDiff ℝ n (stripMoserDyCoeff g) :=
  (contDiff_parametric_primitive_of_contDiff
    (f := fun (p : ℝ × ℝ) s ↦ g (s, p.2) - stripRowMean g p.2)
    ((hg.comp (contDiff_snd.prodMk contDiff_fst.snd)).sub
      ((contDiff_stripRowMean hg).comp contDiff_fst.snd)) 0).comp
    (contDiff_id.prodMk contDiff_fst)

/-- The Moser primitive of a `C^n` function is `C^n`. -/
theorem contDiff_stripMoserPrimitive (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (stripMoserPrimitive g) :=
  (((contDiff_stripMoserDxCoeff hg).comp contDiff_snd).smul Prod.contDiff_realPlaneDx).add
    ((contDiff_stripMoserDyCoeff hg).smul Prod.contDiff_realPlaneDy)

/-- The derivative of the `dx`-coefficient is `-m`. -/
theorem hasDerivAt_stripMoserDxCoeff (hg : Continuous g) (y : ℝ) :
    HasDerivAt (stripMoserDxCoeff g) (-stripRowMean g y) y :=
  ((continuous_stripRowMean hg).integral_hasStrictDerivAt 0 y).hasDerivAt.neg

/-- The partial derivative of the `dy`-coefficient in `x` is `g - m`. -/
theorem hasDerivAt_stripMoserDyCoeff_mk (hg : Continuous g) (x y : ℝ) :
    HasDerivAt (fun x ↦ stripMoserDyCoeff g (x, y)) (g (x, y) - stripRowMean g y) x := by
  have hk : Continuous fun s ↦ g (s, y) - stripRowMean g y :=
    (hg.comp (continuous_id.prodMk continuous_const)).sub continuous_const
  exact (hk.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- For a function `1`-periodic in `x`, the `dy`-coefficient of the Moser primitive is
`1`-periodic in `x`: the integral of `g - m` over a period of a row vanishes. -/
theorem stripMoserDyCoeff_add_one (hg : Continuous g) (hper : ∀ x y, g (x + 1, y) = g (x, y))
    (x y : ℝ) : stripMoserDyCoeff g (x + 1, y) = stripMoserDyCoeff g (x, y) := by
  have hgy : Continuous fun s ↦ g (s, y) := hg.comp (continuous_id.prodMk continuous_const)
  have hk : Continuous fun s ↦ g (s, y) - stripRowMean g y := hgy.sub continuous_const
  have hkper : Function.Periodic (fun s ↦ g (s, y) - stripRowMean g y) 1 := fun s ↦ by
    simp [hper]
  have hperiod : ∫ s in x..x + 1, (g (s, y) - stripRowMean g y) = 0 := by
    rw [hkper.intervalIntegral_add_eq x 0, zero_add,
      integral_sub (hgy.intervalIntegrable 0 1) intervalIntegrable_const]
    simp [stripRowMean]
  simp only [stripMoserDyCoeff]
  rw [← integral_add_adjacent_intervals (hk.intervalIntegrable 0 x) (hk.intervalIntegrable x _),
    hperiod, add_zero]

/-! ### The exterior derivative of the primitive -/

/-- The derivative of the `dy`-coefficient splits into its partial derivative `g - m` in `x` and
its partial derivative in `y`. -/
private theorem fderiv_stripMoserDyCoeff_apply (hg : ContDiff ℝ 1 g) (p u : ℝ × ℝ) :
    fderiv ℝ (stripMoserDyCoeff g) p u =
      u.1 * (g p - stripRowMean g p.2) + u.2 * fderiv ℝ (stripMoserDyCoeff g) p (0, 1) := by
  have hb : HasFDerivAt (stripMoserDyCoeff g) (fderiv ℝ (stripMoserDyCoeff g) p) p :=
    ((contDiff_stripMoserDyCoeff hg).differentiable one_ne_zero p).hasFDerivAt
  -- The partial derivative in `x` is both `D b (1, 0)` and, by the fundamental theorem of
  -- calculus, `g - m`.
  have hx : fderiv ℝ (stripMoserDyCoeff g) p (1, 0) = g p - stripRowMean g p.2 := by
    have hcomp := hb.comp_hasDerivAt (f := fun x ↦ (x, p.2)) p.1
      (HasDerivAt.prodMk (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2))
    exact hcomp.unique (hasDerivAt_stripMoserDyCoeff_mk hg.continuous p.1 p.2)
  have hu : u = u.1 • ((1 : ℝ), (0 : ℝ)) + u.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hu]
  rw [map_add, map_smul, map_smul, hx, smul_eq_mul, smul_eq_mul]

/-- Evaluating the Moser primitive on a fixed vector `w` gives the function
`a(y) w₁ + b(x, y) w₂`, whose derivative is computed from those of `a` and `b`. -/
private theorem fderiv_stripMoserPrimitive_apply_apply (hg : ContDiff ℝ 1 g) (p u w : ℝ × ℝ) :
    fderiv ℝ (fun q ↦ stripMoserPrimitive g q (fun _ ↦ w)) p u =
      -stripRowMean g p.2 * u.2 * w.1 + fderiv ℝ (stripMoserDyCoeff g) p u * w.2 := by
  have ha : HasFDerivAt (fun q : ℝ × ℝ ↦ stripMoserDxCoeff g q.2)
      ((-stripRowMean g p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (hasDerivAt_stripMoserDxCoeff hg.continuous p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have hb : HasFDerivAt (stripMoserDyCoeff g) (fderiv ℝ (stripMoserDyCoeff g) p) p :=
    ((contDiff_stripMoserDyCoeff hg).differentiable one_ne_zero p).hasFDerivAt
  have h : HasFDerivAt (fun q ↦ stripMoserDxCoeff g q.2 * w.1 + stripMoserDyCoeff g q * w.2)
      (w.1 • (-stripRowMean g p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ +
        w.2 • fderiv ℝ (stripMoserDyCoeff g) p) p :=
    (ha.mul_const w.1).add (hb.mul_const w.2)
  simp only [stripMoserPrimitive_apply]
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **The Moser primitive is a primitive of `g dx ∧ dy`.** For a `C¹` function `g`, the
exterior derivative of `β = a dx + b dy` is `g dx ∧ dy`. -/
theorem extDeriv_stripMoserPrimitive (hg : ContDiff ℝ 1 g) (p : ℝ × ℝ) :
    extDeriv (stripMoserPrimitive g) p =
      g p • (Prod.realPlaneDx p).wedge (Prod.realPlaneDy p) := by
  ext v
  -- Normalize the two arguments as a tuple so that the pair formula and the wedge evaluation
  -- apply.
  rw [show v = ![v 0, v 1] by funext i; fin_cases i <;> rfl,
    extDeriv_apply_pair_of_differentiableAt
      ((contDiff_stripMoserPrimitive hg).differentiable one_ne_zero p),
    fderiv_stripMoserPrimitive_apply_apply hg, fderiv_stripMoserPrimitive_apply_apply hg,
    fderiv_stripMoserDyCoeff_apply hg p (v 0), fderiv_stripMoserDyCoeff_apply hg p (v 1)]
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.wedge_apply_one_one,
    Prod.realPlaneDx_apply, Prod.realPlaneDy_apply, Matrix.cons_val_zero, smul_eq_mul]
  ring

/-! ### The Moser vector field -/

/-- The **Moser vector field** `X_t = (1 + t g)⁻¹ (-b, a)` of the straight-line path from
`dx ∧ dy` to `(1 + g) dx ∧ dy`, where `a` and `b` are the coefficients of the Moser primitive
`β = a dx + b dy`. Where `1 + t g ≠ 0` it satisfies `ι_(X_t) ((1 + t g) dx ∧ dy) = -β`
(`TauCeti.curryLeft_stripMoserVectorField`). -/
def stripMoserVectorField (g : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 + t * g p)⁻¹ • (-stripMoserDyCoeff g p, stripMoserDxCoeff g p.2)

/-- The first component of the Moser vector field is `-(1 + t g)⁻¹ b`. -/
@[simp]
theorem stripMoserVectorField_fst (t : ℝ) (p : ℝ × ℝ) :
    (stripMoserVectorField g t p).1 = -(1 + t * g p)⁻¹ * stripMoserDyCoeff g p := by
  simp [stripMoserVectorField]

/-- The second component of the Moser vector field is `(1 + t g)⁻¹ a`. -/
@[simp]
theorem stripMoserVectorField_snd (t : ℝ) (p : ℝ × ℝ) :
    (stripMoserVectorField g t p).2 = (1 + t * g p)⁻¹ * stripMoserDxCoeff g p.2 := by
  simp [stripMoserVectorField]

/-- The Moser vector field is tangent to the bottom boundary line `y = 0`. -/
theorem stripMoserVectorField_snd_mk_zero (t x : ℝ) :
    (stripMoserVectorField g t (x, 0)).2 = 0 := by
  simp

/-- When `∫₀¹ ∫₀¹ g(x, y) dx dy = 0`, the Moser vector field is tangent to the top boundary line
`y = 1`. -/
theorem stripMoserVectorField_snd_mk_one (h : ∫ y in (0 : ℝ)..1, stripRowMean g y = 0) (t x : ℝ) :
    (stripMoserVectorField g t (x, 1)).2 = 0 := by
  simp [stripMoserDxCoeff_one_eq_zero_iff.2 h]

/-- For a function `1`-periodic in `x`, the Moser vector field is invariant under the deck
translation `(x, y) ↦ (x + 1, y)`. -/
theorem stripMoserVectorField_add_one (hg : Continuous g) (hper : ∀ x y, g (x + 1, y) = g (x, y))
    (t x y : ℝ) : stripMoserVectorField g t (x + 1, y) = stripMoserVectorField g t (x, y) := by
  simp [stripMoserVectorField, hper, stripMoserDyCoeff_add_one hg hper]

/-- **The contraction equation of the Moser vector field.** Where `1 + t g ≠ 0`, contracting
`ω_t = (1 - t) dx ∧ dy + t (1 + g) dx ∧ dy` with `X_t` gives `-β`. -/
theorem curryLeft_stripMoserVectorField {t : ℝ} {p : ℝ × ℝ} (h : 1 + t * g p ≠ 0) :
    ((1 - t) • (Prod.realPlaneDx p).wedge (Prod.realPlaneDy p) +
        t • (1 + g p) • (Prod.realPlaneDx p).wedge (Prod.realPlaneDy p)).curryLeft
      (stripMoserVectorField g t p) = -stripMoserPrimitive g p := by
  ext v
  -- Write the single vector as the one-entry tuple `![v 0]` so the wedge evaluation applies.
  rw [← Matrix.cons_head_tail v, Matrix.empty_eq (Matrix.vecTail v)]
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.wedge_apply_one_one,
    Prod.realPlaneDx_apply, Prod.realPlaneDy_apply, ContinuousAlternatingMap.neg_apply,
    stripMoserPrimitive_apply, stripMoserVectorField_fst, stripMoserVectorField_snd,
    Matrix.cons_val_zero, smul_eq_mul]
  field_simp
  ring

/-- The Moser vector field is jointly `C^n` in time and position where `1 + t g ≠ 0`. -/
theorem contDiffOn_stripMoserVectorField (hg : ContDiff ℝ n g) :
    ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) ↦ stripMoserVectorField g q.1 q.2)
      {q | 1 + q.1 * g q.2 ≠ 0} := by
  have hinv : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) ↦ (1 + q.1 * g q.2)⁻¹)
      {q | 1 + q.1 * g q.2 ≠ 0} :=
    (contDiff_const.add (contDiff_fst.mul (hg.comp contDiff_snd))).contDiffOn.inv fun _ hq ↦ hq
  have hv : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦
      (-stripMoserDyCoeff g q.2, stripMoserDxCoeff g q.2.2) :=
    ((contDiff_stripMoserDyCoeff hg).comp contDiff_snd).neg.prodMk
      ((contDiff_stripMoserDxCoeff hg).comp contDiff_snd.snd)
  exact hinv.smul hv.contDiffOn

/-- **Moser's argument on the strip.** Let `g` be `C¹`, and let `ψ_t`, `t ∈ [0, 1]`, be a family
of maps moving along the Moser vector field `X_t`, with `1 + t g ≠ 0` along the trajectory of
`x`; this holds when the density `1 + g` is positive, since `1 + t g = (1 - t) + t (1 + g)`. Then
`ψ₁` pulls `(1 + g) dx ∧ dy` back at `x` to the pullback of `dx ∧ dy` by `ψ₀`. -/
theorem compContinuousLinearMap_fderiv_eq_of_stripMoserVectorField (hg : ContDiff ℝ 1 g)
    {ψ : ℝ → ℝ × ℝ → ℝ × ℝ} {x : ℝ × ℝ}
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, 1 + t * g (ψ t x) ≠ 0)
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s ↦ ψ s x) (stripMoserVectorField g t (ψ t x)) t)
    (hDψ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ fderiv ℝ (ψ s) x)
      (fderiv ℝ (stripMoserVectorField g t) (ψ t x) ∘L fderiv ℝ (ψ t) x) t) :
    ((1 + g (ψ 1 x)) • (Prod.realPlaneDx (ψ 1 x)).wedge
        (Prod.realPlaneDy (ψ 1 x))).compContinuousLinearMap (fderiv ℝ (ψ 1) x) =
      ((Prod.realPlaneDx (ψ 0 x)).wedge (Prod.realPlaneDy (ψ 0 x))).compContinuousLinearMap
        (fderiv ℝ (ψ 0) x) := by
  set A : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] ℝ :=
    fun p ↦ (Prod.realPlaneDx p).wedge (Prod.realPlaneDy p) with hA_def
  have hA : A = fun _ ↦ A 0 := by
    funext p
    simp only [hA_def]
    rw [Prod.realPlaneDx_eq_const, Prod.realPlaneDy_eq_const]
  have hAd : ContDiff ℝ 1 A := by
    rw [hA]
    exact contDiff_const
  have hω₁ : ContDiff ℝ 1 fun p ↦ (1 + g p) • A p := (contDiff_const.add hg).smul hAd
  -- Every three-form on the plane vanishes, so both forms are closed.
  have hclosed : ∀ ω : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] ℝ, ∀ p, extDeriv ω p = 0 := fun ω p ↦
    (extDeriv ω p).eq_zero_of_finrank_lt (by simp)
  -- The contraction equation holds on the open set where `1 + t g ≠ 0`.
  have hopen (t : ℝ) : IsOpen {p : ℝ × ℝ | 1 + t * g p ≠ 0} :=
    isOpen_ne_fun (continuous_const.add (continuous_const.mul hg.continuous)) continuous_const
  refine compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg (ω₀ := A)
    (ω₁ := fun p ↦ (1 + g p) • A p) (α := stripMoserPrimitive g)
    (X := stripMoserVectorField g)
    (fun _ _ ↦ hAd.differentiable one_ne_zero _)
    (fun _ _ ↦ hω₁.differentiable one_ne_zero _)
    (fun _ _ ↦ hclosed _ _) (fun _ _ ↦ hclosed _ _)
    (fun t _ ↦ ?_) (fun t ht ↦ ?_) (fun t ht ↦ ?_) hψ hDψ
  · rw [extDeriv_stripMoserPrimitive hg]
    simp only [A, add_smul, one_smul, add_sub_cancel_left]
  · filter_upwards [(hopen t).mem_nhds (hne t ht)] with p hp
    exact curryLeft_stripMoserVectorField hp
  · have hXd := ((contDiffOn_stripMoserVectorField (n := 1) hg).differentiableOn one_ne_zero)
      (t, ψ t x) (hne t ht)
    have hmem : {q : ℝ × (ℝ × ℝ) | 1 + q.1 * g q.2 ≠ 0} ∈ 𝓝 (t, ψ t x) :=
      (isOpen_ne_fun (continuous_const.add (continuous_fst.mul (hg.continuous.comp
        continuous_snd))) continuous_const).mem_nhds (hne t ht)
    exact (hXd.differentiableAt hmem).comp (ψ t x)
      ((differentiableAt_const t).prodMk differentiableAt_id)

/-! ### The density `1 + ε sin(2π x)` -/

/-- For `g(x, y) = ε sin(2π x)`, the row means vanish. -/
theorem stripRowMean_sin (ε : ℝ) : stripRowMean (fun p ↦ ε * sin (2 * π * p.1)) = 0 := by
  funext y
  simp [stripRowMean]

/-- For `g(x, y) = ε sin(2π x)`, the `dx`-coefficient of the Moser primitive vanishes. -/
theorem stripMoserDxCoeff_sin (ε : ℝ) : stripMoserDxCoeff (fun p ↦ ε * sin (2 * π * p.1)) = 0 := by
  funext y
  simp [stripMoserDxCoeff, stripRowMean_sin]

/-- For `g(x, y) = ε sin(2π x)`, the `dy`-coefficient of the Moser primitive is
`ε (1 - cos(2π x)) / (2π)`. -/
theorem stripMoserDyCoeff_sin (ε : ℝ) (p : ℝ × ℝ) :
    stripMoserDyCoeff (fun p ↦ ε * sin (2 * π * p.1)) p =
      ε * (1 - cos (2 * π * p.1)) / (2 * π) := by
  simp only [stripMoserDyCoeff, stripRowMean_sin, Pi.zero_apply, sub_zero]
  rw [intervalIntegral.integral_const_mul, integral_comp_mul_left (fun s ↦ sin s) (by positivity),
    integral_sin, mul_zero, cos_zero, smul_eq_mul]
  field_simp

end TauCeti
