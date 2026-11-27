/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormSq
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The circle-invariant height on the plane blown up at a point, in charts

The blow-up of `ℂP²` at `[0 : 1 : 0]` is the incidence surface

`B = {([z₀ : z₁ : z₂], [a : b]) | z₀ b = z₂ a} ⊆ ℂP² × ℂP¹`.

Its projection to `ℂP²` is an isomorphism away from `[0 : 1 : 0]`, over which it has the
exceptional sphere `E = {[0 : 1 : 0]} × ℂP¹`. The circle acts on `B` by

`t • ([z₀ : z₁ : z₂], [a : b]) = ([e^{it} z₀ : z₁ : e^{-it} z₂], [e^{it} a : e^{-it} b])`,

and, for a real parameter `ε`, the function

`f = -(|z₀|² - |z₂|²) / (|z₀|² + |z₁|² + |z₂|²) - ε (|a|² - |b|²) / (|a|² + |b|²)`

is invariant. For `0 < ε < 1` it is the moment map of this action for the restriction of the
Kähler form `2π (ω_FS + ε ω_FS)` of `ℂP² × ℂP¹`; that identification is not proved here. This file
works in homogeneous coordinates: `B` is the set `TauCeti.blownUpPlane` of pairs of nonzero
vectors `(z, w) ∈ ℂ³ × ℂ²` with `z₀ w₁ = z₂ w₀`, which is invariant under independent rescaling of
`z` and `w` (`TauCeti.smul_mem_blownUpPlane_iff`), and `f` is `TauCeti.blownUpPlaneHeight ε`,
which is invariant under the same rescalings (`TauCeti.blownUpPlaneHeight_smul`) and under the
circle action (`TauCeti.blownUpPlaneHeight_circleAction`).

The fixed points of the action are the two poles `([0 : 1 : 0], [1 : 0])` and
`([0 : 1 : 0], [0 : 1])` of `E` and the points `([1 : 0 : 0], [1 : 0])` and
`([0 : 0 : 1], [0 : 1])`. Around each one, `B` has an affine chart by `ℂ × ℂ`:

* `(u, v) ↦ ([u : 1 : u v], [1 : v])` at the lower pole of `E`
  (`TauCeti.blownUpPlaneLowerPoleChart`), where `E` is `u = 0`;
* `(s, w) ↦ ([s w : 1 : w], [s : 1])` at the upper pole of `E`
  (`TauCeti.blownUpPlaneUpperPoleChart`), where `E` is `w = 0`;
* `(x, y) ↦ ([1 : x : y], [1 : y])` at `([1 : 0 : 0], [1 : 0])` (`TauCeti.blownUpPlaneMinChart`);
* `(x, y) ↦ ([x : y : 1], [x : 1])` at `([0 : 0 : 1], [0 : 1])` (`TauCeti.blownUpPlaneMaxChart`).

Each chart lands in `B`, and every point of `B` in the corresponding affine open set is a rescaling
of a chart point (for instance `TauCeti.exists_eq_smul_blownUpPlaneLowerPoleChart`). In the pole
charts the circle acts linearly with weights `(1, -2)` and `(2, -1)`
(`TauCeti.blownUpPlaneCircleAction_lowerPoleChart`,
`TauCeti.blownUpPlaneCircleAction_upperPoleChart`): along `E` the weight is `∓2`, normal to it
`±1`.

In each chart `f` is a function `g (‖p.1‖ ², ‖p.2‖ ²)` of the two squared moduli, so its Hessian at
the origin is read off from the partial derivatives of `g`
(`TauCeti.hessianQuadraticForm_comp_norm_sq_prod_zero`). This gives the critical values and
Hessians

| fixed point | value | Hessian at `0` | Morse index |
|---|---|---|---|
| lower pole | `-ε` | `-2 ‖v₁‖² + 4 ε ‖v₂‖²` | `2` for `0 ≤ ε` |
| upper pole | `ε` | `-4 ε ‖v₁‖² + 2 ‖v₂‖²` | `2` for `0 < ε` |
| `([1 : 0 : 0], [1 : 0])` | `-1 - ε` | `2 ‖v₁‖² + 4 (1 + ε) ‖v₂‖²` | `0` for `-1 ≤ ε` |
| `([0 : 0 : 1], [0 : 1])` | `1 + ε` | `-4 (1 + ε) ‖v₁‖² - 2 ‖v₂‖²` | `4` for `-1 < ε` |

and the critical points are nondegenerate when `ε ≠ 0`, respectively `ε ≠ -1`. In particular for
`0 < ε` both poles of the exceptional sphere are nondegenerate critical points of the same index
`2`, with values `-ε < ε`. These are the local inputs of the classical observation that this
invariant height admits no invariant Morse–Smale metric: the gradient of an invariant function for
an invariant metric is tangent to the fixed sphere `E`, so the gradient lines inside `E` join two
critical points of equal index. That global argument, which needs the manifold structure of `B`,
is not formalized here.
-/

public section

open Complex

namespace TauCeti

/-! ### The incidence surface, the height and the circle action -/

/-- The plane blown up at `[0 : 1 : 0]`, in homogeneous coordinates: the pairs `(z, w)` of nonzero
vectors of `ℂ³` and `ℂ²` with `z₀ w₁ = z₂ w₀`, that is `([z₀ : z₁ : z₂], [w₀ : w₁])` lies on the
incidence surface in `ℂP² × ℂP¹`. -/
def blownUpPlane : Set ((Fin 3 → ℂ) × (Fin 2 → ℂ)) :=
  {p | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 0 * p.2 1 = p.1 2 * p.2 0}

theorem mem_blownUpPlane_iff {p : (Fin 3 → ℂ) × (Fin 2 → ℂ)} :
    p ∈ blownUpPlane ↔ p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 0 * p.2 1 = p.1 2 * p.2 0 :=
  Iff.rfl

/-- The blown-up plane is invariant under rescaling of either homogeneous coordinate vector. -/
@[simp]
theorem smul_mem_blownUpPlane_iff {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    {p : (Fin 3 → ℂ) × (Fin 2 → ℂ)} : (c • p.1, d • p.2) ∈ blownUpPlane ↔ p ∈ blownUpPlane := by
  simp only [mem_blownUpPlane_iff, ne_eq, smul_eq_zero, hc, hd, false_or, Pi.smul_apply,
    smul_eq_mul]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [show c * p.1 0 * (d * p.2 1) = c * d * (p.1 0 * p.2 1) by ring,
    show c * p.1 2 * (d * p.2 0) = c * d * (p.1 2 * p.2 0) by ring,
    mul_right_inj' (mul_ne_zero hc hd)]

/-- The circle-invariant height on the blown-up plane in homogeneous coordinates,
`-(|z₀|² - |z₂|²) / (|z₀|² + |z₁|² + |z₂|²) - ε (|w₀|² - |w₁|²) / (|w₀|² + |w₁|²)`. -/
noncomputable def blownUpPlaneHeight (ε : ℝ) (p : (Fin 3 → ℂ) × (Fin 2 → ℂ)) : ℝ :=
  -(‖p.1 0‖ ^ 2 - ‖p.1 2‖ ^ 2) / (‖p.1 0‖ ^ 2 + ‖p.1 1‖ ^ 2 + ‖p.1 2‖ ^ 2) -
    ε * (‖p.2 0‖ ^ 2 - ‖p.2 1‖ ^ 2) / (‖p.2 0‖ ^ 2 + ‖p.2 1‖ ^ 2)

variable {ε : ℝ}

/-- The height does not depend on the choice of homogeneous coordinates. -/
@[simp]
theorem blownUpPlaneHeight_smul {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    (p : (Fin 3 → ℂ) × (Fin 2 → ℂ)) :
    blownUpPlaneHeight ε (c • p.1, d • p.2) = blownUpPlaneHeight ε p := by
  have key : ∀ (r : ℝ), r ≠ 0 → ∀ x y : ℝ, (r * x) / (r * y) = x / y :=
    fun r hr x y ↦ mul_div_mul_left x y hr
  simp only [blownUpPlaneHeight, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [show -(‖c‖ ^ 2 * ‖p.1 0‖ ^ 2 - ‖c‖ ^ 2 * ‖p.1 2‖ ^ 2) =
      ‖c‖ ^ 2 * -(‖p.1 0‖ ^ 2 - ‖p.1 2‖ ^ 2) by ring,
    show ‖c‖ ^ 2 * ‖p.1 0‖ ^ 2 + ‖c‖ ^ 2 * ‖p.1 1‖ ^ 2 + ‖c‖ ^ 2 * ‖p.1 2‖ ^ 2 =
      ‖c‖ ^ 2 * (‖p.1 0‖ ^ 2 + ‖p.1 1‖ ^ 2 + ‖p.1 2‖ ^ 2) by ring,
    show ε * (‖d‖ ^ 2 * ‖p.2 0‖ ^ 2 - ‖d‖ ^ 2 * ‖p.2 1‖ ^ 2) =
      ‖d‖ ^ 2 * (ε * (‖p.2 0‖ ^ 2 - ‖p.2 1‖ ^ 2)) by ring,
    show ‖d‖ ^ 2 * ‖p.2 0‖ ^ 2 + ‖d‖ ^ 2 * ‖p.2 1‖ ^ 2 =
      ‖d‖ ^ 2 * (‖p.2 0‖ ^ 2 + ‖p.2 1‖ ^ 2) by ring,
    key _ (by positivity), key _ (by positivity)]

/-- The circle action `([z₀ : z₁ : z₂], [w₀ : w₁]) ↦ ([e^{it} z₀ : z₁ : e^{-it} z₂],
[e^{it} w₀ : e^{-it} w₁])` on homogeneous coordinates of the blown-up plane. -/
noncomputable def blownUpPlaneCircleAction (t : ℝ) (p : (Fin 3 → ℂ) × (Fin 2 → ℂ)) :
    (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  (![exp (t * I) * p.1 0, p.1 1, exp (-(t * I)) * p.1 2],
    ![exp (t * I) * p.2 0, exp (-(t * I)) * p.2 1])

@[simp]
theorem blownUpPlaneCircleAction_zero (p : (Fin 3 → ℂ) × (Fin 2 → ℂ)) :
    blownUpPlaneCircleAction 0 p = p := by
  refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp [blownUpPlaneCircleAction]

/-- The circle action is an action of the additive group `ℝ`. -/
theorem blownUpPlaneCircleAction_add (s t : ℝ) (p : (Fin 3 → ℂ) × (Fin 2 → ℂ)) :
    blownUpPlaneCircleAction (s + t) p =
      blownUpPlaneCircleAction s (blownUpPlaneCircleAction t p) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [blownUpPlaneCircleAction, add_mul, exp_add, mul_assoc, mul_left_comm]

/-- The circle action preserves the blown-up plane. -/
theorem blownUpPlaneCircleAction_mem_blownUpPlane {p : (Fin 3 → ℂ) × (Fin 2 → ℂ)}
    (hp : p ∈ blownUpPlane) (t : ℝ) : blownUpPlaneCircleAction t p ∈ blownUpPlane := by
  obtain ⟨h₁, h₂, h⟩ := hp
  refine ⟨fun h₀ ↦ h₁ ?_, fun h₀ ↦ h₂ ?_, ?_⟩
  · funext i
    have h := congrFun h₀ i
    fin_cases i <;> simpa [blownUpPlaneCircleAction, exp_ne_zero] using h
  · funext i
    have h := congrFun h₀ i
    fin_cases i <;> simpa [blownUpPlaneCircleAction, exp_ne_zero] using h
  · simp only [blownUpPlaneCircleAction, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
    linear_combination exp (t * I) * exp (-(t * I)) * h

/-- The height is invariant under the circle action. -/
@[simp]
theorem blownUpPlaneHeight_circleAction (t : ℝ) (p : (Fin 3 → ℂ) × (Fin 2 → ℂ)) :
    blownUpPlaneHeight ε (blownUpPlaneCircleAction t p) = blownUpPlaneHeight ε p := by
  simp [blownUpPlaneHeight, blownUpPlaneCircleAction, norm_exp]

/-! ### The four affine charts around the fixed points -/

/-- The chart `(u, v) ↦ ([u : 1 : u v], [1 : v])` of the blown-up plane around the lower pole
`([0 : 1 : 0], [1 : 0])` of the exceptional sphere, which is `u = 0` in this chart. -/
def blownUpPlaneLowerPoleChart (q : ℂ × ℂ) : (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  (![q.1, 1, q.1 * q.2], ![1, q.2])

/-- The chart `(s, w) ↦ ([s w : 1 : w], [s : 1])` of the blown-up plane around the upper pole
`([0 : 1 : 0], [0 : 1])` of the exceptional sphere, which is `w = 0` in this chart. -/
def blownUpPlaneUpperPoleChart (q : ℂ × ℂ) : (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  (![q.1 * q.2, 1, q.2], ![q.1, 1])

/-- The chart `(x, y) ↦ ([1 : x : y], [1 : y])` of the blown-up plane around the minimum
`([1 : 0 : 0], [1 : 0])` of the height. -/
def blownUpPlaneMinChart (q : ℂ × ℂ) : (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  (![1, q.1, q.2], ![1, q.2])

/-- The chart `(x, y) ↦ ([x : y : 1], [x : 1])` of the blown-up plane around the maximum
`([0 : 0 : 1], [0 : 1])` of the height. -/
def blownUpPlaneMaxChart (q : ℂ × ℂ) : (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  (![q.1, q.2, 1], ![q.1, 1])

theorem blownUpPlaneLowerPoleChart_mem_blownUpPlane (q : ℂ × ℂ) :
    blownUpPlaneLowerPoleChart q ∈ blownUpPlane :=
  ⟨fun h ↦ one_ne_zero (congrFun h 1), fun h ↦ one_ne_zero (congrFun h 0), by
    simp [blownUpPlaneLowerPoleChart]⟩

theorem blownUpPlaneUpperPoleChart_mem_blownUpPlane (q : ℂ × ℂ) :
    blownUpPlaneUpperPoleChart q ∈ blownUpPlane :=
  ⟨fun h ↦ one_ne_zero (congrFun h 1), fun h ↦ one_ne_zero (congrFun h 1), by
    simp [blownUpPlaneUpperPoleChart, mul_comm]⟩

theorem blownUpPlaneMinChart_mem_blownUpPlane (q : ℂ × ℂ) :
    blownUpPlaneMinChart q ∈ blownUpPlane :=
  ⟨fun h ↦ one_ne_zero (congrFun h 0), fun h ↦ one_ne_zero (congrFun h 0), by
    simp [blownUpPlaneMinChart]⟩

theorem blownUpPlaneMaxChart_mem_blownUpPlane (q : ℂ × ℂ) :
    blownUpPlaneMaxChart q ∈ blownUpPlane :=
  ⟨fun h ↦ one_ne_zero (congrFun h 2), fun h ↦ one_ne_zero (congrFun h 1), by
    simp [blownUpPlaneMaxChart, mul_comm]⟩

/-- Every point of the blown-up plane with `z₁ ≠ 0` and `w₀ ≠ 0` is a rescaling of a point of the
lower pole chart. -/
theorem exists_eq_smul_blownUpPlaneLowerPoleChart {p : (Fin 3 → ℂ) × (Fin 2 → ℂ)}
    (hp : p ∈ blownUpPlane) (h₁ : p.1 1 ≠ 0) (h₂ : p.2 0 ≠ 0) :
    ∃ q : ℂ × ℂ, ∃ c d : ℂ, c ≠ 0 ∧ d ≠ 0 ∧
      p = (c • (blownUpPlaneLowerPoleChart q).1, d • (blownUpPlaneLowerPoleChart q).2) := by
  refine ⟨(p.1 0 / p.1 1, p.2 1 / p.2 0), p.1 1, p.2 0, h₁, h₂, Prod.ext ?_ ?_⟩ <;> funext i <;>
    fin_cases i <;> simp [blownUpPlaneLowerPoleChart] <;> field_simp
  linear_combination -hp.2.2

/-- Every point of the blown-up plane with `z₁ ≠ 0` and `w₁ ≠ 0` is a rescaling of a point of the
upper pole chart. -/
theorem exists_eq_smul_blownUpPlaneUpperPoleChart {p : (Fin 3 → ℂ) × (Fin 2 → ℂ)}
    (hp : p ∈ blownUpPlane) (h₁ : p.1 1 ≠ 0) (h₂ : p.2 1 ≠ 0) :
    ∃ q : ℂ × ℂ, ∃ c d : ℂ, c ≠ 0 ∧ d ≠ 0 ∧
      p = (c • (blownUpPlaneUpperPoleChart q).1, d • (blownUpPlaneUpperPoleChart q).2) := by
  refine ⟨(p.2 0 / p.2 1, p.1 2 / p.1 1), p.1 1, p.2 1, h₁, h₂, Prod.ext ?_ ?_⟩ <;> funext i <;>
    fin_cases i <;> simp [blownUpPlaneUpperPoleChart] <;> field_simp
  linear_combination hp.2.2

/-- Every point of the blown-up plane with `z₀ ≠ 0` and `w₀ ≠ 0` is a rescaling of a point of the
chart around the minimum. -/
theorem exists_eq_smul_blownUpPlaneMinChart {p : (Fin 3 → ℂ) × (Fin 2 → ℂ)}
    (hp : p ∈ blownUpPlane) (h₁ : p.1 0 ≠ 0) (h₂ : p.2 0 ≠ 0) :
    ∃ q : ℂ × ℂ, ∃ c d : ℂ, c ≠ 0 ∧ d ≠ 0 ∧
      p = (c • (blownUpPlaneMinChart q).1, d • (blownUpPlaneMinChart q).2) := by
  refine ⟨(p.1 1 / p.1 0, p.1 2 / p.1 0), p.1 0, p.2 0, h₁, h₂, Prod.ext ?_ ?_⟩ <;> funext i <;>
    fin_cases i <;> simp [blownUpPlaneMinChart] <;> field_simp
  linear_combination hp.2.2

/-- Every point of the blown-up plane with `z₂ ≠ 0` and `w₁ ≠ 0` is a rescaling of a point of the
chart around the maximum. -/
theorem exists_eq_smul_blownUpPlaneMaxChart {p : (Fin 3 → ℂ) × (Fin 2 → ℂ)}
    (hp : p ∈ blownUpPlane) (h₁ : p.1 2 ≠ 0) (h₂ : p.2 1 ≠ 0) :
    ∃ q : ℂ × ℂ, ∃ c d : ℂ, c ≠ 0 ∧ d ≠ 0 ∧
      p = (c • (blownUpPlaneMaxChart q).1, d • (blownUpPlaneMaxChart q).2) := by
  refine ⟨(p.1 0 / p.1 2, p.1 1 / p.1 2), p.1 2, p.2 1, h₁, h₂, Prod.ext ?_ ?_⟩ <;> funext i <;>
    fin_cases i <;> simp [blownUpPlaneMaxChart] <;> field_simp
  linear_combination -hp.2.2

/-- In the lower pole chart the circle acts linearly with weights `1` normal to the exceptional
sphere and `-2` along it: up to rescaling of `w`, the point `(u, v)` moves to
`(e^{it} u, e^{-2it} v)`. -/
theorem blownUpPlaneCircleAction_lowerPoleChart (t : ℝ) (q : ℂ × ℂ) :
    blownUpPlaneCircleAction t (blownUpPlaneLowerPoleChart q) =
      ((blownUpPlaneLowerPoleChart (exp (t * I) * q.1, exp (-(2 * t * I)) * q.2)).1,
        exp (t * I) •
          (blownUpPlaneLowerPoleChart (exp (t * I) * q.1, exp (-(2 * t * I)) * q.2)).2) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp only [blownUpPlaneCircleAction, blownUpPlaneLowerPoleChart, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_fin_one, mul_one,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.smul_apply, smul_eq_mul]
  · rw [show exp (t * I) * q.1 * (exp (-(2 * t * I)) * q.2) =
      exp (t * I) * exp (-(2 * t * I)) * (q.1 * q.2) by ring, ← exp_add]
    ring_nf
  · rw [← mul_assoc, ← exp_add]
    ring_nf

/-- In the upper pole chart the circle acts linearly with weights `2` along the exceptional
sphere and `-1` normal to it: up to rescaling of `w`, the point `(s, w)` moves to
`(e^{2it} s, e^{-it} w)`. -/
theorem blownUpPlaneCircleAction_upperPoleChart (t : ℝ) (q : ℂ × ℂ) :
    blownUpPlaneCircleAction t (blownUpPlaneUpperPoleChart q) =
      ((blownUpPlaneUpperPoleChart (exp (2 * t * I) * q.1, exp (-(t * I)) * q.2)).1,
        exp (-(t * I)) •
          (blownUpPlaneUpperPoleChart (exp (2 * t * I) * q.1, exp (-(t * I)) * q.2)).2) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp only [blownUpPlaneCircleAction, blownUpPlaneUpperPoleChart, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_fin_one, mul_one,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.smul_apply, smul_eq_mul]
  · rw [show exp (2 * t * I) * q.1 * (exp (-(t * I)) * q.2) =
      exp (2 * t * I) * exp (-(t * I)) * (q.1 * q.2) by ring, ← exp_add]
    ring_nf
  · rw [← mul_assoc, ← exp_add]
    ring_nf

/-! ### The height in the charts -/

theorem blownUpPlaneHeight_lowerPoleChart (q : ℂ × ℂ) :
    blownUpPlaneHeight ε (blownUpPlaneLowerPoleChart q) =
      -(‖q.1‖ ^ 2 - ‖q.1‖ ^ 2 * ‖q.2‖ ^ 2) / (‖q.1‖ ^ 2 + 1 + ‖q.1‖ ^ 2 * ‖q.2‖ ^ 2) -
        ε * (1 - ‖q.2‖ ^ 2) / (1 + ‖q.2‖ ^ 2) := by
  simp [blownUpPlaneHeight, blownUpPlaneLowerPoleChart, mul_pow]

theorem blownUpPlaneHeight_upperPoleChart (q : ℂ × ℂ) :
    blownUpPlaneHeight ε (blownUpPlaneUpperPoleChart q) =
      -(‖q.1‖ ^ 2 * ‖q.2‖ ^ 2 - ‖q.2‖ ^ 2) / (‖q.1‖ ^ 2 * ‖q.2‖ ^ 2 + 1 + ‖q.2‖ ^ 2) -
        ε * (‖q.1‖ ^ 2 - 1) / (‖q.1‖ ^ 2 + 1) := by
  simp [blownUpPlaneHeight, blownUpPlaneUpperPoleChart, mul_pow]

theorem blownUpPlaneHeight_minChart (q : ℂ × ℂ) :
    blownUpPlaneHeight ε (blownUpPlaneMinChart q) =
      -(1 - ‖q.2‖ ^ 2) / (1 + ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) - ε * (1 - ‖q.2‖ ^ 2) / (1 + ‖q.2‖ ^ 2) := by
  simp [blownUpPlaneHeight, blownUpPlaneMinChart]

theorem blownUpPlaneHeight_maxChart (q : ℂ × ℂ) :
    blownUpPlaneHeight ε (blownUpPlaneMaxChart q) =
      -(‖q.1‖ ^ 2 - 1) / (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 + 1) - ε * (‖q.1‖ ^ 2 - 1) / (‖q.1‖ ^ 2 + 1) := by
  simp [blownUpPlaneHeight, blownUpPlaneMaxChart]

/-- The height at the lower pole of the exceptional sphere is `-ε`. -/
@[simp]
theorem blownUpPlaneHeight_lowerPoleChart_zero :
    blownUpPlaneHeight ε (blownUpPlaneLowerPoleChart 0) = -ε := by
  simp [blownUpPlaneHeight_lowerPoleChart]

/-- The height at the upper pole of the exceptional sphere is `ε`. -/
@[simp]
theorem blownUpPlaneHeight_upperPoleChart_zero :
    blownUpPlaneHeight ε (blownUpPlaneUpperPoleChart 0) = ε := by
  simp [blownUpPlaneHeight_upperPoleChart]

/-- The height at `([1 : 0 : 0], [1 : 0])` is `-1 - ε`. -/
@[simp]
theorem blownUpPlaneHeight_minChart_zero :
    blownUpPlaneHeight ε (blownUpPlaneMinChart 0) = -1 - ε := by
  simp [blownUpPlaneHeight_minChart]

/-- The height at `([0 : 0 : 1], [0 : 1])` is `1 + ε`. -/
@[simp]
theorem blownUpPlaneHeight_maxChart_zero :
    blownUpPlaneHeight ε (blownUpPlaneMaxChart 0) = 1 + ε := by
  simp [blownUpPlaneHeight_maxChart]

/-! ### Profiles of the height in the charts and their partial derivatives -/

private theorem contDiffAt_lowerProfile :
    ContDiffAt ℝ 2 (fun x : ℝ × ℝ ↦ -(x.1 - x.1 * x.2) / (x.1 + 1 + x.1 * x.2) -
      ε * (1 - x.2) / (1 + x.2)) 0 := by
  fun_prop (disch := simp)

private theorem hasDerivAt_lowerProfile_fst :
    HasDerivAt (fun x : ℝ ↦ -(x - x * 0) / (x + 1 + x * 0) - ε * (1 - 0) / (1 + 0)) (-1) 0 := by
  have hx := hasDerivAt_id' (0 : ℝ)
  convert (((hx.sub (hx.mul_const 0)).neg.div ((hx.add_const 1).add (hx.mul_const 0))
    (by norm_num)).sub_const (ε * (1 - 0) / (1 + 0))) using 1
  norm_num

private theorem hasDerivAt_lowerProfile_snd :
    HasDerivAt (fun y : ℝ ↦ -(0 - 0 * y) / (0 + 1 + 0 * y) - ε * (1 - y) / (1 + y)) (2 * ε) 0 := by
  have hy := hasDerivAt_id' (0 : ℝ)
  have h0 := hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have h1 := hasDerivAt_const (0 : ℝ) (1 : ℝ)
  convert (((h0.sub (hy.const_mul 0)).neg.div ((h0.add_const 1).add (hy.const_mul 0))
    (by norm_num)).sub (((h1.sub hy).const_mul ε).div (h1.add hy) (by norm_num))) using 1
  norm_num
  ring

private theorem contDiffAt_upperProfile :
    ContDiffAt ℝ 2 (fun x : ℝ × ℝ ↦ -(x.1 * x.2 - x.2) / (x.1 * x.2 + 1 + x.2) -
      ε * (x.1 - 1) / (x.1 + 1)) 0 := by
  fun_prop (disch := simp)

private theorem hasDerivAt_upperProfile_fst :
    HasDerivAt (fun x : ℝ ↦ -(x * 0 - 0) / (x * 0 + 1 + 0) - ε * (x - 1) / (x + 1)) (-2 * ε) 0 := by
  have hx := hasDerivAt_id' (0 : ℝ)
  convert ((((hx.mul_const 0).sub_const 0).neg.div (((hx.mul_const 0).add_const 1).add_const 0)
    (by norm_num)).sub (((hx.sub_const 1).const_mul ε).div (hx.add_const 1) (by norm_num)))
    using 1
  norm_num
  ring

private theorem hasDerivAt_upperProfile_snd :
    HasDerivAt (fun y : ℝ ↦ -(0 * y - y) / (0 * y + 1 + y) - ε * (0 - 1) / (0 + 1)) 1 0 := by
  have hy := hasDerivAt_id' (0 : ℝ)
  convert ((((hy.const_mul 0).sub hy).neg.div (((hy.const_mul 0).add_const 1).add hy)
    (by norm_num)).sub_const (ε * (0 - 1) / (0 + 1))) using 1
  norm_num

private theorem contDiffAt_minProfile :
    ContDiffAt ℝ 2 (fun x : ℝ × ℝ ↦ -(1 - x.2) / (1 + x.1 + x.2) -
      ε * (1 - x.2) / (1 + x.2)) 0 := by
  fun_prop (disch := simp)

private theorem hasDerivAt_minProfile_fst :
    HasDerivAt (fun x : ℝ ↦ -(1 - 0) / (1 + x + 0) - ε * (1 - 0) / (1 + 0)) 1 0 := by
  have hx := hasDerivAt_id' (0 : ℝ)
  have h1 := hasDerivAt_const (0 : ℝ) (1 : ℝ)
  convert (((h1.sub_const 0).neg.div ((h1.add hx).add_const 0) (by norm_num)).sub_const
    (ε * (1 - 0) / (1 + 0))) using 1
  norm_num

private theorem hasDerivAt_minProfile_snd :
    HasDerivAt (fun y : ℝ ↦ -(1 - y) / (1 + 0 + y) - ε * (1 - y) / (1 + y)) (2 + 2 * ε) 0 := by
  have hy := hasDerivAt_id' (0 : ℝ)
  have h1 := hasDerivAt_const (0 : ℝ) (1 : ℝ)
  convert (((h1.sub hy).neg.div ((h1.add_const 0).add hy) (by norm_num)).sub
    (((h1.sub hy).const_mul ε).div (h1.add hy) (by norm_num))) using 1
  norm_num
  ring

private theorem contDiffAt_maxProfile :
    ContDiffAt ℝ 2 (fun x : ℝ × ℝ ↦ -(x.1 - 1) / (x.1 + x.2 + 1) -
      ε * (x.1 - 1) / (x.1 + 1)) 0 := by
  fun_prop (disch := simp)

private theorem hasDerivAt_maxProfile_fst :
    HasDerivAt (fun x : ℝ ↦ -(x - 1) / (x + 0 + 1) - ε * (x - 1) / (x + 1)) (-2 - 2 * ε) 0 := by
  have hx := hasDerivAt_id' (0 : ℝ)
  convert (((hx.sub_const 1).neg.div ((hx.add_const 0).add_const 1) (by norm_num)).sub
    (((hx.sub_const 1).const_mul ε).div (hx.add_const 1) (by norm_num))) using 1
  norm_num
  ring

private theorem hasDerivAt_maxProfile_snd :
    HasDerivAt (fun y : ℝ ↦ -(0 - 1) / (0 + y + 1) - ε * (0 - 1) / (0 + 1)) (-1) 0 := by
  have hy := hasDerivAt_id' (0 : ℝ)
  have h0 := hasDerivAt_const (0 : ℝ) (0 : ℝ)
  convert (((h0.sub_const 1).neg.div ((h0.add hy).add_const 1) (by norm_num)).sub_const
    (ε * (0 - 1) / (0 + 1))) using 1
  norm_num

/-! ### Hessians, nondegeneracy and Morse indices at the fixed points -/

/-- The Hessian of the height at the lower pole of the exceptional sphere, in the lower pole
chart, is `-2 ‖v₁‖² + 4 ε ‖v₂‖²`. -/
theorem hessianQuadraticForm_blownUpPlaneHeight_comp_lowerPoleChart (v : ℂ × ℂ) :
    hessianQuadraticForm (blownUpPlaneHeight ε ∘ blownUpPlaneLowerPoleChart) 0 v =
      -2 * ‖v.1‖ ^ 2 + 4 * ε * ‖v.2‖ ^ 2 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneLowerPoleChart = _ from
    funext blownUpPlaneHeight_lowerPoleChart, hessianQuadraticForm_comp_norm_sq_prod_zero
    contDiffAt_lowerProfile hasDerivAt_lowerProfile_fst hasDerivAt_lowerProfile_snd]
  ring

/-- For `ε ≠ 0`, the lower pole of the exceptional sphere is a nondegenerate critical point of
the height. -/
theorem isNondegenerateCriticalPoint_blownUpPlaneHeight_comp_lowerPoleChart (hε : ε ≠ 0) :
    IsNondegenerateCriticalPoint (blownUpPlaneHeight ε ∘ blownUpPlaneLowerPoleChart) 0 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneLowerPoleChart = _ from
    funext blownUpPlaneHeight_lowerPoleChart]
  exact isNondegenerateCriticalPoint_comp_norm_sq_prod_zero contDiffAt_lowerProfile
    hasDerivAt_lowerProfile_fst hasDerivAt_lowerProfile_snd (by norm_num) (by simpa using hε)

/-- For `0 ≤ ε`, the height has Morse index `2` at the lower pole of the exceptional sphere: it
decreases normal to the sphere. -/
theorem morseIndex_blownUpPlaneHeight_comp_lowerPoleChart (hε : 0 ≤ ε) :
    morseIndex (blownUpPlaneHeight ε ∘ blownUpPlaneLowerPoleChart) 0 = 2 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneLowerPoleChart = _ from
    funext blownUpPlaneHeight_lowerPoleChart, morseIndex_comp_norm_sq_prod_zero
    contDiffAt_lowerProfile hasDerivAt_lowerProfile_fst hasDerivAt_lowerProfile_snd]
  simp [hε, Complex.finrank_real_complex]

/-- The Hessian of the height at the upper pole of the exceptional sphere, in the upper pole
chart, is `-4 ε ‖v₁‖² + 2 ‖v₂‖²`. -/
theorem hessianQuadraticForm_blownUpPlaneHeight_comp_upperPoleChart (v : ℂ × ℂ) :
    hessianQuadraticForm (blownUpPlaneHeight ε ∘ blownUpPlaneUpperPoleChart) 0 v =
      -4 * ε * ‖v.1‖ ^ 2 + 2 * ‖v.2‖ ^ 2 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneUpperPoleChart = _ from
    funext blownUpPlaneHeight_upperPoleChart, hessianQuadraticForm_comp_norm_sq_prod_zero
    contDiffAt_upperProfile hasDerivAt_upperProfile_fst hasDerivAt_upperProfile_snd]
  ring

/-- For `ε ≠ 0`, the upper pole of the exceptional sphere is a nondegenerate critical point of
the height. -/
theorem isNondegenerateCriticalPoint_blownUpPlaneHeight_comp_upperPoleChart (hε : ε ≠ 0) :
    IsNondegenerateCriticalPoint (blownUpPlaneHeight ε ∘ blownUpPlaneUpperPoleChart) 0 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneUpperPoleChart = _ from
    funext blownUpPlaneHeight_upperPoleChart]
  exact isNondegenerateCriticalPoint_comp_norm_sq_prod_zero contDiffAt_upperProfile
    hasDerivAt_upperProfile_fst hasDerivAt_upperProfile_snd (by simpa using hε) one_ne_zero

/-- For `0 < ε`, the height has Morse index `2` at the upper pole of the exceptional sphere: it
decreases along the sphere. -/
theorem morseIndex_blownUpPlaneHeight_comp_upperPoleChart (hε : 0 < ε) :
    morseIndex (blownUpPlaneHeight ε ∘ blownUpPlaneUpperPoleChart) 0 = 2 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneUpperPoleChart = _ from
    funext blownUpPlaneHeight_upperPoleChart, morseIndex_comp_norm_sq_prod_zero
    contDiffAt_upperProfile hasDerivAt_upperProfile_fst hasDerivAt_upperProfile_snd]
  simp [hε, Complex.finrank_real_complex]

/-- The Hessian of the height at `([1 : 0 : 0], [1 : 0])` is `2 ‖v₁‖² + 4 (1 + ε) ‖v₂‖²`. -/
theorem hessianQuadraticForm_blownUpPlaneHeight_comp_minChart (v : ℂ × ℂ) :
    hessianQuadraticForm (blownUpPlaneHeight ε ∘ blownUpPlaneMinChart) 0 v =
      2 * ‖v.1‖ ^ 2 + 4 * (1 + ε) * ‖v.2‖ ^ 2 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneMinChart = _ from
    funext blownUpPlaneHeight_minChart, hessianQuadraticForm_comp_norm_sq_prod_zero
    contDiffAt_minProfile hasDerivAt_minProfile_fst hasDerivAt_minProfile_snd]
  ring

/-- For `ε ≠ -1`, the point `([1 : 0 : 0], [1 : 0])` is a nondegenerate critical point of the
height. -/
theorem isNondegenerateCriticalPoint_blownUpPlaneHeight_comp_minChart (hε : ε ≠ -1) :
    IsNondegenerateCriticalPoint (blownUpPlaneHeight ε ∘ blownUpPlaneMinChart) 0 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneMinChart = _ from
    funext blownUpPlaneHeight_minChart]
  refine isNondegenerateCriticalPoint_comp_norm_sq_prod_zero contDiffAt_minProfile
    hasDerivAt_minProfile_fst hasDerivAt_minProfile_snd one_ne_zero fun h ↦ hε ?_
  linarith

/-- For `-1 ≤ ε`, the height has Morse index `0` at `([1 : 0 : 0], [1 : 0])`. -/
theorem morseIndex_blownUpPlaneHeight_comp_minChart (hε : -1 ≤ ε) :
    morseIndex (blownUpPlaneHeight ε ∘ blownUpPlaneMinChart) 0 = 0 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneMinChart = _ from
    funext blownUpPlaneHeight_minChart, morseIndex_comp_norm_sq_prod_zero
    contDiffAt_minProfile hasDerivAt_minProfile_fst hasDerivAt_minProfile_snd]
  have : ¬ 2 + 2 * ε < 0 := by linarith
  simp [this]

/-- The Hessian of the height at `([0 : 0 : 1], [0 : 1])` is `-4 (1 + ε) ‖v₁‖² - 2 ‖v₂‖²`. -/
theorem hessianQuadraticForm_blownUpPlaneHeight_comp_maxChart (v : ℂ × ℂ) :
    hessianQuadraticForm (blownUpPlaneHeight ε ∘ blownUpPlaneMaxChart) 0 v =
      -4 * (1 + ε) * ‖v.1‖ ^ 2 - 2 * ‖v.2‖ ^ 2 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneMaxChart = _ from
    funext blownUpPlaneHeight_maxChart, hessianQuadraticForm_comp_norm_sq_prod_zero
    contDiffAt_maxProfile hasDerivAt_maxProfile_fst hasDerivAt_maxProfile_snd]
  ring

/-- For `ε ≠ -1`, the point `([0 : 0 : 1], [0 : 1])` is a nondegenerate critical point of the
height. -/
theorem isNondegenerateCriticalPoint_blownUpPlaneHeight_comp_maxChart (hε : ε ≠ -1) :
    IsNondegenerateCriticalPoint (blownUpPlaneHeight ε ∘ blownUpPlaneMaxChart) 0 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneMaxChart = _ from
    funext blownUpPlaneHeight_maxChart]
  refine isNondegenerateCriticalPoint_comp_norm_sq_prod_zero contDiffAt_maxProfile
    hasDerivAt_maxProfile_fst hasDerivAt_maxProfile_snd (fun h ↦ hε ?_) (by norm_num)
  linarith

/-- For `-1 < ε`, the height has Morse index `4` at `([0 : 0 : 1], [0 : 1])`. -/
theorem morseIndex_blownUpPlaneHeight_comp_maxChart (hε : -1 < ε) :
    morseIndex (blownUpPlaneHeight ε ∘ blownUpPlaneMaxChart) 0 = 4 := by
  rw [show blownUpPlaneHeight ε ∘ blownUpPlaneMaxChart = _ from
    funext blownUpPlaneHeight_maxChart, morseIndex_comp_norm_sq_prod_zero
    contDiffAt_maxProfile hasDerivAt_maxProfile_fst hasDerivAt_maxProfile_snd]
  have : -2 - 2 * ε < 0 := by linarith
  simp [this, Complex.finrank_real_complex]

end TauCeti
