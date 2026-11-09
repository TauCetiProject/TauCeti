/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.IntervalBase
public import TauCeti.Analysis.Calculus.Morse.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The ordered-triangle base of a composition of continuations

Two continuations `f₀ ⇝ f₁ ⇝ f₂` and the direct continuation `f₀ ⇝ f₂` are compared through a
two-parameter family over the ordered triangle `0 ≤ v ≤ u ≤ 1` (`TauCeti.triangleBase`). Its base
field is `(a(u), a(v))`, the field `a(t) = C t (1 - t²)` of the interval base
(`TauCeti.intervalBasePotential`) in each coordinate: the negative gradient of the separated sum
`C h(u) + C h(v)` (`TauCeti.triangleBasePotential`) on the `L²` plane. This file describes its
dynamics on the triangle.

* **Vertices.** The zeros of the field in the triangle are its three vertices `(0, 0)`, `(1, 0)`
  and `(1, 1)`, nondegenerate critical points of Morse index `2`, `1` and `0`.
* **Flow and face invariance.** The flow acts coordinatewise by the explicit flow of the interval
  base (`TauCeti.triangleBaseFlow`). It preserves the triangle, and each of its three faces: the
  edge `v = 0` from `(0, 0)` to `(1, 0)`, the edge `u = 1` from `(1, 0)` to `(1, 1)`, and the
  diagonal `u = v` from `(0, 0)` to `(1, 1)`.
* **The interval of source-to-sink orbits.** A point of the triangle with `0 < v` and `u < 1`
  flows from the source `(0, 0)` to the sink `(1, 1)`. Since both coordinates advance at the
  same rate `C` in the time coordinate `U(t) = log t - (1 / 2) log (1 - t²)` of the interval base,
  the difference `U(u) - U(v)` (`TauCeti.triangleBaseOrbitParameter`) is constant along orbits,
  and it classifies them: two such points lie on one orbit exactly when their parameters agree,
  and the parameters fill `[0, ∞)`. The value `0` is the diagonal, the direct edge from the
  source to the sink. As the parameter tends to `∞`, the orbits converge to the broken pair of
  edges through `(1, 0)`: on a fixed level of `u` the coordinate `v` tends to `0`, and on a fixed
  level of `v` the coordinate `u` tends to `1`. So the source-to-sink orbits form a half-open
  interval `[0, ∞)`, and the broken orbit is their limit at `∞`.

## Main declarations

* `TauCeti.triangleBasePotential`, `TauCeti.gradient_triangleBasePotential`: the potential and
  its gradient.
* `TauCeti.gradient_triangleBasePotential_eq_zero_iff`: the zeros of the field in the triangle.
* `TauCeti.morseIndex_triangleBasePotential_toLp_zero_zero`,
  `TauCeti.morseIndex_triangleBasePotential_toLp_one_zero`,
  `TauCeti.morseIndex_triangleBasePotential_toLp_one_one`: the vertex indices `2`, `1`, `0`.
* `TauCeti.triangleBaseFlow`, `TauCeti.isIntegralCurve_triangleBaseFlow`,
  `TauCeti.triangleBaseFlow_add`: the flow.
* `TauCeti.mapsTo_triangleBaseFlow`, `TauCeti.snd_triangleBaseFlow_eq_zero_iff`,
  `TauCeti.fst_triangleBaseFlow_eq_one_iff`, `TauCeti.fst_triangleBaseFlow_eq_snd_iff`: invariance
  of the triangle and of its faces.
* `TauCeti.tendsto_triangleBaseFlow_atBot_toLp_zero_zero`,
  `TauCeti.tendsto_triangleBaseFlow_atTop_toLp_one_one` and the two limits at `(1, 0)`: the ends
  of the orbits.
* `TauCeti.triangleBaseOrbitParameter`, `TauCeti.triangleBaseOrbitParameter_triangleBaseFlow`,
  `TauCeti.exists_triangleBaseFlow_eq_iff`, `TauCeti.surjOn_triangleBaseOrbitParameter`: the
  parameter of the source-to-sink orbits.
* `TauCeti.tendsto_snd_nhds_zero_of_tendsto_triangleBaseOrbitParameter_atTop`,
  `TauCeti.tendsto_fst_nhds_one_of_tendsto_triangleBaseOrbitParameter_atTop`: convergence to the
  broken orbit.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (composition of continuation maps).
-/

public section

open Filter Set
open scoped Gradient Topology

namespace TauCeti

variable {C : ℝ}

/-! ### The potential and its critical points -/

/-- The potential `C h(u) + C h(v)` of the ordered-triangle base, with `h(t) = (t² - 1)² / 4`: the
separated sum of two copies of the interval base potential on the `L²` plane. Its negative
gradient is the field `(C u (1 - u²), C v (1 - v²))`. -/
noncomputable def triangleBasePotential (C : ℝ) : WithLp 2 (ℝ × ℝ) → ℝ :=
  separatedSum (intervalBasePotential C) (intervalBasePotential C)

theorem triangleBasePotential_apply (C : ℝ) (z : WithLp 2 (ℝ × ℝ)) :
    triangleBasePotential C z = intervalBasePotential C z.fst + intervalBasePotential C z.snd := by
  rw [triangleBasePotential, separatedSum_apply]

/-- The potential of the triangle base is smooth. -/
theorem contDiff_triangleBasePotential (C : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (triangleBasePotential C) :=
  (contDiff_intervalBasePotential C).separatedSum (contDiff_intervalBasePotential C)

/-- The gradient of the potential is `(C u (u² - 1), C v (v² - 1))`. -/
@[simp]
theorem gradient_triangleBasePotential (C : ℝ) (z : WithLp 2 (ℝ × ℝ)) :
    ∇ (triangleBasePotential C) z =
      WithLp.toLp 2 (C * z.fst * (z.fst ^ 2 - 1), C * z.snd * (z.snd ^ 2 - 1)) := by
  have hd : Differentiable ℝ (intervalBasePotential C) :=
    (contDiff_intervalBasePotential C (n := 1)).differentiable one_ne_zero
  rw [triangleBasePotential, gradient_separatedSum (hd _) (hd _), gradient_intervalBasePotential,
    gradient_intervalBasePotential]

/-- The ordered triangle `0 ≤ v ≤ u ≤ 1` in the coordinates `z = (u, v)`. -/
def triangleBase : Set (WithLp 2 (ℝ × ℝ)) :=
  {z | 0 ≤ z.snd ∧ z.snd ≤ z.fst ∧ z.fst ≤ 1}

@[simp]
theorem mem_triangleBase {z : WithLp 2 (ℝ × ℝ)} :
    z ∈ triangleBase ↔ 0 ≤ z.snd ∧ z.snd ≤ z.fst ∧ z.fst ≤ 1 :=
  Iff.rfl

private theorem fst_mem_Icc_of_mem_triangleBase {z : WithLp 2 (ℝ × ℝ)} (hz : z ∈ triangleBase) :
    z.fst ∈ Icc 0 1 :=
  ⟨hz.1.trans hz.2.1, hz.2.2⟩

private theorem snd_mem_Icc_of_mem_triangleBase {z : WithLp 2 (ℝ × ℝ)} (hz : z ∈ triangleBase) :
    z.snd ∈ Icc 0 1 :=
  ⟨hz.1, hz.2.1.trans hz.2.2⟩

private theorem mul_mul_sq_sub_one_eq_zero_iff (hC : C ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    C * t * (t ^ 2 - 1) = 0 ↔ t = 0 ∨ t = 1 := by
  rw [mul_eq_zero, mul_eq_zero, sub_eq_zero, pow_eq_one_iff_of_nonneg ht two_ne_zero]
  simp [hC]

/-- **The zeros of the field in the triangle are its vertices** `(0, 0)`, `(1, 0)` and `(1, 1)`. -/
theorem gradient_triangleBasePotential_eq_zero_iff (hC : C ≠ 0) {z : WithLp 2 (ℝ × ℝ)}
    (hz : z ∈ triangleBase) :
    ∇ (triangleBasePotential C) z = 0 ↔
      z = WithLp.toLp 2 (0, 0) ∨ z = WithLp.toLp 2 (1, 0) ∨ z = WithLp.toLp 2 (1, 1) := by
  rw [gradient_triangleBasePotential, WithLp.toLp_eq_zero, Prod.mk_eq_zero,
    mul_mul_sq_sub_one_eq_zero_iff hC (fst_mem_Icc_of_mem_triangleBase hz).1,
    mul_mul_sq_sub_one_eq_zero_iff hC hz.1]
  simp only [WithLp.ext_iff, Prod.ext_iff, WithLp.ofLp_fst, WithLp.ofLp_snd]
  have := hz.2.1
  constructor
  · rintro ⟨hu | hu, hv | hv⟩ <;> simp_all
    linarith
  · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩) <;> simp [hu, hv]

/-- For `C ≠ 0` the source `(0, 0)` is a nondegenerate critical point. -/
theorem isNondegenerateCriticalPoint_triangleBasePotential_toLp_zero_zero (hC : C ≠ 0) :
    IsNondegenerateCriticalPoint (triangleBasePotential C) (WithLp.toLp 2 (0, 0)) :=
  (isNondegenerateCriticalPoint_intervalBasePotential_zero hC).separatedSum
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC)

/-- For `C ≠ 0` the corner `(1, 0)` is a nondegenerate critical point. -/
theorem isNondegenerateCriticalPoint_triangleBasePotential_toLp_one_zero (hC : C ≠ 0) :
    IsNondegenerateCriticalPoint (triangleBasePotential C) (WithLp.toLp 2 (1, 0)) :=
  (isNondegenerateCriticalPoint_intervalBasePotential_one hC).separatedSum
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC)

/-- For `C ≠ 0` the sink `(1, 1)` is a nondegenerate critical point. -/
theorem isNondegenerateCriticalPoint_triangleBasePotential_toLp_one_one (hC : C ≠ 0) :
    IsNondegenerateCriticalPoint (triangleBasePotential C) (WithLp.toLp 2 (1, 1)) :=
  (isNondegenerateCriticalPoint_intervalBasePotential_one hC).separatedSum
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC)

private theorem morseIndex_triangleBasePotential (C : ℝ) (z : WithLp 2 (ℝ × ℝ)) :
    morseIndex (triangleBasePotential C) z =
      morseIndex (intervalBasePotential C) z.fst + morseIndex (intervalBasePotential C) z.snd :=
  morseIndex_separatedSum (contDiff_intervalBasePotential C).contDiffAt
    (contDiff_intervalBasePotential C).contDiffAt

/-- For `C > 0` the source `(0, 0)` is a local maximum: its Morse index is `2`. -/
@[simp]
theorem morseIndex_triangleBasePotential_toLp_zero_zero (hC : 0 < C) :
    morseIndex (triangleBasePotential C) (WithLp.toLp 2 (0, 0)) = 2 := by
  simp [morseIndex_triangleBasePotential, hC]

/-- For `C > 0` the corner `(1, 0)` is a saddle: its Morse index is `1`. -/
@[simp]
theorem morseIndex_triangleBasePotential_toLp_one_zero (hC : 0 < C) :
    morseIndex (triangleBasePotential C) (WithLp.toLp 2 (1, 0)) = 1 := by
  simp [morseIndex_triangleBasePotential, hC]

/-- For `C > 0` the sink `(1, 1)` is a local minimum: its Morse index is `0`. -/
@[simp]
theorem morseIndex_triangleBasePotential_toLp_one_one (hC : 0 < C) :
    morseIndex (triangleBasePotential C) (WithLp.toLp 2 (1, 1)) = 0 := by
  simp [morseIndex_triangleBasePotential, hC]

/-! ### The flow -/

/-- The flow of the triangle base field `(C u (1 - u²), C v (1 - v²))`: the flow
`TauCeti.intervalBaseFlow` of the interval base in each coordinate. It is the negative gradient
flow of `TauCeti.triangleBasePotential` on the square `[-1, 1]²`. -/
noncomputable def triangleBaseFlow (C s : ℝ) (z : WithLp 2 (ℝ × ℝ)) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 (intervalBaseFlow C s z.fst, intervalBaseFlow C s z.snd)

@[simp]
theorem fst_triangleBaseFlow (C s : ℝ) (z : WithLp 2 (ℝ × ℝ)) :
    (triangleBaseFlow C s z).fst = intervalBaseFlow C s z.fst :=
  (rfl)

@[simp]
theorem snd_triangleBaseFlow (C s : ℝ) (z : WithLp 2 (ℝ × ℝ)) :
    (triangleBaseFlow C s z).snd = intervalBaseFlow C s z.snd :=
  (rfl)

/-- At time `0` the flow is the identity. -/
@[simp]
theorem triangleBaseFlow_zero (C : ℝ) (z : WithLp 2 (ℝ × ℝ)) : triangleBaseFlow C 0 z = z := by
  simp [triangleBaseFlow, WithLp.ext_iff, Prod.ext_iff]

/-- **The flow property** on the square `[-1, 1]²`. -/
theorem triangleBaseFlow_add (C s r : ℝ) {z : WithLp 2 (ℝ × ℝ)} (hu : z.fst ∈ Icc (-1) 1)
    (hv : z.snd ∈ Icc (-1) 1) :
    triangleBaseFlow C (s + r) z = triangleBaseFlow C s (triangleBaseFlow C r z) := by
  simp only [triangleBaseFlow, WithLp.toLp_fst, WithLp.toLp_snd, intervalBaseFlow_add C s r hu,
    intervalBaseFlow_add C s r hv]

/-- The flow lines through the square `[-1, 1]²` are negative gradient trajectories of the
potential. -/
theorem isIntegralCurve_triangleBaseFlow (C : ℝ) {z : WithLp 2 (ℝ × ℝ)} (hu : z.fst ∈ Icc (-1) 1)
    (hv : z.snd ∈ Icc (-1) 1) :
    IsIntegralCurve (fun s ↦ triangleBaseFlow C s z)
      (fun _ w ↦ -∇ (triangleBasePotential C) w) := by
  intro s
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.hasFDerivAt.comp_hasDerivAt s
    (HasDerivAt.prodMk (hasDerivAt_intervalBaseFlow C s hu) (hasDerivAt_intervalBaseFlow C s hv))
  refine h.congr_deriv ?_
  simp only [ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
    gradient_triangleBasePotential, fst_triangleBaseFlow, snd_triangleBaseFlow, ← WithLp.toLp_neg,
    Prod.neg_mk]
  congr 2 <;> ring

/-- **The flow preserves the triangle.** -/
theorem mapsTo_triangleBaseFlow (C s : ℝ) :
    MapsTo (triangleBaseFlow C s) triangleBase triangleBase := fun _ hz ↦
  ⟨(intervalBaseFlow_mem_Icc_zero_one C s (snd_mem_Icc_of_mem_triangleBase hz)).1,
    (strictMonoOn_intervalBaseFlow C s).monotoneOn
      (Icc_subset_Icc_left (by norm_num) (snd_mem_Icc_of_mem_triangleBase hz))
      (Icc_subset_Icc_left (by norm_num) (fst_mem_Icc_of_mem_triangleBase hz)) hz.2.1,
    (intervalBaseFlow_mem_Icc_zero_one C s (fst_mem_Icc_of_mem_triangleBase hz)).2⟩

/-- **The flow preserves the edge `v = 0`** and its complement in the triangle. -/
theorem snd_triangleBaseFlow_eq_zero_iff (C s : ℝ) {z : WithLp 2 (ℝ × ℝ)}
    (hv : z.snd ∈ Icc (-1) 1) : (triangleBaseFlow C s z).snd = 0 ↔ z.snd = 0 := by
  rw [snd_triangleBaseFlow, intervalBaseFlow_eq_zero_iff C s hv]

/-- **The flow preserves the edge `u = 1`** and its complement in the triangle. -/
theorem fst_triangleBaseFlow_eq_one_iff (C s : ℝ) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst ∈ Icc (-1) 1) : (triangleBaseFlow C s z).fst = 1 ↔ z.fst = 1 := by
  rw [fst_triangleBaseFlow, intervalBaseFlow_eq_one_iff C s hu]

/-- **The flow preserves the diagonal `u = v`** and its complement in the triangle. -/
theorem fst_triangleBaseFlow_eq_snd_iff (C s : ℝ) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst ∈ Icc (-1) 1) (hv : z.snd ∈ Icc (-1) 1) :
    (triangleBaseFlow C s z).fst = (triangleBaseFlow C s z).snd ↔ z.fst = z.snd := by
  rw [fst_triangleBaseFlow, snd_triangleBaseFlow]
  exact (strictMonoOn_intervalBaseFlow C s).injOn.eq_iff hu hv

/-! ### The ends of the orbits -/

private theorem tendsto_triangleBaseFlow {l : Filter ℝ} {z : WithLp 2 (ℝ × ℝ)} {a b : ℝ}
    (hu : Tendsto (fun s ↦ intervalBaseFlow C s z.fst) l (𝓝 a))
    (hv : Tendsto (fun s ↦ intervalBaseFlow C s z.snd) l (𝓝 b)) :
    Tendsto (fun s ↦ triangleBaseFlow C s z) l (𝓝 (WithLp.toLp 2 (a, b))) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.continuous.tendsto (a, b)).comp
    (hu.prodMk_nhds hv)

/-- For `C > 0`, the flow line through a point of the open square `(-1, 1)²` starts at the
source `(0, 0)`. -/
theorem tendsto_triangleBaseFlow_atBot_toLp_zero_zero (hC : 0 < C) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst ∈ Ioo (-1) 1) (hv : z.snd ∈ Ioo (-1) 1) :
    Tendsto (fun s ↦ triangleBaseFlow C s z) atBot (𝓝 (WithLp.toLp 2 (0, 0))) :=
  tendsto_triangleBaseFlow (tendsto_intervalBaseFlow_atBot hC hu)
    (tendsto_intervalBaseFlow_atBot hC hv)

/-- For `C > 0`, the flow line through a point of `(0, 1]²` ends at the sink `(1, 1)`. -/
theorem tendsto_triangleBaseFlow_atTop_toLp_one_one (hC : 0 < C) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst ∈ Ioc 0 1) (hv : z.snd ∈ Ioc 0 1) :
    Tendsto (fun s ↦ triangleBaseFlow C s z) atTop (𝓝 (WithLp.toLp 2 (1, 1))) :=
  tendsto_triangleBaseFlow (tendsto_intervalBaseFlow_atTop hC hu)
    (tendsto_intervalBaseFlow_atTop hC hv)

/-- For `C > 0`, the flow line through a point of the edge `v = 0` with `0 < u` ends at the
corner `(1, 0)`. -/
theorem tendsto_triangleBaseFlow_atTop_toLp_one_zero (hC : 0 < C) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst ∈ Ioc 0 1) (hv : z.snd = 0) :
    Tendsto (fun s ↦ triangleBaseFlow C s z) atTop (𝓝 (WithLp.toLp 2 (1, 0))) :=
  tendsto_triangleBaseFlow (tendsto_intervalBaseFlow_atTop hC hu)
    (by simp [hv])

/-- For `C > 0`, the flow line through a point of the edge `u = 1` with `-1 < v < 1` starts at the
corner `(1, 0)`. -/
theorem tendsto_triangleBaseFlow_atBot_toLp_one_zero (hC : 0 < C) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst = 1) (hv : z.snd ∈ Ioo (-1) 1) :
    Tendsto (fun s ↦ triangleBaseFlow C s z) atBot (𝓝 (WithLp.toLp 2 (1, 0))) :=
  tendsto_triangleBaseFlow (by simp [hu]) (tendsto_intervalBaseFlow_atBot hC hv)

/-! ### The interval of source-to-sink orbits -/

/-- The parameter `U(u) - U(v)` of the orbits of the triangle base through the open square
`(0, 1)²`, where `U(t) = log t - (1 / 2) log (1 - t²)` is the time coordinate of the interval base
(`TauCeti.intervalBaseTimeCoordinate`). It is constant along the flow
(`TauCeti.triangleBaseOrbitParameter_triangleBaseFlow`) and classifies the orbits
(`TauCeti.exists_triangleBaseFlow_eq_iff`). On the triangle it is nonnegative, and it vanishes
exactly on the diagonal. -/
noncomputable def triangleBaseOrbitParameter (z : WithLp 2 (ℝ × ℝ)) : ℝ :=
  intervalBaseTimeCoordinate z.fst - intervalBaseTimeCoordinate z.snd

theorem triangleBaseOrbitParameter_apply (z : WithLp 2 (ℝ × ℝ)) :
    triangleBaseOrbitParameter z =
      intervalBaseTimeCoordinate z.fst - intervalBaseTimeCoordinate z.snd :=
  (rfl)

/-- **The orbit parameter is a first integral** of the flow on the open square `(0, 1)²`. -/
@[simp]
theorem triangleBaseOrbitParameter_triangleBaseFlow (C s : ℝ) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst ∈ Ioo 0 1) (hv : z.snd ∈ Ioo 0 1) :
    triangleBaseOrbitParameter (triangleBaseFlow C s z) = triangleBaseOrbitParameter z := by
  rw [triangleBaseOrbitParameter, fst_triangleBaseFlow, snd_triangleBaseFlow,
    intervalBaseTimeCoordinate_intervalBaseFlow C s hu,
    intervalBaseTimeCoordinate_intervalBaseFlow C s hv, triangleBaseOrbitParameter]
  ring

/-- On the open square `(0, 1)²` the orbit parameter is nonnegative exactly on the triangle
`v ≤ u`. -/
theorem triangleBaseOrbitParameter_nonneg_iff {z : WithLp 2 (ℝ × ℝ)} (hu : z.fst ∈ Ioo 0 1)
    (hv : z.snd ∈ Ioo 0 1) : 0 ≤ triangleBaseOrbitParameter z ↔ z.snd ≤ z.fst := by
  rw [triangleBaseOrbitParameter, sub_nonneg]
  exact strictMonoOn_intervalBaseTimeCoordinate.le_iff_le hv hu

/-- On the open square `(0, 1)²` the orbit parameter vanishes exactly on the diagonal. -/
theorem triangleBaseOrbitParameter_eq_zero_iff {z : WithLp 2 (ℝ × ℝ)} (hu : z.fst ∈ Ioo 0 1)
    (hv : z.snd ∈ Ioo 0 1) : triangleBaseOrbitParameter z = 0 ↔ z.fst = z.snd := by
  rw [triangleBaseOrbitParameter, sub_eq_zero]
  exact strictMonoOn_intervalBaseTimeCoordinate.injOn.eq_iff hu hv

/-- **The orbit parameter classifies the orbits.** For `C ≠ 0`, two points of the open square
`(0, 1)²` lie on the same flow line exactly when their orbit parameters agree. -/
theorem exists_triangleBaseFlow_eq_iff (hC : C ≠ 0) {z w : WithLp 2 (ℝ × ℝ)}
    (hzu : z.fst ∈ Ioo 0 1) (hzv : z.snd ∈ Ioo 0 1) (hwu : w.fst ∈ Ioo 0 1)
    (hwv : w.snd ∈ Ioo 0 1) :
    (∃ s, triangleBaseFlow C s z = w) ↔
      triangleBaseOrbitParameter z = triangleBaseOrbitParameter w := by
  refine ⟨fun ⟨s, hs⟩ ↦ hs ▸ (triangleBaseOrbitParameter_triangleBaseFlow C s hzu hzv).symm,
    fun h ↦ ?_⟩
  -- Flow for the time that moves the time coordinate of `u` to that of `w.fst`; the equal
  -- parameters then force the time coordinate of `v` to move to that of `w.snd`.
  set s := (intervalBaseTimeCoordinate w.fst - intervalBaseTimeCoordinate z.fst) / C
  have hs : C * s = intervalBaseTimeCoordinate w.fst - intervalBaseTimeCoordinate z.fst :=
    mul_div_cancel₀ _ hC
  rw [triangleBaseOrbitParameter, triangleBaseOrbitParameter] at h
  have h₁ : intervalBaseFlow C s z.fst = w.fst := by
    refine strictMonoOn_intervalBaseTimeCoordinate.injOn
      (intervalBaseFlow_mem_Ioo_zero_one C s hzu) hwu ?_
    rw [intervalBaseTimeCoordinate_intervalBaseFlow C s hzu, hs]
    ring
  have h₂ : intervalBaseFlow C s z.snd = w.snd := by
    refine strictMonoOn_intervalBaseTimeCoordinate.injOn
      (intervalBaseFlow_mem_Ioo_zero_one C s hzv) hwv ?_
    rw [intervalBaseTimeCoordinate_intervalBaseFlow C s hzv, hs]
    linarith
  refine ⟨s, ?_⟩
  simp only [WithLp.ext_iff, Prod.ext_iff, WithLp.ofLp_fst, WithLp.ofLp_snd, fst_triangleBaseFlow,
    snd_triangleBaseFlow]
  exact ⟨h₁, h₂⟩

/-- **The source-to-sink orbits of the triangle form the interval `[0, ∞)`.** Every nonnegative
value is the orbit parameter of a point of the triangle with `0 < v ≤ u < 1`. -/
theorem surjOn_triangleBaseOrbitParameter :
    SurjOn triangleBaseOrbitParameter
      {z | z.fst ∈ Ioo 0 1 ∧ z.snd ∈ Ioo 0 1 ∧ z.snd ≤ z.fst} (Ici 0) := by
  intro c hc
  obtain ⟨v, hv, hUv⟩ := bijOn_intervalBaseTimeCoordinate.surjOn (mem_univ (-c))
  obtain ⟨u, hu, hUu⟩ := bijOn_intervalBaseTimeCoordinate.surjOn (mem_univ 0)
  have hz : (WithLp.toLp 2 (u, v)).fst ∈ Ioo 0 1 ∧ (WithLp.toLp 2 (u, v)).snd ∈ Ioo 0 1 :=
    ⟨hu, hv⟩
  have hP : triangleBaseOrbitParameter (WithLp.toLp 2 (u, v)) = c := by
    rw [triangleBaseOrbitParameter, WithLp.toLp_fst, WithLp.toLp_snd, hUu, hUv, zero_sub, neg_neg]
  exact ⟨WithLp.toLp 2 (u, v), ⟨hz.1, hz.2,
    (triangleBaseOrbitParameter_nonneg_iff hz.1 hz.2).1 (hP ▸ hc)⟩, hP⟩

/-- **Orbits with parameter tending to `∞` approach the edge `v = 0`.** If points with second
coordinates in `(0, 1)` have first coordinates tending to `u₀ ∈ (0, 1)` and orbit parameters
tending to `∞`, their second coordinates tend to `0`. -/
theorem tendsto_snd_nhds_zero_of_tendsto_triangleBaseOrbitParameter_atTop {α : Type*}
    {l : Filter α} {z : α → WithLp 2 (ℝ × ℝ)} {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo 0 1)
    (hz : ∀ᶠ i in l, (z i).snd ∈ Ioo 0 1)
    (hfst : Tendsto (fun i ↦ (z i).fst) l (𝓝 u₀))
    (h : Tendsto (fun i ↦ triangleBaseOrbitParameter (z i)) l atTop) :
    Tendsto (fun i ↦ (z i).snd) l (𝓝 0) := by
  refine tendsto_nhds_zero_of_tendsto_intervalBaseTimeCoordinate_atBot hz ?_
  have hU := ((hasDerivAt_intervalBaseTimeCoordinate hu₀).continuousAt.tendsto.comp hfst).add_atBot
    (tendsto_neg_atTop_atBot.comp h)
  refine hU.congr fun i ↦ ?_
  simp only [Function.comp_apply, triangleBaseOrbitParameter]
  ring

/-- **Orbits with parameter tending to `∞` approach the edge `u = 1`.** If points with first
coordinates in `(0, 1)` have second coordinates tending to `v₀ ∈ (0, 1)` and orbit parameters
tending to `∞`, their first coordinates tend to `1`. -/
theorem tendsto_fst_nhds_one_of_tendsto_triangleBaseOrbitParameter_atTop {α : Type*}
    {l : Filter α} {z : α → WithLp 2 (ℝ × ℝ)} {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo 0 1)
    (hz : ∀ᶠ i in l, (z i).fst ∈ Ioo 0 1)
    (hsnd : Tendsto (fun i ↦ (z i).snd) l (𝓝 v₀))
    (h : Tendsto (fun i ↦ triangleBaseOrbitParameter (z i)) l atTop) :
    Tendsto (fun i ↦ (z i).fst) l (𝓝 1) := by
  refine tendsto_nhds_one_of_tendsto_intervalBaseTimeCoordinate_atTop hz ?_
  have hU := h.atTop_add ((hasDerivAt_intervalBaseTimeCoordinate hv₀).continuousAt.tendsto.comp
    hsnd)
  refine hU.congr fun i ↦ ?_
  simp only [Function.comp_apply, triangleBaseOrbitParameter]
  ring

end TauCeti

end
