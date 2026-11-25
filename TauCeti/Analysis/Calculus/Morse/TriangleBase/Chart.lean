/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.TriangleBase
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The gluing chart of the interval of source-to-sink orbits of the ordered-triangle base

The ordered-triangle base `0 ≤ v ≤ u ≤ 1` (`TauCeti.triangleBase`) carries the field
`(C u (1 - u²), C v (1 - v²))`. Its orbits from the source `(0, 0)` to the sink `(1, 1)` are
classified by the orbit parameter `T = U(u) - U(v) ∈ [0, ∞)`
(`TauCeti.triangleBaseOrbitParameter`), where `U(t) = log t - (1 / 2) log (1 - t²)`. The value
`T = 0` is the diagonal, and as `T → ∞` the orbits converge to the broken orbit, the two edges
`v = 0` and `u = 1` through the corner `(1, 0)`. This file constructs the chart of the
compactified interval `[0, ∞]` at the broken end, together with its evaluations on fixed slices.

The chart is the **gluing parameter** `σ = e^{-T}` (`TauCeti.triangleBaseGluingParameter`). Since
`e^{U(t)} = t / √(1 - t²)` (`TauCeti.exp_intervalBaseTimeCoordinate`), it is

`σ(u, v) = v √(1 - u²) / (u √(1 - v²))`,

which is continuous on the whole triangle away from the source and the sink
(`TauCeti.continuousOn_triangleBaseGluingParameter`). It is constant along the flow, takes values
in `[0, 1]` on the triangle and vanishes there exactly on the broken orbit. Away from the source
and the sink it equals `1` exactly on the diagonal, and its level sets with `0 < σ` are single
orbits. So `σ` identifies the compactified orbit interval
`[0, ∞]` with `[0, 1]`, the broken orbit being `σ = 0`.

The orbits are evaluated on two slices, `u = c` and `v = c` for `0 < c < 1`. The orbit with gluing
parameter `σ` meets them at the points

* `(c, c σ / √(1 - c² + c² σ²))` (`TauCeti.triangleBaseFstSlice`), and
* `(c / √(c² + (1 - c²) σ²), c)` (`TauCeti.triangleBaseSndSlice`).

Both are smooth functions of `σ` on all of `ℝ` (`TauCeti.contDiff_triangleBaseFstSlice`,
`TauCeti.contDiff_triangleBaseSndSlice`), with the diagonal point `(c, c)` at `σ = 1` and the points
`(c, 0)` and `(1, c)` of the broken orbit at `σ = 0`. On `[0, 1]` each is a bijection onto the slice
of the triangle (`TauCeti.bijOn_triangleBaseFstSlice`, `TauCeti.bijOn_triangleBaseSndSlice`),
inverse to `σ`. The two ends of the broken orbit are reached at different orders, because the
interval base leaves its source `0` at rate `C` and enters its sink `1` at rate `2 C`: on the slice
`u = c` the transverse coordinate `v` vanishes to first order in `σ`, with derivative
`c / √(1 - c²) ≠ 0` (`TauCeti.hasDerivAt_snd_triangleBaseFstSlice_zero`), while on the slice `v = c`
the point is even in `σ` and `1 - u²` vanishes to second order
(`TauCeti.one_sub_sq_fst_triangleBaseSndSlice`). In both cases the evaluation is smooth in `σ`
itself. In the parameter `τ = e^{-2T} = σ²` the first evaluation would be
`c √τ / √(1 - c² + c² τ)`, which is not differentiable at the broken end `τ = 0`.
The point of the slice `u = c` and the point of the slice `v = c'` with the same gluing parameter
lie on the same orbit
(`TauCeti.exists_triangleBaseFlow_triangleBaseFstSlice_eq_triangleBaseSndSlice`), so the two
slices give the same chart of the orbit interval.

## Main definitions

* `TauCeti.triangleBaseGluingParameter`: the gluing parameter `σ = e^{-T}` of the orbits.
* `TauCeti.triangleBaseFstSlice`, `TauCeti.triangleBaseSndSlice`: the points of the orbit with
  gluing parameter `σ` on the slices `u = c` and `v = c`.

## Main results

* `TauCeti.triangleBaseGluingParameter_eq_exp`: `σ = e^{-T}` on the open square `(0, 1)²`.
* `TauCeti.triangleBaseGluingParameter_triangleBaseFlow`: `σ` is constant along the flow.
* `TauCeti.exists_triangleBaseFlow_eq_iff_triangleBaseGluingParameter_eq`: `σ` classifies the
  orbits through the open square.
* `TauCeti.triangleBaseGluingParameter_mem_Icc`, `TauCeti.triangleBaseGluingParameter_eq_zero_iff`,
  `TauCeti.triangleBaseGluingParameter_eq_one_iff`, `TauCeti.triangleBaseGluingParameter_pos_iff`:
  on the triangle `σ ∈ [0, 1]`, it vanishes exactly on the broken orbit and is positive exactly
  on the open square, and away from the source and the sink it equals `1` exactly on the
  diagonal.
* `TauCeti.bijOn_triangleBaseFstSlice`, `TauCeti.bijOn_triangleBaseSndSlice`: the slice evaluations
  are bijections from `[0, 1]` onto the slices of the triangle.
* `TauCeti.hasDerivAt_snd_triangleBaseFstSlice_zero`,
  `TauCeti.one_sub_sq_fst_triangleBaseSndSlice`: the orders of vanishing at the broken end.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (composition of continuation maps).
* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and
  associative gluing*, arXiv:1205.0713, §2 (gluing parameters `e^{-T}` at broken trajectories).
-/

public section

open Set

namespace TauCeti

variable {C : ℝ}

/-! ### The gluing parameter -/

/-- The **gluing parameter** `v √(1 - u²) / (u √(1 - v²))` of the orbits of the ordered-triangle
base through `z = (u, v)`. On the open square `(0, 1)²` it is `e^{-T}` for the orbit parameter
`T = U(u) - U(v)` (`TauCeti.triangleBaseGluingParameter_eq_exp`), so it is constant along the flow
and classifies the orbits. Unlike `T`, it is continuous on the triangle away from the source
`(0, 0)` and the sink `(1, 1)`; on the triangle it vanishes exactly on the broken orbit `v = 0` or
`u = 1`. Where `u = 0` or `1 ≤ v²` its denominator vanishes, so it is `0` there, in particular at
the source and the sink. -/
noncomputable def triangleBaseGluingParameter (z : WithLp 2 (ℝ × ℝ)) : ℝ :=
  z.snd * √(1 - z.fst ^ 2) / (z.fst * √(1 - z.snd ^ 2))

theorem triangleBaseGluingParameter_apply (z : WithLp 2 (ℝ × ℝ)) :
    triangleBaseGluingParameter z = z.snd * √(1 - z.fst ^ 2) / (z.fst * √(1 - z.snd ^ 2)) :=
  (rfl)

/-- **The gluing parameter is `e^{-T}`** on the open square `(0, 1)²`, for the orbit parameter
`T = U(u) - U(v)`. -/
theorem triangleBaseGluingParameter_eq_exp {z : WithLp 2 (ℝ × ℝ)} (hu : z.fst ∈ Ioo 0 1)
    (hv : z.snd ∈ Ioo 0 1) :
    triangleBaseGluingParameter z = Real.exp (-triangleBaseOrbitParameter z) := by
  have h1u : 0 < √(1 - z.fst ^ 2) :=
    Real.sqrt_pos.2 (sub_pos.2 (pow_lt_one₀ hu.1.le hu.2 two_ne_zero))
  have h1v : 0 < √(1 - z.snd ^ 2) :=
    Real.sqrt_pos.2 (sub_pos.2 (pow_lt_one₀ hv.1.le hv.2 two_ne_zero))
  rw [triangleBaseOrbitParameter_apply, neg_sub, Real.exp_sub, exp_intervalBaseTimeCoordinate hu,
    exp_intervalBaseTimeCoordinate hv, triangleBaseGluingParameter]
  field_simp [hu.1.ne']

/-- On the open square `(0, 1)²`, the orbit parameter is `-log σ` for the gluing parameter `σ`. -/
theorem triangleBaseOrbitParameter_eq_neg_log_triangleBaseGluingParameter
    {z : WithLp 2 (ℝ × ℝ)} (hu : z.fst ∈ Ioo 0 1) (hv : z.snd ∈ Ioo 0 1) :
    triangleBaseOrbitParameter z = -Real.log (triangleBaseGluingParameter z) := by
  rw [triangleBaseGluingParameter_eq_exp hu hv, Real.log_exp, neg_neg]

/-- The square of the gluing parameter is `v² (1 - u²) / (u² (1 - v²))` where `u² ≤ 1` and
`v² ≤ 1`. -/
theorem sq_triangleBaseGluingParameter {z : WithLp 2 (ℝ × ℝ)} (hu : z.fst ^ 2 ≤ 1)
    (hv : z.snd ^ 2 ≤ 1) :
    triangleBaseGluingParameter z ^ 2 =
      z.snd ^ 2 * (1 - z.fst ^ 2) / (z.fst ^ 2 * (1 - z.snd ^ 2)) := by
  rw [triangleBaseGluingParameter, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith),
    Real.sq_sqrt (by linarith)]

/-- **The gluing parameter is a first integral** of the flow on the closed square `[0, 1]²`, in
particular on the whole triangle. -/
@[simp]
theorem triangleBaseGluingParameter_triangleBaseFlow (C s : ℝ) {z : WithLp 2 (ℝ × ℝ)}
    (hu : z.fst ∈ Icc 0 1) (hv : z.snd ∈ Icc 0 1) :
    triangleBaseGluingParameter (triangleBaseFlow C s z) = triangleBaseGluingParameter z := by
  rcases hv.1.eq_or_lt with hv0 | hv0
  · simp [triangleBaseGluingParameter, ← hv0, intervalBaseFlow_apply_zero]
  rcases hu.2.eq_or_lt with hu1 | hu1
  · simp [triangleBaseGluingParameter, hu1, intervalBaseFlow_apply_one]
  rcases hu.1.eq_or_lt with hu0 | hu0
  · simp [triangleBaseGluingParameter, ← hu0, intervalBaseFlow_apply_zero]
  rcases hv.2.eq_or_lt with hv1 | hv1
  · simp [triangleBaseGluingParameter, hv1, intervalBaseFlow_apply_one]
  have hu' : z.fst ∈ Ioo 0 1 := ⟨hu0, hu1⟩
  have hv' : z.snd ∈ Ioo 0 1 := ⟨hv0, hv1⟩
  have hu'' : (triangleBaseFlow C s z).fst ∈ Ioo 0 1 := by
    rw [fst_triangleBaseFlow]
    exact intervalBaseFlow_mem_Ioo_zero_one C s hu'
  have hv'' : (triangleBaseFlow C s z).snd ∈ Ioo 0 1 := by
    rw [snd_triangleBaseFlow]
    exact intervalBaseFlow_mem_Ioo_zero_one C s hv'
  rw [triangleBaseGluingParameter_eq_exp hu' hv', triangleBaseGluingParameter_eq_exp hu'' hv'',
    triangleBaseOrbitParameter_triangleBaseFlow C s hu' hv']

/-- **The gluing parameter classifies the orbits.** For `C ≠ 0`, two points of the open square
`(0, 1)²` lie on the same flow line exactly when their gluing parameters agree. -/
theorem exists_triangleBaseFlow_eq_iff_triangleBaseGluingParameter_eq (hC : C ≠ 0)
    {z w : WithLp 2 (ℝ × ℝ)} (hzu : z.fst ∈ Ioo 0 1) (hzv : z.snd ∈ Ioo 0 1)
    (hwu : w.fst ∈ Ioo 0 1) (hwv : w.snd ∈ Ioo 0 1) :
    (∃ s, triangleBaseFlow C s z = w) ↔
      triangleBaseGluingParameter z = triangleBaseGluingParameter w := by
  rw [exists_triangleBaseFlow_eq_iff hC hzu hzv hwu hwv, triangleBaseGluingParameter_eq_exp hzu hzv,
    triangleBaseGluingParameter_eq_exp hwu hwv, Real.exp_eq_exp, neg_inj]

/-- The gluing parameter is continuous where `u ≠ 0` and `v² < 1`, in particular on the triangle
away from the source `(0, 0)` and the sink `(1, 1)`. -/
theorem continuousOn_triangleBaseGluingParameter :
    ContinuousOn triangleBaseGluingParameter {z | z.fst ≠ 0 ∧ z.snd ^ 2 < 1} :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz ↦
    mul_ne_zero hz.1 (Real.sqrt_pos.2 (by linarith [hz.2])).ne'

/-- On the triangle the gluing parameter lies in `[0, 1]`. -/
theorem triangleBaseGluingParameter_mem_Icc {z : WithLp 2 (ℝ × ℝ)} (hz : z ∈ triangleBase) :
    triangleBaseGluingParameter z ∈ Icc 0 1 := by
  obtain ⟨hv0, hvu, hu1⟩ := mem_triangleBase.1 hz
  rcases (hv0.trans hvu).eq_or_lt with hu | hu
  · simp [triangleBaseGluingParameter, ← hu]
  rcases (hvu.trans hu1).eq_or_lt with hv | hv
  · simp [triangleBaseGluingParameter, hv]
  have hden : 0 < z.fst * √(1 - z.snd ^ 2) := mul_pos hu (Real.sqrt_pos.2 (by nlinarith))
  refine ⟨div_nonneg (mul_nonneg hv0 (Real.sqrt_nonneg _)) hden.le, (div_le_one hden).2 ?_⟩
  have := pow_le_pow_left₀ hv0 hvu 2
  exact mul_le_mul hvu (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) hu.le

/-- On the triangle the gluing parameter vanishes exactly on the broken orbit, the edges `v = 0`
and `u = 1`. -/
theorem triangleBaseGluingParameter_eq_zero_iff {z : WithLp 2 (ℝ × ℝ)} (hz : z ∈ triangleBase) :
    triangleBaseGluingParameter z = 0 ↔ z.snd = 0 ∨ z.fst = 1 := by
  rw [mem_triangleBase] at hz
  rcases (hz.1.trans hz.2.1).eq_or_lt with hu | hu
  · have hv : z.snd = 0 := le_antisymm (hu ▸ hz.2.1) hz.1
    simp [triangleBaseGluingParameter, ← hu, hv]
  rcases (hz.2.1.trans hz.2.2).eq_or_lt with hv | hv
  · have hu1 : z.fst = 1 := le_antisymm hz.2.2 (hv ▸ hz.2.1)
    simp [triangleBaseGluingParameter, hv, hu1]
  have hden : z.fst * √(1 - z.snd ^ 2) ≠ 0 :=
    (mul_pos hu (Real.sqrt_pos.2 (by nlinarith [hz.1]))).ne'
  rw [triangleBaseGluingParameter, div_eq_zero_iff, or_iff_left hden, mul_eq_zero,
    Real.sqrt_eq_zero', sub_nonpos]
  refine or_congr_right ⟨fun h ↦ le_antisymm hz.2.2 (by nlinarith), fun h ↦ by rw [h]; norm_num⟩

/-- On the triangle away from the source and the sink, the gluing parameter equals `1` exactly on
the diagonal. -/
theorem triangleBaseGluingParameter_eq_one_iff {z : WithLp 2 (ℝ × ℝ)} (hz : z ∈ triangleBase)
    (hu : 0 < z.fst) (hv : z.snd < 1) :
    triangleBaseGluingParameter z = 1 ↔ z.fst = z.snd := by
  rw [mem_triangleBase] at hz
  have hv1 : 0 < √(1 - z.snd ^ 2) := Real.sqrt_pos.2 (by nlinarith [hz.1])
  rw [triangleBaseGluingParameter, div_eq_one_iff_eq (mul_pos hu hv1).ne']
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  by_contra hne
  have hlt : z.snd < z.fst := lt_of_le_of_ne hz.2.1 (Ne.symm hne)
  -- Off the diagonal `v < u`, so both factors on the left are smaller.
  have hsq : z.snd ^ 2 ≤ z.fst ^ 2 := pow_le_pow_left₀ hz.1 hz.2.1 2
  have : z.snd * √(1 - z.fst ^ 2) < z.fst * √(1 - z.snd ^ 2) :=
    calc z.snd * √(1 - z.fst ^ 2) ≤ z.snd * √(1 - z.snd ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hz.1
      _ < z.fst * √(1 - z.snd ^ 2) := mul_lt_mul_of_pos_right hlt hv1
  exact this.ne h

/-- On the triangle the gluing parameter is positive exactly on the open square `(0, 1)²`, where
the source-to-sink orbits run. -/
theorem triangleBaseGluingParameter_pos_iff {z : WithLp 2 (ℝ × ℝ)} (hz : z ∈ triangleBase) :
    0 < triangleBaseGluingParameter z ↔ z.fst ∈ Ioo 0 1 ∧ z.snd ∈ Ioo 0 1 := by
  rw [(triangleBaseGluingParameter_mem_Icc hz).1.lt_iff_ne', ne_eq,
    triangleBaseGluingParameter_eq_zero_iff hz, not_or]
  rw [mem_triangleBase] at hz
  constructor
  · rintro ⟨h0, h1⟩
    have hv : 0 < z.snd := lt_of_le_of_ne hz.1 (Ne.symm h0)
    have hu : z.fst < 1 := lt_of_le_of_ne hz.2.2 h1
    exact ⟨⟨hv.trans_le hz.2.1, hu⟩, ⟨hv, hz.2.1.trans_lt hu⟩⟩
  · rintro ⟨hu', hv'⟩
    exact ⟨hv'.1.ne', hu'.2.ne⟩

/-! ### Evaluation on the slice `u = c` -/

/-- The point `(c, c σ / √(1 - c² + c² σ²))` on the slice `u = c` of the orbit with gluing
parameter `σ`. For `0 < c < 1` and `σ ∈ [0, 1]` it runs over the slice of the triangle, from the
point `(c, 0)` of the broken orbit at `σ = 0` to the diagonal point `(c, c)` at `σ = 1`
(`TauCeti.bijOn_triangleBaseFstSlice`). -/
noncomputable def triangleBaseFstSlice (c σ : ℝ) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 (c, c * σ / √(1 - c ^ 2 + c ^ 2 * σ ^ 2))

@[simp]
theorem fst_triangleBaseFstSlice (c σ : ℝ) : (triangleBaseFstSlice c σ).fst = c :=
  (rfl)

theorem snd_triangleBaseFstSlice (c σ : ℝ) :
    (triangleBaseFstSlice c σ).snd = c * σ / √(1 - c ^ 2 + c ^ 2 * σ ^ 2) :=
  (rfl)

/-- At `σ = 0` the slice `u = c` meets the broken orbit, at `(c, 0)`. -/
@[simp]
theorem triangleBaseFstSlice_zero (c : ℝ) : triangleBaseFstSlice c 0 = WithLp.toLp 2 (c, 0) := by
  simp [triangleBaseFstSlice]

/-- At `σ = 1` the slice `u = c` meets the diagonal, at `(c, c)`. -/
@[simp]
theorem triangleBaseFstSlice_one (c : ℝ) : triangleBaseFstSlice c 1 = WithLp.toLp 2 (c, c) := by
  simp [triangleBaseFstSlice]

private theorem one_sub_sq_add_pos {c : ℝ} (hc : c ^ 2 < 1) (σ : ℝ) :
    0 < 1 - c ^ 2 + c ^ 2 * σ ^ 2 := by
  nlinarith [sq_nonneg (c * σ)]

/-- The square of the transverse coordinate on the slice `u = c` is `c² σ² / (1 - c² + c² σ²)`: it
vanishes to second order at the broken end, so the coordinate itself to first order. -/
theorem sq_snd_triangleBaseFstSlice {c : ℝ} (hc : c ^ 2 ≤ 1) (σ : ℝ) :
    (triangleBaseFstSlice c σ).snd ^ 2 = c ^ 2 * σ ^ 2 / (1 - c ^ 2 + c ^ 2 * σ ^ 2) := by
  rw [snd_triangleBaseFstSlice, div_pow, mul_pow,
    Real.sq_sqrt (by nlinarith [sq_nonneg (c * σ)])]

/-- **The evaluation on the slice `u = c` is smooth** in the gluing parameter, including at the
broken end `σ = 0`. -/
theorem contDiff_triangleBaseFstSlice {n : WithTop ℕ∞} {c : ℝ} (hc : c ^ 2 < 1) :
    ContDiff ℝ n (triangleBaseFstSlice c) := by
  have hs : ContDiff ℝ n fun σ : ℝ ↦ √(1 - c ^ 2 + c ^ 2 * σ ^ 2) :=
    (by fun_prop : ContDiff ℝ n fun σ : ℝ ↦ 1 - c ^ 2 + c ^ 2 * σ ^ 2).sqrt
      fun σ ↦ (one_sub_sq_add_pos hc σ).ne'
  have hv : ContDiff ℝ n fun σ : ℝ ↦ c * σ / √(1 - c ^ 2 + c ^ 2 * σ ^ 2) :=
    (contDiff_const.mul contDiff_id).div hs fun σ ↦ (Real.sqrt_pos.2 (one_sub_sq_add_pos hc σ)).ne'
  exact (WithLp.contDiff_toLp (p := 2)).comp (contDiff_const.prodMk hv)

/-- **The slice `u = c` is transverse to the broken end**: the transverse coordinate `v` has
derivative `c / √(1 - c²)` in the gluing parameter at `σ = 0`, which is nonzero for `c ≠ 0`. -/
theorem hasDerivAt_snd_triangleBaseFstSlice_zero {c : ℝ} (hc : c ^ 2 < 1) :
    HasDerivAt (fun σ ↦ (triangleBaseFstSlice c σ).snd) (c / √(1 - c ^ 2)) 0 := by
  have h1 : 0 < 1 - c ^ 2 := by linarith
  have hD : HasDerivAt (fun σ : ℝ ↦ 1 - c ^ 2 + c ^ 2 * σ ^ 2) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (c ^ 2)).const_add (1 - c ^ 2)
  have hs := hD.sqrt (by simpa using h1.ne')
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul c).div hs (by simpa using (Real.sqrt_pos.2 h1).ne')
  refine h.congr_deriv ?_
  simp only [id, mul_zero, zero_pow two_ne_zero, add_zero, mul_one, zero_div, sub_zero,
    Real.sq_sqrt h1.le]
  field_simp
  rw [Real.sq_sqrt h1.le]

/-- **The gluing parameter inverts the evaluation on the slice `u = c`.** -/
@[simp]
theorem triangleBaseGluingParameter_triangleBaseFstSlice {c : ℝ} (hc₀ : c ≠ 0) (hc₁ : c ^ 2 < 1)
    (σ : ℝ) : triangleBaseGluingParameter (triangleBaseFstSlice c σ) = σ := by
  have hD := one_sub_sq_add_pos hc₁ σ
  have hv : 1 - (triangleBaseFstSlice c σ).snd ^ 2 = (1 - c ^ 2) / (1 - c ^ 2 + c ^ 2 * σ ^ 2) := by
    rw [sq_snd_triangleBaseFstSlice hc₁.le]
    field_simp
    ring
  rw [triangleBaseGluingParameter, hv, Real.sqrt_div' _ hD.le, fst_triangleBaseFstSlice,
    snd_triangleBaseFstSlice]
  field_simp

/-- **Every point of a slice `u = c` is the evaluation of its gluing parameter.** -/
theorem triangleBaseFstSlice_triangleBaseGluingParameter {z : WithLp 2 (ℝ × ℝ)}
    (hu₀ : z.fst ≠ 0) (hu₁ : z.fst ^ 2 < 1) (hv : z.snd ^ 2 < 1) :
    triangleBaseFstSlice z.fst (triangleBaseGluingParameter z) = z := by
  have h1v : 0 < 1 - z.snd ^ 2 := by linarith
  have hD : 1 - z.fst ^ 2 + z.fst ^ 2 * triangleBaseGluingParameter z ^ 2 =
      (1 - z.fst ^ 2) / (1 - z.snd ^ 2) := by
    rw [sq_triangleBaseGluingParameter hu₁.le hv.le]
    field_simp
    ring
  simp only [WithLp.ext_iff, Prod.ext_iff, WithLp.ofLp_fst, WithLp.ofLp_snd]
  refine ⟨rfl, ?_⟩
  rw [snd_triangleBaseFstSlice, hD, Real.sqrt_div' _ h1v.le, triangleBaseGluingParameter]
  field_simp

/-- The evaluation on the slice `u = c`, for `0 < c < 1` and `0 < σ`, lies in the open square
`(0, 1)²`, where the source-to-sink orbits run. -/
theorem snd_triangleBaseFstSlice_mem_Ioo {c σ : ℝ} (hc : c ∈ Ioo 0 1) (hσ : 0 < σ) :
    (triangleBaseFstSlice c σ).snd ∈ Ioo 0 1 := by
  have hc₁ : c ^ 2 < 1 := pow_lt_one₀ hc.1.le hc.2 two_ne_zero
  have hD := one_sub_sq_add_pos hc₁ σ
  rw [snd_triangleBaseFstSlice]
  refine ⟨div_pos (mul_pos hc.1 hσ) (Real.sqrt_pos.2 hD),
    (div_lt_one (Real.sqrt_pos.2 hD)).2 ((Real.lt_sqrt (mul_pos hc.1 hσ).le).2 ?_)⟩
  nlinarith

/-- **The slice `u = c` fills the interval of orbits.** For `0 < c < 1`, the evaluation on the
slice `u = c` is a bijection from `[0, 1]` onto the points of the triangle with `u = c`; the
gluing parameter is its inverse. -/
theorem bijOn_triangleBaseFstSlice {c : ℝ} (hc : c ∈ Ioo 0 1) :
    BijOn (triangleBaseFstSlice c) (Icc 0 1) {z | z ∈ triangleBase ∧ z.fst = c} := by
  have hc₁ : c ^ 2 < 1 := pow_lt_one₀ hc.1.le hc.2 two_ne_zero
  refine ⟨fun σ hσ ↦ ?_, fun σ _ τ _ h ↦ ?_, fun z hz ↦ ?_⟩
  · have hD := one_sub_sq_add_pos hc₁ σ
    refine ⟨mem_triangleBase.2 ⟨?_, ?_, hc.2.le⟩, rfl⟩
    · exact div_nonneg (mul_nonneg hc.1.le hσ.1) (Real.sqrt_nonneg _)
    · rw [snd_triangleBaseFstSlice, fst_triangleBaseFstSlice, div_le_iff₀ (Real.sqrt_pos.2 hD)]
      refine mul_le_mul_of_nonneg_left ((Real.le_sqrt hσ.1 hD.le).2 ?_) hc.1.le
      have hσ₁ : σ ^ 2 ≤ 1 := pow_le_one₀ hσ.1 hσ.2
      nlinarith [mul_nonneg (sub_nonneg.2 hc₁.le) (sub_nonneg.2 hσ₁)]
  · simpa [hc.1.ne', hc₁] using congrArg triangleBaseGluingParameter h
  · obtain ⟨hzT, rfl⟩ := hz
    have hz' := mem_triangleBase.1 hzT
    refine ⟨triangleBaseGluingParameter z,
      triangleBaseGluingParameter_mem_Icc hzT,
      triangleBaseFstSlice_triangleBaseGluingParameter hc.1.ne' hc₁ ?_⟩
    nlinarith [hz'.1, hz'.2.1, hc.2]

/-- On the slice `u = c`, the orbit parameter of the orbit with gluing parameter `σ > 0` is
`-log σ`. -/
theorem triangleBaseOrbitParameter_triangleBaseFstSlice {c σ : ℝ} (hc : c ∈ Ioo 0 1)
    (hσ : 0 < σ) : triangleBaseOrbitParameter (triangleBaseFstSlice c σ) = -Real.log σ := by
  have hc₁ : c ^ 2 < 1 := pow_lt_one₀ hc.1.le hc.2 two_ne_zero
  rw [triangleBaseOrbitParameter_eq_neg_log_triangleBaseGluingParameter
    (z := triangleBaseFstSlice c σ) hc (snd_triangleBaseFstSlice_mem_Ioo hc hσ),
    triangleBaseGluingParameter_triangleBaseFstSlice hc.1.ne' hc₁]

/-! ### Evaluation on the slice `v = c` -/

/-- The point `(c / √(c² + (1 - c²) σ²), c)` on the slice `v = c` of the orbit with gluing
parameter `|σ|`. For `0 < c < 1` and `σ ∈ [0, 1]` it runs over the slice of the triangle, from
the point `(1, c)` of the broken orbit at `σ = 0` to the diagonal point `(c, c)` at `σ = 1`
(`TauCeti.bijOn_triangleBaseSndSlice`). -/
noncomputable def triangleBaseSndSlice (c σ : ℝ) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 (c / √(c ^ 2 + (1 - c ^ 2) * σ ^ 2), c)

theorem fst_triangleBaseSndSlice (c σ : ℝ) :
    (triangleBaseSndSlice c σ).fst = c / √(c ^ 2 + (1 - c ^ 2) * σ ^ 2) :=
  (rfl)

@[simp]
theorem snd_triangleBaseSndSlice (c σ : ℝ) : (triangleBaseSndSlice c σ).snd = c :=
  (rfl)

/-- For `0 < c`, at `σ = 0` the slice `v = c` meets the broken orbit, at `(1, c)`. -/
theorem triangleBaseSndSlice_zero {c : ℝ} (hc : 0 < c) :
    triangleBaseSndSlice c 0 = WithLp.toLp 2 (1, c) := by
  simp [triangleBaseSndSlice, Real.sqrt_sq hc.le, hc.ne']

/-- At `σ = 1` the slice `v = c` meets the diagonal, at `(c, c)`. -/
@[simp]
theorem triangleBaseSndSlice_one (c : ℝ) : triangleBaseSndSlice c 1 = WithLp.toLp 2 (c, c) := by
  simp [triangleBaseSndSlice]

/-- The evaluation on the slice `v = c` is even in the gluing parameter. -/
@[simp]
theorem triangleBaseSndSlice_neg (c σ : ℝ) :
    triangleBaseSndSlice c (-σ) = triangleBaseSndSlice c σ := by
  simp [triangleBaseSndSlice]

private theorem sq_add_one_sub_sq_pos {c : ℝ} (hc₀ : c ≠ 0) (hc₁ : c ^ 2 ≤ 1) (σ : ℝ) :
    0 < c ^ 2 + (1 - c ^ 2) * σ ^ 2 := by
  nlinarith [sq_pos_of_ne_zero hc₀, sq_nonneg σ]

/-- **The slice `v = c` meets the broken end to second order**: on it,
`1 - u² = (1 - c²) σ² / (c² + (1 - c²) σ²)`. -/
theorem one_sub_sq_fst_triangleBaseSndSlice {c : ℝ} (hc₀ : c ≠ 0) (hc₁ : c ^ 2 ≤ 1) (σ : ℝ) :
    1 - (triangleBaseSndSlice c σ).fst ^ 2 =
      (1 - c ^ 2) * σ ^ 2 / (c ^ 2 + (1 - c ^ 2) * σ ^ 2) := by
  have hE := sq_add_one_sub_sq_pos hc₀ hc₁ σ
  rw [fst_triangleBaseSndSlice, div_pow, Real.sq_sqrt hE.le]
  field_simp
  ring

/-- **The evaluation on the slice `v = c` is smooth** in the gluing parameter, including at the
broken end `σ = 0`. -/
theorem contDiff_triangleBaseSndSlice {n : WithTop ℕ∞} {c : ℝ} (hc₀ : c ≠ 0) (hc₁ : c ^ 2 ≤ 1) :
    ContDiff ℝ n (triangleBaseSndSlice c) := by
  have hs : ContDiff ℝ n fun σ : ℝ ↦ √(c ^ 2 + (1 - c ^ 2) * σ ^ 2) :=
    (by fun_prop : ContDiff ℝ n fun σ : ℝ ↦ c ^ 2 + (1 - c ^ 2) * σ ^ 2).sqrt
      fun σ ↦ (sq_add_one_sub_sq_pos hc₀ hc₁ σ).ne'
  have hu : ContDiff ℝ n fun σ : ℝ ↦ c / √(c ^ 2 + (1 - c ^ 2) * σ ^ 2) :=
    contDiff_const.div hs fun σ ↦ (Real.sqrt_pos.2 (sq_add_one_sub_sq_pos hc₀ hc₁ σ)).ne'
  exact (WithLp.contDiff_toLp (p := 2)).comp (hu.prodMk contDiff_const)

/-- **The gluing parameter inverts the evaluation on the slice `v = c`** up to sign: the gluing
parameter of `triangleBaseSndSlice c σ` is `|σ|`. -/
@[simp]
theorem triangleBaseGluingParameter_triangleBaseSndSlice {c : ℝ} (hc₀ : c ≠ 0) (hc₁ : c ^ 2 < 1)
    (σ : ℝ) : triangleBaseGluingParameter (triangleBaseSndSlice c σ) = |σ| := by
  have h1 : 0 < 1 - c ^ 2 := by linarith
  have hE := sq_add_one_sub_sq_pos hc₀ hc₁.le σ
  rw [triangleBaseGluingParameter, one_sub_sq_fst_triangleBaseSndSlice hc₀ hc₁.le,
    Real.sqrt_div' _ hE.le, Real.sqrt_mul h1.le, Real.sqrt_sq_eq_abs, snd_triangleBaseSndSlice,
    fst_triangleBaseSndSlice]
  field_simp

/-- **Every point of a slice `v = c` with `0 < c` and `0 < u` is the evaluation of its gluing
parameter.** -/
theorem triangleBaseSndSlice_triangleBaseGluingParameter {z : WithLp 2 (ℝ × ℝ)}
    (hu₀ : 0 < z.fst) (hu₁ : z.fst ^ 2 ≤ 1) (hv₀ : 0 < z.snd) (hv₁ : z.snd ^ 2 < 1) :
    triangleBaseSndSlice z.snd (triangleBaseGluingParameter z) = z := by
  have hE : z.snd ^ 2 + (1 - z.snd ^ 2) * triangleBaseGluingParameter z ^ 2 =
      (z.snd / z.fst) ^ 2 := by
    rw [sq_triangleBaseGluingParameter hu₁ hv₁.le]
    field_simp
    ring
  simp only [WithLp.ext_iff, Prod.ext_iff, WithLp.ofLp_fst, WithLp.ofLp_snd]
  refine ⟨?_, rfl⟩
  rw [fst_triangleBaseSndSlice, hE, Real.sqrt_sq (div_pos hv₀ hu₀).le]
  field_simp

/-- The evaluation on the slice `v = c`, for `0 < c < 1` and `σ ≠ 0`, lies in the open square
`(0, 1)²`, where the source-to-sink orbits run. -/
theorem fst_triangleBaseSndSlice_mem_Ioo {c σ : ℝ} (hc : c ∈ Ioo 0 1) (hσ : σ ≠ 0) :
    (triangleBaseSndSlice c σ).fst ∈ Ioo 0 1 := by
  have hc₁ : c ^ 2 < 1 := pow_lt_one₀ hc.1.le hc.2 two_ne_zero
  have hE := sq_add_one_sub_sq_pos hc.1.ne' hc₁.le σ
  rw [fst_triangleBaseSndSlice]
  refine ⟨div_pos hc.1 (Real.sqrt_pos.2 hE),
    (div_lt_one (Real.sqrt_pos.2 hE)).2 ((Real.lt_sqrt hc.1.le).2 ?_)⟩
  nlinarith [sq_pos_of_ne_zero hσ]

/-- **The slice `v = c` fills the interval of orbits.** For `0 < c < 1`, the evaluation on the
slice `v = c` is a bijection from `[0, 1]` onto the points of the triangle with `v = c`; the
gluing parameter is its inverse. -/
theorem bijOn_triangleBaseSndSlice {c : ℝ} (hc : c ∈ Ioo 0 1) :
    BijOn (triangleBaseSndSlice c) (Icc 0 1) {z | z ∈ triangleBase ∧ z.snd = c} := by
  have hc₁ : c ^ 2 < 1 := pow_lt_one₀ hc.1.le hc.2 two_ne_zero
  refine ⟨fun σ hσ ↦ ?_, fun σ hσ τ hτ h ↦ ?_, fun z hz ↦ ?_⟩
  · have hE := sq_add_one_sub_sq_pos hc.1.ne' hc₁.le σ
    have hE' := Real.sqrt_pos.2 hE
    refine ⟨mem_triangleBase.2 ⟨hc.1.le, ?_, ?_⟩, rfl⟩
    · rw [snd_triangleBaseSndSlice, fst_triangleBaseSndSlice, le_div_iff₀ hE']
      have hσ₁ : σ ^ 2 ≤ 1 := pow_le_one₀ hσ.1 hσ.2
      exact mul_le_of_le_one_right hc.1.le
        (Real.sqrt_le_one.2 (by nlinarith [mul_nonneg (sub_nonneg.2 hc₁.le) (sub_nonneg.2 hσ₁)]))
    · rw [fst_triangleBaseSndSlice, div_le_one hE']
      exact (Real.le_sqrt hc.1.le hE.le).2 (by nlinarith [sq_nonneg σ])
  · have := congrArg triangleBaseGluingParameter h
    rwa [triangleBaseGluingParameter_triangleBaseSndSlice hc.1.ne' hc₁,
      triangleBaseGluingParameter_triangleBaseSndSlice hc.1.ne' hc₁, abs_of_nonneg hσ.1,
      abs_of_nonneg hτ.1] at this
  · obtain ⟨hzT, rfl⟩ := hz
    have hz' := mem_triangleBase.1 hzT
    have hu : 0 < z.fst := hc.1.trans_le hz'.2.1
    refine ⟨triangleBaseGluingParameter z, triangleBaseGluingParameter_mem_Icc hzT,
      triangleBaseSndSlice_triangleBaseGluingParameter hu ?_ hc.1 hc₁⟩
    nlinarith [hz'.2.2]

/-- On the slice `v = c`, the orbit parameter of the orbit through the evaluation at `σ ≠ 0` is
`-log |σ|`. -/
theorem triangleBaseOrbitParameter_triangleBaseSndSlice {c σ : ℝ} (hc : c ∈ Ioo 0 1)
    (hσ : σ ≠ 0) : triangleBaseOrbitParameter (triangleBaseSndSlice c σ) = -Real.log |σ| := by
  have hc₁ : c ^ 2 < 1 := pow_lt_one₀ hc.1.le hc.2 two_ne_zero
  rw [triangleBaseOrbitParameter_eq_neg_log_triangleBaseGluingParameter
    (z := triangleBaseSndSlice c σ) (fst_triangleBaseSndSlice_mem_Ioo hc hσ) hc,
    triangleBaseGluingParameter_triangleBaseSndSlice hc.1.ne' hc₁]

/-- **The two slices give the same chart of the orbit interval.** For `C ≠ 0`, `0 < c, c' < 1`
and `0 < σ`, the point with gluing parameter `σ` on the slice `u = c` flows to the point with
gluing parameter `σ` on the slice `v = c'`. -/
theorem exists_triangleBaseFlow_triangleBaseFstSlice_eq_triangleBaseSndSlice (hC : C ≠ 0)
    {c c' σ : ℝ} (hc : c ∈ Ioo 0 1) (hc' : c' ∈ Ioo 0 1) (hσ : 0 < σ) :
    ∃ s, triangleBaseFlow C s (triangleBaseFstSlice c σ) = triangleBaseSndSlice c' σ := by
  rw [exists_triangleBaseFlow_eq_iff_triangleBaseGluingParameter_eq (z := triangleBaseFstSlice c σ)
    (w := triangleBaseSndSlice c' σ) hC hc (snd_triangleBaseFstSlice_mem_Ioo hc hσ)
    (fst_triangleBaseSndSlice_mem_Ioo hc' hσ.ne') hc',
    triangleBaseGluingParameter_triangleBaseFstSlice hc.1.ne'
      (pow_lt_one₀ hc.1.le hc.2 two_ne_zero),
    triangleBaseGluingParameter_triangleBaseSndSlice hc'.1.ne'
      (pow_lt_one₀ hc'.1.le hc'.2 two_ne_zero),
    abs_of_pos hσ]

end TauCeti
