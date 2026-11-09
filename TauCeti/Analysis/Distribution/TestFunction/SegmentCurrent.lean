/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Convex.Topology
import TauCeti.MeasureTheory.Integral.CurveIntegral.Line
import TauCeti.MeasureTheory.Integral.CurveIntegral.Segment

/-!
# The oriented segment current

Let `Ω` be an open set of a real normed space `E` and let `p q : E`. The *oriented segment current*
`[[p, q]]` is the `1`-current on `Ω` that integrates a test `1`-form along the segment from `p` to
`q`. It is Mathlib's curve integral `curveIntegral` along the affine path `Path.segment p q`, a
`1`-form `ω` being read as the field of continuous linear maps `v ↦ ω x ![v]`:

`[[p, q]] ω = ∫ t in 0..1, ω (p + t • (q - p)) ![q - p]`.

It is a continuous linear functional on the test `1`-forms `𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ)`, since
it factors through the bounded continuous functions, where curve integration along the segment is
the functional `BoundedContinuousFunction.curveIntegralSegmentCLM p q` of norm at most `‖q - p‖`.
Its boundary is the difference of the endpoint point currents,

`∂[[p, q]] = δ_q - δ_p`, that is, `[[p, q]] (d g) = g q - g p` for every test `0`-form `g`,

by the fundamental theorem of calculus along the segment. This holds for all `p` and `q`: the
segment current reverses sign when its endpoints are exchanged, and it is zero when they agree.
On the real line, `[[a, b]] ω = ∫ t in a..b, ω t ![1]` is the parametrized interval current, with
the orientation of the oriented interval integral, so `∂[[a, b]] = δ_b - δ_a` also for `b < a` and
`a = b`. The current `[[p, q]]` is supported in the closed segment `[p, q]`; when an endpoint lies
outside `Ω`, its point current evaluates every test form on `Ω` to zero.

Segment currents are the oriented `1`-simplices of the current complex, the building blocks of
polyhedral `1`-chains. Their mass is computed in
`TauCeti.Analysis.Distribution.Mass.SegmentCurrent`.

## Main declarations

* `Distribution.segmentCurrent p q`: the oriented segment current `[[p, q]]`.
* `Distribution.segmentCurrent_apply`: it is the curve integral along `Path.segment p q`;
  `Distribution.segmentCurrent_apply_eq_intervalIntegral_lineMap` writes it as an interval
  integral over `[0, 1]`.
* `Distribution.norm_segmentCurrent_apply_le`: `|[[p, q]] ω| ≤ sup ‖ω‖ * ‖q - p‖`.
* `Distribution.segmentCurrent_extDerivCLM`, `Distribution.segmentCurrent_comp_extDerivCLM`:
  `∂[[p, q]] = δ_q - δ_p`.
* `Distribution.segmentCurrent_symm`, `Distribution.segmentCurrent_self`: reversing the endpoints
  negates `[[p, q]]`, and `[[p, p]] = 0`.
* `Distribution.segmentCurrent_monoCLM`: compatibility with restriction to an open subset.
* `Distribution.dsupport_segmentCurrent_subset`: `[[p, q]]` is supported in the segment `[p, q]`.
* `Distribution.segmentCurrent_apply_eq_intervalIntegral_real`: the interval current `[[a, b]]` on
  the real line.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.8 (oriented simplexes) and §4.1.7 (boundary of a
  current).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §1.
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction AffineMap
open scoped Distributions BoundedContinuousFunction

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' : Opens E} {n : ℕ∞}

/-- The **oriented segment current** `[[p, q]]`: the `1`-current on `Ω` integrating a test
`1`-form along the segment from `p` to `q`. It is the curve integral along `Path.segment p q`
(`Distribution.segmentCurrent_apply`), that is `ω ↦ ∫ t in 0..1, ω (lineMap p q t) ![q - p]`
(`Distribution.segmentCurrent_apply_eq_intervalIntegral_lineMap`).
Its boundary is `δ_q - δ_p` (`Distribution.segmentCurrent_extDerivCLM`). -/
def segmentCurrent (p q : E) : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  BoundedContinuousFunction.curveIntegralSegmentCLM p q ∘L toBoundedContinuousFunctionCLM ℝ

/-- The segment current evaluated on a test `1`-form `ω` is the curve integral along the segment
path of the `1`-form `ω`, seen as a field of continuous linear maps `v ↦ ω x ![v]`. -/
theorem segmentCurrent_apply (p q : E) (ω : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ)) :
    segmentCurrent p q ω =
      ∫ᶜ x in .segment p q,
        (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm (ω x) := by
  simp [segmentCurrent]

/-- The segment current evaluated on a test `1`-form is the integral of the form along the
affinely parametrized segment, applied to the direction `q - p`. -/
theorem segmentCurrent_apply_eq_intervalIntegral_lineMap (p q : E)
    (ω : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ)) :
    segmentCurrent p q ω = ∫ t in (0 : ℝ)..1, ω (lineMap p q t) ![q - p] := by
  rw [segmentCurrent_apply, curveIntegral_segment]
  simp only [ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply, Matrix.vec_single_eq_const]

/-- If a test `1`-form is bounded by `C`, its value on the segment current `[[p, q]]` is at most
`C * ‖q - p‖`. -/
theorem norm_segmentCurrent_apply_le (p q : E) (ω : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ)) {C : ℝ}
    (hω : ∀ x, ‖ω x‖ ≤ C) : ‖segmentCurrent p q ω‖ ≤ C * ‖q - p‖ := by
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm
  have h := norm_curveIntegral_segment_le (ω := fun x => e (ω x)) (a := p) (b := q)
    fun z _ => (e.norm_map (ω z)).trans_le (hω z)
  simpa [segmentCurrent_apply, e] using h

/-- The degenerate segment current `[[p, p]]` is zero. -/
@[simp]
theorem segmentCurrent_self (p : E) :
    (segmentCurrent p p : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 := by
  ext ω
  have h (x : E) : ω x ![0] = 0 := (ω x).map_coord_zero 0 rfl
  simp [segmentCurrent_apply_eq_intervalIntegral_lineMap, h]

/-- **Orientation reversal**: exchanging the endpoints negates the segment current,
`[[q, p]] = -[[p, q]]`. -/
theorem segmentCurrent_symm (p q : E) :
    (segmentCurrent q p : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ) = -segmentCurrent p q := by
  ext ω
  rw [neg_apply, segmentCurrent_apply, segmentCurrent_apply,
    ← Path.segment_symm p q, curveIntegral_symm]

/-- **The boundary of a segment current**: `∂[[p, q]] = δ_q - δ_p`. For every test `0`-form `g`,
`[[p, q]] (d g) = g q - g p`. This holds for all endpoints, in particular when `p = q`. -/
@[simp]
theorem segmentCurrent_extDerivCLM (p q : E) (g : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ)) :
    segmentCurrent p q (extDerivCLM g) = g q ![] - g p ![] := by
  let ev := ContinuousAlternatingMap.apply ℝ E ℝ (![] : Fin 0 → E)
  have hg : ContDiff ℝ 1 (g : E → E [⋀^Fin 0]→L[ℝ] ℝ) := g.contDiff.of_le (by simp)
  -- Along the segment, the `1`-form `d g` applied to `q - p` is the derivative of `t ↦ g γ(t)`.
  have hd (t : ℝ) : HasDerivAt (fun t => ev (g (lineMap p q t)))
      (extDerivCLM g (lineMap p q t) ![q - p]) t := by
    have hx := hg.differentiable one_ne_zero (lineMap p q t)
    refine (ev.hasFDerivAt.comp_hasDerivAt t
      (hx.hasFDerivAt.comp_hasDerivAt t hasDerivAt_lineMap)).congr_deriv ?_
    simp [TauCeti.extDeriv_apply_fin_one, ev]
  have hcont : Continuous fun t : ℝ => extDerivCLM g (lineMap p q t) ![q - p] :=
    ((ContinuousAlternatingMap.apply ℝ E ℝ ![q - p]).continuous.comp
      (extDerivCLM g).continuous).comp lineMap_continuous
  rw [segmentCurrent_apply_eq_intervalIntegral_lineMap,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable 0 1)]
  simp [ev]

/-- **The boundary of a segment current**, as an identity of continuous linear maps: `[[p, q]] ∘ d`
is the difference of the degree-zero point currents at `q` and at `p`. -/
@[simp]
theorem segmentCurrent_comp_extDerivCLM (p q : E) :
    (segmentCurrent p q ∘L extDerivCLM : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      ContinuousAlternatingMap.apply ℝ E ℝ ![] ∘L
        (BoundedContinuousFunction.evalCLM ℝ q - BoundedContinuousFunction.evalCLM ℝ p) ∘L
          toBoundedContinuousFunctionCLM ℝ := by
  ext g
  simp

/-- The segment current is compatible with restriction: on a test form extended by zero from a
smaller open set `Ω'`, the segment current on `Ω` is the segment current on `Ω'`. -/
@[simp]
theorem segmentCurrent_monoCLM (p q : E) (h : Ω' ≤ Ω) (ω : 𝓓^{n}(Ω', E [⋀^Fin 1]→L[ℝ] ℝ)) :
    segmentCurrent p q (monoCLM ℝ ω : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ)) =
      segmentCurrent p q ω := by
  simp [segmentCurrent_apply_eq_intervalIntegral_lineMap, monoCLM_apply, h]

/-- The segment current `[[p, q]]` is supported in the closed segment `[p, q]`. -/
theorem dsupport_segmentCurrent_subset (p q : E) :
    dsupport (segmentCurrent p q : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ) ⊆ segment ℝ p q := by
  refine compl_subset_compl.1 fun y hy => ?_
  rw [mem_compl_iff, notMem_dsupport_iff]
  refine ⟨(segment ℝ p q)ᶜ, fun ω hω => ?_,
    (TauCeti.isCompact_segment ℝ p q).isClosed.isOpen_compl, hy⟩
  rw [segmentCurrent_apply_eq_intervalIntegral_lineMap]
  refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le zero_le_one] at ht
  simp [image_eq_zero_of_notMem_tsupport fun h => hω h (lineMap_mem_segment ℝ p q
    (Ioc_subset_Icc_self ht))]

/-- **The interval current** on the real line: `[[a, b]] ω = ∫ t in a..b, ω t ![1]`, with the
orientation of the oriented interval integral, for all `a` and `b`. -/
theorem segmentCurrent_apply_eq_intervalIntegral_real {Ω : Opens ℝ} (a b : ℝ)
    (ω : 𝓓^{n}(Ω, ℝ [⋀^Fin 1]→L[ℝ] ℝ)) :
    segmentCurrent a b ω = ∫ t in a..b, ω t ![1] := by
  have h := TauCeti.curveIntegral_segment_line
    (fun x => (ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ (0 : Fin 1)).symm (ω x)) 0 1 a b
  rw [show (0 : ℝ) + a • 1 = a by simp, show (0 : ℝ) + b • 1 = b by simp] at h
  simpa [segmentCurrent_apply, Matrix.vec_single_eq_const] using h

end Distribution
