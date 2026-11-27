/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Curve integrals of continuous `1`-forms along segments

A continuous field `ω : E → E →L[𝕜] F` of continuous linear maps is curve integrable along every
segment `Path.segment a b`. Reading a `1`-form `α : E [⋀^Fin 1]→L[𝕜] F` as the continuous linear
map `v ↦ α ![v]` through `ContinuousAlternatingMap.ofSubsingletonLIE`, curve integration along the
segment from `a` to `b` is therefore a continuous linear functional on bounded continuous
`1`-form fields, of norm at most the length `‖b - a‖` of the segment.

For a complex function `F` with continuous derivative `f` on the segment, the curve integral of
the exact form `f(z) dz` along the segment from `a` to `b` is `F b - F a`
(`TauCeti.curveIntegral_segment_toSpanSingleton_eq_sub`). Consequently, if `F` is a primitive of
`f` on a set `S` star-convex at `c`, the curve integral of `f(z) dz` along the polygonal path from
`a ∈ S` through `c` to `b ∈ S` is `F b - F a`
(`TauCeti.curveIntegral_segment_add_segment_toSpanSingleton_eq_sub`).

A real-affine field of continuous linear maps is integrated exactly by the midpoint rule
(`AffineMap.curveIntegral_segment_eq_apply_midpoint`). In a complete, possibly non-unital, normed
ring `A` with compatible real scalars, this computes the ordered integrals of `g(x) dx` and
`dx g(x)` along a segment for real-affine `g : A → A`. Around a closed polygon with vertices
`p 0, …, p (n - 1)`, the integral of `(a + b x) dx` is `b * (∑ₖ (pₖ pₖ₊₁ - pₖ₊₁ pₖ)) / 2`,
and that of `dx (a + x b)` is `(∑ₖ (pₖ₊₁ pₖ - pₖ pₖ₊₁)) * b / 2`; they need not vanish when `A`
is not commutative.

## Main declarations

* `Continuous.curveIntegrable_segment`: a continuous field is curve integrable along segments.
* `BoundedContinuousFunction.curveIntegralSegmentCLM a b`: curve integration along the segment
  from `a` to `b`, as a continuous linear functional on bounded continuous `1`-form fields.
* `BoundedContinuousFunction.norm_curveIntegralSegmentCLM_le`: its norm is at most `‖b - a‖`.
* `TauCeti.curveIntegral_segment_toSpanSingleton_eq_sub`: the fundamental theorem of calculus
  along a segment in `ℂ`.
* `TauCeti.curveIntegral_segment_add_segment_toSpanSingleton_eq_sub`: the same along a two-segment
  path through the center of a star-convex domain of a primitive.
* `AffineMap.curveIntegral_segment_eq_apply_midpoint`: the midpoint rule for real-affine
  `1`-forms along a segment.
* `AffineMap.curveIntegral_segment_mul`, `AffineMap.curveIntegral_segment_mul_flip`: the ordered
  integrals of `g(x) dx` and `dx g(x)` along a segment, for real-affine `g` in a normed ring.
* `TauCeti.sum_curveIntegral_segment_mul_const_add_const_mul`,
  `TauCeti.sum_curveIntegral_segment_mul_flip_const_add_mul_const`: the integrals of
  `(a + b x) dx` and `dx (a + x b)` around a closed polygon, as commutator sums of consecutive
  vertices.
* `TauCeti.sum_curveIntegral_segment_mul_of_eqOn`,
  `TauCeti.sum_curveIntegral_segment_mul_flip_of_eqOn`: the same for `f dx` and `dx f`, when `f`
  agrees with `x ↦ a + b x`, respectively `x ↦ a + x b`, on a set containing the edges.
-/

public section

noncomputable section

open AffineMap ContinuousAlternatingMap
open scoped BoundedContinuousFunction

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous field of continuous linear maps is curve integrable along every segment. -/
theorem Continuous.curveIntegrable_segment {ω : E → E →L[𝕜] F} (hω : Continuous ω) (a b : E) :
    CurveIntegrable ω (.segment a b) :=
  _root_.curveIntegrable_segment.2 <|
    ((hω.clm_apply continuous_const).comp lineMap_continuous).intervalIntegrable 0 1

/-- **Midpoint rule for affine `1`-forms.** The curve integral of a real-affine field `ω` of
continuous linear maps along the segment from `a` to `b` is the value of `ω` at the midpoint of
the segment, applied to the displacement `b - a`. -/
theorem AffineMap.curveIntegral_segment_eq_apply_midpoint {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (ω : V →ᵃ[ℝ] V →L[ℝ] W) (a b : V) : ∫ᶜ x in .segment a b, ω x = ω (midpoint ℝ a b) (b - a) := by
  have h (t : ℝ) : ω (lineMap a b t) (b - a) =
      ω a (b - a) + t • (ω b (b - a) - ω a (b - a)) := by
    rw [ω.apply_lineMap, lineMap_apply_module']
    simp [add_comm]
  have hi : IntervalIntegrable (fun t : ℝ ↦ t • (ω b (b - a) - ω a (b - a)))
      MeasureTheory.volume 0 1 :=
    (continuous_id.smul continuous_const).intervalIntegrable 0 1
  rw [_root_.curveIntegral_segment, midpoint, h]
  simp_rw [h]
  rw [intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_smul_const, integral_id]
  simp [invOf_eq_inv]

section NormedAlgebra

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [CompleteSpace A]

/-- The integral of the ordered `1`-form `g(x) dx` along a segment, for a real-affine `g`, is the
value of `g` at the midpoint times the displacement. -/
theorem AffineMap.curveIntegral_segment_mul (g : A →ᵃ[ℝ] A) (p q : A) :
    ∫ᶜ x in .segment p q, ContinuousLinearMap.mul ℝ A (g x) = g (midpoint ℝ p q) * (q - p) := by
  have h := ((ContinuousLinearMap.mul ℝ A).toLinearMap.toAffineMap.comp
    g).curveIntegral_segment_eq_apply_midpoint p q
  simp only [AffineMap.coe_comp, Function.comp_apply, LinearMap.coe_toAffineMap,
    ContinuousLinearMap.coe_coe] at h
  rw [h, ContinuousLinearMap.mul_apply']

/-- The integral of the ordered `1`-form `dx g(x)` along a segment, for a real-affine `g`, is the
displacement times the value of `g` at the midpoint. -/
theorem AffineMap.curveIntegral_segment_mul_flip (g : A →ᵃ[ℝ] A) (p q : A) :
    ∫ᶜ x in .segment p q, (ContinuousLinearMap.mul ℝ A).flip (g x) =
      (q - p) * g (midpoint ℝ p q) := by
  have h := ((ContinuousLinearMap.mul ℝ A).flip.toLinearMap.toAffineMap.comp
    g).curveIntegral_segment_eq_apply_midpoint p q
  simp only [AffineMap.coe_comp, Function.comp_apply, LinearMap.coe_toAffineMap,
    ContinuousLinearMap.coe_coe] at h
  rw [h, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']

end NormedAlgebra

namespace BoundedContinuousFunction

/-- Curve integration of bounded continuous `1`-form fields along the segment from `a` to `b`,
a `1`-form `α` being read as the continuous linear map `v ↦ α ![v]`. It is a continuous linear
functional of norm at most `‖b - a‖` (`BoundedContinuousFunction.norm_curveIntegralSegmentCLM_le`).
-/
def curveIntegralSegmentCLM (a b : E) : (E →ᵇ E [⋀^Fin 1]→L[𝕜] F) →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun ω := ∫ᶜ x in .segment a b, (ofSubsingletonLIE (0 : Fin 1)).symm (ω x)
      map_add' ω η := by
        simp only [FunLike.coe_add, Pi.add_apply, map_add]
        exact curveIntegral_fun_add
          (((ofSubsingletonLIE 0).symm.continuous.comp ω.continuous).curveIntegrable_segment a b)
          (((ofSubsingletonLIE 0).symm.continuous.comp η.continuous).curveIntegrable_segment a b)
      map_smul' c ω := by
        simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
        exact curveIntegral_fun_smul }
    ‖b - a‖ fun ω => (norm_curveIntegral_segment_le fun z _ =>
      ((ofSubsingletonLIE 0).symm.norm_map (ω z)).trans_le (ω.norm_coe_le_norm z)).trans_eq
        (mul_comm _ _)

/-- `BoundedContinuousFunction.curveIntegralSegmentCLM a b ω` is the curve integral of `ω` along
`Path.segment a b`, with `ω x` read as the continuous linear map `v ↦ ω x ![v]`. -/
@[simp]
theorem curveIntegralSegmentCLM_apply (a b : E) (ω : E →ᵇ E [⋀^Fin 1]→L[𝕜] F) :
    curveIntegralSegmentCLM a b ω =
      ∫ᶜ x in .segment a b, (ofSubsingleton 𝕜 E F (0 : Fin 1)).symm (ω x) := by
  simp [curveIntegralSegmentCLM]

/-- Curve integration along the segment from `a` to `b` has norm at most `‖b - a‖`. -/
theorem norm_curveIntegralSegmentCLM_le (a b : E) :
    ‖(curveIntegralSegmentCLM a b : (E →ᵇ E [⋀^Fin 1]→L[𝕜] F) →L[𝕜] F)‖ ≤ ‖b - a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end BoundedContinuousFunction

namespace TauCeti

open Set

/-- **Fundamental theorem of calculus along a segment.** If `F` has complex derivative `f` at every
point of the segment `[a, b]` and `f` is continuous there, the curve integral of `f(z) dz` along
`Path.segment a b` is `F b - F a`. -/
theorem curveIntegral_segment_toSpanSingleton_eq_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {F f : ℂ → E} {a b : ℂ}
    (hF : ∀ z ∈ segment ℝ a b, HasDerivAt F (f z) z) (hf : ContinuousOn f (segment ℝ a b)) :
    ∫ᶜ z in Path.segment a b, ContinuousLinearMap.toSpanSingleton ℂ (f z) = F b - F a := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, AffineMap.lineMap a b t ∈ segment ℝ a b := fun t ht =>
    lineMap_mem_segment ℝ a b (by rwa [uIcc_of_le zero_le_one] at ht)
  rw [curveIntegral_segment]
  simp only [ContinuousLinearMap.toSpanSingleton_apply]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (AffineMap.lineMap a b t))
        ((b - a) • f (AffineMap.lineMap a b t)) t := fun t ht =>
    (hF _ (hmem t ht)).scomp t (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero]
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.smul (hf.comp ?_ hmem)
  exact (AffineMap.lineMap_continuous (R := ℝ)).continuousOn

/-- **Fundamental theorem of calculus along a path through a star center.** If `F` has complex
derivative `f` on a set `S` that is star-convex at `c`, and `f` is continuous on `S`, then for
`a b ∈ S` the curve integrals of `f(z) dz` along `Path.segment a c` and `Path.segment c b` add up
to `F b - F a`. -/
theorem curveIntegral_segment_add_segment_toSpanSingleton_eq_sub {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {F f : ℂ → E} {S : Set ℂ}
    {a b c : ℂ} (hS : StarConvex ℝ c S) (ha : a ∈ S) (hb : b ∈ S)
    (hF : ∀ z ∈ S, HasDerivAt F (f z) z) (hf : ContinuousOn f S) :
    (∫ᶜ z in Path.segment a c, ContinuousLinearMap.toSpanSingleton ℂ (f z)) +
        ∫ᶜ z in Path.segment c b, ContinuousLinearMap.toSpanSingleton ℂ (f z) =
      F b - F a := by
  have h₁ : segment ℝ a c ⊆ S := by
    rw [segment_symm]
    exact hS.segment_subset ha
  have h₂ : segment ℝ c b ⊆ S := hS.segment_subset hb
  rw [curveIntegral_segment_toSpanSingleton_eq_sub (fun z hz => hF z (h₁ hz)) (hf.mono h₁),
    curveIntegral_segment_toSpanSingleton_eq_sub (fun z hz => hF z (h₂ hz)) (hf.mono h₂)]
  abel

section NormedAlgebra

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [CompleteSpace A] {n : ℕ}

/-- The integral of `(a + b x) dx` around the closed polygon with vertices `p 0, …, p (n - 1)` is
`b / 2` times the sum of the commutators `p k * p (k + 1) - p (k + 1) * p k` of consecutive
vertices. It vanishes when `A` is commutative, but not in general. -/
theorem sum_curveIntegral_segment_mul_const_add_const_mul (p : Fin n → A) (a b : A) :
    ∑ k, ∫ᶜ x in .segment (p k) (p (finRotate n k)), ContinuousLinearMap.mul ℝ A (a + b * x) =
      (2 : ℝ)⁻¹ • (b * ∑ k, (p k * p (finRotate n k) - p (finRotate n k) * p k)) := by
  let g : A →ᵃ[ℝ] A := AffineMap.const ℝ A a + (LinearMap.mulLeft ℝ b).toAffineMap
  have hg (x : A) : g x = a + b * x := by simp [g]
  simp_rw [← hg, AffineMap.curveIntegral_segment_mul, hg, midpoint_eq_smul_add]
  have hk (k : Fin n) :
      (a + b * ((⅟2 : ℝ) • (p k + p (finRotate n k)))) * (p (finRotate n k) - p k) =
        a * (p (finRotate n k) - p k) +
          (2 : ℝ)⁻¹ • (b * (p k * p (finRotate n k) - p (finRotate n k) * p k)) +
          (2 : ℝ)⁻¹ • (b * (p (finRotate n k) * p (finRotate n k) - p k * p k)) := by
    simp only [invOf_eq_inv, mul_add, add_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
      mul_assoc, smul_add, smul_sub]
    abel
  simp_rw [hk, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.smul_sum, ← Finset.mul_sum,
    Fin.sum_univ_finRotate_sub (fun k ↦ p k * p k), Fin.sum_univ_finRotate_sub p]
  simp

/-- The integral of `dx (a + x b)` around the closed polygon with vertices `p 0, …, p (n - 1)` is
half the sum of the commutators `p (k + 1) * p k - p k * p (k + 1)` of consecutive vertices,
times `b`. It vanishes when `A` is commutative, but not in general. -/
theorem sum_curveIntegral_segment_mul_flip_const_add_mul_const (p : Fin n → A) (a b : A) :
    ∑ k, ∫ᶜ x in .segment (p k) (p (finRotate n k)),
        (ContinuousLinearMap.mul ℝ A).flip (a + x * b) =
      (2 : ℝ)⁻¹ • ((∑ k, (p (finRotate n k) * p k - p k * p (finRotate n k))) * b) := by
  let g : A →ᵃ[ℝ] A := AffineMap.const ℝ A a + (LinearMap.mulRight ℝ b).toAffineMap
  have hg (x : A) : g x = a + x * b := by simp [g]
  simp_rw [← hg, AffineMap.curveIntegral_segment_mul_flip, hg, midpoint_eq_smul_add]
  have hk (k : Fin n) :
      (p (finRotate n k) - p k) * (a + ((⅟2 : ℝ) • (p k + p (finRotate n k))) * b) =
        (p (finRotate n k) - p k) * a +
          (2 : ℝ)⁻¹ • ((p (finRotate n k) * p k - p k * p (finRotate n k)) * b) +
          (2 : ℝ)⁻¹ • ((p (finRotate n k) * p (finRotate n k) - p k * p k) * b) := by
    simp only [invOf_eq_inv, mul_add, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc,
      mul_assoc, smul_add, smul_sub]
    abel
  simp_rw [hk, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.smul_sum, ← Finset.sum_mul,
    Fin.sum_univ_finRotate_sub (fun k ↦ p k * p k), Fin.sum_univ_finRotate_sub p]
  simp

/-- Around a closed polygon whose edges lie in `s`, the integral of `f dx` for `f` agreeing on `s`
with `x ↦ a + b * x` is `b / 2` times the commutator sum of the vertices. -/
theorem sum_curveIntegral_segment_mul_of_eqOn {f : A → A} {s : Set A} {a b : A}
    (hab : ∀ x ∈ s, f x = a + b * x) (p : Fin n → A)
    (hp : ∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) :
    ∑ k, ∫ᶜ x in .segment (p k) (p (finRotate n k)), ContinuousLinearMap.mul ℝ A (f x) =
      (2 : ℝ)⁻¹ • (b * ∑ k, (p k * p (finRotate n k) - p (finRotate n k) * p k)) := by
  rw [← sum_curveIntegral_segment_mul_const_add_const_mul p a b]
  refine Finset.sum_congr rfl fun k _ ↦ curveIntegral_congr ?_
  rw [Path.range_segment]
  intro x hx
  simp only [hab x (hp k hx)]

/-- Around a closed polygon whose edges lie in `s`, the integral of `dx f` for `f` agreeing on `s`
with `x ↦ a + x * b` is the commutator sum of the vertices times `b / 2`. -/
theorem sum_curveIntegral_segment_mul_flip_of_eqOn {f : A → A} {s : Set A} {a b : A}
    (hab : ∀ x ∈ s, f x = a + x * b) (p : Fin n → A)
    (hp : ∀ k, segment ℝ (p k) (p (finRotate n k)) ⊆ s) :
    ∑ k, ∫ᶜ x in .segment (p k) (p (finRotate n k)), (ContinuousLinearMap.mul ℝ A).flip (f x) =
      (2 : ℝ)⁻¹ • ((∑ k, (p (finRotate n k) * p k - p k * p (finRotate n k))) * b) := by
  rw [← sum_curveIntegral_segment_mul_flip_const_add_mul_const p a b]
  refine Finset.sum_congr rfl fun k _ ↦ curveIntegral_congr ?_
  rw [Path.range_segment]
  intro x hx
  simp only [hab x (hp k hx)]

end NormedAlgebra

end TauCeti
