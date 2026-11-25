/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Dynamics.Billiard.Circle
public import TauCeti.Dynamics.Billiard.NextCollision
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Dynamics.Billiard.Inverse
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Convex billiard tables of class `C^k`

A *convex billiard table* of class `C^k` (`1 ≤ k ≤ ∞`) and perimeter `ℓ > 0` is an arclength
parametrisation `γ : ℝ → ℂ` of the boundary of a strictly convex domain in the plane `ℂ`: `γ` is
of class `C^k`, `ℓ`-periodic, of unit speed, and every other point of the curve lies strictly to
the left of each tangent line, `0 < τ(s) × (γ t - γ s)` whenever `t - s ∉ ℓℤ`, where `τ = γ'` is
the unit tangent and `a × b = Im (conj a * b)` is the cross product of `ℂ`. This single inequality
encodes the strict convexity of the table, the positive (counterclockwise) orientation of its
boundary and the injectivity of `γ` on a period; the curvature is allowed to vanish. Convex tables
in this sense are the tables on which the billiard ball map of a convex billiard is defined.

## Main definitions

* `TauCeti.ConvexTable k ℓ`: convex billiard tables of class `C^k` and perimeter `ℓ`.
* `TauCeti.ConvexTable.curvature`: the signed curvature `τ × τ'` of a table.
* `TauCeti.ConvexTable.circleParam`: the parametrisation of the boundary by `AddCircle ℓ`.
* `TauCeti.ConvexTable.shift`, `TauCeti.ConvexTable.rigidMotion`, `TauCeti.ConvexTable.ofLE`:
  the reparametrised table `γ (· + c)`, the image `a γ + b` under a rotation followed by a
  translation, and the same table regarded at a lower regularity.
* `TauCeti.ConvexTable.circle`: the circle of radius `R`, a table of class `C^∞`.
* `TauCeti.ConvexTable.toStrictConvexBilliardTable`: a table is a strictly convex billiard table
  for the standard orientation of `ℂ`, so the next-collision map of
  `TauCeti.StrictConvexBilliardTable` applies to it.

## Main results

* `TauCeti.ConvexTable.apply_eq_apply_iff`: `γ s = γ t` exactly when `s ≡ t` modulo `ℓ`.
* `TauCeti.ConvexTable.isClosedEmbedding_circleParam`, `TauCeti.ConvexTable.isJordanCurve_range`:
  `γ` descends to a homeomorphism of `AddCircle ℓ` onto its image, which is a Jordan curve. Both
  hold for every strictly convex billiard table
  (`TauCeti.StrictConvexBilliardTable.isClosedEmbedding_circleParam`,
  `TauCeti.StrictConvexBilliardTable.isJordanCurve_range`).
* `TauCeti.ConvexTable.deriv_deriv`: the unit tangent of a table satisfies `τ' = i κ τ`.
* `TauCeti.ConvexTable.curvature_nonneg`: the curvature of a table is nonnegative.
* `TauCeti.ConvexTable.curvature_shift`, `TauCeti.ConvexTable.curvature_rigidMotion`: the
  curvature transforms by `κ ↦ κ (· + c)` under a shift of the origin and is unchanged by
  rotations and translations.
* `TauCeti.ConvexTable.curvature_circle`: the circle of radius `R` has curvature `1 / R`.
* `TauCeti.ConvexTable.coe_ne_comp_neg`: reversing the orientation of a table never gives a
  table.

## References

* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
* Anatole Katok and Boris Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Section 9.2.
-/

public section

noncomputable section

open Function Set Filter Topology Complex
open scoped ComplexConjugate

namespace TauCeti

/-- A **convex billiard table** of class `C^k` (`1 ≤ k`) with perimeter `ℓ > 0`: an arclength
parametrisation `γ : ℝ → ℂ` of class `C^k`, `ℓ`-periodic, of unit speed, such that every point
`γ t` with `t - s ∉ ℓℤ` lies strictly to the left of the tangent line at `γ s`, that is
`0 < Im (conj (γ' s) * (γ t - γ s))`. The strict inequality makes the curve strictly convex,
positively oriented and injective on a period (`TauCeti.ConvexTable.apply_eq_apply_iff`); the
curvature may vanish. -/
structure ConvexTable (k : ℕ∞) (ℓ : ℝ) [Fact (0 < ℓ)] where
  /-- The arclength parametrisation of the boundary. -/
  toFun : ℝ → ℂ
  /-- The regularity is at least `C¹`. -/
  one_le : 1 ≤ k
  /-- The parametrisation is of class `C^k`. -/
  contDiff' : ContDiff ℝ k toFun
  /-- The parametrisation is `ℓ`-periodic. -/
  periodic' : Periodic toFun ℓ
  /-- The parametrisation has unit speed. -/
  norm_deriv' : ∀ s, ‖deriv toFun s‖ = 1
  /-- Every other point of the curve lies strictly to the left of each tangent line. -/
  left_of_tangent' : ∀ s t : ℝ, (∀ m : ℤ, t - s ≠ m * ℓ) →
    0 < (conj (deriv toFun s) * (toFun t - toFun s)).im

namespace ConvexTable

variable {j k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (T : ConvexTable k ℓ)

instance : FunLike (ConvexTable k ℓ) ℝ ℂ where
  coe := toFun
  coe_injective T T' h := by cases T; cases T'; congr

@[simp]
theorem toFun_eq_coe : T.toFun = ⇑T := rfl

@[simp]
theorem coe_mk (f : ℝ → ℂ) (h₁ h₂ h₃ h₄ h₅) :
    ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : ConvexTable k ℓ) = f :=
  rfl

/-- Two tables with the same parametrisation are equal. -/
@[ext]
theorem ext {T T' : ConvexTable k ℓ} (h : ∀ s, T s = T' s) : T = T' :=
  DFunLike.ext _ _ h

/-! ### Basic properties of the parametrisation -/

theorem contDiff : ContDiff ℝ k T := T.contDiff'

theorem periodic : Periodic T ℓ := T.periodic'

@[simp]
theorem apply_add_period (s : ℝ) : T (s + ℓ) = T s := T.periodic s

@[simp]
theorem norm_deriv (s : ℝ) : ‖deriv T s‖ = 1 := T.norm_deriv' s

theorem deriv_ne_zero (s : ℝ) : deriv T s ≠ 0 :=
  norm_ne_zero_iff.1 (by simp)

theorem differentiable : Differentiable ℝ T :=
  T.contDiff.differentiable (zero_lt_one.trans_le (by exact_mod_cast T.one_le)).ne'

theorem continuous : Continuous T := T.differentiable.continuous

theorem hasDerivAt (s : ℝ) : HasDerivAt T (deriv T s) s :=
  (T.differentiable s).hasDerivAt

/-- The unit tangent of a table is continuous. -/
theorem continuous_deriv : Continuous (deriv T) :=
  T.contDiff.continuous_deriv (by exact_mod_cast T.one_le)

/-- The unit tangent of a table is `ℓ`-periodic. -/
theorem periodic_deriv : Periodic (deriv T) ℓ := T.periodic.deriv

/-- Every point `γ t` with `t ≢ s` modulo `ℓ` lies strictly to the left of the tangent line at
`γ s`. -/
theorem im_conj_deriv_mul_sub_pos {s t : ℝ} (h : (s : AddCircle ℓ) ≠ t) :
    0 < (conj (deriv T s) * (T t - T s)).im := by
  refine T.left_of_tangent' s t fun m hm => h ?_
  rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  exact ⟨m, by rw [hm, zsmul_eq_mul]⟩

/-- A table is injective on every half-open interval of length `ℓ`. -/
theorem injOn_Ico (a : ℝ) : InjOn T (Ico a (a + ℓ)) := fun _ hs _ ht hst => by_contra fun h => by
  simpa [hst] using T.im_conj_deriv_mul_sub_pos
    (mt (AddCircle.coe_eq_coe_iff_of_mem_Ico hs ht).1 h)

/-! ### Curvature -/

/-- The signed curvature `κ = τ × τ' = Im (conj (γ' s) * γ'' s)` of a table at the parameter
`s`. The unit tangent turns according to `τ' = i κ τ` (`TauCeti.ConvexTable.deriv_deriv`). Where
`τ` is not differentiable, which cannot happen when `2 ≤ k`
(`TauCeti.ConvexTable.differentiable_deriv`), the curvature takes the junk value `0`. -/
def curvature (s : ℝ) : ℝ := (conj (deriv T s) * deriv (deriv T) s).im

theorem curvature_def (s : ℝ) : T.curvature s = (conj (deriv T s) * deriv (deriv T) s).im :=
  (rfl)

theorem periodic_curvature : Periodic T.curvature ℓ := fun s => by
  simp only [curvature_def, T.periodic_deriv s, T.periodic_deriv.deriv s]

/-- The unit tangent of a table of class `C²` is differentiable. -/
theorem differentiable_deriv (hk : 2 ≤ k) : Differentiable ℝ (deriv T) := by
  have h2 : ContDiff ℝ 2 T := T.contDiff.of_le (WithTop.coe_le_coe.2 hk)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num] at h2
  exact (contDiff_succ_iff_deriv.1 h2).2.2.differentiable one_ne_zero

/-- **The Frenet equation of a table.** The unit tangent of a table turns at the rate given by the
curvature: `τ' = i κ τ`. Where `τ` is not differentiable both sides are the junk value `0`. -/
theorem deriv_deriv (s : ℝ) : deriv (deriv T) s = I * T.curvature s * deriv T s := by
  by_cases hd : DifferentiableAt ℝ (deriv T) s
  swap
  · simp [curvature_def, deriv_zero_of_not_differentiableAt hd]
  -- Differentiating `‖τ‖² = 1` shows that `conj τ * τ'` is purely imaginary, so it is `i κ`.
  have hτ := hd.hasDerivAt
  have h0 : HasDerivAt (fun t => ‖deriv T t‖ ^ 2) 0 s := by
    simpa using hasDerivAt_const s (1 : ℝ)
  have hre : (conj (deriv T s) * deriv (deriv T) s).re = 0 := by
    have := h0.unique hτ.norm_sq
    rw [Complex.inner, mul_comm (deriv (deriv T) s)] at this
    linarith
  have hw : conj (deriv T s) * deriv (deriv T) s = I * T.curvature s := by
    apply Complex.ext <;> simp [hre, curvature_def]
  calc deriv (deriv T) s = (deriv T s * conj (deriv T s)) * deriv (deriv T) s := by
        rw [mul_conj', T.norm_deriv, ofReal_one, one_pow, one_mul]
    _ = I * T.curvature s * deriv T s := by rw [mul_assoc, hw, mul_comm]

/-- **The curvature of a table is nonnegative.** -/
theorem curvature_nonneg (s : ℝ) : 0 ≤ T.curvature s := by
  -- The height `τ(s) × (γ t - γ s)` of the curve above the tangent line at `γ s` vanishes at
  -- `t = s` and is positive at every other nearby `t`, so `s` is a local minimum of it; its second
  -- derivative there is `κ(s)`.
  by_contra! hκ
  have hd : DifferentiableAt ℝ (deriv T) s := by
    by_contra hd
    simp [curvature_def, deriv_zero_of_not_differentiableAt hd] at hκ
  have hℓ : 0 < ℓ := Fact.out
  let φ : ℂ →L[ℝ] ℝ := imCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) (conj (deriv T s)))
  have hφ (z : ℂ) : φ z = (conj (deriv T s) * z).im := by simp [φ]
  -- The height `h t = φ (γ t - γ s)` has derivative `φ (τ t)`, whose derivative at `s` is `κ(s)`.
  have hh : deriv (fun t => φ (T t - T s)) = fun u => φ (deriv T u) := funext fun u =>
    (φ.hasFDerivAt.comp_hasDerivAt u ((T.hasDerivAt u).sub_const (T s))).deriv
  have hh' : deriv (fun u => φ (deriv T u)) s = T.curvature s :=
    (φ.hasFDerivAt.comp_hasDerivAt s hd.hasDerivAt).deriv.trans (by rw [hφ, curvature_def])
  have hh₀ : φ (deriv T s) = 0 := by rw [hφ, ← normSq_eq_conj_mul_self, ofReal_im]
  -- If `κ(s) < 0`, the second derivative test makes `s` a local maximum of the height.
  have hmax : IsLocalMax (fun t => φ (T t - T s)) s :=
    isLocalMax_of_deriv_deriv_neg (by rwa [hh, hh']) (by rw [hh]; exact hh₀)
      (φ.continuous.comp (T.continuous.sub continuous_const)).continuousAt
  obtain ⟨t, hts, ht⟩ := (Filter.Eventually.and
    (hmax.filter_mono (nhdsWithin_le_nhds (s := Ioi s))) (Ioo_mem_nhdsGT (by linarith :
      s < s + ℓ))).exists
  have hpos : 0 < φ (T t - T s) := by
    rw [hφ]
    exact T.im_conj_deriv_mul_sub_pos fun h =>
      ht.1.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico ⟨le_rfl, by linarith⟩ ⟨ht.1.le, ht.2⟩).1 h)
  simp only [sub_self, map_zero] at hts
  linarith

/-! ### Operations on tables -/

/-- The reparametrised table `s ↦ γ (s + c)`, the same curve with its origin moved to `γ c`. -/
def shift (c : ℝ) : ConvexTable k ℓ where
  toFun s := T (s + c)
  one_le := T.one_le
  contDiff' := T.contDiff.comp (contDiff_id.add contDiff_const)
  periodic' s := by simp only [add_right_comm s ℓ c, T.periodic _]
  norm_deriv' s := by rw [deriv_comp_add_const, T.norm_deriv]
  left_of_tangent' s t h := by
    rw [deriv_comp_add_const]
    exact T.left_of_tangent' _ _ fun m hm => h m (by rw [← hm]; ring)

@[simp]
theorem shift_apply (c s : ℝ) : T.shift c s = T (s + c) := (rfl)

/-- The unit tangent of the shifted table `γ (· + c)` at `s` is that of `γ` at `s + c`. -/
@[simp]
theorem deriv_shift (c s : ℝ) : deriv (T.shift c) s = deriv T (s + c) :=
  deriv_comp_add_const _ c s

/-- The curvature of the shifted table `γ (· + c)` at `s` is that of `γ` at `s + c`. -/
@[simp]
theorem curvature_shift (c s : ℝ) : (T.shift c).curvature s = T.curvature (s + c) := by
  have h : deriv (T.shift c) = fun s => deriv T (s + c) := funext (T.deriv_shift c)
  rw [curvature_def, curvature_def, h, deriv_comp_add_const]

/-- The image `s ↦ a * γ s + b` of a table under the rotation by the unit complex number `a`
followed by the translation by `b`. -/
def rigidMotion (a : Circle) (b : ℂ) : ConvexTable k ℓ where
  toFun s := a * T s + b
  one_le := T.one_le
  contDiff' := (contDiff_const.mul T.contDiff).add contDiff_const
  periodic' s := by simp only [T.periodic s]
  norm_deriv' s := by
    rw [deriv_add_const, deriv_const_mul _ (T.differentiable s), norm_mul, Circle.norm_coe,
      T.norm_deriv, one_mul]
  left_of_tangent' s t h := by
    rw [deriv_add_const, deriv_const_mul _ (T.differentiable s), add_sub_add_right_eq_sub,
      ← mul_sub, Circle.conj_coe_mul_mul_coe_mul]
    exact T.left_of_tangent' s t h

@[simp]
theorem rigidMotion_apply (a : Circle) (b : ℂ) (s : ℝ) : T.rigidMotion a b s = a * T s + b := (rfl)

/-- The unit tangent of the table `a γ + b` is the unit tangent of `γ` rotated by `a`. -/
@[simp]
theorem deriv_rigidMotion (a : Circle) (b : ℂ) (s : ℝ) :
    deriv (T.rigidMotion a b) s = a * deriv T s :=
  (((T.hasDerivAt s).const_mul (a : ℂ)).add_const b).deriv

/-- A rotation followed by a translation does not change the curvature of a table. -/
@[simp]
theorem curvature_rigidMotion (a : Circle) (b : ℂ) (s : ℝ) :
    (T.rigidMotion a b).curvature s = T.curvature s := by
  have h : deriv (T.rigidMotion a b) = fun s => (a : ℂ) * deriv T s :=
    funext (T.deriv_rigidMotion a b)
  rw [curvature_def, curvature_def, h, deriv_const_mul_field', Circle.conj_coe_mul_mul_coe_mul]

/-- A table of class `C^k` regarded as a table of class `C^j` for `1 ≤ j ≤ k`. -/
def ofLE (hj : 1 ≤ j) (hjk : j ≤ k) : ConvexTable j ℓ where
  toFun := T
  one_le := hj
  contDiff' := T.contDiff.of_le (by exact_mod_cast hjk)
  periodic' := T.periodic
  norm_deriv' := T.norm_deriv
  left_of_tangent' := T.left_of_tangent'

@[simp]
theorem coe_ofLE (hj : 1 ≤ j) (hjk : j ≤ k) : ⇑(T.ofLE hj hjk) = T := (rfl)

/-- Lowering the regularity of a table does not change its curvature. -/
@[simp]
theorem curvature_ofLE (hj : 1 ≤ j) (hjk : j ≤ k) (s : ℝ) :
    (T.ofLE hj hjk).curvature s = T.curvature s :=
  (rfl)

/-- **Orientation is part of a table.** Running through a table backwards, `s ↦ γ (-s)`, never
gives a table, of any regularity: the curve lies to the right of the reversed tangents. -/
theorem coe_ne_comp_neg (T' : ConvexTable j ℓ) : ⇑T' ≠ T ∘ Neg.neg := by
  intro h
  have hℓ : 0 < ℓ := Fact.out
  have hne' : ((0 : ℝ) : AddCircle ℓ) ≠ ((ℓ / 2 : ℝ) : AddCircle ℓ) := fun h' => by
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (p := ℓ)
      ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩).1 h'
    linarith
  have hne : ((0 : ℝ) : AddCircle ℓ) ≠ ((-(ℓ / 2) : ℝ) : AddCircle ℓ) := fun h' =>
    hne' (by simpa using congrArg Neg.neg h')
  have h₁ := T.im_conj_deriv_mul_sub_pos hne
  have h₂ := T'.im_conj_deriv_mul_sub_pos hne'
  have hd : deriv T' 0 = -deriv T 0 := by
    rw [h, comp_def, deriv_comp_neg, neg_zero]
  rw [hd, h] at h₂
  simp only [comp_apply, neg_zero, map_neg, neg_mul, neg_im] at h₂
  linarith

/-! ### The circle -/

attribute [local instance] Complex.finrank_real_complex_fact

/-- The counterclockwise **circle** `s ↦ R exp(i s / R)` of radius `R > 0` and perimeter `2πR`, a
table of class `C^∞`. It is the circle billiard table `TauCeti.StrictConvexBilliardTable.circle`. -/
def circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] : ConvexTable ⊤ (2 * Real.pi * R) where
  toFun := StrictConvexBilliardTable.circle (Real.pos_of_fact_two_pi_mul_pos (R := R))
  one_le := le_top
  contDiff' := StrictConvexBilliardTable.contDiff_circle
  periodic' := by
    simpa using
      (StrictConvexBilliardTable.circle (Real.pos_of_fact_two_pi_mul_pos (R := R))).periodic
  norm_deriv' :=
    (StrictConvexBilliardTable.circle (Real.pos_of_fact_two_pi_mul_pos (R := R))).norm_deriv
  left_of_tangent' s t h := by
    have hR : 0 < R := Real.pos_of_fact_two_pi_mul_pos
    -- This is the `areaForm_pos` field of the circle billiard table.
    rw [← Complex.areaForm]
    refine (StrictConvexBilliardTable.circle hR).areaForm_pos s t fun hts => ?_
    rw [StrictConvexBilliardTable.apply_eq_apply_iff, ← sub_eq_zero, ← AddCircle.coe_sub,
      AddCircle.coe_eq_zero_iff] at hts
    obtain ⟨m, hm⟩ := hts
    exact h m (by rw [← hm, zsmul_eq_mul, StrictConvexBilliardTable.period_circle])

@[simp]
theorem circle_apply (R : ℝ) [Fact (0 < 2 * Real.pi * R)] (s : ℝ) :
    circle R s = circleMap 0 R (s / R) :=
  StrictConvexBilliardTable.circle_apply s

/-- The unit tangent of the circle `s ↦ R exp(i s / R)` is `i exp(i s / R)`. -/
@[simp]
theorem deriv_circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] (s : ℝ) :
    deriv (circle R) s = circleMap 0 1 (s / R) * I :=
  StrictConvexBilliardTable.deriv_circle s

/-- The circle of radius `R` has constant curvature `1 / R`. -/
@[simp]
theorem curvature_circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] (s : ℝ) :
    (circle R).curvature s = R⁻¹ := by
  have hR : R ≠ 0 := Real.pos_of_fact_two_pi_mul_pos.ne'
  -- The unit tangent `i exp(i t / R)` is the point `R exp(i t / R)` multiplied by `i / R`, so it
  -- turns according to `τ' = (i / R) τ`.
  have hd : deriv (circle R) = fun t => I / R * circle R t := funext fun t => by
    rw [deriv_circle, circle_apply, circleMap_zero, circleMap_zero, ofReal_one, one_mul]
    field_simp [ofReal_ne_zero.2 hR]
  have h2 : deriv (deriv (circle R)) s = I / R * deriv (circle R) s := by
    conv_lhs => rw [hd]
    exact congrFun (deriv_const_mul_field' _) s
  rw [curvature_def, h2, mul_left_comm, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq,
    norm_deriv]
  simp

/-! ### Comparison with strictly convex billiard tables -/

/-- A convex table is a strictly convex billiard table, of period `ℓ`, for the standard orientation
of `ℂ`, whose area form is the cross product `(a, b) ↦ Im (conj a * b)`. -/
def toStrictConvexBilliardTable : StrictConvexBilliardTable Complex.orientation where
  toFun := T
  period := ℓ
  period_pos := Fact.out
  periodic := T.periodic
  norm_deriv := T.norm_deriv
  injOn := by simpa using T.injOn_Ico 0
  areaForm_pos s t h := by
    rw [Complex.areaForm]
    exact T.im_conj_deriv_mul_sub_pos fun h' => h (by simpa using congrArg T.periodic.lift h'.symm)

@[simp]
theorem coe_toStrictConvexBilliardTable : ⇑T.toStrictConvexBilliardTable = T := (rfl)

@[simp]
theorem toStrictConvexBilliardTable_period : T.toStrictConvexBilliardTable.period = ℓ := (rfl)

/-- **Injectivity modulo the period.** Two parameters give the same point of a table exactly when
they agree modulo `ℓ`. -/
theorem apply_eq_apply_iff {s t : ℝ} : T s = T t ↔ (s : AddCircle ℓ) = t :=
  T.toStrictConvexBilliardTable.apply_eq_apply_iff

/-- The parametrisation of the boundary of a table by the circle `AddCircle ℓ`, induced by the
`ℓ`-periodic map `γ` (`TauCeti.StrictConvexBilliardTable.circleParam`). -/
def circleParam : AddCircle ℓ → ℂ := T.toStrictConvexBilliardTable.circleParam

@[simp]
theorem circleParam_coe (s : ℝ) : T.circleParam s = T s :=
  T.toStrictConvexBilliardTable.circleParam_coe s

@[simp]
theorem range_circleParam : range T.circleParam = range T :=
  T.toStrictConvexBilliardTable.range_circleParam

theorem circleParam_injective : Injective T.circleParam :=
  T.toStrictConvexBilliardTable.circleParam_injective

theorem continuous_circleParam : Continuous T.circleParam :=
  T.toStrictConvexBilliardTable.continuous_circleParam

/-- A table descends to a homeomorphism of the circle `AddCircle ℓ` onto its image. -/
theorem isClosedEmbedding_circleParam : IsClosedEmbedding T.circleParam :=
  T.toStrictConvexBilliardTable.isClosedEmbedding_circleParam

/-- **The boundary of a table is a Jordan curve.** -/
theorem isJordanCurve_range : IsJordanCurve (range T) :=
  T.toStrictConvexBilliardTable.isJordanCurve_range

/-- The convex table `circle R` is the circle billiard table
`TauCeti.StrictConvexBilliardTable.circle`. -/
@[simp]
theorem toStrictConvexBilliardTable_circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] :
    (circle R).toStrictConvexBilliardTable =
      StrictConvexBilliardTable.circle (Real.pos_of_fact_two_pi_mul_pos (R := R)) := by
  -- Both tables have the parametrization `s ↦ circleMap 0 R (s / R)` and the period `2πR`.
  refine StrictConvexBilliardTable.ext (funext fun s => ?_) ?_
  · exact (circle_apply R s).trans (StrictConvexBilliardTable.circle_apply s).symm
  · exact StrictConvexBilliardTable.period_circle.symm

end ConvexTable

end TauCeti
