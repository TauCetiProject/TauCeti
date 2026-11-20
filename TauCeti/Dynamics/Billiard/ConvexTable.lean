/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Dynamics.Billiard.NextCollision
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Calculus.PeriodicDeriv

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
  `γ` descends to a homeomorphism of `AddCircle ℓ` onto its image, which is a Jordan curve.
* `TauCeti.ConvexTable.deriv_deriv`: the unit tangent of a table satisfies `τ' = i κ τ`.
* `TauCeti.ConvexTable.curvature_nonneg`: the curvature of a table is nonnegative.
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

/-- **Injectivity modulo the period.** Two parameters give the same point of a table exactly when
they agree modulo `ℓ`. -/
theorem apply_eq_apply_iff {s t : ℝ} : T s = T t ↔ (s : AddCircle ℓ) = t := by
  refine ⟨fun hst => by_contra fun h => ?_, fun hst => ?_⟩
  · simpa [hst] using T.im_conj_deriv_mul_sub_pos h
  · obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff ℓ (x := s - t)).1
      (by rw [AddCircle.coe_sub, hst, sub_self])
    rw [show s = t + m • ℓ by rw [hm]; ring, T.periodic.zsmul m]

/-- A table is injective on every half-open interval of length `ℓ`. -/
theorem injOn_Ico (a : ℝ) : InjOn T (Ico a (a + ℓ)) := fun _ hs _ ht hst =>
  (AddCircle.coe_eq_coe_iff_of_mem_Ico hs ht).1 (T.apply_eq_apply_iff.1 hst)

/-! ### The parametrisation by the circle -/

/-- The parametrisation of the boundary of a table by the circle `AddCircle ℓ`, induced by the
`ℓ`-periodic map `γ`. -/
def circleParam : AddCircle ℓ → ℂ := T.periodic.lift

@[simp]
theorem circleParam_coe (s : ℝ) : T.circleParam s = T s := T.periodic.lift_coe s

@[simp]
theorem range_circleParam : range T.circleParam = range T := by
  rw [← QuotientAddGroup.mk_surjective.range_comp]
  exact congrArg range (funext T.circleParam_coe)

theorem injective_circleParam : Injective T.circleParam := by
  intro x y hxy
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact T.apply_eq_apply_iff.1 (by simpa using hxy)

theorem continuous_circleParam : Continuous T.circleParam :=
  (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 <| by
    simpa only [comp_def, circleParam_coe] using T.continuous

/-- A table descends to a homeomorphism of the circle `AddCircle ℓ` onto its image. -/
theorem isClosedEmbedding_circleParam : IsClosedEmbedding T.circleParam :=
  T.continuous_circleParam.isClosedEmbedding T.injective_circleParam

/-- **The boundary of a table is a Jordan curve.** -/
theorem isJordanCurve_range : IsJordanCurve (range T) := by
  have huniv : IsJordanCurve (univ : Set (AddCircle ℓ)) :=
    isJordanCurve_iff.2
      ⟨(Homeomorph.Set.univ (AddCircle ℓ)).trans
        (AddCircle.homeomorphCircle (Fact.out : 0 < ℓ).ne')⟩
  simpa using huniv.image T.continuous_circleParam.continuousOn T.injective_circleParam.injOn

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

/-- **The curvature of a table is nonnegative.** The height `τ(s) × (γ t - γ s)` of the curve
above the tangent line at `γ s` vanishes at `t = s` and is positive at every other nearby `t`, so
`s` is a local minimum of it; its second derivative there is `κ(s)`. -/
theorem curvature_nonneg (s : ℝ) : 0 ≤ T.curvature s := by
  by_contra! hκ
  have hd : DifferentiableAt ℝ (deriv T) s := by
    by_contra hd
    simp [curvature_def, deriv_zero_of_not_differentiableAt hd] at hκ
  have hℓ : 0 < ℓ := Fact.out
  let φ : ℂ →L[ℝ] ℝ := imCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) (conj (deriv T s)))
  have hφ (z : ℂ) : φ z = (conj (deriv T s) * z).im := rfl
  -- The height `h t = φ (γ t - γ s)` has derivative `φ (τ t)`, whose derivative at `s` is `κ(s)`.
  have hh : deriv (fun t => φ (T t - T s)) = fun u => φ (deriv T u) := funext fun u =>
    (φ.hasFDerivAt.comp_hasDerivAt u ((T.hasDerivAt u).sub_const (T s))).deriv
  have hh' : deriv (fun u => φ (deriv T u)) s = T.curvature s :=
    (φ.hasFDerivAt.comp_hasDerivAt s hd.hasDerivAt).deriv
  have hh₀ : φ (deriv T s) = 0 := by rw [hφ, ← normSq_eq_conj_mul_self, ofReal_im]
  -- If `κ(s) < 0`, the second derivative test makes `s` a local maximum of the height.
  have hmax : IsLocalMax (fun t => φ (T t - T s)) s :=
    isLocalMax_of_deriv_deriv_neg (by rwa [hh, hh']) (by rw [hh]; exact hh₀)
      (φ.continuous.comp (T.continuous.sub continuous_const)).continuousAt
  obtain ⟨t, hts, ht⟩ := (Filter.Eventually.and
    (hmax.filter_mono (nhdsWithin_le_nhds (s := Ioi s))) (Ioo_mem_nhdsGT (by linarith :
      s < s + ℓ))).exists
  have hpos : 0 < φ (T t - T s) := T.im_conj_deriv_mul_sub_pos fun h =>
    ht.1.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico ⟨le_rfl, by linarith⟩ ⟨ht.1.le, ht.2⟩).1 h)
  have hts' : φ (T t - T s) ≤ φ (T s - T s) := hts
  rw [sub_self, map_zero] at hts'
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
      ← mul_sub, map_mul, mul_mul_mul_comm, ← normSq_eq_conj_mul_self, Circle.normSq_coe,
      ofReal_one, one_mul]
    exact T.left_of_tangent' s t h

@[simp]
theorem rigidMotion_apply (a : Circle) (b : ℂ) (s : ℝ) : T.rigidMotion a b s = a * T s + b := (rfl)

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

/-- **Orientation is part of a table.** Running through a table backwards, `s ↦ γ (-s)`, never
gives a table, of any regularity: the curve lies to the right of the reversed tangents. -/
theorem coe_ne_comp_neg (T' : ConvexTable j ℓ) : ⇑T' ≠ T ∘ Neg.neg := by
  intro h
  have hℓ : 0 < ℓ := Fact.out
  have hne : ((0 : ℝ) : AddCircle ℓ) ≠ ((-(ℓ / 2) : ℝ) : AddCircle ℓ) := fun h' => by
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := -(ℓ / 2)) (p := ℓ)
      ⟨by linarith, by linarith⟩ ⟨le_rfl, by linarith⟩).1 h'
    linarith
  have hne' : ((0 : ℝ) : AddCircle ℓ) ≠ ((ℓ / 2 : ℝ) : AddCircle ℓ) := fun h' => by
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (p := ℓ)
      ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩).1 h'
    linarith
  have h₁ := T.im_conj_deriv_mul_sub_pos hne
  have h₂ := T'.im_conj_deriv_mul_sub_pos hne'
  have hd : deriv T' 0 = -deriv T 0 := by
    rw [h, show (T ∘ Neg.neg : ℝ → ℂ) = fun x => T (-x) from rfl, deriv_comp_neg, neg_zero]
  rw [hd, h] at h₂
  simp only [comp_apply, neg_zero, map_neg, neg_mul, neg_im] at h₂
  linarith

/-! ### The circle -/

/-- The unit tangent `i exp(i s / R)` of the circle `s ↦ R exp(i s / R)`. -/
private theorem deriv_circle_aux {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    deriv (fun s : ℝ => (R : ℂ) * exp ((s / R : ℝ) * I)) s = I * exp ((s / R : ℝ) * I) := by
  refine ((((hasDerivAt_id s).div_const R).ofReal_comp.mul_const I).cexp.const_mul
    (R : ℂ)).deriv.trans ?_
  simp only [id, ofReal_div, ofReal_one]
  field_simp [ofReal_ne_zero.2 hR]

/-- The height of the point of parameter `t` of the circle `s ↦ R exp(i s / R)` above the tangent
line at the point of parameter `s`. -/
private theorem im_circle_aux (R s t : ℝ) :
    (conj (I * exp ((s / R : ℝ) * I)) * (R * exp ((t / R : ℝ) * I) - R * exp ((s / R : ℝ) * I))).im
      = R * (1 - Real.cos ((t - s) / R)) := by
  rw [sub_div, Real.cos_sub]
  generalize t / R = a
  generalize s / R = b
  simp [mul_im, mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  linear_combination R * Real.sin_sq_add_cos_sq b

/-- The counterclockwise **circle** `s ↦ R exp(i s / R)` of radius `R > 0` and perimeter `2πR`, a
table of class `C^∞`: the defining quantity is `R (1 - cos ((t - s) / R))`. -/
def circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] : ConvexTable ⊤ (2 * Real.pi * R) :=
  have hR : 0 < R := pos_of_mul_pos_right (Fact.out : 0 < 2 * Real.pi * R) Real.two_pi_pos.le
  { toFun s := R * exp ((s / R : ℝ) * I)
    one_le := le_top
    contDiff' := contDiff_const.mul <| contDiff_exp.comp <|
      (ofRealCLM.contDiff.comp (contDiff_id.div_const R)).mul contDiff_const
    periodic' s := by
      simp only
      rw [add_div, mul_div_cancel_right₀ _ hR.ne', ofReal_add, add_mul, exp_add,
        ofReal_mul, ofReal_ofNat, exp_two_pi_mul_I, mul_one]
    norm_deriv' s := by
      rw [deriv_circle_aux hR.ne', norm_mul, norm_I, one_mul, norm_exp_ofReal_mul_I]
    left_of_tangent' s t h := by
      rw [deriv_circle_aux hR.ne', im_circle_aux]
      refine mul_pos hR (sub_pos.2 (lt_of_le_of_ne (Real.cos_le_one _) fun hc => ?_))
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hc
      refine h n ?_
      rw [eq_div_iff hR.ne'] at hn
      rw [← hn]
      ring }

@[simp]
theorem circle_apply (R : ℝ) [Fact (0 < 2 * Real.pi * R)] (s : ℝ) :
    circle R s = R * exp ((s / R : ℝ) * I) := (rfl)

/-- The circle of radius `R` has constant curvature `1 / R`. -/
@[simp]
theorem curvature_circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] (s : ℝ) :
    (circle R).curvature s = R⁻¹ := by
  have hR : R ≠ 0 := by rintro rfl; simpa using (Fact.out : 0 < 2 * Real.pi * 0)
  have hd : deriv (circle R) = fun s => I * exp ((s / R : ℝ) * I) := by
    have hc : ⇑(circle R) = fun s : ℝ => (R : ℂ) * exp ((s / R : ℝ) * I) :=
      funext (circle_apply R)
    rw [hc]
    exact funext (deriv_circle_aux hR)
  have h := (((hasDerivAt_id s).div_const R).ofReal_comp.mul_const I).cexp.const_mul I
  simp only [id] at h
  rw [curvature_def, hd, h.deriv]
  beta_reduce
  generalize s / R = b
  simp [mul_im, mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  linear_combination R⁻¹ * Real.sin_sq_add_cos_sq b

/-! ### Comparison with strictly convex billiard tables -/

attribute [local instance] Complex.finrank_real_complex_fact

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
    exact T.im_conj_deriv_mul_sub_pos fun h' => h (T.apply_eq_apply_iff.2 h'.symm)

@[simp]
theorem coe_toStrictConvexBilliardTable : ⇑T.toStrictConvexBilliardTable = T := (rfl)

@[simp]
theorem toStrictConvexBilliardTable_period : T.toStrictConvexBilliardTable.period = ℓ := (rfl)

end ConvexTable

end TauCeti
