/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Calculus.Deriv.Growth

/-!
# The scalar center equation at a degenerate end

Near a degenerate critical point whose linearization has a one-dimensional kernel and a nonzero
quadratic fold coefficient `κ`, the component `β` of a gradient trajectory along the kernel (its
*center amplitude*) satisfies, after reduction to a center manifold, the scalar equation

`β' = -κ β² + o(β²)` as `s → +∞`.

This file shows that, when `κ > 0`, such an amplitude which tends to `0` and is not eventually
zero decays polynomially rather than exponentially, at the exact rate of the model solution
`β(s) = (κ s)⁻¹` of `β' = -κ β²`:

* it is eventually positive (`IsCenterEquationSolution.eventually_pos`); without the
  nonvanishing assumption, it is either eventually zero or eventually positive
  (`IsCenterEquationSolution.eventuallyEq_zero_or_eventually_pos`);
* `s β(s) → κ⁻¹` (`IsCenterEquationSolution.tendsto_mul`), that is `β ~ (κ s)⁻¹`
  (`IsCenterEquationSolution.isEquivalent`), and `β' ~ -(κ s²)⁻¹`
  (`IsCenterEquationSolution.isEquivalent_deriv`);
* hence the two-sided bounds `c s⁻¹ ≤ β(s) ≤ C s⁻¹` and `c s⁻² ≤ |β'(s)| ≤ C s⁻²` for large `s`
  (equivalently with `1 + s` in place of `s`), stated as `IsTheta` relations
  (`IsCenterEquationSolution.isTheta`, `IsCenterEquationSolution.isTheta_deriv`).

The remainder is only assumed to be `o(β²)`, which includes the usual `O(β³)` remainder of a center
manifold reduction since `β → 0` (`Asymptotics.IsBigO.trans_isLittleO`). It may depend on `s`, so
that the transverse components of the trajectory can enter it.

For an autonomous equation `β' = f(β)` with `f(0) = f'(0) = 0` and `f''(0) = -2κ`, every
solution tending to `0` solves the center equation (`TauCeti.isCenterEquationSolution_comp`). If
moreover `κ > 0` and the solution is not eventually zero, the second derivative
`β'' = f'(β) f(β)` is equivalent to `2 (κ s³)⁻¹`, the second derivative of the model solution
(`IsCenterEquationSolution.isEquivalent_comp_mul_comp`), so `β'' =Θ s⁻³`
(`IsCenterEquationSolution.isTheta_comp_mul_comp`).

## Main definitions

* `TauCeti.IsCenterEquationSolution κ β β'`: `β` has derivative `β'` near `+∞`, satisfies
  `β' + κ β² = o(β²)` and tends to `0`.

## Implementation notes

The proof passes to `y = 1 / β`: the equation becomes `y' = κ + o(1)`, so `y(s) / s → κ` by the
mean value inequality (`TauCeti.tendsto_inv_smul_atTop_of_tendsto_deriv`). Positivity comes from
monotonicity: `β' ≤ -(κ / 2) β² ≤ 0` eventually, so `β` decreases to its limit `0`.

## References

* J. Carr, *Applications of Centre Manifold Theory*, Springer, 1981, Chapter 2: the reduced
  equation on a center manifold.
-/

public section

open Filter Topology Asymptotics Set

namespace TauCeti

/-- `β` solves the **scalar center equation** `β' = -κ β² + o(β²)` near `+∞`, with derivative `β'`,
and tends to `0`. This is the equation of the center amplitude of a trajectory that converges to a
degenerate critical point with fold coefficient `κ`. -/
structure IsCenterEquationSolution (κ : ℝ) (β β' : ℝ → ℝ) : Prop where
  /-- `β` has derivative `β'` near `+∞`. -/
  hasDerivAt : ∀ᶠ s in atTop, HasDerivAt β (β' s) s
  /-- The remainder `β' + κ β²` is negligible compared with `β²`. -/
  isLittleO : (fun s ↦ β' s + κ * β s ^ 2) =o[atTop] fun s ↦ β s ^ 2
  /-- `β` tends to `0` at `+∞`. -/
  tendsto : Tendsto β atTop (𝓝 0)

/-- The model solution `β(s) = (κ s)⁻¹` of `β' = -κ β²`. -/
theorem isCenterEquationSolution_inv_mul {κ : ℝ} (hκ : κ ≠ 0) :
    IsCenterEquationSolution κ (fun s ↦ (κ * s)⁻¹) fun s ↦ -(κ * s ^ 2)⁻¹ where
  hasDerivAt := by
    filter_upwards [eventually_ne_atTop 0] with s hs
    convert ((hasDerivAt_id' s).const_mul κ).inv (mul_ne_zero hκ hs) using 1
    field_simp
  isLittleO := by
    refine (isLittleO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop 0] with s hs
    field_simp
    ring
  tendsto := by
    have := tendsto_inv_atTop_zero.const_mul κ⁻¹
    rw [mul_zero] at this
    exact this.congr fun s ↦ (mul_inv κ s).symm

namespace IsCenterEquationSolution

variable {κ : ℝ} {β β' : ℝ → ℝ}

/-- Eventually `β' ≤ -(κ / 2) β²`. -/
private lemma eventually_deriv_le (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ) :
    ∀ᶠ s in atTop, β' s ≤ -(κ / 2) * β s ^ 2 := by
  filter_upwards [h.isLittleO.def (half_pos hκ)] with s hs
  rw [Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, sq_abs] at hs
  linarith [le_abs_self (β' s + κ * β s ^ 2)]

/-- For `κ > 0`, a solution of the center equation is eventually antitone. -/
theorem exists_antitoneOn_Ici (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ) :
    ∃ a, AntitoneOn β (Ici a) := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 (h.hasDerivAt.and (h.eventually_deriv_le hκ))
  refine ⟨a, antitoneOn_of_hasDerivWithinAt_nonpos (f' := β') (convex_Ici a)
    (fun s hs ↦ (ha s hs).1.continuousAt.continuousWithinAt) ?_ ?_⟩ <;> rw [interior_Ici]
  · exact fun s hs ↦ (ha s hs.le).1.hasDerivWithinAt
  · intro s hs
    nlinarith [(ha s hs.le).2, sq_nonneg (β s)]

/-- For `κ > 0`, a solution of the center equation is eventually nonnegative: it decreases to its
limit `0`. -/
theorem eventually_nonneg (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ) :
    ∀ᶠ s in atTop, 0 ≤ β s := by
  obtain ⟨a, ha⟩ := h.exists_antitoneOn_Ici hκ
  filter_upwards [eventually_ge_atTop a] with s hs
  by_contra! hneg
  obtain ⟨t, ht, hst⟩ :=
    ((h.tendsto.eventually (lt_mem_nhds hneg)).and (eventually_ge_atTop s)).exists
  exact absurd ht (not_lt.2 (ha (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst))

/-- For `κ > 0`, a solution of the center equation is either eventually zero or eventually
positive. -/
theorem eventuallyEq_zero_or_eventually_pos (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ) :
    β =ᶠ[atTop] 0 ∨ ∀ᶠ s in atTop, 0 < β s := by
  obtain ⟨a, ha⟩ := h.exists_antitoneOn_Ici hκ
  obtain ⟨b, hb⟩ := eventually_atTop.1 (h.eventually_nonneg hκ)
  by_cases hz : ∃ s ≥ max a b, β s = 0
  · -- Once `β` vanishes it stays at `0`, being antitone and nonnegative.
    obtain ⟨s, hs, hs0⟩ := hz
    refine Or.inl ?_
    filter_upwards [eventually_ge_atTop s] with t ht
    have hat : a ≤ s := (le_max_left a b).trans hs
    have hts := ha (mem_Ici.2 hat) (mem_Ici.2 (hat.trans ht)) ht
    rw [hs0] at hts
    exact le_antisymm hts (hb t (((le_max_right a b).trans hs).trans ht))
  · push Not at hz
    refine Or.inr ?_
    filter_upwards [eventually_ge_atTop (max a b)] with s hs
    exact (hb s ((le_max_right a b).trans hs)).lt_of_ne (hz s hs).symm

/-- For `κ > 0`, a solution of the center equation that is not eventually zero is eventually
positive. -/
theorem eventually_pos (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ)
    (hne : ¬β =ᶠ[atTop] 0) : ∀ᶠ s in atTop, 0 < β s :=
  (h.eventuallyEq_zero_or_eventually_pos hκ).resolve_left hne

/-- **Polynomial decay at the exact rate.** For `κ > 0`, a solution of the center equation that is
not eventually zero satisfies `s β(s) → κ⁻¹`. -/
theorem tendsto_mul (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ) (hne : ¬β =ᶠ[atTop] 0) :
    Tendsto (fun s ↦ s * β s) atTop (𝓝 κ⁻¹) := by
  have hpos := h.eventually_pos hκ hne
  -- The reciprocal `y = 1 / β` satisfies `y' = κ - (β' + κ β²) / β² = κ + o(1)`.
  have hinv : ∀ᶠ s in atTop,
      HasDerivAt (fun s ↦ (β s)⁻¹) (κ - (β' s + κ * β s ^ 2) / β s ^ 2) s := by
    filter_upwards [h.hasDerivAt, hpos] with s hs hs0
    convert hs.inv hs0.ne' using 1
    field_simp
    ring
  have hlim : Tendsto (fun s ↦ κ - (β' s + κ * β s ^ 2) / β s ^ 2) atTop (𝓝 κ) := by
    simpa using h.isLittleO.tendsto_div_nhds_zero.const_sub κ
  refine ((tendsto_inv_smul_atTop_of_tendsto_deriv hinv hlim).inv₀ hκ.ne').congr' ?_
  filter_upwards [hpos] with s _
  simp [mul_comm]

/-- For `κ > 0`, a solution of the center equation that is not eventually zero is asymptotically
equivalent to the model solution `(κ s)⁻¹`. -/
theorem isEquivalent (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ) (hne : ¬β =ᶠ[atTop] 0) :
    β ~[atTop] fun s ↦ (κ * s)⁻¹ := by
  refine isEquivalent_of_tendsto_one ?_
  have := (h.tendsto_mul hκ hne).const_mul κ
  rw [mul_inv_cancel₀ hκ.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with s _
  simp only [Pi.div_apply, div_inv_eq_mul]
  ring

/-- For `κ > 0`, the derivative of a solution of the center equation that is not eventually zero
is asymptotically equivalent to the derivative `-(κ s²)⁻¹` of the model solution. -/
theorem isEquivalent_deriv (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ)
    (hne : ¬β =ᶠ[atTop] 0) : β' ~[atTop] fun s ↦ -(κ * s ^ 2)⁻¹ := by
  -- First `β' ~ -κ β²`, since the remainder is `o(β²)`.
  have h₁ : β' ~[atTop] fun s ↦ -κ * β s ^ 2 :=
    (h.isLittleO.trans_isBigO
      ((isTheta_const_mul_left (neg_ne_zero.2 hκ.ne')).2 (isTheta_refl _ _)).2).congr_left
      fun s ↦ by simp
  have h₂ : (fun s ↦ -κ * β s ^ 2) ~[atTop] fun s ↦ -κ * (κ * s)⁻¹ ^ 2 :=
    (IsEquivalent.refl (u := fun _ ↦ -κ)).mul ((h.isEquivalent hκ hne).pow 2)
  refine (h₁.trans h₂).congr_right ?_
  filter_upwards [eventually_ne_atTop 0] with s hs
  field_simp

/-- **Two-sided polynomial bounds.** For `κ > 0`, a solution of the center equation that is not
eventually zero satisfies `β =Θ s⁻¹` at `+∞`: `c / s ≤ β(s) ≤ C / s` for large `s`. -/
theorem isTheta (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ) (hne : ¬β =ᶠ[atTop] 0) :
    β =Θ[atTop] fun s ↦ s⁻¹ :=
  (h.isEquivalent hκ hne).isTheta.trans <|
    EventuallyEq.trans_isTheta (f₂ := fun s ↦ κ⁻¹ * s⁻¹) (.of_forall fun s ↦ mul_inv κ s)
      ((isTheta_const_mul_left (inv_ne_zero hκ.ne')).2 (isTheta_refl _ _))

/-- **Two-sided polynomial bounds on the derivative.** For `κ > 0`, the derivative of a solution
of the center equation that is not eventually zero satisfies `β' =Θ (s²)⁻¹` at `+∞`. -/
theorem isTheta_deriv (h : IsCenterEquationSolution κ β β') (hκ : 0 < κ)
    (hne : ¬β =ᶠ[atTop] 0) : β' =Θ[atTop] fun s ↦ (s ^ 2)⁻¹ :=
  (h.isEquivalent_deriv hκ hne).isTheta.trans <|
    EventuallyEq.trans_isTheta (f₂ := fun s ↦ -κ⁻¹ * (s ^ 2)⁻¹)
      (.of_forall fun s ↦ by simp only [mul_inv, neg_mul])
      ((isTheta_const_mul_left (neg_ne_zero.2 (inv_ne_zero hκ.ne'))).2 (isTheta_refl _ _))

end IsCenterEquationSolution

/-! ### The autonomous center equation -/

section Autonomous

variable {κ : ℝ} {β f f' : ℝ → ℝ}

/-- **The autonomous center equation.** Let `f` be differentiable near `0` with `f(0) = 0`,
`f'(0) = 0` and `f''(0) = -2κ`. A solution `β` of `β' = f(β)` that tends to `0` at `+∞` solves the
center equation `β' = -κ β² + o(β²)`. -/
theorem isCenterEquationSolution_comp (hf : ∀ᶠ x in 𝓝 0, HasDerivAt f (f' x) x) (hf₀ : f 0 = 0)
    (hf'₀ : f' 0 = 0) (hf' : HasDerivAt f' (-(2 * κ)) 0)
    (hβ : ∀ᶠ s in atTop, HasDerivAt β (f (β s)) s) (hlim : Tendsto β atTop (𝓝 0)) :
    IsCenterEquationSolution κ β fun s ↦ f (β s) where
  hasDerivAt := hβ
  isLittleO := by
    -- `f x + κ x²` has derivative `f' x + 2 κ x = o(x)`, so it is `o(x²)`.
    have hg : ∀ᶠ x in 𝓝 0, HasDerivAt (fun x ↦ f x + κ * x ^ 2) (f' x + 2 * κ * x) x :=
      hf.mono fun x hx ↦ by
        convert hx.add ((hasDerivAt_pow 2 x).const_mul κ) using 1
        ring
    have hg' : (fun x ↦ f' x + 2 * κ * x) =o[𝓝 0] fun x ↦ (x - 0) ^ 1 := by
      simpa [hf'₀, sub_eq_add_neg, mul_comm] using (hasDerivAt_iff_isLittleO.1 hf')
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg
    have h₀ : (0 : ℝ) ∈ Metric.ball 0 δ := Metric.mem_ball_self hδ
    have hnhds := Metric.isOpen_ball.nhdsWithin_eq h₀
    have := (convex_ball (0 : ℝ) δ).isLittleO_pow_succ_real h₀
      (fun x hx ↦ (hball x hx).hasDerivWithinAt) (by rwa [hnhds])
    rw [hnhds] at this
    simp only [hf₀, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero] at this
    exact this.comp_tendsto hlim
  tendsto := hlim

namespace IsCenterEquationSolution

/-- **Second derivative at the exact rate.** Let `κ > 0`, and let `β` be a solution of the
autonomous center equation `β' = f(β)`, not eventually zero, where `f'(0) = 0` and
`f''(0) = -2κ`. Then `f'(β) f(β)`, which is `β''` by the chain rule when `f` has derivative `f'`
near `0`, is asymptotically equivalent to `2 (κ s³)⁻¹`, the second derivative of the model
solution `(κ s)⁻¹`. -/
theorem isEquivalent_comp_mul_comp (h : IsCenterEquationSolution κ β fun s ↦ f (β s))
    (hκ : 0 < κ) (hne : ¬β =ᶠ[atTop] 0) (hf'₀ : f' 0 = 0) (hf' : HasDerivAt f' (-(2 * κ)) 0) :
    (fun s ↦ f' (β s) * f (β s)) ~[atTop] fun s ↦ 2 * (κ * s ^ 3)⁻¹ := by
  -- `f' x ~ -2 κ x` at `0`, hence `f'(β) ~ -2 κ β ~ -2 κ (κ s)⁻¹`.
  have hf'eq : f' ~[𝓝 0] fun x ↦ -(2 * κ) * x := by
    simpa [hf'₀, Function.comp_def, mul_comm] using
      hf'.isEquivalent_sub (neg_ne_zero.2 (by positivity))
  have h₁ : (fun s ↦ f' (β s)) ~[atTop] fun s ↦ -(2 * κ) * (κ * s)⁻¹ :=
    (hf'eq.comp_tendsto h.tendsto).trans
      ((IsEquivalent.refl (u := fun _ ↦ -(2 * κ))).mul (h.isEquivalent hκ hne))
  refine (h₁.mul (h.isEquivalent_deriv hκ hne)).congr_right ?_
  filter_upwards [eventually_ne_atTop 0] with s hs
  simp only [Pi.mul_apply]
  field_simp

/-- **Two-sided polynomial bounds on the second derivative.** Under the hypotheses of
`IsCenterEquationSolution.isEquivalent_comp_mul_comp`, `f'(β) f(β) =Θ (s³)⁻¹` at `+∞`. -/
theorem isTheta_comp_mul_comp (h : IsCenterEquationSolution κ β fun s ↦ f (β s))
    (hκ : 0 < κ) (hne : ¬β =ᶠ[atTop] 0) (hf'₀ : f' 0 = 0) (hf' : HasDerivAt f' (-(2 * κ)) 0) :
    (fun s ↦ f' (β s) * f (β s)) =Θ[atTop] fun s ↦ (s ^ 3)⁻¹ :=
  (h.isEquivalent_comp_mul_comp hκ hne hf'₀ hf').isTheta.trans <|
    EventuallyEq.trans_isTheta (f₂ := fun s ↦ 2 * κ⁻¹ * (s ^ 3)⁻¹)
      (.of_forall fun s ↦ by simp only [mul_inv, mul_assoc])
      ((isTheta_const_mul_left (mul_ne_zero two_ne_zero (inv_ne_zero hκ.ne'))).2
        (isTheta_refl _ _))

end IsCenterEquationSolution

end Autonomous

end TauCeti
