/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The explicit error predicate `a = b + O*(e)`

In the explicit literature of analytic number theory, `a = b + O*(e)` means that `a` differs
from `b` by at most `e` in absolute value: unlike Landau's `O`, the error `e` is a displayed real
quantity and no constant is implied. This file defines the predicate `TauCeti.BigOStar a b e`,
which is `‖a - b‖ ≤ e` for `a b` in a seminormed additive group, and its pointwise form
`TauCeti.BigOStarOn f g h S`, which is "`f = g + O*(h)` on `S`", and develops the calculus in
which explicit error terms are combined: errors add under transitivity, addition and finite
sums, scale by the norm of a scalar, pass to norms, and integrate.

The predicate is a statement, never an existential: a negative error is never admissible, and the
bound is absolute rather than relative. In a commutative group it says that `a` lies in the closed
ball `Metric.closedBall b e` (`TauCeti.bigOStar_iff_mem_closedBall`); the separate name keeps the
error, rather than the centre, as the quantity that explicit statements display and combine.

## Main declarations

* `TauCeti.BigOStar`: `a = b + O*(e)`, that is `‖a - b‖ ≤ e`.
* `TauCeti.BigOStar.nonneg`, `TauCeti.bigOStar_self_iff`: an error is nonnegative, and
  `a = a + O*(e)` exactly when `0 ≤ e`.
* `TauCeti.bigOStar_comm`, `TauCeti.BigOStar.trans`, `TauCeti.BigOStar.weaken`: symmetry,
  transitivity with added errors, and enlarging the error.
* `TauCeti.BigOStar.add`, `TauCeti.BigOStar.sub`, `TauCeti.BigOStar.sum`,
  `TauCeti.BigOStar.smul`: the errors of sums and finite sums add, and a scalar multiplies the
  error by its norm.
* `TauCeti.BigOStar.norm`, `TauCeti.BigOStar.norm_le`, `TauCeti.BigOStar.sub_le_norm`: the norms
  satisfy `‖a‖ = ‖b‖ + O*(e)`.
* `TauCeti.bigOStar_iff_sub_le_and_le_add`: on `ℝ`, `a = b + O*(e)` iff `b - e ≤ a ≤ b + e`.
* `TauCeti.bigOStar_iff_dist`, `TauCeti.bigOStar_iff_mem_closedBall`: the metric readings.
* `TauCeti.BigOStarOn`: `f = g + O*(h)` on a set `S`.
* `TauCeti.bigOStar_integral`, `TauCeti.BigOStarOn.setIntegral`: integrating an explicit error
  term gives an explicit error term, `∫_S f = ∫_S g + O*(∫_S h)`.

## References

The notation `O*` and its reading `‖a - b‖ ≤ e` are those of the explicit literature, for instance:

* H. Kadiri, *Une région explicite sans zéros pour la fonction ζ de Riemann*, Acta Arith. 117
  (2005), 303–339;
* O. Ramaré, *An explicit density estimate for Dirichlet L-series*, Math. Comp. 85 (2016),
  325–356;
* O. Ramaré, *Excursions in Multiplicative Number Theory*, Birkhäuser (2022), §1.
-/

public section

open MeasureTheory

namespace TauCeti

variable {ι α E 𝕜 : Type*}

section SeminormedAddGroup

variable [SeminormedAddGroup E] {a b c : E} {e e₁ e₂ e' : ℝ}

/-- `BigOStar a b e`, written `a = b + O*(e)` in the explicit literature: `a` equals `b` up to an
error of norm at most `e`, that is `‖a - b‖ ≤ e`. The error `e` is a displayed real number; in
particular a negative `e` is never admissible, and the error is absolute, not relative to `b`. -/
def BigOStar (a b : E) (e : ℝ) : Prop :=
  ‖a - b‖ ≤ e

/-- The defining inequality of `a = b + O*(e)`. -/
theorem bigOStar_iff : BigOStar a b e ↔ ‖a - b‖ ≤ e :=
  Iff.rfl

/-- On `ℝ`, `a = b + O*(e)` iff `b - e ≤ a ≤ b + e`. -/
theorem bigOStar_iff_sub_le_and_le_add {a b e : ℝ} :
    BigOStar a b e ↔ b - e ≤ a ∧ a ≤ b + e := by
  rw [bigOStar_iff, Real.norm_eq_abs, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- An explicit error is nonnegative. -/
theorem BigOStar.nonneg (h : BigOStar a b e) : 0 ≤ e :=
  (norm_nonneg _).trans h

/-- `a = a + O*(e)` holds exactly for the nonnegative errors `e`. -/
@[simp]
theorem bigOStar_self_iff : BigOStar a a e ↔ 0 ≤ e := by
  simp [bigOStar_iff]

/-- `a = 0 + O*(e)` says that `‖a‖ ≤ e`. -/
@[simp]
theorem bigOStar_zero_right_iff : BigOStar a 0 e ↔ ‖a‖ ≤ e := by
  rw [bigOStar_iff, sub_zero]

/-- Every element equals itself up to any nonnegative error. -/
theorem BigOStar.refl (a : E) (he : 0 ≤ e) : BigOStar a a e :=
  bigOStar_self_iff.2 he

/-- Symmetry: `a = b + O*(e)` iff `b = a + O*(e)`. -/
theorem bigOStar_comm : BigOStar a b e ↔ BigOStar b a e := by
  rw [bigOStar_iff, bigOStar_iff, norm_sub_rev]

/-- Symmetry: from `a = b + O*(e)` follows `b = a + O*(e)`. -/
theorem BigOStar.symm (h : BigOStar a b e) : BigOStar b a e :=
  bigOStar_comm.1 h

/-- Transitivity: from `a = b + O*(e₁)` and `b = c + O*(e₂)` follows `a = c + O*(e₁ + e₂)`. -/
theorem BigOStar.trans (h₁ : BigOStar a b e₁) (h₂ : BigOStar b c e₂) :
    BigOStar a c (e₁ + e₂) :=
  (norm_sub_le_norm_sub_add_norm_sub a b c).trans (add_le_add h₁ h₂)

/-- Monotonicity: an explicit error may be enlarged. -/
theorem BigOStar.weaken (h : BigOStar a b e) (he : e ≤ e') : BigOStar a b e' :=
  le_trans h he

/-- From `a = b + O*(e)` follows `‖a‖ ≤ ‖b‖ + e`. -/
theorem BigOStar.norm_le (h : BigOStar a b e) : ‖a‖ ≤ ‖b‖ + e :=
  (norm_le_norm_add_norm_sub' a b).trans (add_le_add_right h _)

/-- From `a = b + O*(e)` follows `‖b‖ - e ≤ ‖a‖`. -/
theorem BigOStar.sub_le_norm (h : BigOStar a b e) : ‖b‖ - e ≤ ‖a‖ :=
  sub_le_iff_le_add.2 h.symm.norm_le

/-- The norms satisfy `‖a‖ = ‖b‖ + O*(e)` whenever `a = b + O*(e)`. -/
theorem BigOStar.norm (h : BigOStar a b e) : BigOStar ‖a‖ ‖b‖ e :=
  bigOStar_iff_sub_le_and_le_add.2 ⟨h.sub_le_norm, h.norm_le⟩

end SeminormedAddGroup

/-- In a normed additive group, `a = b + O*(0)` iff `a = b`. -/
@[simp]
theorem bigOStar_zero_iff [NormedAddGroup E] {a b : E} : BigOStar a b 0 ↔ a = b := by
  rw [bigOStar_iff, norm_le_zero_iff, sub_eq_zero]

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E] {a a₁ a₂ b b₁ b₂ : E} {e e₁ e₂ : ℝ}

/-- `a = b + O*(e)` says that `a` lies within distance `e` of `b`. -/
theorem bigOStar_iff_dist : BigOStar a b e ↔ dist a b ≤ e := by
  rw [bigOStar_iff, dist_eq_norm_sub]

/-- `a = b + O*(e)` says that `a` lies in the closed ball of radius `e` about `b`. -/
theorem bigOStar_iff_mem_closedBall : BigOStar a b e ↔ a ∈ Metric.closedBall b e := by
  rw [bigOStar_iff, mem_closedBall_iff_norm]

/-- Negation preserves explicit errors: `-a = -b + O*(e)` iff `a = b + O*(e)`. -/
@[simp]
theorem bigOStar_neg_neg_iff : BigOStar (-a) (-b) e ↔ BigOStar a b e := by
  rw [bigOStar_iff, bigOStar_iff, neg_sub_neg, norm_sub_rev]

/-- Additivity: from `a₁ = b₁ + O*(e₁)` and `a₂ = b₂ + O*(e₂)` follows
`a₁ + a₂ = b₁ + b₂ + O*(e₁ + e₂)`. -/
theorem BigOStar.add (h₁ : BigOStar a₁ b₁ e₁) (h₂ : BigOStar a₂ b₂ e₂) :
    BigOStar (a₁ + a₂) (b₁ + b₂) (e₁ + e₂) := by
  rw [bigOStar_iff, add_sub_add_comm]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

/-- From `a₁ = b₁ + O*(e₁)` and `a₂ = b₂ + O*(e₂)` follows
`a₁ - a₂ = b₁ - b₂ + O*(e₁ + e₂)`: errors add under subtraction too. -/
theorem BigOStar.sub (h₁ : BigOStar a₁ b₁ e₁) (h₂ : BigOStar a₂ b₂ e₂) :
    BigOStar (a₁ - a₂) (b₁ - b₂) (e₁ + e₂) := by
  simpa only [sub_eq_add_neg] using h₁.add (bigOStar_neg_neg_iff.2 h₂)

/-- Additivity for a finite family: if `a i = b i + O*(e i)` for each `i ∈ s`, then
`∑ i ∈ s, a i = ∑ i ∈ s, b i + O*(∑ i ∈ s, e i)`. -/
theorem BigOStar.sum {s : Finset ι} {a b : ι → E} {e : ι → ℝ}
    (h : ∀ i ∈ s, BigOStar (a i) (b i) (e i)) :
    BigOStar (∑ i ∈ s, a i) (∑ i ∈ s, b i) (∑ i ∈ s, e i) := by
  rw [bigOStar_iff, ← Finset.sum_sub_distrib]
  exact norm_sum_le_of_le s h

/-- Scaling: from `a = b + O*(e)` follows `c • a = c • b + O*(‖c‖ * e)`. -/
theorem BigOStar.smul [SeminormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (c : 𝕜)
    (h : BigOStar a b e) : BigOStar (c • a) (c • b) (‖c‖ * e) := by
  rw [bigOStar_iff, ← smul_sub]
  exact (norm_smul_le c _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg c))

end SeminormedAddCommGroup

section Pointwise

variable [SeminormedAddGroup E] {f g k : α → E} {h h₁ h₂ h' : α → ℝ} {S T : Set α}

/-- `BigOStarOn f g h S`, written "`f = g + O*(h)` on `S`": for every `x ∈ S`,
`f x = g x + O*(h x)`, that is `‖f x - g x‖ ≤ h x`. -/
def BigOStarOn (f g : α → E) (h : α → ℝ) (S : Set α) : Prop :=
  ∀ x ∈ S, BigOStar (f x) (g x) (h x)

/-- The defining property of `f = g + O*(h)` on `S`. -/
theorem bigOStarOn_iff : BigOStarOn f g h S ↔ ∀ x ∈ S, BigOStar (f x) (g x) (h x) :=
  Iff.rfl

/-- On a point of `S`, `f = g + O*(h)` on `S` gives `f x = g x + O*(h x)`. -/
theorem BigOStarOn.bigOStar (hfg : BigOStarOn f g h S) {x : α} (hx : x ∈ S) :
    BigOStar (f x) (g x) (h x) :=
  hfg x hx

/-- `f = g + O*(h)` holds on a subset of a set where it holds. -/
theorem BigOStarOn.mono (hfg : BigOStarOn f g h S) (hTS : T ⊆ S) : BigOStarOn f g h T :=
  fun x hx ↦ hfg x (hTS hx)

/-- Symmetry: from `f = g + O*(h)` on `S` follows `g = f + O*(h)` on `S`. -/
theorem BigOStarOn.symm (hfg : BigOStarOn f g h S) : BigOStarOn g f h S :=
  fun x hx ↦ (hfg x hx).symm

/-- Transitivity: from `f = g + O*(h₁)` and `g = k + O*(h₂)` on `S` follows
`f = k + O*(h₁ + h₂)` on `S`. -/
theorem BigOStarOn.trans (hfg : BigOStarOn f g h₁ S) (hgk : BigOStarOn g k h₂ S) :
    BigOStarOn f k (h₁ + h₂) S :=
  fun x hx ↦ (hfg x hx).trans (hgk x hx)

/-- Monotonicity: the error of `f = g + O*(h)` on `S` may be enlarged pointwise on `S`. -/
theorem BigOStarOn.weaken (hfg : BigOStarOn f g h S) (hh : ∀ x ∈ S, h x ≤ h' x) :
    BigOStarOn f g h' S :=
  fun x hx ↦ (hfg x hx).weaken (hh x hx)

end Pointwise

/-- Additivity of pointwise explicit errors: from `f₁ = g₁ + O*(h₁)` and `f₂ = g₂ + O*(h₂)` on `S`
follows `f₁ + f₂ = g₁ + g₂ + O*(h₁ + h₂)` on `S`. -/
theorem BigOStarOn.add [SeminormedAddCommGroup E] {f₁ f₂ g₁ g₂ : α → E} {h₁ h₂ : α → ℝ}
    {S : Set α} (hfg₁ : BigOStarOn f₁ g₁ h₁ S) (hfg₂ : BigOStarOn f₂ g₂ h₂ S) :
    BigOStarOn (f₁ + f₂) (g₁ + g₂) (h₁ + h₂) S :=
  fun x hx ↦ (hfg₁ x hx).add (hfg₂ x hx)

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace α] {μ : Measure α}
  {f g : α → E} {h : α → ℝ} {S : Set α}

/-- Integrating an explicit error term: if `f = g + O*(h)` almost everywhere, with `f`, `g` and
`h` integrable, then `∫ f = ∫ g + O*(∫ h)`. -/
theorem bigOStar_integral (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hfg : ∀ᵐ x ∂μ, BigOStar (f x) (g x) (h x)) :
    BigOStar (∫ x, f x ∂μ) (∫ x, g x ∂μ) (∫ x, h x ∂μ) := by
  rw [bigOStar_iff, ← integral_sub hf hg]
  exact norm_integral_le_of_norm_le hh hfg

/-- Integrating an explicit error term over a set: if `f = g + O*(h)` on a measurable set `S`,
with `f`, `g` and `h` integrable on `S`, then `∫_S f = ∫_S g + O*(∫_S h)`. -/
theorem BigOStarOn.setIntegral (hfg : BigOStarOn f g h S) (hS : MeasurableSet S)
    (hf : IntegrableOn f S μ) (hg : IntegrableOn g S μ) (hh : IntegrableOn h S μ) :
    BigOStar (∫ x in S, f x ∂μ) (∫ x in S, g x ∂μ) (∫ x in S, h x ∂μ) :=
  bigOStar_integral hf hg hh ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hfg))

end Integral

end TauCeti
