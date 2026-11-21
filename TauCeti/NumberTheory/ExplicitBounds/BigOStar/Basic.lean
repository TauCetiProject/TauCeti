/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Explicit absolute errors

`BigOStar a b e` means that `a` differs from `b` by at most the displayed real error `e`.
Unlike asymptotic big-O, it has no implicit constant or limiting filter. `BigOStarOn` is its
pointwise version on a set. These predicates let explicit estimates be composed by adding,
scaling, and summing their errors.

The convention is that of O. Ramaré, *Excursions in Multiplicative Number Theory* (2022), §1.
In particular, errors are not replaced by their absolute values: a negative error is impossible.
-/

public section

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E]

/-- An absolute error bound with its constant displayed: `‖a - b‖ ≤ e`. -/
def BigOStar (a b : E) (e : ℝ) : Prop := ‖a - b‖ ≤ e

/-- Explicit errors bounded pointwise on a set. -/
def BigOStarOn {α : Type*} (f g : α → E) (h : α → ℝ) (s : Set α) : Prop :=
  ∀ x ∈ s, BigOStar (f x) (g x) (h x)

/-- The norm characterization of an explicit absolute error. -/
theorem bigOStar_iff {a b : E} {e : ℝ} : BigOStar a b e ↔ ‖a - b‖ ≤ e := Iff.rfl

/-- The pointwise characterization of an explicit error on a set. -/
theorem bigOStarOn_iff {α : Type*} {f g : α → E} {h : α → ℝ} {s : Set α} :
    BigOStarOn f g h s ↔ ∀ x ∈ s, BigOStar (f x) (g x) (h x) := Iff.rfl

namespace BigOStar

variable {a b c a₁ a₂ b₁ b₂ : E} {e e' e₁ e₂ : ℝ}

/-- An explicit error is nonnegative. -/
theorem nonneg (h : BigOStar a b e) : 0 ≤ e := (norm_nonneg _).trans h

/-- Approximating an element by itself permits exactly the nonnegative errors. -/
@[simp] theorem self_iff : BigOStar a a e ↔ 0 ≤ e := by
  simp [BigOStar]

/-- Every nonnegative error bounds the error of an exact equality. -/
theorem refl (a : E) (he : 0 ≤ e) : BigOStar a a e := self_iff.mpr he

/-- An error bound is symmetric in the two approximated quantities. -/
theorem symm (h : BigOStar a b e) : BigOStar b a e := by
  simpa only [BigOStar, norm_sub_rev] using h

/-- Symmetry as an equivalence, for rewriting. -/
theorem comm : BigOStar a b e ↔ BigOStar b a e := ⟨symm, symm⟩

/-- Enlarging the displayed error preserves the bound. -/
theorem mono (h : BigOStar a b e) (he : e ≤ e') : BigOStar a b e' := h.trans he

/-- Errors add when chaining approximations. -/
theorem trans (h₁ : BigOStar a b e₁) (h₂ : BigOStar b c e₂) :
    BigOStar a c (e₁ + e₂) :=
  (norm_sub_le_norm_sub_add_norm_sub a b c).trans (add_le_add h₁ h₂)

/-- Errors add under addition. -/
theorem add (h₁ : BigOStar a₁ b₁ e₁) (h₂ : BigOStar a₂ b₂ e₂) :
    BigOStar (a₁ + a₂) (b₁ + b₂) (e₁ + e₂) := by
  rw [BigOStar, add_sub_add_comm]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

/-- Negation leaves an absolute error unchanged. -/
theorem neg (h : BigOStar a b e) : BigOStar (-a) (-b) e := by
  simpa only [BigOStar, neg_sub_neg, norm_sub_rev] using h

/-- Errors add under subtraction. -/
theorem sub (h₁ : BigOStar a₁ b₁ e₁) (h₂ : BigOStar a₂ b₂ e₂) :
    BigOStar (a₁ - a₂) (b₁ - b₂) (e₁ + e₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Scaling multiplies an error by the norm of the scalar. -/
theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (h : BigOStar a b e) (c : 𝕜) : BigOStar (c • a) (c • b) (‖c‖ * e) := by
  rw [BigOStar, ← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg c)

/-- An explicit error gives an upper bound for the norm. -/
theorem norm_le (h : BigOStar a b e) : ‖a‖ ≤ ‖b‖ + e := by
  have := (norm_sub_norm_le a b).trans h
  linarith

/-- An explicit error also gives a lower bound for the norm. -/
theorem le_norm (h : BigOStar a b e) : ‖b‖ - e ≤ ‖a‖ := by
  have := h.symm.norm_le
  linarith

end BigOStar

/-- Zero error is exact equality in a normed group. -/
@[simp] theorem bigOStar_zero_iff {F : Type*} [NormedAddCommGroup F] {a b : F} :
    BigOStar a b 0 ↔ a = b := by
  simp [BigOStar, sub_eq_zero]

/-- For real quantities, an explicit error is a two-sided interval bound. -/
theorem bigOStar_real_iff {a b e : ℝ} : BigOStar a b e ↔ b - e ≤ a ∧ a ≤ b + e := by
  rw [BigOStar, Real.norm_eq_abs, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

namespace BigOStarOn

variable {α : Type*} {f g k : α → E} {h h' : α → ℝ} {s t : Set α}

/-- There is no pointwise error condition on the empty set. -/
@[simp] theorem empty : BigOStarOn f g h ∅ := by simp [BigOStarOn]

/-- Approximating a function by itself permits exactly the pointwise nonnegative errors. -/
@[simp] theorem self_iff : BigOStarOn f f h s ↔ ∀ x ∈ s, 0 ≤ h x := by
  simp [BigOStarOn]

/-- Evaluate a pointwise explicit error at a point of the set. -/
theorem apply (H : BigOStarOn f g h s) {x : α} (hx : x ∈ s) :
    BigOStar (f x) (g x) (h x) := H x hx

/-- Restrict a pointwise error to a smaller set. -/
theorem mono_set (H : BigOStarOn f g h s) (ht : t ⊆ s) : BigOStarOn f g h t :=
  fun _ hx ↦ H _ (ht hx)

/-- Enlarge the error function on the set. -/
theorem mono (H : BigOStarOn f g h s) (hh : ∀ x ∈ s, h x ≤ h' x) :
    BigOStarOn f g h' s := fun x hx ↦ (H x hx).mono (hh x hx)

/-- Interchanging the two functions preserves the pointwise error. -/
theorem symm (H : BigOStarOn f g h s) : BigOStarOn g f h s :=
  fun x hx ↦ (H x hx).symm

/-- Pointwise errors add when chaining approximations. -/
theorem trans (H : BigOStarOn f g h s) (H' : BigOStarOn g k h' s) :
    BigOStarOn f k (fun x ↦ h x + h' x) s := fun x hx ↦ (H x hx).trans (H' x hx)

/-- Pointwise errors add under addition of functions. -/
theorem add {f' g' : α → E} (H : BigOStarOn f g h s) (H' : BigOStarOn f' g' h' s) :
    BigOStarOn (fun x ↦ f x + f' x) (fun x ↦ g x + g' x)
      (fun x ↦ h x + h' x) s := fun x hx ↦ (H x hx).add (H' x hx)

/-- Scaling a function multiplies its pointwise error by the scalar norm. -/
theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (H : BigOStarOn f g h s) (c : 𝕜) :
    BigOStarOn (fun x ↦ c • f x) (fun x ↦ c • g x) (fun x ↦ ‖c‖ * h x) s :=
  fun x hx ↦ (H x hx).smul c

end BigOStarOn

end TauCeti

namespace Finset

open TauCeti

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A finite sum has error at most the sum of its errors. -/
theorem bigOStar_sum {ι : Type*} (s : Finset ι) {f g : ι → E} {h : ι → ℝ}
    (hs : ∀ i ∈ s, BigOStar (f i) (g i) (h i)) :
    BigOStar (∑ i ∈ s, f i) (∑ i ∈ s, g i) (∑ i ∈ s, h i) := by
  rw [bigOStar_iff, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ bigOStar_iff.mp (hs i hi))

/-- A finite sum of pointwise estimates has the sum of their errors. -/
theorem bigOStarOn_sum {α ι : Type*} (t : Finset ι) {s : Set α}
    {F G : ι → α → E} {e : ι → α → ℝ}
    (H : ∀ i ∈ t, BigOStarOn (F i) (G i) (e i) s) :
    BigOStarOn (fun x ↦ ∑ i ∈ t, F i x) (fun x ↦ ∑ i ∈ t, G i x)
      (fun x ↦ ∑ i ∈ t, e i x) s := by
  rw [bigOStarOn_iff]
  exact fun _ hx ↦ t.bigOStar_sum (fun i hi ↦ (H i hi).apply hx)

end Finset
