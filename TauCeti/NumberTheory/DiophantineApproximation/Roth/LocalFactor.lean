/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.ApproximationClass

import TauCeti.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# The local factors of Roth's inequality over a number field and their approximation classes

Let `K` be a number field, `F` a `K`-algebra (in the application a finite field extension of
`K`), and `Sinf`, `Sfin` finite sets of infinite and finite places of `K`. At each place `v` of
`Sinf ∪ Sfin` fix an absolute value `w v` of `F` and a target `α v ∈ F`. Roth's theorem over `K`
is about the `β ∈ K` with

```text
(∏ v ∈ Sinf, min 1 (w v (β - α v)) ^ mult v) * ∏ v ∈ Sfin, min 1 (w v (β - α v)) ≤ H(β) ^ (-κ),
```

where `H` is Mathlib's relative height `Height.mulHeight₁`. The places are indexed jointly by
`↥Sinf ⊕ ↥Sfin`, with `NumberField.sPlaceAbsValue` and `NumberField.sPlaceWeight` reading off
the absolute value of a place and its weight (`mult v` at an infinite place, `1` at a finite
one). The local factor of `β` at a place is `NumberField.approxFactor`, and the left side above is
their product (`NumberField.prod_approxFactor`).

Mahler's reduction sorts the `β` by how the product splits among the places: the
**approximation class** `NumberField.approxClass Sinf Sfin w α N β` is the label of the cell of
side `1 / N` of the standard simplex containing the logarithmic profile of the local factors
(`TauCeti.cellIndex` of `TauCeti.logProfile`). A `β` equal to the target at some place has a
vanishing local factor and no profile; it is put into the corner of the simplex at one such
place, where the label is `N` at that place and `0` elsewhere. With that convention every `β`
has a class, so no solution equal to a target has to be discarded, and the corner satisfies the
two estimates that make the classes useful:

* each local factor is at most the product raised to the power `label / N`
  (Bombieri–Gubler (6.9));
* for a product less than `1` the label sums to more than `N - |S|`, where `|S| = #Sinf + #Sfin`
  (Bombieri–Gubler (6.10)).

Every label sums to at most `N`, so at most `(N + |S|).choose |S|` classes occur.

## Main results

* `NumberField.prod_approxFactor`: the product of the local factors is the left side of Roth's
  inequality.
* `NumberField.approxClass_of_forall_ne_zero` and
  `NumberField.exists_approxClass_eq_of_approxFactor_eq_zero`: the two cases of the definition.
* `NumberField.approxFactor_le_rpow_approxClass`: the upper half of (6.9) for the class.
* `NumberField.lt_sum_approxClass_add_card`: (6.10) for the class.
* `NumberField.sum_approxClass_le` and `NumberField.ncard_image_approxClass_le`: labels sum to at
  most `N`, so at most `(N + |S|).choose |S|` classes occur.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  6.4.2–6.4.4.
-/

public section

open Finset Real TauCeti

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Places indexed jointly -/

section SPlace

variable {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}

/-- The absolute value of `K` at a place of `Sinf ∪ Sfin`, the places being indexed by
`↥Sinf ⊕ ↥Sfin`. -/
def sPlaceAbsValue : ↥Sinf ⊕ ↥Sfin → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ v.1.1) fun v ↦ v.1.1

@[simp]
theorem sPlaceAbsValue_inl (v : ↥Sinf) :
    sPlaceAbsValue (Sum.inl v : ↥Sinf ⊕ ↥Sfin) = v.1.1 :=
  (rfl)

@[simp]
theorem sPlaceAbsValue_inr (v : ↥Sfin) :
    sPlaceAbsValue (Sum.inr v : ↥Sinf ⊕ ↥Sfin) = v.1.1 :=
  (rfl)

/-- The weight of a place of `Sinf ∪ Sfin` in the product formula: `mult v` at an infinite place
and `1` at a finite place. -/
noncomputable def sPlaceWeight : ↥Sinf ⊕ ↥Sfin → ℕ :=
  Sum.elim (fun v ↦ v.1.mult) fun _ ↦ 1

@[simp]
theorem sPlaceWeight_inl (v : ↥Sinf) :
    sPlaceWeight (Sum.inl v : ↥Sinf ⊕ ↥Sfin) = v.1.mult :=
  (rfl)

@[simp]
theorem sPlaceWeight_inr (v : ↥Sfin) : sPlaceWeight (Sum.inr v : ↥Sinf ⊕ ↥Sfin) = 1 :=
  (rfl)

/-- Every place of `Sinf ∪ Sfin` has positive weight. -/
theorem sPlaceWeight_ne_zero (s : ↥Sinf ⊕ ↥Sfin) : sPlaceWeight s ≠ 0 := by
  rcases s with v | _
  · exact v.1.mult_ne_zero
  · exact one_ne_zero

/-- A product over the places of `Sinf ∪ Sfin`, weighted by `sPlaceWeight`, is the product over
`Sinf` weighted by `mult` times the product over `Sfin`. -/
theorem prod_pow_sPlaceWeight (g : AbsoluteValue K ℝ → ℝ) :
    ∏ s : ↥Sinf ⊕ ↥Sfin, g (sPlaceAbsValue s) ^ sPlaceWeight s =
      (∏ v ∈ Sinf, g v.1 ^ v.mult) * ∏ v ∈ Sfin, g v.1 := by
  simp only [Fintype.prod_sum_type, sPlaceAbsValue_inl, sPlaceAbsValue_inr, sPlaceWeight_inl,
    sPlaceWeight_inr, pow_one]
  exact congr_arg₂ (· * ·) (prod_coe_sort Sinf fun v ↦ g v.1 ^ v.mult)
    (prod_coe_sort Sfin fun v ↦ g v.1)

end SPlace

/-! ### The local factors and the approximation class -/

section ApproxClass

variable {F : Type*} [Ring F] [Algebra K F]
  (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
  (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)

/-- The local factor `min 1 (w v (β - α v)) ^ mult v` of `β ∈ K` at a place `v` of `Sinf ∪ Sfin`,
measuring how close `β` is to the target `α v ∈ F` in the absolute value `w v` of `F`; the
exponent `mult v` is `1` at a finite place. The data `w` and `α` are indexed by the underlying
absolute value of a place. -/
noncomputable def approxFactor (β : K) (s : ↥Sinf ⊕ ↥Sfin) : ℝ :=
  min 1 (w (sPlaceAbsValue s) (algebraMap K F β - α (sPlaceAbsValue s))) ^ sPlaceWeight s

theorem approxFactor_def (β : K) (s : ↥Sinf ⊕ ↥Sfin) :
    approxFactor Sinf Sfin w α β s =
      min 1 (w (sPlaceAbsValue s) (algebraMap K F β - α (sPlaceAbsValue s))) ^
        sPlaceWeight s :=
  (rfl)

variable {Sinf Sfin w α}

theorem approxFactor_nonneg (β : K) (s : ↥Sinf ⊕ ↥Sfin) : 0 ≤ approxFactor Sinf Sfin w α β s :=
  pow_nonneg (le_min zero_le_one (AbsoluteValue.nonneg _ _)) _

theorem approxFactor_le_one (β : K) (s : ↥Sinf ⊕ ↥Sfin) : approxFactor Sinf Sfin w α β s ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (AbsoluteValue.nonneg _ _)) (min_le_left _ _)

/-- A local factor vanishes exactly when `β` is the target at that place. -/
@[simp]
theorem approxFactor_eq_zero_iff {β : K} {s : ↥Sinf ⊕ ↥Sfin} :
    approxFactor Sinf Sfin w α β s = 0 ↔ algebraMap K F β = α (sPlaceAbsValue s) := by
  rw [approxFactor_def, pow_eq_zero_iff (sPlaceWeight_ne_zero s), min_eq_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h one_ne_zero
    · exact sub_eq_zero.mp ((AbsoluteValue.eq_zero _).mp h)
  · intro h
    exact Or.inr ⟨by simp [h], by simp [h]⟩

/-- The product of the local factors of `β` is the left side of Roth's inequality over `K`. -/
theorem prod_approxFactor (β : K) :
    ∏ s, approxFactor Sinf Sfin w α β s =
      (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) :=
  prod_pow_sPlaceWeight fun v ↦ min 1 (w v (algebraMap K F β - α v))

variable (Sinf Sfin w α) in
open Classical in
/-- The **approximation class** of `β ∈ K` of side `1 / N`: the label `TauCeti.cellIndex N` of
the logarithmic profile of the local factors of `β`, a point of the standard simplex. When `β`
is the target at some place, its local factor there vanishes and the class is the corner of the
simplex at one such place: the label is `N` there and `0` at every other place. -/
noncomputable def approxClass (N : ℕ) (β : K) : ↥Sinf ⊕ ↥Sfin → ℕ :=
  if h : ∃ s, approxFactor Sinf Sfin w α β s = 0 then fun s ↦ if s = h.choose then N else 0
  else cellIndex N (logProfile (approxFactor Sinf Sfin w α β))

/-- Away from the targets, the approximation class is the cell of the logarithmic profile of the
local factors. -/
theorem approxClass_of_forall_ne_zero {N : ℕ} {β : K}
    (h : ∀ s, approxFactor Sinf Sfin w α β s ≠ 0) :
    approxClass Sinf Sfin w α N β = cellIndex N (logProfile (approxFactor Sinf Sfin w α β)) := by
  rw [approxClass, dite_eq_right (not_exists.mpr h)]

open Classical in
/-- At a target, the approximation class is the corner of the simplex at a place where `β` is
the target. -/
theorem exists_approxClass_eq_of_approxFactor_eq_zero {N : ℕ} {β : K} {s : ↥Sinf ⊕ ↥Sfin}
    (h : approxFactor Sinf Sfin w α β s = 0) :
    ∃ s₀, approxFactor Sinf Sfin w α β s₀ = 0 ∧
      approxClass Sinf Sfin w α N β = fun t ↦ if t = s₀ then N else 0 := by
  have h' : ∃ s, approxFactor Sinf Sfin w α β s = 0 := ⟨s, h⟩
  exact ⟨h'.choose, h'.choose_spec, by rw [approxClass, dite_eq_left h']⟩

/-- The logarithmic profile of the local factors is a point of the standard simplex when no local
factor vanishes. -/
private theorem logProfile_approxFactor_mem {β : K}
    (h : ∀ s, approxFactor Sinf Sfin w α β s ≠ 0) :
    (∀ s, 0 ≤ logProfile (approxFactor Sinf Sfin w α β) s) ∧
      ∑ s, logProfile (approxFactor Sinf Sfin w α β) s ≤ 1 := by
  have hpos s := (approxFactor_nonneg (w := w) (α := α) β s).lt_of_ne' (h s)
  refine ⟨logProfile_nonneg hpos (approxFactor_le_one β), ?_⟩
  by_cases hprod : ∏ s, approxFactor Sinf Sfin w α β s = 1
  · simp [logProfile_apply, hprod]
  · exact (sum_logProfile hpos hprod).le

/-- **The upper half of Bombieri–Gubler (6.9)** for the approximation class: each local factor of
`β` is at most the product of all of them raised to the power `c s / N`, where `c` is the class
of `β`. -/
theorem approxFactor_le_rpow_approxClass (N : ℕ) (β : K) (s : ↥Sinf ⊕ ↥Sfin) :
    approxFactor Sinf Sfin w α β s ≤
      (∏ t, approxFactor Sinf Sfin w α β t) ^
        ((approxClass Sinf Sfin w α N β s : ℝ) / N) := by
  by_cases h : ∀ t, approxFactor Sinf Sfin w α β t ≠ 0
  · rw [approxClass_of_forall_ne_zero h]
    exact le_rpow_cellIndex_div N (fun t ↦ (approxFactor_nonneg β t).lt_of_ne' (h t))
      (approxFactor_le_one β) s
  simp only [ne_eq, not_forall, not_not] at h
  obtain ⟨t, ht⟩ := h
  obtain ⟨s₀, hs₀, hc⟩ := exists_approxClass_eq_of_approxFactor_eq_zero (N := N) ht
  have hprod : ∏ t, approxFactor Sinf Sfin w α β t = 0 := prod_eq_zero (mem_univ _) hs₀
  rw [hc, hprod]
  by_cases hs : s = s₀
  · simp only [hs, hs₀, ↓reduceIte]
    exact rpow_nonneg le_rfl _
  · simpa [hs] using approxFactor_le_one β s

/-- The label of an approximation class sums to at most `N`. -/
theorem sum_approxClass_le (N : ℕ) (β : K) : ∑ s, approxClass Sinf Sfin w α N β s ≤ N := by
  by_cases h : ∀ t, approxFactor Sinf Sfin w α β t ≠ 0
  · rw [approxClass_of_forall_ne_zero h]
    exact sum_cellIndex_le N (logProfile_approxFactor_mem h).1 (logProfile_approxFactor_mem h).2
  simp only [ne_eq, not_forall, not_not] at h
  obtain ⟨t, ht⟩ := h
  obtain ⟨s₀, -, hc⟩ := exists_approxClass_eq_of_approxFactor_eq_zero (N := N) ht
  simp [hc]

/-- At most `(N + |S|).choose |S|` approximation classes of side `1 / N` occur, where
`|S| = #Sinf + #Sfin` is the number of places. -/
theorem ncard_image_approxClass_le (N : ℕ) (X : Set K) :
    (approxClass Sinf Sfin w α N '' X).ncard ≤
      (N + (#Sinf + #Sfin)).choose (#Sinf + #Sfin) := by
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = #Sinf + #Sfin := by simp
  rw [← hcard, ← ncard_setOf_sum_le _ N]
  refine Set.ncard_le_ncard ?_ (finite_setOf_sum_le _ N)
  rintro _ ⟨β, -, rfl⟩
  exact sum_approxClass_le N β

/-- **Bombieri–Gubler (6.10)** for the approximation class: when the product of the local
factors of `β` is less than `1`, the label of its class of side `1 / N` sums to more than
`N - |S|`, where `|S| = #Sinf + #Sfin`. -/
theorem lt_sum_approxClass_add_card (N : ℕ) {β : K}
    (hprod : ∏ s, approxFactor Sinf Sfin w α β s < 1) :
    N < ∑ s, approxClass Sinf Sfin w α N β s + (#Sinf + #Sfin) := by
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = #Sinf + #Sfin := by simp
  -- A product less than `1` is not empty.
  have hS : 0 < #Sinf + #Sfin := by
    rw [← hcard, Fintype.card_pos_iff]
    by_contra h
    simp [univ_eq_empty_iff.mpr (not_nonempty_iff.mp h)] at hprod
  rcases N.eq_zero_or_pos with rfl | hN
  · lia
  by_cases h : ∀ t, approxFactor Sinf Sfin w α β t ≠ 0
  · have hpos t := (approxFactor_nonneg (w := w) (α := α) β t).lt_of_ne' (h t)
    have key := one_sub_card_div_lt_sum_cellIndex_div hN (sum_logProfile hpos hprod.ne)
    rw [← approxClass_of_forall_ne_zero h, ← Finset.sum_div, lt_div_iff₀ (by positivity),
      sub_mul, one_mul, div_mul_cancel₀ _ (by positivity), sub_lt_iff_lt_add, hcard] at key
    exact_mod_cast key
  simp only [ne_eq, not_forall, not_not] at h
  obtain ⟨t, ht⟩ := h
  obtain ⟨s₀, -, hc⟩ := exists_approxClass_eq_of_approxFactor_eq_zero (N := N) ht
  simp only [hc, sum_ite_eq', mem_univ, ↓reduceIte]
  lia

end ApproxClass

end NumberField
