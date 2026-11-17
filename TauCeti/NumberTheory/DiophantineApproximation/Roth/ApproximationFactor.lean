/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.ApproximationClass

/-!
# Local approximation factors and approximation classes over a number field

Let `K` be a number field, `F` a field extension of `K`, and fix finite sets `Sinf` of infinite
places and `Sfin` of finite places of `K`, at each such place `v` an absolute value `w v` of `F`
and a target `α v ∈ F`. The left side of Roth's inequality for `β ∈ K`,

`(∏ v ∈ Sinf, min 1 (w v (β - α v)) ^ mult v) * ∏ v ∈ Sfin, min 1 (w v (β - α v))`,

is a product of local factors indexed by the disjoint union `Sinf ⊕ Sfin` of the two sets of
places. The approximation class of `β` at side `1 / N` is the class `TauCeti.profileClass` of
this family: the cell of side `1 / N` containing its logarithmic profile, or a corner of the
simplex when `β` is one of the targets. At most `(N + |S|).choose |S|` classes occur, where `|S|`
is the number of places.

## Main definitions

* `NumberField.sPlaceAbsValue` and `NumberField.sPlaceWeight`: the absolute value and the weight
  (`mult v` at an infinite place, `1` at a finite one) of a place of `Sinf ⊕ Sfin`.
* `NumberField.approxFactor`: the local factor `min 1 (w v (β - α v)) ^ weight` at a place.
* `NumberField.approxClass`: the approximation class of `β` at side `1 / N`.

## Main results

* `NumberField.prod_approxFactor`: the product of the local factors is the left side of Roth's
  inequality.
* `NumberField.ncard_image_approxClass_le`: at most `(N + |S|).choose |S|` classes occur.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), 6.4.2–6.4.4 and Lemma 6.5.6.
-/

public section

open Finset

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]
variable (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))

/-! ### The places of `Sinf` and `Sfin` as one index type -/

/-- The absolute value of `K` underlying a place of `Sinf` or of `Sfin`, the two sets of places
being joined into the index type `Sinf ⊕ Sfin`. -/
def sPlaceAbsValue : Sinf ⊕ Sfin → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ v.1.1) fun v ↦ v.1.1

@[simp]
theorem sPlaceAbsValue_inl (v : Sinf) : sPlaceAbsValue Sinf Sfin (.inl v) = v.1.1 :=
  (rfl)

@[simp]
theorem sPlaceAbsValue_inr (v : Sfin) : sPlaceAbsValue Sinf Sfin (.inr v) = v.1.1 :=
  (rfl)

/-- The weight of a place of `Sinf` or of `Sfin` in Mathlib's relative normalization of heights:
`mult v` at an infinite place and `1` at a finite place. -/
noncomputable def sPlaceWeight : Sinf ⊕ Sfin → ℕ :=
  Sum.elim (fun v ↦ v.1.mult) fun _ ↦ 1

@[simp]
theorem sPlaceWeight_inl (v : Sinf) : sPlaceWeight Sinf Sfin (.inl v) = v.1.mult :=
  (rfl)

@[simp]
theorem sPlaceWeight_inr (v : Sfin) : sPlaceWeight Sinf Sfin (.inr v) = 1 :=
  (rfl)

/-! ### Local factors and approximation classes -/

/-- The local approximation factor `min 1 (w v (β - α v)) ^ weight` of `β ∈ K` to the target
`α v ∈ F` at a place `v` of `Sinf` or of `Sfin`, measured by the absolute value `w v` of `F` and
raised to the weight `mult v` at an infinite place. Its product over the places is the left side
of Roth's inequality (`NumberField.prod_approxFactor`). As for `NumberField.approxProd`, the data
`w` and `α` are indexed by the underlying absolute value of a place. -/
noncomputable def approxFactor (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (α : AbsoluteValue K ℝ → F) (β : K) (a : Sinf ⊕ Sfin) : ℝ :=
  min 1 (w (sPlaceAbsValue Sinf Sfin a) (algebraMap K F β - α (sPlaceAbsValue Sinf Sfin a))) ^
    sPlaceWeight Sinf Sfin a

variable {Sinf Sfin} (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)

@[simp]
theorem approxFactor_inl (β : K) (v : Sinf) :
    approxFactor Sinf Sfin w α β (.inl v) =
      min 1 (w v.1.1 (algebraMap K F β - α v.1.1)) ^ v.1.mult :=
  (rfl)

@[simp]
theorem approxFactor_inr (β : K) (v : Sfin) :
    approxFactor Sinf Sfin w α β (.inr v) = min 1 (w v.1.1 (algebraMap K F β - α v.1.1)) := by
  simp [approxFactor]

theorem approxFactor_nonneg (β : K) (a : Sinf ⊕ Sfin) : 0 ≤ approxFactor Sinf Sfin w α β a :=
  pow_nonneg (le_min zero_le_one (AbsoluteValue.nonneg _ _)) _

theorem approxFactor_le_one (β : K) (a : Sinf ⊕ Sfin) : approxFactor Sinf Sfin w α β a ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (AbsoluteValue.nonneg _ _)) (min_le_left _ _)

/-- The product of the local approximation factors of `β` is the left side of Roth's inequality,
a product over the infinite places of `Sinf` with exponents `mult v` times a product over the
finite places of `Sfin`. -/
theorem prod_approxFactor (β : K) :
    ∏ a, approxFactor Sinf Sfin w α β a =
      (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) := by
  rw [Fintype.prod_sum_type]
  simp only [approxFactor_inl, approxFactor_inr]
  rw [Finset.prod_coe_sort Sinf (fun v ↦ min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult),
    Finset.prod_coe_sort Sfin (fun v ↦ min 1 (w v.1 (algebraMap K F β - α v.1)))]

variable (Sinf Sfin) in
/-- The approximation class of `β ∈ K` at side `1 / N`: the class `TauCeti.profileClass` of its
family of local approximation factors. When `β` is none of the targets it labels the cell of side
`1 / N` containing the logarithmic profile `log Λ_v(β) / log Λ(β)` of the local factors; when `β`
is the target at a place `v`, it is the corner `N • e v` of the simplex. -/
noncomputable def approxClass (N : ℕ) (β : K) : Sinf ⊕ Sfin → ℕ :=
  TauCeti.profileClass N (approxFactor Sinf Sfin w α β)

theorem approxClass_def (N : ℕ) (β : K) :
    approxClass Sinf Sfin w α N β = TauCeti.profileClass N (approxFactor Sinf Sfin w α β) :=
  (rfl)

/-- At most `(N + |S|).choose |S|` approximation classes occur, where `|S|` is the number of
places of `Sinf` and `Sfin`. -/
theorem ncard_image_approxClass_le (X : Set K) (N : ℕ) :
    (approxClass Sinf Sfin w α N '' X).ncard ≤
      (N + (#Sinf + #Sfin)).choose (#Sinf + #Sfin) := by
  have h := TauCeti.ncard_image_profileClass_le (X := X) (approxFactor Sinf Sfin w α)
    (fun β _ ↦ approxFactor_nonneg w α β) (fun β _ ↦ approxFactor_le_one w α β) N
  simpa only [Fintype.card_sum, Fintype.card_coe, ← approxClass_def] using h

end NumberField
