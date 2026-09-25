/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

-- Roadmap source: `TauCetiRoadmap/NumberFieldArithmetic/README.md` @ `ce02686a0c05`, Layer 8.1,
-- which specifies the predicate below and the sign-recovery statement proved from
-- `NumberField.sign_discr`. This credit sits outside the module docstring deliberately: the
-- docstring documents the mathematics, so the roadmap citation belongs here rather than in
-- its References section.

/-!
# The intrinsic label prefix of a number field

Three invariants form the intrinsic prefix of a number field's LMFDB label: its degree `d`, its
number of real places `r`, and the absolute value `D` of its discriminant. They group the fields
of the tables rather than single one out — distinct fields can share a prefix. This file packages
them as a predicate `HasLMFDBIntrinsicLabel K d r D`.

The prefix carries more information than it appears to: it determines the **signed**
discriminant, not merely its absolute value. The sign is recovered from `d` and `r` alone,
because `(d - r) / 2` is the number of complex places and `NumberField.sign_discr` reads the
sign off that count.

Only the prefix is intrinsic. The index that separates distinct fields sharing a prefix is not
determined by these invariants — it depends on an external ordering of a certified complete
list — and nothing here defines or approximates it.

## Main definitions

* `TauCeti.NumberField.HasLMFDBIntrinsicLabel`: the degree, real-place count and absolute
  discriminant of `K` are `d`, `r` and `D`.

## Main results

* `TauCeti.NumberField.hasLMFDBIntrinsicLabel_iff`: the defining conjunction, in `simp` normal
  form — the stable rewriting interface for the predicate.
* `TauCeti.NumberField.exists_hasLMFDBIntrinsicLabel`: every number field has such a triple, so
  the predicate is not vacuous.
* `TauCeti.NumberField.HasLMFDBIntrinsicLabel.unique`: and the triple is the only one.
* `TauCeti.NumberField.HasLMFDBIntrinsicLabel.sub_div_two_eq_nrComplexPlaces`: `(d - r) / 2`
  counts the complex places, read off a full label. The general statement about `K` alone is
  `NumberField.InfinitePlace.finrank_sub_nrRealPlaces_div_two_eq_nrComplexPlaces`, in
  `TauCeti/NumberTheory/NumberField/InfinitePlace/Basic.lean`.
* `TauCeti.NumberField.HasLMFDBIntrinsicLabel.discr_eq`: **sign recovery**,
  `discr K = (-1) ^ ((d - r) / 2) * D`.

## References

* The sign of the discriminant is Mathlib's `NumberField.sign_discr`; this file combines it with
  the label data and does not reprove it.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- `K` has **intrinsic label prefix** `d.r.D` when its degree is `d`, it has `r` real places,
and the absolute value of its discriminant is `D`.

These three invariants are intrinsic to `K`. The index disambiguating fields that share a prefix
is not, and is deliberately absent. -/
def HasLMFDBIntrinsicLabel (d r D : ℕ) : Prop :=
  Module.finrank ℚ K = d ∧ nrRealPlaces K = r ∧ (discr K).natAbs = D

variable {K}

/-- The defining conjunction of `HasLMFDBIntrinsicLabel`, in `simp` normal form: the stable
rewriting interface downstream code uses to prove or consume the predicate. -/
@[simp]
theorem hasLMFDBIntrinsicLabel_iff {d r D : ℕ} :
    HasLMFDBIntrinsicLabel K d r D ↔
      Module.finrank ℚ K = d ∧ nrRealPlaces K = r ∧ (discr K).natAbs = D :=
  Iff.rfl

variable (K) in
/-- Every number field has an intrinsic label prefix, namely its own invariants. -/
theorem exists_hasLMFDBIntrinsicLabel : ∃ d r D, HasLMFDBIntrinsicLabel K d r D :=
  ⟨_, _, _, rfl, rfl, rfl⟩

namespace HasLMFDBIntrinsicLabel

variable {d r D d' r' D' : ℕ}

/-- The prefix is determined by the field: a field has at most one intrinsic label prefix. -/
theorem unique (h : HasLMFDBIntrinsicLabel K d r D) (h' : HasLMFDBIntrinsicLabel K d' r' D') :
    d = d' ∧ r = r' ∧ D = D' :=
  ⟨h.1.symm.trans h'.1, h.2.1.symm.trans h'.2.1, h.2.2.symm.trans h'.2.2⟩

/-- **`(d - r) / 2` counts the complex places**, read off a full label. The discriminant
component plays no part: only the degree and real-place components are used. -/
theorem sub_div_two_eq_nrComplexPlaces (h : HasLMFDBIntrinsicLabel K d r D) :
    (d - r) / 2 = nrComplexPlaces K := by
  rw [← h.1, ← h.2.1]
  exact _root_.NumberField.InfinitePlace.finrank_sub_nrRealPlaces_div_two_eq_nrComplexPlaces K

/-- **Sign recovery: the intrinsic prefix determines the signed discriminant.** The absolute
value is `D` by definition, and the sign is `(-1) ^ ((d - r) / 2)` because that exponent counts
the complex places. -/
theorem discr_eq (h : HasLMFDBIntrinsicLabel K d r D) :
    discr K = (-1) ^ ((d - r) / 2) * D := by
  rw [h.sub_div_two_eq_nrComplexPlaces, ← h.2.2, ← sign_discr K, Int.sign_mul_natAbs]

end HasLMFDBIntrinsicLabel

end TauCeti.NumberField

end
