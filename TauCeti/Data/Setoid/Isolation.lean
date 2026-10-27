/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Basic.Countable.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Isolation of an equivalence relation by a family of equivalence relations

An equivalence relation `R` on `X` is **isolated** by a family `E : I → Setoid X` when every point
`x` has an index `i`, depending on `x`, such that every `y` that is `E i`-equivalent to `x` is
`R`-equivalent to `x`. Then each `R`-class is pinned by one class of one `E i`, so the
`R`-classes inject into the dependent sum of the `E i`-classes. Over a countable index type,
countably many `E i`-classes each give countably many `R`-classes, and more generally the
`R`-classes are bounded by any infinite bound on the `E i`-classes.

Isolation is one-sided: the `E i`-class of `x` decides `R`-equivalence with `x`, for the index
chosen for `x`.

Isolation is an assumption, not a consequence of the sizes of the quotients: on Cantor space the
relations "agreeing on the first `n` coordinates" each have finitely many classes, while their
intersection, equality, has continuum many classes.

## Main definitions

* `Setoid.IsolatedBy R E`: `R` is isolated by the family `E`.

## Main results

* `Setoid.IsolatedBy.exists_injective_sigma`: the `R`-classes inject into the dependent sum of the
  `E i`-classes.
* `Setoid.IsolatedBy.countable_quotient`: countably many relations with countable quotients give
  `R` a countable quotient.
* `Setoid.IsolatedBy.lift_mk_quotient_le`: the general cardinal transfer, for an infinite bound.

## References

* Adapted from `Setoid.IsolatedBy` and its transfer theorems in `cameronfreer/infinitary-logic` at
  commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/ModelTheory/BFLimitIsolation.lean`; only the generic part about setoids is
  taken, without back-and-forth levels.
* Divergences from that source: the target relation is the first argument, so that isolation is
  written `R.IsolatedBy E`, and the transfer theorems are stated on the isolation hypothesis; the
  cardinal transfer uses Mathlib's bound on sums by suprema.
-/

public section

open Cardinal

universe u v

namespace Setoid

variable {X : Type u} {I : Type v}

/-- `R` is **isolated** by the family `E`: every point `x` has an index `i` such that every point
`E i`-equivalent to `x` is `R`-equivalent to `x`. The index may depend on the point. -/
def IsolatedBy (R : Setoid X) (E : I → Setoid X) : Prop :=
  ∀ x, ∃ i, ∀ y, E i x y → R x y

variable {R : Setoid X} {E : I → Setoid X}

/-- Unfolding lemma for `Setoid.IsolatedBy`. -/
theorem isolatedBy_iff : R.IsolatedBy E ↔ ∀ x, ∃ i, ∀ y, E i x y → R x y :=
  Iff.rfl

/-- **The classes inject into the dependent sum.** Send an `R`-class to an isolating index of a
representative, together with the class of that representative there. -/
theorem IsolatedBy.exists_injective_sigma (h : R.IsolatedBy E) :
    ∃ f : Quotient R → Σ i, Quotient (E i), Function.Injective f := by
  choose idx hidx using h
  refine ⟨fun q => ⟨idx q.out, Quotient.mk _ q.out⟩, fun q₁ q₂ hq => ?_⟩
  obtain ⟨hi, hcls⟩ := Sigma.mk.inj_iff.1 hq
  rw [hi] at hcls
  have he : E (idx q₂.out) q₁.out q₂.out := Quotient.exact (eq_of_heq hcls)
  rw [← q₁.out_eq, ← q₂.out_eq]
  exact Quotient.sound (R.symm (hidx q₂.out q₁.out ((E _).symm he)))

/-- **Countable transfer.** If `R` is isolated by countably many relations with countable
quotients, then `R` has countably many classes. -/
theorem IsolatedBy.countable_quotient [Countable I] [∀ i, Countable (Quotient (E i))]
    (h : R.IsolatedBy E) : Countable (Quotient R) :=
  let ⟨_, hf⟩ := h.exists_injective_sigma
  hf.countable

/-- **Cardinal transfer.** If `R` is isolated by countably many relations, each with at most `κ`
classes for an infinite cardinal `κ`, then `R` has at most `κ` classes. -/
theorem IsolatedBy.lift_mk_quotient_le [Countable I] {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ)
    (hE : ∀ i, lift.{v} #(Quotient (E i)) ≤ κ) (h : R.IsolatedBy E) :
    lift.{v} #(Quotient R) ≤ κ := by
  obtain ⟨f, hf⟩ := h.exists_injective_sigma
  calc lift.{v} #(Quotient R) ≤ lift.{u} #(Σ i, Quotient (E i)) := by
        rw [← lift_umax.{u, v}]
        exact lift_mk_le_lift_mk_of_injective hf
    _ = sum fun i => #(Quotient (E i)) := by rw [mk_sigma, lift_id'.{u, v}]
    _ ≤ lift.{u} #I * ⨆ i, lift.{v} #(Quotient (E i)) := sum_le_lift_mk_mul_iSup_lift _
    _ ≤ ℵ₀ * κ := by
        gcongr
        · exact lift_le_aleph0.2 (mk_le_aleph0_iff.2 inferInstance)
        · exact ciSup_le' hE
    _ = κ := aleph0_mul_eq hκ

end Setoid
