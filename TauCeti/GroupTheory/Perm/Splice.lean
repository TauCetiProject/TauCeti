/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Orbit bijections when inserting a point into a cycle

Adjoin one fixed point to a permutation, then transpose it with an old point. The old
cycles survive, with the new point inserted into the cycle of its transposition partner.
The resulting orbit bijection sends every old point to its own image, rather than choosing
an arbitrary bijection from an equality of orbit counts. This permits transport of data
attached to individual cycles, such as the framing coefficients of a braid closure.

The construction uses Mathlib's cycle quotient and Tau Ceti's transposition merge theorem
`Equiv.Perm.SameCycle.sameCycle_or_of_swap_mul`.
-/

public section

namespace Equiv.Perm

open Function

variable {α β : Type*}

/-- Splicing a fixed point `p` into the cycle of `a` preserves the cycle relation between
points other than `p`. No finiteness or periodicity is required. -/
theorem sameCycle_mul_swap_iff_of_apply_eq_self [DecidableEq β] {τ : Perm β} {p a x y : β}
    (hp : τ p = p) (hxp : x ≠ p) (hyp : y ≠ p) :
    (τ * Equiv.swap a p).SameCycle x y ↔ τ.SameCycle x y := by
  rw [Equiv.mul_swap_eq_swap_mul, hp]
  have hab : (Equiv.swap (τ a) p * τ).SameCycle (τ a) p := by
    have hstep : (Equiv.swap (τ a) p * τ) p = τ a := by simp [hp]
    exact (SameCycle.symm ⟨1, by simpa using hstep⟩)
  constructor
  · intro h
    rcases h.sameCycle_or_of_swap_mul with h | ⟨hx, hy⟩
    · exact h
    · have hx' := hx.resolve_right (fun h => hxp (h.eq_of_right hp))
      have hy' := hy.resolve_right (fun h => hyp (h.eq_of_right hp))
      exact hx'.trans hy'.symm
  · exact fun h => hab.swap_mul_of_sameCycle h

/-- A permutation extending another across a single missing point fixes that point. -/
theorem apply_eq_self_of_semiconj {σ : Perm α} {τ : Perm β} {f : α → β} {p : β}
    (hfp : ∀ x, f x ≠ p) (hsurj : ∀ y, y ≠ p → ∃ x, f x = y)
    (hcomm : Semiconj f σ τ) : τ p = p := by
  by_contra h
  obtain ⟨x, hx⟩ := hsurj (τ p) h
  apply hfp (σ⁻¹ x)
  apply τ.injective
  rw [← hcomm (σ⁻¹ x)]
  simp [hx]

/-- Insert a new point into the orbit of `a`, after extending `σ` along an injection `f`
whose image misses exactly that point. The orbit bijection follows `f` on old points. -/
noncomputable def orbitQuotientEquivSplice [DecidableEq β] (σ : Perm α) (τ : Perm β)
    (f : α → β) (p : β) (a : α) (hf : Injective f) (hfp : ∀ x, f x ≠ p)
    (hsurj : ∀ y, y ≠ p → ∃ x, f x = y) (hcomm : Semiconj f σ τ) :
    Quotient (SameCycle.setoid σ) ≃ Quotient (SameCycle.setoid (τ * Equiv.swap (f a) p)) := by
  have hp := apply_eq_self_of_semiconj hfp hsurj hcomm
  have hcycle (x y : α) : σ.SameCycle x y ↔
      (τ * Equiv.swap (f a) p).SameCycle (f x) (f y) := by
    rw [sameCycle_mul_swap_iff_of_apply_eq_self hp (hfp x) (hfp y)]
    constructor
    · exact fun h => h.map hcomm
    · rintro ⟨k, hk⟩
      exact ⟨k, hf ((hcomm.perm_zpow_right k x).trans hk)⟩
  refine Equiv.ofBijective (Quotient.map f (fun x y h => (hcycle x y).mp h)) ⟨?_, ?_⟩
  · intro c d h
    induction c using Quotient.inductionOn with
    | _ x =>
      induction d using Quotient.inductionOn with
      | _ y => exact Quotient.sound ((hcycle x y).mpr (Quotient.exact h))
  · intro c
    induction c using Quotient.inductionOn with
    | _ y =>
      by_cases hy : y = p
      · subst y
        refine ⟨Quotient.mk _ a, Quotient.sound ?_⟩
        exact ⟨1, by simp [hp]⟩
      · obtain ⟨x, rfl⟩ := hsurj y hy
        exact ⟨Quotient.mk _ x, rfl⟩

/-- On old points the orbit bijection is the given inclusion. -/
@[simp] theorem orbitQuotientEquivSplice_mk [DecidableEq β] (σ : Perm α) (τ : Perm β)
    (f : α → β) (p : β) (a : α) (hf : Injective f) (hfp : ∀ x, f x ≠ p)
    (hsurj : ∀ y, y ≠ p → ∃ x, f x = y) (hcomm : Semiconj f σ τ) (x : α) :
    orbitQuotientEquivSplice σ τ f p a hf hfp hsurj hcomm (Quotient.mk _ x) =
      Quotient.mk _ (f x) := by
  unfold orbitQuotientEquivSplice
  rfl

/-- The inverse orbit bijection sends an old point back to its original orbit. -/
@[simp] theorem orbitQuotientEquivSplice_symm_mk [DecidableEq β] (σ : Perm α) (τ : Perm β)
    (f : α → β) (p : β) (a : α) (hf : Injective f) (hfp : ∀ x, f x ≠ p)
    (hsurj : ∀ y, y ≠ p → ∃ x, f x = y) (hcomm : Semiconj f σ τ) (x : α) :
    (orbitQuotientEquivSplice σ τ f p a hf hfp hsurj hcomm).symm
      (Quotient.mk _ (f x)) = Quotient.mk _ x := by
  rw [← orbitQuotientEquivSplice_mk σ τ f p a hf hfp hsurj hcomm x]
  exact Equiv.symm_apply_apply _ _

/-- The inserted point belongs to the orbit of its old transposition partner. -/
@[simp] theorem orbitQuotientEquivSplice_symm_mk_new [DecidableEq β] (σ : Perm α) (τ : Perm β)
    (f : α → β) (p : β) (a : α) (hf : Injective f) (hfp : ∀ x, f x ≠ p)
    (hsurj : ∀ y, y ≠ p → ∃ x, f x = y) (hcomm : Semiconj f σ τ) :
    (orbitQuotientEquivSplice σ τ f p a hf hfp hsurj hcomm).symm
      (Quotient.mk _ p) = Quotient.mk _ a := by
  apply (orbitQuotientEquivSplice σ τ f p a hf hfp hsurj hcomm).injective
  rw [Equiv.apply_symm_apply, orbitQuotientEquivSplice_mk]
  apply Quotient.sound
  have hp := apply_eq_self_of_semiconj hfp hsurj hcomm
  exact (SameCycle.symm ⟨1, by simp [hp]⟩)

end Equiv.Perm
