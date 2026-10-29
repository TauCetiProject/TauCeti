/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Preorder.Finite

/-!
# Free actions

## A descent principle

Let a monoid `G` act freely on `X`, and let `E, P ⊆ G` with `1 ∈ P` be such that `e * p ∈ P` and
`e * p ≠ 1` for all `e ∈ E` and `p ∈ P`. Then a finite subset `s ⊆ X` in which every point is
moved back into `s` by some element of `E` is empty: following such moves from a point of `s`,
some point must return to itself under a product `e * p ≠ 1`, which freeness forbids.

## Counting

If a group `G` acts freely on `X`, every orbit is a copy of `G`, so `Nat.card G` divides
`Nat.card X`.

## Orbit decomposition

Mathlib's `MulAction.selfEquivOrbitsQuotientProd` identifies `X` with the product of its orbit space
and `G`; its inverse sends `(q, g)` to the translate `g • q.out` of the chosen representative.

## Main results

* `TauCeti.MulAction.eq_empty_of_forall_exists_smul_mem`: the descent principle.
* `TauCeti.MulAction.natCard_dvd_natCard_of_isCancelSMul`: the order of a group acting freely
  divides the number of points.
* `MulAction.selfEquivOrbitsQuotientProd_symm_apply`: the inverse of the orbit decomposition of a
  free action evaluated at `(q, g)` is `g • q.out`.

## References

This is the descent in the proof of Lemma 2 of A. Popa and D. Zagier, *An elementary proof of the
Eichler–Selberg trace formula*, J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327,
§3, with `G = PSL(2, ℤ)`, `E = {T, T′}` and `P` the classes of matrices with non-negative entries.
-/

public section

namespace TauCeti.MulAction

variable {G X : Type*} [Monoid G] [MulAction G X]

/-- **Descent for free actions.** If `G` acts freely on `X`, `1 ∈ P`, and `e * p ∈ P` with
`e * p ≠ 1` for all `e ∈ E`, `p ∈ P`, then a finite set `s` in which every point is moved back
into `s` by an element of `E` is empty. -/
theorem eq_empty_of_forall_exists_smul_mem [IsCancelSMul G X] {E P : Set G} (hP : 1 ∈ P)
    (hE : ∀ e ∈ E, ∀ p ∈ P, e * p ∈ P ∧ e * p ≠ 1) {s : Finset X}
    (hs : ∀ x ∈ s, ∃ e ∈ E, e • x ∈ s) : s = ∅ := by
  choose! e he hes using hs
  set f : X → X := fun x ↦ e x • x
  -- every iterate of `f` stays in `s` and is the action of an element of `P`
  have hiter (m : ℕ) : ∀ x ∈ s, f^[m] x ∈ s ∧ ∃ p ∈ P, f^[m] x = p • x := by
    induction m with
    | zero => exact fun x hx ↦ ⟨hx, 1, hP, by simp⟩
    | succ m ih =>
      intro x hx
      obtain ⟨hmem, p, hp, hpx⟩ := ih x hx
      rw [Function.iterate_succ_apply']
      exact ⟨hes _ hmem, e (f^[m] x) * p, (hE _ (he _ hmem) p hp).1, by rw [mul_smul, ← hpx]⟩
  -- by pigeonhole some `y = f^[i] x` returns to itself, under an element `e * p ≠ 1`
  refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨i, j, hij, heq⟩ := s.finite_toSet.exists_lt_map_eq_of_forall_mem
    (f := fun m ↦ f^[m] x) fun m ↦ (hiter m x hx).1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
  obtain ⟨hmem, p, hp, hpx⟩ := hiter m _ (hiter i x hx).1
  rw [add_assoc i m 1, add_comm i (m + 1), Function.iterate_add_apply,
    Function.iterate_succ_apply'] at heq
  refine (hE _ (he _ hmem) p hp).2 (IsCancelSMul.eq_one_of_smul (x := f^[i] x) ?_)
  rw [mul_smul, ← hpx]
  exact heq.symm

open _root_.MulAction in
/-- **The order of a group acting freely divides the number of points**: every orbit of a free
action of `G` is a copy of `G`. No finiteness is needed, as `Nat.card` vanishes on infinite types,
and a free action on a nonempty finite type is by a finite group. -/
theorem natCard_dvd_natCard_of_isCancelSMul {G X : Type*} [Group G] [MulAction G X]
    [IsCancelSMul G X] : Nat.card G ∣ Nat.card X := by
  classical
  rcases finite_or_infinite X with hX | hX
  swap
  · simp
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · simp
  have : Finite G := .of_injective (· • x) fun _ _ ↦ IsCancelSMul.right_cancel _ _ x
  let Ω := orbitRel.Quotient G X
  let _ : Fintype Ω := Fintype.ofFinite Ω
  let _ (ω : Ω) : Finite (G ⧸ stabilizer G ω.out) := Quotient.finite _
  rw [Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer G X), Nat.card_sigma]
  simp_rw [IsCancelSMul.stabilizer_eq_bot]
  rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  simp

end TauCeti.MulAction

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- For a free action, the inverse of the orbit decomposition `selfEquivOrbitsQuotientProd'`
attached to a choice `φ` of orbit representatives sends `(q, g)` to `g • φ q`. -/
@[to_additive (attr := simp) selfEquivOrbitsQuotientProd'_symm_apply
  /-- For a free additive action, the inverse of the orbit decomposition
  `selfEquivOrbitsQuotientProd'` attached to a choice `φ` of orbit representatives sends `(q, g)`
  to `g +ᵥ φ q`. -/]
theorem selfEquivOrbitsQuotientProd'_symm_apply {φ : orbitRel.Quotient G X → X}
    (hφ : Function.LeftInverse Quotient.mk'' φ) (h : ∀ b : X, stabilizer G b = ⊥)
    (q : orbitRel.Quotient G X) (g : G) :
    (selfEquivOrbitsQuotientProd' hφ h).symm (q, g) = g • φ q := by
  -- Mathlib states no evaluation lemma for `selfEquivOrbitsQuotientProd'` or for the class-formula
  -- equivalences it is assembled from, in either direction, so the definitions must be unfolded.
  simp [selfEquivOrbitsQuotientProd', selfEquivSigmaOrbitsQuotientStabilizer',
    selfEquivSigmaOrbits', QuotientGroup.quotientEquivSelf, Subgroup.quotientEquivOfEq,
    Equiv.sigmaCongrRight_symm]

/-- For a free action, the inverse of the orbit decomposition `selfEquivOrbitsQuotientProd` sends
`(q, g)` to the translate `g • q.out` of the chosen representative of the orbit `q`. -/
@[to_additive (attr := simp) selfEquivOrbitsQuotientProd_symm_apply
  /-- For a free additive action, the inverse of the orbit decomposition
  `selfEquivOrbitsQuotientProd` sends `(q, g)` to the translate `g +ᵥ q.out` of the chosen
  representative of the orbit `q`. -/]
theorem selfEquivOrbitsQuotientProd_symm_apply (h : ∀ b : X, stabilizer G b = ⊥)
    (q : orbitRel.Quotient G X) (g : G) :
    (selfEquivOrbitsQuotientProd h).symm (q, g) = g • q.out :=
  selfEquivOrbitsQuotientProd'_symm_apply _ h q g

end MulAction
