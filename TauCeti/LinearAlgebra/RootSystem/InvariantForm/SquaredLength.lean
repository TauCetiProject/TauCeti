/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.RootSystem.LacingNumber
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.InvariantForm

/-!
# Squared root lengths of an invariant form and the Dynkin type

For a reduced irreducible crystallographic root system whose base has Cartan type `t`, this file
computes the squared lengths of the roots for an arbitrary invariant form: up to one nonzero
scale `s`, the simple root at node `i` has squared length `s * t.rootLength i`, and the set of all
squared root lengths is `{s, r * s}` for `r` the lacing number of `t`. Both values occur. So the
ratio of the two squared lengths of Mathlib's two-length theorem
`RootPairing.InvariantForm.exists_apply_eq_or` is `1` for the types `A`, `D`, `E`, is `2` for `B`,
`C`, `F₄` and is `3` for `G₂`.

The comparison goes through the identity
`⟨αⱼ, αᵢ^∨⟩ ⟨αᵢ, αᵢ⟩ = ⟨αᵢ, αⱼ^∨⟩ ⟨αⱼ, αⱼ⟩`, which makes the squared lengths of the simple roots a
right symmetriser of the Cartan matrix, as is the table `TauCeti.DynkinType.rootLength`. Since the
Dynkin diagram is connected, two such symmetrisers are proportional. Every root has the squared
length of a simple root, by `RootPairing.InvariantForm.exists_mem_support_apply_root_root_eq`.

## Main results

* `RootPairing.InvariantForm.exists_forall_apply_root_root_eq_mul_rootLength`: the squared lengths
  of the simple roots are one scale times the length table of the type.
* `RootPairing.InvariantForm.exists_range_apply_root_root_eq`: the set of all squared root lengths
  is `{s, r * s}`, with `r` the lacing number.
* `RootPairing.InvariantForm.exists_pos_range_apply_root_root_eq`: the same with `0 < s` for a
  positive-definite form.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, Appendix C(g), table (180).
-/

public section

namespace RootPairing.InvariantForm

open TauCeti

variable {ι K M N : Type*} [Finite ι] [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] {P : RootPairing ι K M N} [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

section CharZero

variable [CharZero K]

/-- **The simple roots of an irreducible root system have squared lengths proportional to the
length table of its Dynkin type.** The matching `e` of the base with the nodes of `t` is taken as
data so that the statement can name the node; any witness of `TauCeti.HasCartanType` supplies
one. -/
theorem exists_forall_apply_root_root_eq_mul_rootLength [Nonempty ι] (B : P.InvariantForm)
    {b : P.Base} {t : DynkinType} {e : b.support ≃ Fin t.rank}
    (he : ∀ i j, b.cartanMatrix i j = t.cartanMatrix (e i) (e j)) :
    ∃ s : K, s ≠ 0 ∧ ∀ i : b.support,
      B.form (P.root i) (P.root i) = s * (t.rootLength (e i) : K) := by
  obtain ⟨i₀, hi₀⟩ := b.support_nonempty
  let i₀' : b.support := ⟨i₀, hi₀⟩
  have hℓ (i : b.support) : (t.rootLength (e i) : K) ≠ 0 :=
    Int.cast_ne_zero.mpr (t.rootLength_pos (e i)).ne'
  refine ⟨B.form (P.root i₀) (P.root i₀) / (t.rootLength (e i₀') : K),
    div_ne_zero (B.ne_zero i₀) (hℓ i₀'), fun j ↦ ?_⟩
  refine b.induction_on_cartanMatrix
    (fun k ↦ B.form (P.root k) (P.root k) = B.form (P.root i₀) (P.root i₀) /
      (t.rootLength (e i₀') : K) * (t.rootLength (e k) : K)) (i := i₀') ?_ ?_
  · rw [div_mul_cancel₀ _ (hℓ i₀')]
  · intro u v hu huv
    have huv' : b.cartanMatrix u v ≠ 0 := fun h ↦ huv (b.cartanMatrix_apply_eq_zero_iff_symm.mp h)
    have hne : ((b.cartanMatrix u v : ℤ) : K) ≠ 0 := Int.cast_ne_zero.mpr huv'
    -- The squared lengths and the table are both right symmetrisers of the Cartan matrix.
    have hcast (i j : b.support) : ((b.cartanMatrix i j : ℤ) : K) = P.pairing i j := by
      simpa using b.algebraMap_cartanMatrixIn_apply ℤ i j
    have hB : ((b.cartanMatrix v u : ℤ) : K) * B.form (P.root u) (P.root u) =
        ((b.cartanMatrix u v : ℤ) : K) * B.form (P.root v) (P.root v) := by
      simpa only [hcast] using B.pairing_mul_eq_pairing_mul_swap u v
    have hA : ((b.cartanMatrix u v : ℤ) : K) * (t.rootLength (e v) : K) =
        ((b.cartanMatrix v u : ℤ) : K) * (t.rootLength (e u) : K) := by
      rw [he u v, he v u]
      exact_mod_cast t.cartanMatrix_mul_rootLength (e u) (e v)
    refine mul_left_cancel₀ hne ?_
    rw [← hB, hu]
    linear_combination (-(B.form (P.root i₀) (P.root i₀) / (t.rootLength (e i₀') : K))) * hA

/-- **The squared root lengths of an irreducible root system.** For a base of valid Cartan type `t`,
any invariant form has a nonzero scale `s` such that the squared lengths of the roots are exactly
`s` and `r * s`, with `r` the lacing number of `t`. -/
theorem exists_range_apply_root_root_eq (B : P.InvariantForm) {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    ∃ s : K, s ≠ 0 ∧ Set.range (fun k ↦ B.form (P.root k) (P.root k)) =
      {s, (t.lacingNumber : K) * s} := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  have : Nonempty b.support := e.symm.nonempty_congr.mp ⟨⟨0, DynkinType.rank_pos ht⟩⟩
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  obtain ⟨s, hs, hlen⟩ := B.exists_forall_apply_root_root_eq_mul_rootLength he
  refine ⟨s, hs, ?_⟩
  have hrange : Set.range (fun k ↦ B.form (P.root k) (P.root k)) =
      (fun r : ℤ ↦ (r : K) * s) '' Set.range t.rootLength := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨k, rfl⟩
      obtain ⟨i, hi, hk⟩ := B.exists_mem_support_apply_root_root_eq b k
      exact ⟨_, ⟨e ⟨i, hi⟩, rfl⟩, by simp [hk, hlen ⟨i, hi⟩, mul_comm]⟩
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      have := hlen (e.symm n)
      rw [Equiv.apply_symm_apply] at this
      exact ⟨((e.symm n : b.support) : ι), by simpa [mul_comm] using this⟩
  rw [hrange, DynkinType.range_rootLength ht]
  simp

end CharZero

/-- **The squared root lengths of a positive-definite invariant form.** For a base of valid Cartan
type `t` there is a positive `s` such that the squared lengths of the roots are exactly `s` and
`r * s`, with `r` the lacing number of `t`. -/
theorem exists_pos_range_apply_root_root_eq [LinearOrder K] [IsStrictOrderedRing K]
    (B : P.InvariantForm) (hB : B.form.toQuadraticMap.PosDef) {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    ∃ s : K, 0 < s ∧ Set.range (fun k ↦ B.form (P.root k) (P.root k)) =
      {s, (t.lacingNumber : K) * s} := by
  obtain ⟨s, -, hs⟩ := B.exists_range_apply_root_root_eq h ht
  refine ⟨s, ?_, hs⟩
  -- `s` is itself a squared root length.
  obtain ⟨k, rfl⟩ : s ∈ Set.range (fun k ↦ B.form (P.root k) (P.root k)) := hs ▸ Set.mem_insert _ _
  exact hB _ (P.ne_zero k)

end RootPairing.InvariantForm
