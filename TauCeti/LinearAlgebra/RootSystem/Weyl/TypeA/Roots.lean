/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
public import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA.Presentation
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# The roots of type `Aₙ` as ordered pairs of letters

Let `P` be a finite reduced crystallographic root pairing over a commutative domain of
characteristic zero, with a base `b` whose simple roots are labelled by the nodes `0, …, n - 1` of
the chain `Aₙ` compatibly with the Cartan matrices. The marked isomorphism
`RootPairing.typeAWeylGroupEquiv` identifies the Weyl group with `Equiv.Perm (Fin (n + 1))`. This
file completes the dictionary on the roots: they correspond to the ordered pairs `(x, y)` of
distinct letters, the root `eₓ - e_y` of the classical model, in such a way that

* the simple root labelled `k` is the pair `(k, k + 1)`;
* a Weyl group element acts on the roots as its permutation acts on both letters of a pair;
* the reflection in the root of the pair `(x, y)` is the transposition of `x` and `y`;
* a root is positive exactly when its first letter is smaller than its second, and its negative
  is the reversed pair.

The pairs are defined by transport: a root is `w αᵢ` for some Weyl group element `w` and some
simple root `αᵢ` (`TauCeti.exists_mem_support_weylGroupToPerm_eq`), and it is sent to the image of
the pair of `αᵢ` under the permutation of `w`. This does not depend on the choice of `w` and `i`:
if `u αᵢ = αⱼ`, then the permutation of `u` conjugates the transposition of `αᵢ` to that of `αⱼ`,
and since it keeps the letters of `αᵢ` in order it sends them to those of `αⱼ` in order. The
resulting map is surjective because permutations act transitively on ordered pairs of distinct
letters, hence bijective because both sides have `n (n + 1)` elements
(`RootPairing.natCard_eq_of_hasCartanType_A`). No spanning hypothesis on `P` is needed.

## Main definitions

* `RootPairing.typeARootIndexEquiv`: the bijection from the root indices of `P` to the ordered
  pairs of distinct elements of `Fin (n + 1)`.

## Main results

* `RootPairing.typeARootIndexEquiv_simple`: the simple root labelled `k` is the pair `(k, k + 1)`.
* `RootPairing.typeARootIndexEquiv_weylGroupToPerm`: the bijection intertwines the action of the
  Weyl group on roots with the action of permutations on both letters of a pair.
* `RootPairing.typeAWeylGroupEquiv_ofIdx_eq_swap`: the reflection in a root is the transposition of
  its two letters.
* `RootPairing.isPos_iff_typeARootIndexEquiv`: a root is positive exactly when its first letter is
  smaller than its second.
* `RootPairing.eq_typeARootIndexEquiv`: the bijection is the only map with the first two
  properties.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29 (1990), Section 2.10, type `A`.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
-/

public section

open TauCeti TauCeti.DynkinType TauCeti.SplitTorus

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {n : ℕ} (e : b.support ≃ Fin n)
  (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))

/-- The ordered pair of letters `(σ k, σ (k + 1))`, the image under `σ` of the pair of the simple
root labelled `k`. -/
private def letterPair (σ : Equiv.Perm (Fin (n + 1))) (k : Fin n) : TypeAIndex n :=
  ⟨(σ k.castSucc, σ k.succ), σ.injective.ne Fin.castSucc_lt_succ.ne⟩

/-- The pair of a product of permutations is obtained by applying the left factor to both letters
of the pair of the right factor. -/
private theorem letterPair_mul (σ τ : Equiv.Perm (Fin (n + 1))) (k : Fin n) :
    letterPair (σ * τ) k = coordinatePermRootIndex σ (letterPair τ k) :=
  Subtype.ext (by simp [letterPair])

/-- A permutation keeping the letters `k` and `k + 1` in order and conjugating the transposition
`(k k+1)` to the transposition `(l l+1)` sends `k` to `l` and `k + 1` to `l + 1`. -/
private theorem letterPair_eq_of_swap_eq {σ : Equiv.Perm (Fin (n + 1))} {k l : Fin n}
    (hlt : σ k.castSucc < σ k.succ)
    (hσ : Equiv.swap l.castSucc l.succ = σ * Equiv.swap k.castSucc k.succ * σ⁻¹) :
    letterPair σ k = letterPair 1 l := by
  rw [← Equiv.swap_apply_apply] at hσ
  set x := σ k.castSucc
  set y := σ k.succ
  have hl : Equiv.swap x y l.castSucc ≠ l.castSucc := by
    rw [← hσ, Equiv.swap_apply_left]
    exact Fin.castSucc_lt_succ.ne'
  obtain ⟨-, hx | hy⟩ := Equiv.swap_apply_ne_self_iff.mp hl
  · -- The first letters agree, and then so do the second ones.
    have h2 : l.succ = y := by
      rw [← Equiv.swap_apply_left l.castSucc l.succ, hσ, ← hx, Equiv.swap_apply_left]
    exact Subtype.ext (Prod.ext hx.symm h2.symm)
  · -- The letters cannot be exchanged, since `σ` keeps them in order.
    have h2 : l.succ = x := by
      rw [← Equiv.swap_apply_left l.castSucc l.succ, hσ, ← hy, Equiv.swap_apply_right]
    exact absurd (hy ▸ h2 ▸ hlt) (not_lt.mpr Fin.castSucc_lt_succ.le)

/-- A Weyl group element carrying the simple root `i` to the simple root `j` sends the letters of
`i` to those of `j`, in order. -/
private theorem letterPair_typeAWeylGroupEquiv_of_weylGroupToPerm_eq {u : P.weylGroup}
    {i j : b.support} (hu : P.weylGroupToPerm u i = j) :
    letterPair (P.typeAWeylGroupEquiv b e he u) (e i) = letterPair 1 (e j) := by
  refine letterPair_eq_of_swap_eq ?_ ?_
  · rw [← isPos_weylGroupToPerm_iff_typeAWeylGroupEquiv, hu]
    exact Base.isPos_of_mem_support j.2
  · rw [← P.typeAWeylGroupEquiv_ofIdx b e he, ← P.typeAWeylGroupEquiv_ofIdx b e he, ← map_inv,
      ← map_mul, ← map_mul, ← hu, weylGroup.ofIdx_weylGroupToPerm_eq_conj]

/-- The ordered pair of letters attached to a root index: the image of the pair of a simple root
`αᵢ` under the permutation of a Weyl group element `w` with `w αᵢ` the given root. Both choices are
made by `TauCeti.exists_mem_support_weylGroupToPerm_eq`;
`RootPairing.typeARootIndex_weylGroupToPerm` shows that the result does not depend on them. -/
private noncomputable def typeARootIndex (k : ι) : TypeAIndex n :=
  have h := exists_mem_support_weylGroupToPerm_eq b k
  letterPair (P.typeAWeylGroupEquiv b e he h.choose_spec.2.choose)
    (e ⟨h.choose, h.choose_spec.1⟩)

/-- The pair of letters of the root `w αᵢ` is the image of the pair of `αᵢ` under the permutation
of `w`, for every Weyl group element `w` and every simple root `αᵢ`. -/
private theorem typeARootIndex_weylGroupToPerm (w : P.weylGroup) (i : b.support) :
    P.typeARootIndex b e he (P.weylGroupToPerm w i) =
      letterPair (P.typeAWeylGroupEquiv b e he w) (e i) := by
  have h := exists_mem_support_weylGroupToPerm_eq b (P.weylGroupToPerm w i)
  set j : b.support := ⟨h.choose, h.choose_spec.1⟩
  set v := h.choose_spec.2.choose
  have hv : P.weylGroupToPerm v j = P.weylGroupToPerm w i := h.choose_spec.2.choose_spec
  have hdef : P.typeARootIndex b e he (P.weylGroupToPerm w i) =
      letterPair (P.typeAWeylGroupEquiv b e he v) (e j) := rfl
  -- The element `v⁻¹ * w` carries the simple root `i` to the simple root `j`.
  have hu : P.weylGroupToPerm (v⁻¹ * w) i = j := by
    rw [map_mul, Equiv.Perm.mul_apply, ← hv, map_inv, Equiv.Perm.inv_eq_iff_eq]
  rw [hdef, ← mul_inv_cancel_left v w, map_mul, letterPair_mul,
    P.letterPair_typeAWeylGroupEquiv_of_weylGroupToPerm_eq b e he hu, ← letterPair_mul, mul_one]

/-- Permutations act transitively on ordered pairs of distinct letters: every such pair is the
image of the pair `(k, k + 1)` of a simple root under some permutation. -/
private theorem exists_letterPair_eq (k : Fin n) (q : TypeAIndex n) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), letterPair σ k = q := by
  obtain ⟨σ, h1, h2⟩ := MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive _ 2) Fin.castSucc_lt_succ.ne q.property
  exact ⟨σ, Subtype.ext (Prod.ext h1 h2)⟩

/-- **The roots of type `Aₙ` are the ordered pairs of distinct letters.** For a base `b` whose
simple roots are labelled by `e` as the nodes of the chain `Aₙ`, compatibly with the Cartan
matrices, this is the bijection from the root indices to the ordered pairs `(x, y)` of distinct
elements of `Fin (n + 1)`, the root `eₓ - e_y` of the classical model. The simple root `i` is the
pair `(e i, e i + 1)` (`RootPairing.typeARootIndexEquiv_simple`), and the Weyl group acts through
`RootPairing.typeAWeylGroupEquiv` on both letters of a pair
(`RootPairing.typeARootIndexEquiv_weylGroupToPerm`); these two properties determine it
(`RootPairing.eq_typeARootIndexEquiv`). -/
noncomputable def typeARootIndexEquiv : ι ≃ TypeAIndex n :=
  Equiv.ofBijective (P.typeARootIndex b e he) <| by
    have hsurj : Function.Surjective (P.typeARootIndex b e he) := by
      intro q
      -- A pair of distinct letters exists only when `n ≥ 1`, so there is a simple root.
      have hn : 0 < n := by
        have := Fintype.one_lt_card_iff.mpr ⟨q.val.1, q.val.2, q.property⟩
        rw [Fintype.card_fin] at this
        omega
      set i := e.symm ⟨0, hn⟩
      obtain ⟨σ, hσ⟩ := exists_letterPair_eq (e i) q
      obtain ⟨w, rfl⟩ := (P.typeAWeylGroupEquiv b e he).surjective σ
      exact ⟨P.weylGroupToPerm w i, by rw [typeARootIndex_weylGroupToPerm, hσ]⟩
    refine hsurj.bijective_of_nat_card_le ?_
    have h : HasCartanType P b (.A n) := (hasCartanType_iff b _).mpr
      ⟨e, by rw [DynkinType.cartanMatrix_A]; exact he⟩
    rw [P.natCard_eq_of_hasCartanType_A b h, Nat.card_congr (typeAIndexEquiv n), Nat.card_fin]

/-- **The Weyl group acts on the roots of type `Aₙ` by permuting letters**: the pair of the image
of a root under a Weyl group element is obtained by applying its permutation to both letters. -/
theorem typeARootIndexEquiv_weylGroupToPerm (w : P.weylGroup) (k : ι) :
    P.typeARootIndexEquiv b e he (P.weylGroupToPerm w k) =
      coordinatePermRootIndex (P.typeAWeylGroupEquiv b e he w)
        (P.typeARootIndexEquiv b e he k) := by
  obtain ⟨i, hi, v, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b k
  simp only [typeARootIndexEquiv, Equiv.ofBijective_apply]
  rw [← Equiv.Perm.mul_apply, ← map_mul, typeARootIndex_weylGroupToPerm (i := ⟨i, hi⟩),
    typeARootIndex_weylGroupToPerm (i := ⟨i, hi⟩), map_mul, letterPair_mul]

/-- The bijection intertwines the permutation of the roots by a Weyl group element with the
action of its permutation on both letters of a pair. -/
theorem typeARootIndexEquiv_permCongr_weylGroupToPerm (w : P.weylGroup) :
    (P.typeARootIndexEquiv b e he).permCongr (P.weylGroupToPerm w) =
      coordinatePermRootIndex (P.typeAWeylGroupEquiv b e he w) :=
  _root_.Equiv.ext fun q ↦ by
    rw [Equiv.permCongr_apply, typeARootIndexEquiv_weylGroupToPerm, Equiv.apply_symm_apply]

/-- **The simple root labelled `k` is the pair `(k, k + 1)`.** -/
@[simp]
theorem typeARootIndexEquiv_simple (i : b.support) :
    (P.typeARootIndexEquiv b e he i).val = ((e i).castSucc, (e i).succ) := by
  have h := typeARootIndex_weylGroupToPerm P b e he 1 i
  rw [map_one, Equiv.Perm.one_apply, map_one] at h
  simp only [typeARootIndexEquiv, Equiv.ofBijective_apply, h, letterPair, Equiv.Perm.one_apply]

/-- **The reflection in a root of type `Aₙ` is the transposition of its two letters.** This extends
`RootPairing.typeAWeylGroupEquiv_ofIdx` from the simple roots to all roots. -/
theorem typeAWeylGroupEquiv_ofIdx_eq_swap (k : ι) :
    P.typeAWeylGroupEquiv b e he (weylGroup.ofIdx P k) =
      Equiv.swap (P.typeARootIndexEquiv b e he k).val.1
        (P.typeARootIndexEquiv b e he k).val.2 := by
  obtain ⟨i, hi, v, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b k
  have hk := typeARootIndexEquiv_simple P b e he ⟨i, hi⟩
  rw [typeARootIndexEquiv_weylGroupToPerm, coordinatePermRootIndex_coe, hk,
    weylGroup.ofIdx_weylGroupToPerm_eq_conj, map_mul, map_mul, map_inv,
    typeAWeylGroupEquiv_ofIdx (i := ⟨i, hi⟩), Equiv.swap_apply_apply]

/-- **A root of type `Aₙ` is positive exactly when its first letter is smaller than its
second.** -/
theorem isPos_iff_typeARootIndexEquiv (k : ι) :
    b.IsPos k ↔
      (P.typeARootIndexEquiv b e he k).val.1 < (P.typeARootIndexEquiv b e he k).val.2 := by
  obtain ⟨i, hi, v, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b k
  rw [typeARootIndexEquiv_weylGroupToPerm, coordinatePermRootIndex_coe,
    typeARootIndexEquiv_simple P b e he ⟨i, hi⟩]
  exact isPos_weylGroupToPerm_iff_typeAWeylGroupEquiv P b e he v ⟨i, hi⟩

/-- The negative of a root of type `Aₙ` is the reversed pair of letters. -/
theorem typeARootIndexEquiv_neg (k : ι) :
    letI := P.indexNeg
    (P.typeARootIndexEquiv b e he (-k)).val =
      ((P.typeARootIndexEquiv b e he k).val.2, (P.typeARootIndexEquiv b e he k).val.1) := by
  let := P.indexNeg
  -- The negative `-k` is the reflection of `k` in itself.
  have h : -k = P.weylGroupToPerm (weylGroup.ofIdx P k) k := by
    rw [weylGroupToPerm_ofIdx_apply, indexNeg_neg]
  rw [h, typeARootIndexEquiv_weylGroupToPerm, coordinatePermRootIndex_coe,
    typeAWeylGroupEquiv_ofIdx_eq_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- **The bijection is determined by the simple roots and the Weyl action.** A map from the root
indices to the ordered pairs of distinct letters, sending the simple root `i` to `(e i, e i + 1)`
and intertwining the Weyl group action with the action of permutations on both letters, is
`RootPairing.typeARootIndexEquiv`. -/
theorem eq_typeARootIndexEquiv (f : ι → TypeAIndex n)
    (hsimple : ∀ i : b.support, (f i).val = ((e i).castSucc, (e i).succ))
    (hweyl : ∀ (w : P.weylGroup) (k : ι), f (P.weylGroupToPerm w k) =
      coordinatePermRootIndex (P.typeAWeylGroupEquiv b e he w) (f k)) :
    f = P.typeARootIndexEquiv b e he := by
  funext k
  obtain ⟨i, hi, v, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b k
  rw [hweyl, typeARootIndexEquiv_weylGroupToPerm]
  congr 1
  exact Subtype.ext ((hsimple ⟨i, hi⟩).trans (typeARootIndexEquiv_simple P b e he ⟨i, hi⟩).symm)

end RootPairing
