/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import TauCeti.GroupTheory.CoprodI.Basic
import TauCeti.GroupTheory.CoprodI.Torsion

/-!
# Torsion in binary free products

In a binary free product `M ∗ N` of monoids, the product `inl x * inr y` (or `inr y * inl x`) of
two nonidentity elements from distinct factors corresponds under `Monoid.Coprod.toCoprodI` to a
two-letter reduced word with distinct endpoint factors, so it has infinite order.

When the factors are groups, transporting the indexed classification
`Monoid.CoprodI.isOfFinOrder_iff` across `Monoid.Coprod.toCoprodI` shows that every finite-order
element of `G ∗ H` is conjugate to an element of `G` or `H` of the same order.

## Main results

* `Monoid.Coprod.not_isOfFinOrder_inl_mul_inr`, `Monoid.Coprod.orderOf_inl_mul_inr_eq_zero`,
  `Monoid.Coprod.orderOf_inr_mul_inl_eq_zero`: the product of two nonidentity elements from
  distinct factors of `M ∗ N` has infinite order.
* `Monoid.Coprod.isOfFinOrder_iff`, `Monoid.Coprod.orderOf_eq_iff`: classification of
  finite-order elements and elements of given finite order `n > 1` in a binary free product `G ∗ H`
  of groups.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, §1,
  Theorem 1.4.
* J.-P. Serre, *Trees*, Springer, 1980, Chapter I, §4.2, Corollary 1.
-/

public section

open scoped Monoid.Coprod

namespace Monoid.Coprod

section Monoid

variable {M : Type u₁} {N : Type u₂} [Monoid M] [Monoid N]

/-- In `M ∗ N`, the product `inl x * inr y` of two nonidentity elements from distinct factors does
not have finite order. -/
theorem not_isOfFinOrder_inl_mul_inr {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    ¬ IsOfFinOrder (inl x * inr y : M ∗ N) := by
  let x' : Factors M N false := ULift.up.{u₂} x
  let y' : Factors M N true := ULift.up.{u₁} y
  have hx' : x' ≠ 1 := fun h ↦ hx (congrArg ULift.down h)
  have hy' : y' ≠ 1 := fun h ↦ hy (congrArg ULift.down h)
  let w : CoprodI.NeWord (Factors M N) false true :=
    .append (.singleton x' hx') (by decide) (.singleton y' hy')
  have hw : toCoprodI (inl x * inr y : M ∗ N) = w.prod := by
    rw [map_mul, toCoprodI_inl, toCoprodI_inr, CoprodI.NeWord.append_prod,
      CoprodI.NeWord.prod_singleton, CoprodI.NeWord.prod_singleton]
  intro hfin
  exact w.not_isOfFinOrder_prod_of_ne (by decide)
    (hw ▸ (toCoprodI (M := M) (N := N)).toMonoidHom.isOfFinOrder hfin)

/-- In `M ∗ N`, the product `inl x * inr y` of two nonidentity elements from distinct factors has
infinite order (`orderOf = 0`). -/
theorem orderOf_inl_mul_inr_eq_zero {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    orderOf (inl x * inr y : M ∗ N) = 0 :=
  orderOf_eq_zero (not_isOfFinOrder_inl_mul_inr hx hy)

/-- In `M ∗ N`, the product `inr y * inl x` of two nonidentity elements from distinct factors has
infinite order (`orderOf = 0`). -/
theorem orderOf_inr_mul_inl_eq_zero {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    orderOf (inr y * inl x : M ∗ N) = 0 := by
  let e : M ∗ N ≃* N ∗ M := MulEquiv.coprodComm M N
  rw [← orderOf_injective e.toMonoidHom e.injective]
  simpa [e] using orderOf_inl_mul_inr_eq_zero hy hx

end Monoid

section Group

variable {G : Type u₁} {H : Type u₂} [Group G] [Group H]

/-- **Torsion in a binary free product of groups.** An element of `G ∗ H` has finite order if and
only if it is conjugate to `inl x` for a finite-order element `x : G` or to `inr y` for a
finite-order element `y : H`. -/
theorem isOfFinOrder_iff {g : G ∗ H} :
    IsOfFinOrder g ↔
      (∃ x : G, IsOfFinOrder x ∧ IsConj g (inl x)) ∨
        (∃ y : H, IsOfFinOrder y ∧ IsConj g (inr y)) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have hg' : IsOfFinOrder (toCoprodI g) :=
      (toCoprodI (M := G) (N := H)).toMonoidHom.isOfFinOrder hg
    rcases CoprodI.isOfFinOrder_iff.mp hg' with h1 | ⟨b, x, -, hx, hconj⟩
    · have hg1 : g = 1 := toCoprodI.injective (by simpa using h1)
      exact Or.inl ⟨1, IsOfFinOrder.one, by simp [hg1]⟩
    · cases b
      · refine Or.inl ⟨x.down, (MulEquiv.ulift : ULift.{u₂} G ≃* G).toMonoidHom.isOfFinOrder hx, ?_⟩
        have hc := toCoprodI.symm.toMonoidHom.map_isConj hconj
        rwa [MulEquiv.coe_toMonoidHom, toCoprodI.symm_apply_apply,
          toCoprodI_symm_of_false] at hc
      · refine Or.inr ⟨x.down, (MulEquiv.ulift : ULift.{u₁} H ≃* H).toMonoidHom.isOfFinOrder hx, ?_⟩
        have hc := toCoprodI.symm.toMonoidHom.map_isConj hconj
        rwa [MulEquiv.coe_toMonoidHom, toCoprodI.symm_apply_apply,
          toCoprodI_symm_of_true] at hc
  · rintro (⟨x, hx, hconj⟩ | ⟨y, hy, hconj⟩)
    · exact hconj.symm.isOfFinOrder ((inl : G →* G ∗ H).isOfFinOrder hx)
    · exact hconj.symm.isOfFinOrder ((inr : H →* G ∗ H).isOfFinOrder hy)

/-- For `1 < n`, an element of `G ∗ H` has order `n` if and only if it is conjugate to `inl x` for
some `x : G` of order `n` or to `inr y` for some `y : H` of order `n`. -/
theorem orderOf_eq_iff {g : G ∗ H} {n : ℕ} (hn : 1 < n) :
    orderOf g = n ↔
      (∃ x : G, orderOf x = n ∧ IsConj g (inl x)) ∨
        (∃ y : H, orderOf y = n ∧ IsConj g (inr y)) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
    rcases isOfFinOrder_iff.mp hfin with ⟨x, -, hconj⟩ | ⟨y, -, hconj⟩
    · let ⟨_, hc⟩ := hconj
      exact Or.inl ⟨x, by rw [← orderOf_injective (inl : G →* G ∗ H) inl_injective x,
        ← hc.orderOf_eq, hg], hconj⟩
    · let ⟨_, hc⟩ := hconj
      exact Or.inr ⟨y, by rw [← orderOf_injective (inr : H →* G ∗ H) inr_injective y,
        ← hc.orderOf_eq, hg], hconj⟩
  · rintro (⟨x, hx, ⟨_, hc⟩⟩ | ⟨y, hy, ⟨_, hc⟩⟩)
    · rw [hc.orderOf_eq, orderOf_injective (inl : G →* G ∗ H) inl_injective x, hx]
    · rw [hc.orderOf_eq, orderOf_injective (inr : H →* G ∗ H) inr_injective y, hy]

end Group

end Monoid.Coprod
