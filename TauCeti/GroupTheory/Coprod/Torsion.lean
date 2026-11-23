/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import TauCeti.Algebra.Group.Conj
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.GroupTheory.CoprodI.Basic
import TauCeti.GroupTheory.CoprodI.Torsion

/-!
# Torsion elements in binary free products

Every element of finite order in the binary free product `G ∗ H` of two groups is conjugate to an
element of finite order in `G` or in `H`; in particular, a free product of two torsion-free groups
is torsion-free, and any mixed two-letter product `inl x * inr y` of nontrivial factor elements has
infinite order.

## Main results

* `Monoid.Coprod.isOfFinOrder_inl_iff`, `Monoid.Coprod.isOfFinOrder_inr_iff`,
  `Monoid.Coprod.orderOf_inl`, `Monoid.Coprod.orderOf_inr`: the canonical embeddings `inl` and
  `inr` preserve and reflect finite order and element orders.
* `Monoid.Coprod.not_isOfFinOrder_inl_mul_inr`, `Monoid.Coprod.not_isOfFinOrder_inr_mul_inl`:
  mixed products of nontrivial elements from `M` and `N` have infinite order.
* `Monoid.Coprod.exists_isConj_of_isOfFinOrder_of_ne_one`,
  `Monoid.Coprod.exists_isConj_inl_or_inr_of_isOfFinOrder`,
  `Monoid.Coprod.isOfFinOrder_iff`: classification of torsion elements in `G ∗ H`.
* `Monoid.Coprod.instIsMulTorsionFree`: the free product of two torsion-free groups is
  torsion-free.

## Implementation notes

Binary `Monoid.Coprod` results across arbitrary universes reduce to the indexed torsion
classification (`TauCeti.GroupTheory.CoprodI.Torsion`) over `Bool` via
`Monoid.CoprodI.uliftBoolEquivCoprod`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, Theorem 1.4.
-/

public section

namespace Monoid.Coprod

section Monoid

variable {M N : Type*} [Monoid M] [Monoid N]

/-- An element of `M` has finite order in `M ∗ N` if and only if it has finite order in `M`. -/
@[simp]
theorem isOfFinOrder_inl_iff {x : M} : IsOfFinOrder (inl x : M ∗ N) ↔ IsOfFinOrder x :=
  (inl_injective (N := N)).isOfFinOrder_iff

/-- An element of `N` has finite order in `M ∗ N` if and only if it has finite order in `N`. -/
@[simp]
theorem isOfFinOrder_inr_iff {y : N} : IsOfFinOrder (inr y : M ∗ N) ↔ IsOfFinOrder y :=
  (inr_injective (M := M)).isOfFinOrder_iff

/-- The canonical left embedding `inl : M →* M ∗ N` preserves element orders. -/
@[simp]
theorem orderOf_inl (x : M) : orderOf (inl x : M ∗ N) = orderOf x :=
  orderOf_injective (inl : M →* M ∗ N) inl_injective x

/-- The canonical right embedding `inr : N →* M ∗ N` preserves element orders. -/
@[simp]
theorem orderOf_inr (y : N) : orderOf (inr y : M ∗ N) = orderOf y :=
  orderOf_injective (inr : N →* M ∗ N) inr_injective y

/-- In `M ∗ N`, the product `inl x * inr y` of two nontrivial factor elements has infinite
order. -/
theorem not_isOfFinOrder_inl_mul_inr {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    ¬IsOfFinOrder (inl x * inr y : M ∗ N) := by
  intro hfin
  have hfin' : IsOfFinOrder ((CoprodI.uliftBoolEquivCoprod M N).symm (inl x * inr y)) :=
    (CoprodI.uliftBoolEquivCoprod M N).symm.isOfFinOrder_iff.mpr hfin
  rw [map_mul, CoprodI.uliftBoolEquivCoprod_symm_inl,
    CoprodI.uliftBoolEquivCoprod_symm_inr] at hfin'
  exact CoprodI.not_isOfFinOrder_of_mul_of Bool.false_ne_true
    (fun h => hx (congrArg ULift.down h)) (fun h => hy (congrArg ULift.down h)) hfin'

/-- In `M ∗ N`, the product `inr y * inl x` of two nontrivial factor elements has infinite
order. -/
theorem not_isOfFinOrder_inr_mul_inl {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    ¬IsOfFinOrder (inr y * inl x : M ∗ N) := fun h =>
  not_isOfFinOrder_inl_mul_inr hy hx <| by
    simpa using (MulEquiv.coprodComm M N).isOfFinOrder_iff.mpr h

end Monoid

section Group

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

-- Helper unpacking a nontrivial finite-order element of a `ULift` factor into the underlying group.
private theorem exists_of_ulift_branch {A K : Type*} [Group A] [Group K] {g : A}
    {f : K →* A} {z : ULift K} (hz1 : z ≠ 1) (hconj : IsConj g (f z.down))
    (hz_fin : IsOfFinOrder z) :
    ∃ x : K, x ≠ 1 ∧ IsConj g (f x) ∧ IsOfFinOrder x :=
  ⟨z.down, fun hx => hz1 (ULift.ext hx), hconj,
    (MulEquiv.ulift (α := K)).isOfFinOrder_iff.mpr hz_fin⟩

/-- Every nontrivial element of finite order in the free product `G ∗ H` of two groups is conjugate
to a nontrivial element of finite order in `G` or in `H`. -/
theorem exists_isConj_of_isOfFinOrder_of_ne_one {g : G ∗ H}
    (hg : IsOfFinOrder g) (hg1 : g ≠ 1) :
    (∃ x : G, x ≠ 1 ∧ IsConj g (inl x) ∧ IsOfFinOrder x) ∨
       (∃ y : H, y ≠ 1 ∧ IsConj g (inr y) ∧ IsOfFinOrder y) := by
  have hg' : IsOfFinOrder ((CoprodI.uliftBoolEquivCoprod G H).symm g) :=
    (CoprodI.uliftBoolEquivCoprod G H).symm.isOfFinOrder_iff.mpr hg
  have hg1' : (CoprodI.uliftBoolEquivCoprod G H).symm g ≠ 1 := by simp [hg1]
  obtain ⟨b, z, hz1, hconj, hz_fin⟩ :=
    CoprodI.exists_isConj_of_isOfFinOrder_of_ne_one hg' hg1'
  have he : IsConj g (CoprodI.uliftBoolEquivCoprod G H (CoprodI.of (i := b) z)) := by
    simpa only [MulEquiv.apply_symm_apply] using
      (CoprodI.uliftBoolEquivCoprod G H).isConj_apply_iff.mpr hconj
  cases b with
  | false =>
    rw [CoprodI.uliftBoolEquivCoprod_of_false (x := z)] at he
    exact Or.inl (exists_of_ulift_branch hz1 he hz_fin)
  | true =>
    rw [CoprodI.uliftBoolEquivCoprod_of_true (y := z)] at he
    exact Or.inr (exists_of_ulift_branch hz1 he hz_fin)

/-- Every element of finite order in `G ∗ H` is conjugate to an element of finite order in `G` or
in `H`. -/
theorem exists_isConj_inl_or_inr_of_isOfFinOrder {g : G ∗ H} (hg : IsOfFinOrder g) :
    (∃ x : G, IsConj g (inl x) ∧ IsOfFinOrder x) ∨
      (∃ y : H, IsConj g (inr y) ∧ IsOfFinOrder y) := by
  by_cases hg1 : g = 1
  · subst hg1
    exact Or.inl ⟨1, by simp, .one⟩
  · rcases exists_isConj_of_isOfFinOrder_of_ne_one hg hg1 with ⟨x, -, h, hx⟩ | ⟨y, -, h, hy⟩
    · exact Or.inl ⟨x, h, hx⟩
    · exact Or.inr ⟨y, h, hy⟩

/-- An element of `G ∗ H` has finite order if and only if it is conjugate to an element of finite
order in `G` or in `H`. -/
theorem isOfFinOrder_iff {g : G ∗ H} :
    IsOfFinOrder g ↔
      (∃ x : G, IsConj g (inl x) ∧ IsOfFinOrder x) ∨
        (∃ y : H, IsConj g (inr y) ∧ IsOfFinOrder y) := by
  refine ⟨exists_isConj_inl_or_inr_of_isOfFinOrder, ?_⟩
  rintro (⟨x, h, hx⟩ | ⟨y, h, hy⟩)
  · exact h.symm.isOfFinOrder ((inl : G →* G ∗ H).isOfFinOrder hx)
  · exact h.symm.isOfFinOrder ((inr : H →* G ∗ H).isOfFinOrder hy)

/-- The free product of two torsion-free groups is torsion-free. -/
instance instIsMulTorsionFree [IsMulTorsionFree G] [IsMulTorsionFree H] :
    IsMulTorsionFree (G ∗ H) := by
  have : ∀ b, IsMulTorsionFree (CoprodI.boolFactors G H b)
    | false => (MulEquiv.ulift (α := G)).isMulTorsionFree_iff.mpr inferInstance
    | true => (MulEquiv.ulift (α := H)).isMulTorsionFree_iff.mpr inferInstance
  exact (CoprodI.uliftBoolEquivCoprod G H).isMulTorsionFree_iff.mp
    CoprodI.instIsMulTorsionFree

end Group

end Monoid.Coprod
