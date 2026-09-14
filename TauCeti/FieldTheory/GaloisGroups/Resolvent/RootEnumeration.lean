/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Roots

/-!
# Enumerating the roots of a polynomial

A root-side resolvent is evaluated on a family `x : Fin n → L`.  To compare that family with
a coefficient-side construction, one must say that it lists every root of the polynomial with
the correct multiplicity.  `IsRootEnumeration f x` records exactly that multiset equation.

The equation has two important consequences.  If `n = f.natDegree`, it forces `f` to split in
`L`.  Subject to the same degree condition, the enumeration is injective exactly when the mapped
polynomial is separable.  Thus an injective root enumeration has precisely the content needed to
identify `Fin n` with the distinct root set; repeated roots are not silently discarded.

## Main definitions

* `TauCeti.IsRootEnumeration`: `x : Fin n → L` lists the roots of `f` in `L`, with
  multiplicity.

## Main results

* `TauCeti.IsRootEnumeration.splits`: a full root enumeration forces the mapped polynomial to
  split.
* `TauCeti.IsRootEnumeration.injective_iff_separable`: a full enumeration has no repetitions
  exactly when the mapped polynomial is separable.
* `TauCeti.IsRootEnumeration.comp_perm`: permuting the indices preserves a root enumeration.
* `TauCeti.IsRootEnumeration.equivRootSet`: an injective full enumeration identifies its index
  type with the root set.
* `Polynomial.Separable.isRootEnumeration`: a numbering of the root set of a separable
  polynomial supplies a root enumeration.
-/

public section

namespace TauCeti

open Finset Polynomial

universe u v

variable {F : Type u} [Field F] {L : Type v} [Field L] [Algebra F L]
  {n : ℕ} {f : F[X]} {x : Fin n → L}

/-- `x : Fin n → L` is a root enumeration of `f` if it lists the roots of `f` in `L`, with
multiplicity.  Unlike an enumeration of `f.rootSet L`, this definition also applies when roots
repeat. -/
def IsRootEnumeration (f : F[X]) (x : Fin n → L) : Prop :=
  (f.map (algebraMap F L)).roots = Multiset.map x univ.val

/-- The defining multiset equation for a root enumeration. -/
theorem isRootEnumeration_iff :
    IsRootEnumeration f x ↔
      (f.map (algebraMap F L)).roots = Multiset.map x univ.val :=
  Iff.rfl

namespace IsRootEnumeration

/-- A root enumeration contains `n` roots, counted with multiplicity. -/
theorem card_roots (hx : IsRootEnumeration f x) :
    (f.map (algebraMap F L)).roots.card = n := by
  rw [hx, Multiset.card_map]
  change Fintype.card (Fin n) = n
  exact Fintype.card_fin n

/-- Membership in the root multiset is equivalent to occurring in a root enumeration. -/
theorem mem_roots_iff (hx : IsRootEnumeration f x) {a : L} :
    a ∈ (f.map (algebraMap F L)).roots ↔ ∃ i : Fin n, x i = a := by
  rw [hx]
  simp

/-- Permuting the indices of a root enumeration preserves the enumerated multiset. -/
theorem comp_perm (hx : IsRootEnumeration f x) (σ : Equiv.Perm (Fin n)) :
    IsRootEnumeration f (x ∘ σ) := by
  rw [IsRootEnumeration, hx, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Whether a family enumerates the roots is independent of a permutation of its indices. -/
@[simp]
theorem comp_perm_iff (σ : Equiv.Perm (Fin n)) :
    IsRootEnumeration f (x ∘ σ) ↔ IsRootEnumeration f x := by
  change (f.map (algebraMap F L)).roots = Multiset.map (x ∘ σ) univ.val ↔
    (f.map (algebraMap F L)).roots = Multiset.map x univ.val
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Membership in the root set is equivalent to occurring in a root enumeration. -/
theorem mem_rootSet_iff (hx : IsRootEnumeration f x) {a : L} :
    a ∈ f.rootSet L ↔ ∃ i : Fin n, x i = a :=
  Polynomial.mem_rootSet'.trans <| Polynomial.mem_aroots'.symm.trans hx.mem_roots_iff

/-- Listing `f.natDegree` roots with multiplicity forces the mapped polynomial to split. -/
theorem splits (hx : IsRootEnumeration f x) (hdeg : f.natDegree = n) :
    (f.map (algebraMap F L)).Splits := by
  rw [Polynomial.splits_iff_card_roots, hx.card_roots, ← hdeg,
    Polynomial.natDegree_map]

/-- For a full root enumeration, injectivity is exactly separability of the mapped polynomial.

The splitting hypothesis needed by `Polynomial.nodup_roots_iff_of_splits` is derived from the
enumeration itself. -/
theorem injective_iff_separable (hx : IsRootEnumeration f x) (hf : f ≠ 0)
    (hdeg : f.natDegree = n) :
    Function.Injective x ↔ (f.map (algebraMap F L)).Separable := by
  rw [← Fintype.nodup_map_univ_iff_injective, ← hx,
    Polynomial.nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf) (hx.splits hdeg)]

/-- A full injective root enumeration identifies its indexing type with the distinct root set. -/
noncomputable def equivRootSet (hx : IsRootEnumeration f x) (hinj : Function.Injective x) :
    Fin n ≃ f.rootSet L where
  toFun i := ⟨x i, hx.mem_rootSet_iff.2 ⟨i, rfl⟩⟩
  invFun a := Classical.choose (hx.mem_rootSet_iff.1 a.2)
  left_inv i := by
    apply hinj
    exact Classical.choose_spec (hx.mem_rootSet_iff.1 <| hx.mem_rootSet_iff.2 ⟨i, rfl⟩)
  right_inv a := by
    apply Subtype.ext
    exact Classical.choose_spec (hx.mem_rootSet_iff.1 a.2)

@[simp]
theorem coe_equivRootSet (hx : IsRootEnumeration f x) (hinj : Function.Injective x)
    (i : Fin n) : (hx.equivRootSet hinj i : L) = x i :=
  by exact (rfl)

theorem equivRootSet_symm_apply (hx : IsRootEnumeration f x) (hinj : Function.Injective x)
    (a : f.rootSet L) : x ((hx.equivRootSet hinj).symm a) = a := by
  simpa only [coe_equivRootSet] using
    congrArg Subtype.val ((hx.equivRootSet hinj).apply_symm_apply a)

end IsRootEnumeration

/-- A numbering of the root set of a separable polynomial enumerates the full root multiset.
This packages `Polynomial.Separable.roots_map_eq_map_numbering` as an
`IsRootEnumeration`. -/
theorem _root_.Polynomial.Separable.isRootEnumeration (hf : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet L) :
    IsRootEnumeration f (fun i ↦ (e i : L)) :=
  hf.roots_map_eq_map_numbering e

end TauCeti
