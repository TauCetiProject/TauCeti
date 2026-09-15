/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# Numbering and enumerating the roots of a polynomial

This file relates an explicit numbering of a polynomial's root set to its multiset of roots, and
records what it means for a family `x : Fin n → E` to list *all* the roots of `f`.

A root-side resolvent is evaluated on such a family.  To compare it with a coefficient-side
construction, one must say that the family lists every root of the polynomial with the correct
multiplicity.  `IsRootEnumeration f x` records exactly that multiset equation.

Over fields the equation has two important consequences.  If `n = f.natDegree`, it forces `f` to
split in `E`.  Subject to the same degree condition and to `f ≠ 0`, the enumeration is injective
exactly when the mapped polynomial is separable.  Thus an injective root enumeration has precisely
the content needed to identify `Fin n` with the distinct root set; repeated roots are not silently
discarded.

## Main definitions

* `TauCeti.IsRootEnumeration`: `x : Fin n → E` lists the roots of `f` in `E`, with multiplicity.

## Main results

* `Polynomial.Separable.roots_map_eq_map_numbering`: for a separable polynomial, a numbering of
  its root set enumerates its full root multiset after base change.
* `TauCeti.IsRootEnumeration.comp_perm_iff`: whether a family enumerates the roots is unchanged
  by permuting its indices.
* `TauCeti.IsRootEnumeration.equivRootSet`: an injective full enumeration identifies its index
  type with the root set.
* `Polynomial.Separable.isRootEnumeration`: a numbering of the root set of a separable
  polynomial supplies a root enumeration.
* `TauCeti.IsRootEnumeration.splits`: over fields, a full root enumeration forces the mapped
  polynomial to split.
* `TauCeti.IsRootEnumeration.injective_iff_separable`: over fields, a full enumeration of a
  nonzero polynomial has no repetitions exactly when the mapped polynomial is separable.

The numbering lemma lets root-product formulas be expressed as finite products indexed by
`Fin f.natDegree`, without choosing a global order on the root set.

## References

`IsRootEnumeration`, together with the splitting and separability statements about it, is the
Layer 4 milestone "The root data that a resolvent statement assumes" of the
[polynomial Galois groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/PolynomialGaloisGroups/README.md);
the definition itself is stated in that roadmap's
[`Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/PolynomialGaloisGroups/Suggested.lean).
-/

public section

namespace TauCeti

open Finset Polynomial

section Domain

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E]
  {n : ℕ} {f : F[X]} {x : Fin n → E}

/-- A numbering of the root set of a separable polynomial enumerates the whole root multiset:
separability makes the roots simple, so the multiset is the image of the numbering. -/
theorem _root_.Polynomial.Separable.roots_map_eq_map_numbering (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    (f.map (algebraMap F E)).roots = Multiset.map (fun i ↦ ((e i : E))) univ.val := by
  have hmem : ∀ {a : E}, a ∈ (f.map (algebraMap F E)).roots ↔ a ∈ f.rootSet E := fun {_} ↦
    Polynomial.mem_aroots'.trans Polynomial.mem_rootSet'.symm
  refine (Multiset.Nodup.ext (nodup_roots hsep.map) ?_).mpr ?_
  · exact univ.nodup.map fun i j h ↦ e.injective (Subtype.ext h)
  · intro a
    simp only [Multiset.mem_map, Finset.mem_val, mem_univ, true_and]
    exact ⟨fun ha ↦ ⟨e.symm ⟨a, hmem.mp ha⟩, by simp⟩, fun ⟨i, hi⟩ ↦ hi ▸ hmem.mpr (e i).2⟩

/-- `x : Fin n → E` is a root enumeration of `f` if it lists the roots of `f` in `E`, with
multiplicity.  Unlike an enumeration of `f.rootSet E`, this definition also applies when roots
repeat. -/
def IsRootEnumeration (f : F[X]) (x : Fin n → E) : Prop :=
  (f.map (algebraMap F E)).roots = Multiset.map x univ.val

-- `IsRootEnumeration` is not `@[expose]`d, so its body is unavailable to importing modules:
-- this theorem is the only way to unfold the definition outside this file.
/-- The defining multiset equation for a root enumeration. -/
theorem isRootEnumeration_iff :
    IsRootEnumeration f x ↔
      (f.map (algebraMap F E)).roots = Multiset.map x univ.val :=
  Iff.rfl

namespace IsRootEnumeration

/-- A root enumeration contains `n` roots, counted with multiplicity. -/
theorem card_roots (hx : IsRootEnumeration f x) :
    (f.map (algebraMap F E)).roots.card = n := by
  rw [hx]
  simp

/-- Membership in the root multiset is equivalent to occurring in a root enumeration. -/
theorem mem_roots_iff (hx : IsRootEnumeration f x) {a : E} :
    a ∈ (f.map (algebraMap F E)).roots ↔ ∃ i : Fin n, x i = a := by
  rw [hx]
  simp

/-- Whether a family enumerates the roots is independent of a permutation of its indices. -/
@[simp]
theorem comp_perm_iff (σ : Equiv.Perm (Fin n)) :
    IsRootEnumeration f (x ∘ σ) ↔ IsRootEnumeration f x := by
  rw [isRootEnumeration_iff, isRootEnumeration_iff, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- Membership in the root set is equivalent to occurring in a root enumeration. -/
theorem mem_rootSet_iff (hx : IsRootEnumeration f x) {a : E} :
    a ∈ f.rootSet E ↔ ∃ i : Fin n, x i = a :=
  Polynomial.mem_rootSet'.trans <| Polynomial.mem_aroots'.symm.trans hx.mem_roots_iff

/-- A full injective root enumeration identifies its indexing type with the distinct root set. -/
noncomputable def equivRootSet (hx : IsRootEnumeration f x) (hinj : Function.Injective x) :
    Fin n ≃ f.rootSet E :=
  Equiv.ofBijective (fun i ↦ ⟨x i, hx.mem_rootSet_iff.2 ⟨i, rfl⟩⟩)
    ⟨fun _ _ hij ↦ hinj (congrArg Subtype.val hij),
      fun a ↦ (hx.mem_rootSet_iff.1 a.2).imp fun _ hi ↦ Subtype.ext hi⟩

@[simp]
theorem coe_equivRootSet (hx : IsRootEnumeration f x) (hinj : Function.Injective x)
    (i : Fin n) : (hx.equivRootSet hinj i : E) = x i :=
  congrArg Subtype.val (Equiv.ofBijective_apply _ _ i)

theorem equivRootSet_symm_apply (hx : IsRootEnumeration f x) (hinj : Function.Injective x)
    (a : f.rootSet E) : x ((hx.equivRootSet hinj).symm a) = a := by
  simpa only [coe_equivRootSet] using
    congrArg Subtype.val ((hx.equivRootSet hinj).apply_symm_apply a)

end IsRootEnumeration

/-- A numbering of the root set of a separable polynomial enumerates the full root multiset.
This packages `Polynomial.Separable.roots_map_eq_map_numbering` as an
`IsRootEnumeration`. -/
theorem _root_.Polynomial.Separable.isRootEnumeration (hf : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    IsRootEnumeration f (fun i ↦ (e i : E)) :=
  hf.roots_map_eq_map_numbering e

end Domain

section Field

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {n : ℕ} {f : F[X]} {x : Fin n → E}

namespace IsRootEnumeration

/-- Listing `f.natDegree` roots with multiplicity forces the mapped polynomial to split. -/
theorem splits (hx : IsRootEnumeration f x) (hdeg : f.natDegree = n) :
    (f.map (algebraMap F E)).Splits := by
  rw [Polynomial.splits_iff_card_roots, hx.card_roots, ← hdeg,
    Polynomial.natDegree_map]

/-- A full root enumeration of a nonzero polynomial is injective exactly when the mapped
polynomial is separable: injectivity says the `f.natDegree` listed roots are distinct, which for
a split polynomial is simplicity of every root. -/
theorem injective_iff_separable (hx : IsRootEnumeration f x) (hf : f ≠ 0)
    (hdeg : f.natDegree = n) :
    Function.Injective x ↔ (f.map (algebraMap F E)).Separable := by
  rw [← Fintype.nodup_map_univ_iff_injective, ← hx,
    Polynomial.nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf) (hx.splits hdeg)]

end IsRootEnumeration

end Field

end TauCeti
