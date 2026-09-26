/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# Root sets: numbering the roots, the roots of a product, and removing a simple root

This file records three facts about the root set `f.rootSet E` of a polynomial `f` after base
change to a domain `E`.

First, an explicit numbering of the root set of a separable polynomial enumerates its full root
multiset: separability makes the roots simple, so the multiset is the image of the numbering.
This lets root-product formulas be expressed as finite products indexed by `Fin f.natDegree`,
without choosing a global order on the root set.

Second, the root set of a product of polynomials whose base changes to `E` are nonzero is the
union of the root sets of the factors. This is the lemma that decomposes the roots of a
polynomial along a factorisation, for instance the roots of a monic integer polynomial along its
monic irreducible factors.

Third, dividing a polynomial by the linear factor of a simple root removes exactly that root
from the root set, where a root `a` is simple when the derivative does not vanish at `a`.

## Main results

* `Polynomial.Separable.roots_map_eq_map_numbering`: for a separable polynomial, a numbering of
  its root set enumerates its full root multiset after base change.
* `Polynomial.rootSet_mul`: the root set of a product of polynomials whose base changes to `E` are
  nonzero is the union of the root sets of the factors.
* `Polynomial.rootSet_divByMonic_X_sub_C`: for a root `a` of `f` with `f' a ≠ 0`, the roots of
  `f /ₘ (X - C a)` are the roots of `f` other than `a`.
-/

public section

namespace TauCeti

open Finset Polynomial

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

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

/-- The root set of a product of polynomials is the union of the root sets of the factors,
provided neither factor vanishes after base change to `E`. -/
@[simp]
theorem _root_.Polynomial.rootSet_mul {g : F[X]} (hf : f.map (algebraMap F E) ≠ 0)
    (hg : g.map (algebraMap F E) ≠ 0) : (f * g).rootSet E = f.rootSet E ∪ g.rootSet E := by
  ext x
  simp only [Set.mem_union, mem_rootSet', Polynomial.map_mul, map_mul, mul_eq_zero, ne_eq, hf, hg,
    or_self, not_false_eq_true, true_and]

/-- Removing the linear factor of a simple root `a` removes exactly that root: if `f a = 0` and
`f' a ≠ 0`, then the roots of `f /ₘ (X - C a)` in `E` are the roots of `f` other than `a`. -/
@[simp]
theorem _root_.Polynomial.rootSet_divByMonic_X_sub_C [FaithfulSMul F E] {a : F} (ha : f.eval a = 0)
    (ha' : f.derivative.eval a ≠ 0) :
    (f /ₘ (X - C a)).rootSet E = f.rootSet E \ {algebraMap F E a} := by
  classical
  have hinj := FaithfulSMul.algebraMap_injective F E
  -- `a` is not a root of the quotient: the quotient takes the value `f' a ≠ 0` there.
  have hq := congrArg (eval a) (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a)
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hq
  have hq0 := hq.trans_ne ha'
  -- The roots of `f = (X - C a) * (f /ₘ (X - C a))` in `E` are `a` together with the roots of the
  -- quotient.
  rw [rootSet_def, rootSet_def]
  conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr ha, aroots_def, Polynomial.map_mul,
    roots_mul (((monic_X_sub_C a).map _).mul_right_ne_zero <| (Polynomial.map_ne_zero_iff hinj).mpr
      fun h ↦ hq0 (congrArg (eval a) h |>.trans eval_zero)), ← aroots_def, aroots_X_sub_C,
    Multiset.singleton_add, Multiset.toFinset_cons, Finset.coe_insert,
    Set.insert_sdiff_self_of_notMem <|
      mt (fun h ↦ (mem_roots'.mp (Multiset.mem_toFinset.mp h)).2.of_map hinj) hq0]

end TauCeti
