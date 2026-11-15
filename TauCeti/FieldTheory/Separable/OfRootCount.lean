/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# A polynomial that attains its degree in distinct roots is separable

A polynomial has at most `natDegree p` roots counted with multiplicity, and at most that many
distinct ones. If it has at least that many *distinct* roots then both bounds are equalities: it
splits, and none of its roots repeats — which is separability.

No closure assumption is needed. The root count already forces `p` to split, by
`Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero` and `Polynomial.splits_iff_card_roots`;
assuming an algebraically closed field would only be a way of guaranteeing the hypothesis, not of
using it.

Mathlib has the corresponding equivalence as `Polynomial.card_rootSet_eq_natDegree_iff_of_splits`,
phrased with `rootSet` over an extension and with splitting and equality as hypotheses. A counting
argument supplies none of those: it supplies a lower bound on the number of roots in the field
itself. This is that form, and it is the shape every root-counting proof of separability ends in.

The same bound can be read on the root set in an extension field. In particular, a numbering of
those roots by the degree gives the same conclusion, without separately assuming that the
polynomial splits in that field.

## Main results

* `Polynomial.separable_of_natDegree_le_card_roots`
* `Polynomial.separable_of_natDegree_le_card_rootSet`
* `Polynomial.separable_of_rootSet_equiv_fin`
-/

public section

namespace Polynomial

open Finset

/-- **A polynomial with at least as many distinct roots as its degree is separable.** The
hypothesis is a lower bound because that is what a counting argument gives; the reverse inequality
always holds, and the two together force `p` to split with distinct roots. -/
theorem separable_of_natDegree_le_card_roots {F : Type*} [Field F] [DecidableEq F]
    {p : F[X]} (hp : p ≠ 0) (h : p.natDegree ≤ #p.roots.toFinset) : p.Separable := by
  -- The distinct roots already exhaust the degree, so they are *all* the roots with multiplicity:
  -- `p.roots` is its own deduplication. Splitting and `Nodup` both read off that one equality.
  have hroots : p.roots = p.roots.toFinset.val :=
    roots_eq_of_natDegree_le_card_of_ne_zero
      (fun _ hx ↦ (mem_roots hp).mp (Multiset.mem_toFinset.mp hx)) h hp
  have hcard : p.roots.card = p.natDegree :=
    le_antisymm (card_roots' p) (by rw [hroots]; exact h)
  exact (nodup_roots_iff_of_splits hp (splits_iff_card_roots.mpr hcard)).mp
    (by rw [hroots]; exact p.roots.toFinset.nodup)

/-- A nonzero polynomial with at least its degree in distinct roots in an extension field is
separable. No separate splitting or monicity hypothesis is needed. -/
theorem separable_of_natDegree_le_card_rootSet {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : F[X]} (hp : p ≠ 0) (h : p.natDegree ≤ Fintype.card (p.rootSet E)) : p.Separable := by
  classical
  exact (separable_map (algebraMap F E)).mp
    (separable_of_natDegree_le_card_roots (map_ne_zero hp)
      (by simpa [rootSet_def] using h))

/-- A nonzero polynomial is separable if its roots in an extension field can be numbered by its
degree. No separate splitting or monicity hypothesis is needed. -/
theorem separable_of_rootSet_equiv_fin {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : F[X]} {n : ℕ} (hp : p ≠ 0) (hdeg : p.natDegree = n) (e : p.rootSet E ≃ Fin n) :
    p.Separable :=
  separable_of_natDegree_le_card_rootSet hp (by simpa [hdeg] using (Fintype.card_congr e).ge)

end Polynomial

end
