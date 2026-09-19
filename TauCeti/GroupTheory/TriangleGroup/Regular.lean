/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.PermutationRepresentation
public import TauCeti.Combinatorics.PermutationTriple.Regular
public import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# Regular triples and normal subgroups of triangle groups

A permutation triple `t` of degree `n` whose components have orders dividing `a`, `b`, `c` is a
permutation representation `TauCeti.TriangleGroup.toPerm t : Δ(a, b, c) →* Equiv.Perm (Fin n)`.
The preimage of the stabilizer of a sheet `i` is the point stabilizer of this action.

This file proves the *normality criterion*: for a connected triple, the point stabilizer is a
normal subgroup of `Δ(a, b, c)` exactly when the triple is regular. In that case the point
stabilizer is the kernel of the representation, a normal subgroup whose index is the degree
`n`, the order of the monodromy group.

## Main results

* `TauCeti.TriangleGroup.normal_comap_stabilizer_toPerm_iff`: for a connected triple, the point
  stabilizer of its representation is normal exactly when the triple is regular.
* `TauCeti.TriangleGroup.comap_stabilizer_toPerm_eq_ker`: when a sheet has trivial monodromy
  stabilizer (e.g. for a regular triple), its point stabilizer is the kernel of the representation.
* `TauCeti.TriangleGroup.index_ker_toPerm`: the kernel of the representation has index the order
  of the monodromy group, and `TauCeti.TriangleGroup.index_ker_toPerm_of_isRegular`: for a
  regular triple this is the degree.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, Definition 2.64 and Proposition 2.66.
* G. A. Jones, D. Singerman, *Belyi functions, hypermaps and Galois groups*, Bull. London Math.
  Soc. 28 (1996), 561–590.
-/

open Equiv

public section

namespace TauCeti

namespace TriangleGroup

variable {a b c n : ℕ} (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
  (hc : t.σinf ^ c = 1)

/-- If a sheet has trivial monodromy stabilizer, its point stabilizer under the representation of
the triangle group is the kernel of the representation. -/
theorem comap_stabilizer_toPerm_eq_ker (i : Fin n)
    (hi : MulAction.stabilizer t.monodromyGroup i = ⊥) :
    (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc) =
      (toPerm t ha hb hc).ker :=
  (toPerm t ha hb hc).comap_stabilizer_eq_ker i (by
    rw [range_toPerm]
    exact hi)

/-- **The normality criterion.** For a connected triple, the point stabilizer of a sheet under the
representation of the triangle group is a normal subgroup exactly when the triple is regular. -/
theorem normal_comap_stabilizer_toPerm_iff (ht : t.IsConnected) (i : Fin n) :
    ((MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)).Normal ↔ t.IsRegular := by
  rw [(toPerm t ha hb hc).normal_comap_stabilizer_iff_isCancelSMul
      (by rw [range_toPerm]; exact ht.isPretransitive) i,
    range_toPerm, PermutationTriple.isRegular_iff_isCancelSMul, and_iff_right ht]

/-- The kernel of the representation of a triple has index the order of its monodromy group, the
image of the representation. -/
theorem index_ker_toPerm : (toPerm t ha hb hc).ker.index = Nat.card t.monodromyGroup := by
  rw [Subgroup.index_ker, range_toPerm]

/-- The kernel of the representation of a regular triple has index the degree. -/
theorem index_ker_toPerm_of_isRegular (ht : t.IsRegular) : (toPerm t ha hb hc).ker.index = n :=
  (index_ker_toPerm t ha hb hc).trans (PermutationTriple.isRegular_iff_card_monodromyGroup.mp ht).2

end TriangleGroup

end TauCeti
