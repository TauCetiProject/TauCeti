/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Topology.Constructions.Basic

/-!
# Separation axioms for quotient spaces

This file shows that the quotient of a compact space by an equivalence relation is Hausdorff
exactly when the relation is a closed subset of `X × X`. Together with Mathlib's
`Quotient.compactSpace`, this says that the quotients of a compact Hausdorff space by closed
equivalence relations are again compact Hausdorff. Conversely every compact Hausdorff space `T`
arises in this way from a profinite set: the Stone–Čech presentation
`CompHaus.projectivePresentation T` is a surjection `S → T` from an extremally disconnected space,
and its kernel relation is closed because `T` is Hausdorff. This is how compact Hausdorff spaces
are presented by profinite sets in the theory of diamonds (Scholze, *Étale cohomology of
diamonds*, Remark 2.8 and Example 11.12).

The proof only uses compactness of `X`, not the Hausdorff property: the quotient map of a compact
space by a closed relation is a closed map (`Setoid.isClosedMap_quotient_mk_of_isClosed`) whose
fibres, the equivalence classes, are closed and hence compact. So the quotient map is proper, and
the diagonal of the quotient is the image of the relation under the proper map `Prod.map`.

## Main results

* `Setoid.isClosed_setOf_rel_of_t2Space_quotient`: if the quotient is Hausdorff, then the relation
  is closed in `X × X`.
* `Setoid.t2Space_quotient_of_isClosed`: the quotient of a compact space, in particular of a
  compact Hausdorff space, by a closed equivalence relation is Hausdorff.
* `Setoid.t2Space_quotient_iff_isClosed`: for a compact space the two conditions are equivalent.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Remark 2.8, and §11,
  Example 11.12.
-/

public section

open Set Topology

namespace Setoid

variable {X : Type*} [TopologicalSpace X] (s : Setoid X)

/-- If the quotient by an equivalence relation is Hausdorff, then the relation is closed in
`X × X`. -/
theorem isClosed_setOf_rel_of_t2Space_quotient [T2Space (Quotient s)] :
    IsClosed {p : X × X | s p.1 p.2} := by
  have hc : Continuous (Quotient.mk s) := continuous_quotient_mk'
  simpa only [Function.comp_apply, Quotient.eq] using
    isClosed_eq (hc.comp continuous_fst) (hc.comp continuous_snd)

/-- **The quotient of a compact Hausdorff space by a closed equivalence relation is Hausdorff.**
More generally it suffices that `X` be compact. -/
theorem t2Space_quotient_of_isClosed [CompactSpace X]
    (hs : IsClosed {p : X × X | s p.1 p.2}) : T2Space (Quotient s) := by
  -- The quotient map is closed, and its fibres are the equivalence classes, which are closed and
  -- hence compact; so it is proper.
  have hq : IsProperMap (Quotient.mk s) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨continuous_quotient_mk',
      isClosedMap_quotient_mk_of_isClosed s hs, Quotient.ind fun x => by
        have hclass : Quotient.mk s ⁻¹' {Quotient.mk s x} = {y | s x y} := by
          ext y
          simpa only [mem_preimage, mem_singleton_iff, mem_ofPred_eq] using
            Quotient.eq.trans (s.comm' (x := y))
        exact hclass ▸ (hs.preimage (Continuous.prodMk_right x)).isCompact⟩
  -- The diagonal of the quotient is the image of the relation under the proper map `q × q`.
  have hdiag : diagonal (Quotient s) =
      Prod.map (Quotient.mk s) (Quotient.mk s) '' {p : X × X | s p.1 p.2} := by
    ext ⟨a, b⟩
    induction a using Quotient.ind
    induction b using Quotient.ind
    simp only [mem_diagonal_iff, mem_image, mem_ofPred_eq, Prod.exists, Prod.map_apply,
      Prod.mk.injEq, Quotient.eq]
    exact ⟨fun h => ⟨_, _, h, s.refl _, s.refl _⟩,
      fun ⟨x, y, hxy, hx, hy⟩ => s.trans (s.symm hx) (s.trans hxy hy)⟩
  rw [t2_iff_isClosed_diagonal, hdiag]
  exact (hq.prodMap hq).isClosedMap _ hs

/-- The quotient of a compact space, in particular of a compact Hausdorff space, by an
equivalence relation is Hausdorff if and only if the relation is closed in `X × X`. -/
theorem t2Space_quotient_iff_isClosed [CompactSpace X] :
    T2Space (Quotient s) ↔ IsClosed {p : X × X | s p.1 p.2} :=
  ⟨fun _ => s.isClosed_setOf_rel_of_t2Space_quotient, s.t2Space_quotient_of_isClosed⟩

end Setoid
