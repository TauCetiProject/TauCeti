/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.Constructions.Basic

/-!
# Separation axioms for quotient spaces

This file shows that the quotient of a compact Hausdorff space by an equivalence relation is
Hausdorff exactly when the relation is a closed subset of `X × X`. Together with Mathlib's
`Quotient.compactSpace`, this says that the quotients of a compact Hausdorff space by closed
equivalence relations are again compact Hausdorff. Conversely every compact Hausdorff space `T`
arises in this way from a profinite set: the Stone–Čech presentation
`CompHaus.projectivePresentation T` is a surjection `S → T` from an extremally disconnected space,
and its kernel relation is closed because `T` is Hausdorff. This is how compact Hausdorff spaces
are presented by profinite sets in the theory of diamonds (Scholze, *Étale cohomology of
diamonds*, Remark 2.8 and Example 11.12).

The proof only uses normality of `X`, not the Hausdorff property: the quotient map of a compact
space by a closed relation is a closed map (`Setoid.isClosedMap_quotient_mk_of_isClosed`), the
image of a normal space under a continuous closed surjection is normal
(`IsClosedMap.normalSpace`), and the points of the quotient are closed because the equivalence
classes are (`Setoid.t1Space_quotient_iff`).

## Main results

* `IsClosedMap.normalSpace`: the image of a normal space under a continuous closed surjection is
  normal.
* `Setoid.t1Space_quotient_iff`: the quotient is T₁ if and only if every equivalence class is
  closed.
* `Setoid.isClosed_setOf_rel_of_t2Space_quotient`: if the quotient is Hausdorff, then the relation
  is closed in `X × X`.
* `Setoid.t2Space_quotient_of_isClosed`: the quotient of a compact normal space, in particular of a
  compact Hausdorff space, by a closed equivalence relation is Hausdorff.
* `Setoid.t2Space_quotient_iff_isClosed`: for a compact normal space the two conditions are
  equivalent.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Remark 2.8, and §11,
  Example 11.12.
* R. Engelking, *General Topology*, Heldermann (1989), Theorem 1.5.20.
-/

public section

open Set Topology

/-- The image of a normal space under a continuous closed surjection is normal. -/
theorem IsClosedMap.normalSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormalSpace X] {f : X → Y} (hf : IsClosedMap f) (hc : Continuous f)
    (hsurj : Function.Surjective f) : NormalSpace Y where
  normal s t hs ht hst := by
    -- Separate the preimages by open sets `U` and `V`, then keep the points of `Y` all of whose
    -- preimages lie in `U`, respectively in `V`.
    obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ :=
      normal_separation (hs.preimage hc) (ht.preimage hc) (hst.preimage f)
    refine ⟨(f '' Uᶜ)ᶜ, (f '' Vᶜ)ᶜ, (hf _ hU.isClosed_compl).isOpen_compl,
      (hf _ hV.isClosed_compl).isOpen_compl, ?_, ?_, disjoint_left.2 fun y hyU hyV => ?_⟩
    · rintro y hy ⟨x, hx, rfl⟩
      exact hx (hsU hy)
    · rintro y hy ⟨x, hx, rfl⟩
      exact hx (htV hy)
    · obtain ⟨x, rfl⟩ := hsurj y
      exact disjoint_left.1 hUV (by_contra fun h => hyU ⟨x, h, rfl⟩)
        (by_contra fun h => hyV ⟨x, h, rfl⟩)

namespace Setoid

variable {X : Type*} [TopologicalSpace X] (s : Setoid X)

/-- The quotient by an equivalence relation is T₁ if and only if every equivalence class is
closed. -/
theorem t1Space_quotient_iff : T1Space (Quotient s) ↔ ∀ x, IsClosed {y | s x y} := by
  have hq : IsQuotientMap (Quotient.mk s) := isQuotientMap_quotient_mk'
  have hclass : ∀ x, Quotient.mk s ⁻¹' {Quotient.mk s x} = {y | s x y} := fun x => by
    ext y
    simpa only [mem_preimage, mem_singleton_iff, mem_ofPred_eq] using
      Quotient.eq.trans (s.comm' (x := y))
  refine ⟨fun _ x => hclass x ▸ isClosed_singleton.preimage continuous_quotient_mk', fun h => ?_⟩
  refine ⟨Quotient.ind fun x => ?_⟩
  rw [← hq.isClosed_preimage, hclass]
  exact h x

/-- If the quotient by an equivalence relation is Hausdorff, then the relation is closed in
`X × X`. -/
theorem isClosed_setOf_rel_of_t2Space_quotient [T2Space (Quotient s)] :
    IsClosed {p : X × X | s p.1 p.2} := by
  have hc : Continuous (Quotient.mk s) := continuous_quotient_mk'
  simpa only [Function.comp_apply, Quotient.eq] using
    isClosed_eq (hc.comp continuous_fst) (hc.comp continuous_snd)

/-- **The quotient of a compact Hausdorff space by a closed equivalence relation is Hausdorff.**
More generally it suffices that `X` be compact and normal. -/
theorem t2Space_quotient_of_isClosed [CompactSpace X] [NormalSpace X]
    (hs : IsClosed {p : X × X | s p.1 p.2}) : T2Space (Quotient s) :=
  have : T1Space (Quotient s) :=
    (t1Space_quotient_iff s).2 fun x => hs.preimage (Continuous.prodMk_right x)
  have : NormalSpace (Quotient s) := (isClosedMap_quotient_mk_of_isClosed s hs).normalSpace
    continuous_quotient_mk' Quotient.mk_surjective
  inferInstance

/-- The quotient of a compact normal space, in particular of a compact Hausdorff space, by an
equivalence relation is Hausdorff if and only if the relation is closed in `X × X`. -/
theorem t2Space_quotient_iff_isClosed [CompactSpace X] [NormalSpace X] :
    T2Space (Quotient s) ↔ IsClosed {p : X × X | s p.1 p.2} :=
  ⟨fun _ => s.isClosed_setOf_rel_of_t2Space_quotient, s.t2Space_quotient_of_isClosed⟩

end Setoid
