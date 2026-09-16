/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
import TauCeti.Topology.Homeomorph.Quotient

/-!
# The fundamental-group quotient of the universal cover

The fundamental group of a path-connected, locally path-connected, semilocally simply connected
space acts on its based-path universal cover. Two points of the universal cover have the same
endpoint exactly when they belong to the same orbit. The endpoint projection therefore descends to
a homeomorphism

`UniversalCover x₀ / FundamentalGroup X x₀ ≃ₜ X`.

This is the topological quotient statement associated to the universal cover. It uses the actual
fundamental-group action on based path classes, rather than first replacing that action by the
isomorphic deck-transformation group.

## Main declaration

* `TauCeti.UniversalCover.orbitQuotientHomeomorph`: the fundamental-group orbit quotient of the
  universal cover is homeomorphic to the base.

## References

Compare Hatcher, *Algebraic Topology*, Section 1.3, especially Propositions 1.39 and 1.40. The
based-path construction and action are adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292).
-/

public section
noncomputable section

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
  [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- **The quotient of the universal cover by its fundamental-group action is homeomorphic to the
base space.** The homeomorphism sends the orbit of a based path to its endpoint. -/
noncomputable def orbitQuotientHomeomorph (x₀ : X) :
    MulAction.orbitRel.Quotient (FundamentalGroup X x₀) (UniversalCover x₀) ≃ₜ X :=
  let hp := isQuotientCoveringMap (x₀ := x₀)
  let p : C(UniversalCover x₀, X) := ⟨proj, hp.continuous⟩
  (Homeomorph.Quotient.congrRight (r' := Setoid.ker p) fun e e' ↦ by
      rw [MulAction.orbitRel_apply, Setoid.ker_def]
      -- Display the coercion of the bundled endpoint projection so its fibre relation can be
      -- rewritten by the orbit characterization.
      change e ∈ MulAction.orbit (FundamentalGroup X x₀) e' ↔ proj e = proj e'
      exact proj_eq_iff_mem_orbit.symm).trans
    (show Topology.IsQuotientMap p from hp.toIsQuotientMap).homeomorph

/-- On an orbit representative, the quotient homeomorphism is the endpoint projection. -/
@[simp]
lemma orbitQuotientHomeomorph_mk (x₀ : X) (p : UniversalCover x₀) :
    orbitQuotientHomeomorph x₀
        (Quotient.mk'' p :
          MulAction.orbitRel.Quotient (FundamentalGroup X x₀) (UniversalCover x₀)) =
      proj p := by
  rw [orbitQuotientHomeomorph, Homeomorph.trans_apply,
    Homeomorph.Quotient.congrRight_mk, Topology.IsQuotientMap.homeomorph_apply,
    Setoid.kerLift_mk]
  rfl

/-- The inverse quotient homeomorphism sends an endpoint to the orbit of any lift with that
endpoint. -/
@[simp]
lemma orbitQuotientHomeomorph_symm_apply_proj (x₀ : X) (p : UniversalCover x₀) :
    (orbitQuotientHomeomorph x₀).symm (proj p) =
      (Quotient.mk'' p :
        MulAction.orbitRel.Quotient (FundamentalGroup X x₀) (UniversalCover x₀)) := by
  apply (orbitQuotientHomeomorph x₀).injective
  rw [Homeomorph.apply_symm_apply, orbitQuotientHomeomorph_mk]

end TauCeti.UniversalCover
