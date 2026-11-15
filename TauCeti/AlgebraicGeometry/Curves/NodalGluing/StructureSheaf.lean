/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Quotient
public import TauCeti.Geometry.Manifold.Instances.Sigma

/-!
# Stalks of the structure sheaf of a glued nodal curve

Let `d` be flag-pair gluing data on finitely many flag pairs, whose normalization components
`X i` are Hausdorff charted spaces on a common complex model. The holomorphic structure sheaf of
the glued curve `NodalGluing.GluedCurve d` is the quotient sheaf
`holomorphicStructureSheaf.quotientSheaf I (gluedRelSetoid d)` on the disjoint union
`Σ i, X i`: holomorphic functions on the normalization with equal values at the two points of
each flag pair. This file identifies its stalks.

* `NodalGluing.quotientStalkBranchEquiv`: at a point of the normalization which is not a flag
  point, the stalk of the glued curve is the holomorphic stalk of the normalization.
* `NodalGluing.quotientStalkToNodeEquiv`: at the node `nodeOfFlag d f` of a flag pair `f`, the
  stalk of the glued curve is the branch-pair node ring at `fstPoint d f` and `sndPoint d f`,
  the ring of pairs of holomorphic germs on the two branches with equal values at the node.

Both follow from the corresponding local statements for quotients of a complex manifold,
`holomorphicStructureSheaf.quotientStalkBranch_bijective` and
`holomorphicStructureSheaf.quotientStalkToNode_bijective`: finitely many flag points form a
closed set, so near a flag pair nothing but its two points is identified.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), for the normalization description of nodal Riemann surfaces.
-/

public noncomputable section

open Set Topology

namespace TauCeti.NodalGluing

open holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {ι : Type} {Flag : Type*} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace H (X i)] (d : FlagPairData ι Flag X) [Finite Flag]

/-- **Stalks at smooth points of a glued nodal curve.** Away from the flag points, restriction
to the normalization identifies the stalks of the glued curve with the holomorphic stalks of the
normalization. -/
theorem quotientStalkBranch_bijective [∀ i, T1Space (X i)] {x : Σ i, X i}
    (hx : x ∉ flagPointSet d) :
    Function.Bijective (quotientStalkBranch I (gluedRelSetoid d) _ x rfl) := by
  refine holomorphicStructureSheaf.quotientStalkBranch_bijective x ?_
  filter_upwards [(flagPointSet_finite d).isClosed.isOpen_compl.mem_nhds hx] with w hw v hwv
  rcases eq_or_mem_flagPointSet_of_gluedRel d ((gluedRelSetoid_r d _ _).mp hwv) with h | ⟨h, -⟩
  exacts [h.symm, (hw h).elim]

/-- **Stalks at the nodes of a glued nodal curve.** At the node of a flag pair, the restrictions
to the two branches identify the stalk of the glued curve with the branch-pair node ring. -/
theorem quotientStalkToNode_bijective [∀ i, T2Space (X i)] (f : Flag) :
    Function.Bijective (quotientStalkToNode I (gluedRelSetoid d) (fstPoint d f) (sndPoint d f)
      (gluedRelSetoid_fstPoint_sndPoint d f)) := by
  -- Near the two points of `f`, no other flag point is present.
  have hN : IsOpen (flagPointSet d \ {fstPoint d f, sndPoint d f})ᶜ :=
    ((flagPointSet_finite d).sdiff).isClosed.isOpen_compl
  have hloc : ∀ w ∈ (flagPointSet d \ {fstPoint d f, sndPoint d f})ᶜ, ∀ v,
      gluedRelSetoid d w v → v = w ∨ gluedRelSetoid d (fstPoint d f) w := by
    intro w hw v hwv
    rcases eq_or_mem_flagPointSet_of_gluedRel d ((gluedRelSetoid_r d _ _).mp hwv) with h | ⟨h, -⟩
    · exact Or.inl h.symm
    obtain rfl | rfl : w ∈ ({fstPoint d f, sndPoint d f} : Set (Σ i, X i)) :=
      not_not.mp fun hc ↦ hw ⟨h, hc⟩
    exacts [Or.inr ((gluedRelSetoid d).refl' _), Or.inr (gluedRelSetoid_fstPoint_sndPoint d f)]
  exact holomorphicStructureSheaf.quotientStalkToNode_bijective _ (fstPoint_ne_sndPoint d f f)
    (fun _ ↦ eq_or_eq_of_gluedRelSetoid_fstPoint d)
    (Filter.mem_of_superset (hN.mem_nhds (by simp)) hloc)
    (Filter.mem_of_superset (hN.mem_nhds (by simp)) hloc)

/-- Away from the flag points, the stalk of the glued curve is the holomorphic stalk of the
normalization. -/
def quotientStalkBranchEquiv [∀ i, T1Space (X i)] {x : Σ i, X i} (hx : x ∉ flagPointSet d) :
    (quotientSheaf I (gluedRelSetoid d)).presheaf.stalk (Quotient.mk _ x) ≃+*
      (holomorphicStructureSheaf I (Σ i, X i)).presheaf.stalk x :=
  RingEquiv.ofBijective _ (NodalGluing.quotientStalkBranch_bijective I d hx)

/-- The stalk isomorphism at a smooth point is restriction to the branch. -/
@[simp]
theorem quotientStalkBranchEquiv_apply [∀ i, T1Space (X i)] {x : Σ i, X i}
    (hx : x ∉ flagPointSet d)
    (g : (quotientSheaf I (gluedRelSetoid d)).presheaf.stalk (Quotient.mk _ x)) :
    quotientStalkBranchEquiv I d hx g = quotientStalkBranch I (gluedRelSetoid d) _ x rfl g :=
  (rfl)

/-- The stalk of the glued curve at the node of a flag pair is the branch-pair node ring. -/
def quotientStalkToNodeEquiv [∀ i, T2Space (X i)] (f : Flag) :
    (quotientSheaf I (gluedRelSetoid d)).presheaf.stalk (nodeOfFlag d f) ≃+*
      nodeLocalRing I I (fstPoint d f) (sndPoint d f) :=
  ((quotientSheaf I (gluedRelSetoid d)).presheaf.stalkCongr
      (.of_eq (mk_fstPoint d f).symm)).commRingCatIsoToRingEquiv.trans
    (RingEquiv.ofBijective _ (NodalGluing.quotientStalkToNode_bijective I d f))

/-- The stalk isomorphism at a node is the pair of branch restrictions, after identifying the
node with the class of the first point of the flag pair. -/
@[simp]
theorem quotientStalkToNodeEquiv_apply [∀ i, T2Space (X i)] (f : Flag)
    (g : (quotientSheaf I (gluedRelSetoid d)).presheaf.stalk (nodeOfFlag d f)) :
    quotientStalkToNodeEquiv I d f g =
      quotientStalkToNode I (gluedRelSetoid d) (fstPoint d f) (sndPoint d f)
        (gluedRelSetoid_fstPoint_sndPoint d f)
        ((quotientSheaf I (gluedRelSetoid d)).presheaf.stalkSpecializes
          (specializes_of_eq (mk_fstPoint d f)) g) :=
  (rfl)

end TauCeti.NodalGluing
