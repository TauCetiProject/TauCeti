/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalCoefficients
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Trivialization

/-!
# Monodromy of the local system on a classifying space

The local system associated to `A : Rep k G` has monodromy `A.ρ` under the fixed
identification `π₁(BG) ≃ G`. The fibre is identified with `A` using the distinguished
sheet `(0, 1)` of Milnor's cover. A loop corresponding to `g` lifts to a path ending
at `(0, g⁻¹)`, whereas the associated-system sheet coordinates use the inverse action;
the two inversions cancel.

`TauCeti.classifyingSpaceLocalSystem_map_comp_basepointIso` pins this normalization
as an equality of actual transport maps. It ensures that local-system-valued cochains
on the classifying space use the prescribed coefficient representation, rather than
its inverse or a dual.

## References

* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

variable (k : Type u) [CommRing k] {G : Type u} [Group G] (A : Rep.{u} k G)

/-- Identify the basepoint fibre of the associated local system with its coefficient
module using the distinguished sheet of Milnor's cover. -/
def classifyingSpaceLocalSystemBasepointIso :
    (classifyingSpaceLocalSystem k A).obj
        (FundamentalGroupoid.mk (classifyingSpaceBasepoint G)) ≅ ModuleCat.of k A :=
  (isQuotientCoveringMap_classifyingSpaceProj G).associatedLocalSystemFiberIso k A
    ⟨universalGSpaceBasepoint G, classifyingSpaceProj_universalGSpaceBasepoint G⟩

/-- The basepoint identification is the sheet-coordinate isomorphism at the distinguished
sheet, so its forward and inverse coordinate formulas are those of
`IsQuotientCoveringMap.associatedLocalSystemFiberIso`. -/
theorem classifyingSpaceLocalSystemBasepointIso_def :
    classifyingSpaceLocalSystemBasepointIso k A =
      IsQuotientCoveringMap.associatedLocalSystemFiberIso
        (E := TopCat.of (universalGSpace G))
        (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
        (isQuotientCoveringMap_classifyingSpaceProj G) k A
        ⟨universalGSpaceBasepoint G, classifyingSpaceProj_universalGSpaceBasepoint G⟩ :=
  (rfl)

/-- Under the basepoint fibre identification, transport around a loop is the action of
its image in `G` under `classifyingSpaceFundamentalGroupMulEquiv`. -/
@[reassoc]
theorem classifyingSpaceLocalSystem_map_comp_basepointIso
    (γ : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G)) :
    (classifyingSpaceLocalSystem k A).map γ.asHom ≫
        (classifyingSpaceLocalSystemBasepointIso k A).hom =
      (classifyingSpaceLocalSystemBasepointIso k A).hom ≫
        ModuleCat.ofHom (A.ρ (classifyingSpaceFundamentalGroupMulEquiv G γ)) := by
  let hG := isQuotientCoveringMap_classifyingSpaceProj G
  let e : classifyingSpaceProj G ⁻¹' {classifyingSpaceBasepoint G} :=
    ⟨universalGSpaceBasepoint G, classifyingSpaceProj_universalGSpaceBasepoint G⟩
  have hg : hG.fiberEquivGroup e (hG.isCoveringMap.monodromy γ.asHom e) =
      (classifyingSpaceFundamentalGroupMulEquiv G γ)⁻¹ := by
    apply (hG.fiberEquivGroup_eq_iff _ _ _).2
    exact (classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff.mp rfl).trans
      (smul_universalGSpaceBasepoint _).symm
  apply (cancel_epi (classifyingSpaceLocalSystemBasepointIso k A).inv).1
  rw [classifyingSpaceLocalSystemBasepointIso_def]
  rw [← Category.assoc, hG.associatedLocalSystemFiberIso_inv_map,
    hG.associatedLocalSystemFiberIso_inv_comp_hom, hg]
  simp

/-- The basepoint fibre identification commutes with morphisms of representations. -/
@[reassoc]
theorem classifyingSpaceLocalSystemBasepointIso_hom_naturality {A A' : Rep.{u} k G}
    (f : A ⟶ A') :
    (classifyingSpaceLocalSystemMap f).app
        (FundamentalGroupoid.mk (classifyingSpaceBasepoint G)) ≫
        (classifyingSpaceLocalSystemBasepointIso k A').hom =
      (classifyingSpaceLocalSystemBasepointIso k A).hom ≫
        (forget₂ (Rep k G) (ModuleCat k)).map f := by
  simp only [classifyingSpaceLocalSystemBasepointIso_def]
  exact IsQuotientCoveringMap.associatedLocalSystemFiberIso_hom_naturality
    (E := TopCat.of (universalGSpace G))
    (p := TopCat.ofHom ⟨classifyingSpaceProj G, continuous_classifyingSpaceProj G⟩)
    (isQuotientCoveringMap_classifyingSpaceProj G) k f
    ⟨universalGSpaceBasepoint G, classifyingSpaceProj_universalGSpaceBasepoint G⟩

end TauCeti
