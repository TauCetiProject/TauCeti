/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Geometry
public import TauCeti.MeasureTheory.Group.DirichletDomain.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Geodesic convexity of Dirichlet domains

A Dirichlet domain in the upper half-plane is an intersection of closed geodesic half-planes:
for each translate of the centre different from the centre itself, the corresponding
perpendicular bisector bounds the distance dominance region. Constraints coming from the
stabilizer are automatically satisfied and are omitted from this intersection.

Consequently the domain contains the geodesic segment between any two of its points. Neither
this convexity nor the half-plane description requires discreteness or a trivial stabilizer.
They provide the geometric description of the Dirichlet domain needed to construct its sides.

`UpperHalfPlane.dirichletDomain_eq_iInter_of_inter_eq` gives a globalization criterion:
inequalities agreeing with the domain on an open neighbourhood of the whole domain
define it globally. This applies when a bounded core and finitely many cusp ends cover the
domain. The proof uses geodesic convexity and Mathlib's `IsClopen.eq_univ` on a segment.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

open UpperHalfPlane Set
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

variable (G : Type*) [SMul G ℍ]

/-- A Dirichlet domain in `ℍ` is the intersection of the closed geodesic half-planes bounded
by the bisectors between its centre and the distinct points of the orbit of that centre.
Translates fixing the centre impose no constraint. -/
theorem dirichletDomain_eq_iInter_closure_leftHalfPlane (p : ℍ) :
    dirichletDomain G p =
      ⋂ g : G, ⋂ (_ : p ≠ g • p), closure (leftHalfPlane (perpBisector p (g • p))) := by
  ext z
  simp only [mem_dirichletDomain, mem_iInter]
  constructor
  · intro hz g hg
    exact (mem_closure_leftHalfPlane_perpBisector_iff hg z).mpr (hz g)
  · intro hz g
    by_cases hg : p = g • p
    · rw [← hg]
    · exact (mem_closure_leftHalfPlane_perpBisector_iff hg z).mp (hz g hg)

/-- **Dirichlet domains in the hyperbolic plane are geodesically convex.** This applies to
any family of translates, without discreteness, freeness, or isometry assumptions. -/
theorem geodesicSegment_subset_dirichletDomain {p z w : ℍ}
    (hz : z ∈ dirichletDomain G p) (hw : w ∈ dirichletDomain G p) :
    geodesicSegment z w ⊆ dirichletDomain G p := by
  rw [mem_dirichletDomain] at hz hw
  intro u hu
  exact mem_dirichletDomain.mpr fun g ↦
    geodesicSegment_subset_setOf_dist_le_dist (hz g) (hw g) hu

/-- Along any geodesic line the parameters lying in a Dirichlet domain form an interval. -/
theorem ordConnected_preimage_geodesicLine_dirichletDomain {k : PSL(2, ℝ)} {p : ℍ} :
    (geodesicLine k ⁻¹' dirichletDomain G p).OrdConnected := by
  rw [dirichletDomain_eq_iInter_closure_leftHalfPlane, preimage_iInter]
  exact ordConnected_iInter fun g ↦ by
    rw [preimage_iInter]
    exact ordConnected_iInter fun _ ↦
      ordConnected_preimage_geodesicLine_closure_leftHalfPlane k _

variable {G}

/-- A family of Dirichlet inequalities which agrees with the domain on an open neighbourhood
of the whole domain defines it globally. Geodesic convexity prevents the intersection from
having an extra component outside that neighbourhood. -/
theorem _root_.UpperHalfPlane.dirichletDomain_eq_iInter_of_inter_eq
    (p : ℍ) (s : Set G)
    {U : Set ℍ} (hU : IsOpen U) (hDU : dirichletDomain G p ⊆ U)
    (heq : dirichletDomain G p ∩ U =
      (⋂ g ∈ s, {z : ℍ | dist z p ≤ dist z (g • p)}) ∩ U) :
    dirichletDomain G p = ⋂ g ∈ s, {z : ℍ | dist z p ≤ dist z (g • p)} := by
  refine subset_antisymm (fun z hz ↦ mem_iInter₂.mpr fun g _ ↦
    mem_dirichletDomain.mp hz g) ?_
  intro z hz
  let S := geodesicSegment p z
  have hS : IsPreconnected S := by
    dsimp only [S]
    rw [geodesicSegment_def]
    exact isPreconnected_Icc.image _ (isometry_geodesicLine _).continuous.continuousOn
  have hSC : S ⊆ ⋂ g ∈ s, {z : ℍ | dist z p ≤ dist z (g • p)} := by
    intro w hw
    exact mem_iInter₂.mpr fun g hg ↦ geodesicSegment_subset_setOf_dist_le_dist
      (by simp [dist_nonneg]) (mem_iInter₂.mp hz g hg) hw
  let := Subtype.preconnectedSpace hS
  have hpre : ((↑) : S → ℍ) ⁻¹' dirichletDomain G p = ((↑) : S → ℍ) ⁻¹' U := by
    ext w
    refine ⟨fun hw ↦ hDU hw, fun hw ↦ ?_⟩
    have hwD : (w : ℍ) ∈ dirichletDomain G p ∩ U := by
      rw [heq]
      exact ⟨hSC w.property, hw⟩
    exact hwD.1
  have hclopen : IsClopen (((↑) : S → ℍ) ⁻¹' dirichletDomain G p) :=
    ⟨(isClosed_dirichletDomain G p).preimage continuous_subtype_val,
      hpre ▸ hU.preimage continuous_subtype_val⟩
  have hall := hclopen.eq_univ
    ⟨⟨p, left_mem_geodesicSegment p z⟩, self_mem_dirichletDomain p⟩
  exact (Set.eq_univ_iff_forall.mp hall) ⟨z, right_mem_geodesicSegment p z⟩

end TauCeti.UpperHalfPlane
