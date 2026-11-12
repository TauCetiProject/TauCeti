/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LocallyClosed
import TauCeti.AlgebraicGeometry.AugmentationPoint.Dense

/-!
# Degeneration into the boundary of a projective orbit

Over an algebraically closed field, the orbit through a rational boundary point stays in
the boundary of the original orbit, including at nonclosed points of the new orbit.
Consequently such an orbit has strictly smaller closure. This is the descent step in the
closed-orbit argument for projective representations of affine algebraic groups.

First, a closed subset invariant under rational group translations contains the full orbit
image as soon as it contains the identity image. Density of rational points in the group
promotes invariance on rational points to this assertion on the full spectrum. Applying it
to the closed boundary gives orbit containment and strict containment of closures.

Neither connectedness nor smoothness nor reducedness of the group is required.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.c, orbits and homogeneous spaces.
-/

public section

open AlgebraicGeometry WithConv

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- A closed subset invariant under rational projective translations contains the full orbit
image exactly when it contains the image of the identity point. -/
theorem range_projectiveOrbitMap_subset_iff_of_isClosed
    (m : M) (hm : Module.IsUnimodular k m)
    {Z : Set (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z)
    (hinvariant : ∀ g : WithConv (H →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) g).hom Z Z) :
    Set.range (projectiveOrbitMap (H := H) m hm) ⊆ Z ↔
      projectiveOrbitMap (H := H) m hm
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z := by
  refine ⟨fun h ↦ h ⟨_, rfl⟩, fun h ↦ ?_⟩
  rintro _ ⟨x, rfl⟩
  refine (denseRange_kernelPoint (k := k) (A := H)).induction_on
    (p := fun x ↦ projectiveOrbitMap (H := H) m hm x ∈ Z) x
    (hZ.preimage (projectiveOrbitMap (H := H) m hm).continuous) ?_
  intro g
  have hpoint : (projectivePointTranslation (M := M) (toConv g)).hom
      (projectiveOrbitMap (H := H) m hm
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) =
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g) := by
    have htranslation :=
      projectivePointTranslation_projectiveOrbitMap_kernelPoint (toConv g) 1 m hm
    rw [mul_one] at htranslation
    simpa only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp, ofConv_toConv]
      using htranslation
  rw [← hpoint]
  exact hinvariant (toConv g) h

/-- The closure of an orbit through a boundary point is contained in the boundary of the
original orbit. Both orbits are the full images of scheme morphisms. -/
theorem closure_range_projectiveOrbitMap_subset_boundary
    (m : M) (hm : Module.IsUnimodular k m)
    (n : M) (hn : Module.IsUnimodular k n)
    (hboundary : projectiveOrbitMap (H := H) n hn
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm)) :
    closure (Set.range (projectiveOrbitMap (H := H) n hn)) ⊆
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm) := by
  let O := Set.range (projectiveOrbitMap (H := H) m hm)
  have hclosed : IsClosed (closure O \ O) := by
    simpa only [coborder, compl_compl] using
      (isLocallyClosed_range_projectiveOrbitMap (H := H) m hm).isOpen_coborder.isClosed_compl
  apply closure_minimal ((range_projectiveOrbitMap_subset_iff_of_isClosed n hn hclosed
    (fun g ↦ ?_)).mpr hboundary) hclosed
  have himage : (projectivePointTranslation (M := M) g).hom '' O = O :=
    image_projectivePointTranslation_range_projectiveOrbitMap g m hm
  have hclosure : (projectivePointTranslation (M := M) g).hom '' closure O = closure O := by
    simpa only [Scheme.coe_homeoOfIso, himage] using
      (Scheme.homeoOfIso (projectivePointTranslation (M := M) g)).image_closure O
  have hboundaryImage : (projectivePointTranslation (M := M) g).hom '' (closure O \ O) =
      closure O \ O := by
    have hinj : Function.Injective (projectivePointTranslation (M := M) g).hom := by
      simpa only [Scheme.coe_homeoOfIso] using
        (Scheme.homeoOfIso (projectivePointTranslation (M := M) g)).injective
    rw [Set.image_sdiff hinj, hclosure, himage]
  intro x hx
  rw [← hboundaryImage]
  exact ⟨x, hx, rfl⟩

/-- Passing to an orbit through the boundary strictly decreases the orbit closure.
This strict inclusion supports Noetherian induction in the closed-orbit argument. -/
theorem closure_range_projectiveOrbitMap_ssubset_of_mem_boundary
    (m : M) (hm : Module.IsUnimodular k m)
    (n : M) (hn : Module.IsUnimodular k n)
    (hboundary : projectiveOrbitMap (H := H) n hn
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm)) :
    closure (Set.range (projectiveOrbitMap (H := H) n hn)) ⊂
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  have hsub := closure_range_projectiveOrbitMap_subset_boundary m hm n hn hboundary
  refine ⟨fun x hx ↦ (hsub hx).1, fun h ↦ ?_⟩
  have hx := hsub (h (subset_closure (Set.mem_range_self
    (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)))))
  exact hx.2 (Set.mem_range_self _)

end TauCeti.Comodule
