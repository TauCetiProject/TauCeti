/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Action

/-!
# Closed-point homogeneity of projective orbit schemes

Every closed point of the projective orbit scheme lifts to a rational group point.
Rational group translations therefore act transitively on its closed points, through
automorphisms of the full scheme-theoretic orbit image. This is the homogeneity input
for transporting flatness of the orbit morphism from a nonempty open to the whole orbit.

The group need not be reduced or smooth. Transitivity is asserted on closed points;
rational translations need not act transitively on all scheme points.

The results use `Scheme.Hom.image_closedPoints_eq_range_inter_closedPoints`,
`range_kernelPoint_eq_closedPoints`, and `Comodule.projectiveOrbitTranslation`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv TopologicalSpace

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- The rational group points map onto exactly the closed points of the orbit scheme. -/
theorem range_toProjectiveOrbit_kernelPoint_eq_closedPoints
    (m : M) (hm : Module.IsUnimodular k m) :
    Set.range (fun g : WithConv (H →ₐ[k] k) ↦
      toProjectiveOrbit (H := H) m hm (AlgHom.kernelPoint g.ofConv)) =
        closedPoints (projectiveOrbitScheme (H := H) m hm) := by
  rw [← Set.univ_inter (closedPoints _),
    ← (toProjectiveOrbit (H := H) m hm).surjective.range_eq,
    ← (toProjectiveOrbit (H := H) m hm).image_closedPoints_eq_range_inter_closedPoints,
    ← range_kernelPoint_eq_closedPoints (k := k) (A := H), ← Set.range_comp]
  exact (ofConv_surjective (A := H →ₐ[k] k)).range_comp
    (⇑(toProjectiveOrbit (H := H) m hm) ∘ AlgHom.kernelPoint)

/-- On rational orbit images, orbit translation is left multiplication of group points. -/
@[simp]
theorem projectiveOrbitTranslation_toProjectiveOrbit_kernelPoint
    (m : M) (hm : Module.IsUnimodular k m) (g h : WithConv (H →ₐ[k] k)) :
    (projectiveOrbitTranslation m hm g).hom
        (toProjectiveOrbit (H := H) m hm (AlgHom.kernelPoint h.ofConv)) =
      toProjectiveOrbit (H := H) m hm (AlgHom.kernelPoint (g * h).ofConv) := by
  apply (projectiveOrbitι (H := H) m hm).isEmbedding.injective
  have hi := congrArg (fun f : projectiveOrbitScheme (H := H) m hm ⟶ _ ↦
    f (toProjectiveOrbit (H := H) m hm (AlgHom.kernelPoint h.ofConv)))
    (projectiveOrbitTranslation_hom_ι m hm g)
  have hf (a : WithConv (H →ₐ[k] k)) := congrArg (fun f : Spec (.of H) ⟶ _ ↦
    f (AlgHom.kernelPoint a.ofConv)) (toProjectiveOrbit_projectiveOrbitι (H := H) m hm)
  simp only [Scheme.Hom.comp_apply] at hf
  simp only [Scheme.Hom.comp_apply, hf] at hi ⊢
  exact hi.trans (projectivePointTranslation_projectiveOrbitMap_kernelPoint g h m hm)

/-- Rational group translations act transitively on the closed points of the orbit scheme,
as automorphisms retaining its full scheme structure. -/
theorem exists_projectiveOrbitTranslation_eq_of_mem_closedPoints
    (m : M) (hm : Module.IsUnimodular k m)
    {x y : projectiveOrbitScheme (H := H) m hm}
    (hx : x ∈ closedPoints _) (hy : y ∈ closedPoints _) :
    ∃ g : WithConv (H →ₐ[k] k), (projectiveOrbitTranslation m hm g).hom x = y := by
  rw [← range_toProjectiveOrbit_kernelPoint_eq_closedPoints m hm] at hx hy
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  refine ⟨h * g⁻¹, ?_⟩
  rw [projectiveOrbitTranslation_toProjectiveOrbit_kernelPoint]
  simp

end TauCeti.Comodule
