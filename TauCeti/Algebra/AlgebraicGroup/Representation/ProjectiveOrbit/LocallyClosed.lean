/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Translation
public import TauCeti.Topology.Algebra.MulAction.Orbit

/-!
# Projective orbit images are locally closed

The full topological image of a finite-type affine group's projective orbit morphism is
locally closed over an algebraically closed field. This includes its nonclosed points;
it is not a statement only about the orbit of rational points. Neither smoothness nor
reducedness of the group is required.

This supplies the locally closed subset on which to construct the orbit scheme, a geometric
model for the homogeneous space of the stabilizer of the chosen line. It does not identify
scheme-theoretic fibers or prove flatness or representability of a quotient sheaf.

The argument combines `isConstructible_range_projectiveOrbitMap`,
`range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints`, translation invariance,
and `isLocallyClosed_of_isConstructible_of_closedPoints_transitive`. Rational translations
are transitive on the closed points of the image, even though they need not be transitive
on all its points. Consequently the boundary `closure O \ O` of the orbit `O` is closed
(`TauCeti.Comodule.isClosed_closure_diff_range_projectiveOrbitMap`).

The same transitivity shows that a line in the orbit `O` of `[m]` is a rational translate of `[m]`,
so its orbit is `O` again (`TauCeti.Comodule.range_projectiveOrbitMap_eq_iff`).

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

/-- Rational translations are transitive on the closed points of the full projective
orbit image. -/
theorem exists_smul_eq_of_mem_range_projectiveOrbitMap_inter_closedPoints
    (m : M) (hm : Module.IsUnimodular k m)
    {x y : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))}
    (hx : x ∈ Set.range (projectiveOrbitMap (H := H) m hm) ∩ closedPoints _)
    (hy : y ∈ Set.range (projectiveOrbitMap (H := H) m hm) ∩ closedPoints _) :
    letI := projectivePointMulAction (R := k) (H := H) (M := M)
    ∃ g : WithConv (H →ₐ[k] k), g • x = y := by
  let := projectivePointMulAction (R := k) (H := H) (M := M)
  rw [← range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints m hm] at hx hy
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  refine ⟨h * g⁻¹, ?_⟩
  rw [projectivePoint_smul_def]
  exact (projectivePointTranslation_projectiveOrbitMap_kernelPoint
    (h * g⁻¹) g m hm).trans (by simp)

/-- A line whose image lies in the orbit of the line `[m]` is a rational translate of `[m]`. -/
theorem exists_span_basePointsRepresentation_eq_of_mem_range
    (m : M) (hm : Module.IsUnimodular k m) (n : M) (hn : Module.IsUnimodular k n)
    (hnm : projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      Set.range (projectiveOrbitMap (H := H) m hm)) :
    ∃ g : WithConv (H →ₐ[k] k), k ∙ basePointsRepresentation M g m = k ∙ n := by
  -- As a closed point of the orbit of `[m]`, the line `[n]` is the image of a rational point.
  obtain ⟨g, hg⟩ : projectiveOrbitMap (H := H) n hn
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Set.range
        (fun g : WithConv (H →ₐ[k] k) ↦
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)) := by
    rw [range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints]
    exact ⟨hnm, projectiveOrbitMap_kernelPoint_mem_closedPoints n hn _⟩
  refine ⟨g, ?_⟩
  have h := (projectiveOrbitMap_kernelPoint_eq_iff_span_eq m hm n hn g 1).mp
    (by simpa [AlgHom.convOne_def] using hg)
  simpa using h

/-- **Orbits are equal or disjoint at lines.** The orbit of the line `[n]` equals the orbit of
`[m]` exactly when `[n]` lies in the orbit of `[m]`. Both orbits are full topological images,
including nonclosed points. -/
theorem range_projectiveOrbitMap_eq_iff
    (m : M) (hm : Module.IsUnimodular k m) (n : M) (hn : Module.IsUnimodular k n) :
    Set.range (projectiveOrbitMap (H := H) n hn) = Set.range (projectiveOrbitMap (H := H) m hm) ↔
      projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
        Set.range (projectiveOrbitMap (H := H) m hm) := by
  refine ⟨fun h ↦ h ▸ Set.mem_range_self _, fun hnm ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_span_basePointsRepresentation_eq_of_mem_range m hm n hn hnm
  exact (range_projectiveOrbitMap_eq_of_span_basePointsRepresentation_eq hm hn hg).symm

/-- The entire topological image of a finite-type affine group's projective orbit morphism
is locally closed over an algebraically closed field, including for nonreduced groups. -/
theorem isLocallyClosed_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular k m) :
    IsLocallyClosed (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  let := projectivePointMulAction (R := k) (H := H) (M := M)
  have := projectivePointMulAction_continuousConstSMul (R := k) (H := H) (M := M)
  apply isLocallyClosed_of_isConstructible_of_closedPoints_transitive
    (G := WithConv (H →ₐ[k] k)) (isConstructible_range_projectiveOrbitMap m hm)
  · intro g
    rw [Set.preimage_smul, ← Set.image_smul]
    simpa only [projectivePoint_smul_def] using
      image_projectivePointTranslation_range_projectiveOrbitMap g⁻¹ m hm
  · intro x hx y hy
    exact exists_smul_eq_of_mem_range_projectiveOrbitMap_inter_closedPoints m hm hx hy

/-- The boundary `closure O \ O` of the orbit `O` of a line is closed, because the orbit is
locally closed. -/
theorem isClosed_closure_diff_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular k m) :
    IsClosed (closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
      Set.range (projectiveOrbitMap (H := H) m hm)) :=
  isOpen_compl_iff.mp (isLocallyClosed_range_projectiveOrbitMap (H := H) m hm).isOpen_coborder

end TauCeti.Comodule
