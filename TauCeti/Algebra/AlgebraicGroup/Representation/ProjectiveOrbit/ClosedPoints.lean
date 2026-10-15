/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
public import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedPoints

/-!
# Closed points of a projective orbit image

Over an algebraically closed field, every closed point in the full image of a finite-type
affine group's projective orbit morphism is the image of a rational group point. Conversely,
all rational orbit images are closed. The existing rational-fiber characterization therefore
describes every closed point of the image, rather than only a possibly smaller rational subset.

This is the closed-point lifting input for realizing homogeneous spaces as locally closed
projective orbits. The full image may also include nonclosed points. No smoothness or
reducedness hypothesis is imposed on the group.

The comparison uses `range_kernelPoint_eq_closedPoints` and the closed-point image theorem
for locally finite-type morphisms. Together with
`projectiveOrbitMap_kernelPoint_eq_iff_span_eq`, it identifies closed orbit images with
the lines through translated vectors.

The closed points of the whole projective space of lines are likewise the lines `k ∙ m` for
nonzero vectors `m`, that is, the images of the identity point under the orbit morphisms of
nonzero vectors. One direction is the description of closed points of `Proj (Sym N)` by
nonzero functionals (`TauCeti.SymmetricAlgebra.exists_ne_zero_forall_mem_iff_of_isClosed`),
applied to `N = M∨`; the other is Mathlib's `pointEquivClosedPoint`. This part needs neither
finite generation nor reducedness of the Hopf algebra.

## Main declarations

* `TauCeti.Comodule.mem_closedPoints_iff_exists_projectiveOrbitMap_eq`: the closed points of
  projective space are the identity images of orbit morphisms of nonzero vectors.
* `TauCeti.Comodule.range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints`: the
  rational orbit images are the closed points of the orbit.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv TopologicalSpace

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- Over an algebraically closed field, the closed points of the projective space of lines in a
finite-dimensional representation are exactly the images of the identity point under the
projective orbit morphisms of its nonzero vectors, that is, the lines `k ∙ m`. Neither finite
generation nor reducedness of the Hopf algebra is needed. -/
theorem mem_closedPoints_iff_exists_projectiveOrbitMap_eq
    (x : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))) :
    x ∈ closedPoints _ ↔ ∃ (m : M) (hm : Module.IsUnimodular k m),
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) = x := by
  constructor
  · intro hx
    obtain ⟨v, hv0, hv⟩ :=
      TauCeti.SymmetricAlgebra.exists_ne_zero_forall_mem_iff_of_isClosed x hx
    obtain ⟨φ, hφ⟩ : ∃ φ, v φ ≠ 0 := by
      by_contra! h
      exact hv0 (LinearMap.ext h)
    set m := (Module.evalEquiv k M).symm v
    have hmv : Module.Dual.eval k M m = v :=
      LinearMap.ext fun ψ ↦ Module.apply_evalEquiv_symm_apply k M ψ v
    have hφm : φ m = v φ := by simpa using LinearMap.congr_fun hmv φ
    have hm : Module.IsUnimodular k m := Module.isUnimodular_of_apply_eq_one (f := (v φ)⁻¹ • φ)
      (by rw [LinearMap.smul_apply, hφm, smul_eq_mul, inv_mul_cancel₀ hφ])
    refine ⟨m, hm, ProjectiveSpectrum.ext_of_mem_pos fun n hn s hs ↦ ?_⟩
    have h := mem_projectiveOrbitMap_kernelPoint_iff (H := H) m hm 1 hn hs
    simp only [map_one, Module.End.one_apply] at h
    simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] at h
    rw [h, hv n hn s hs, hmv]
  · rintro ⟨m, hm, rfl⟩
    let p := Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k H : H →+* k)) ≫
      projectiveOrbitMap (H := H) m hm
    have hp : p ≫ TauCeti.SymmetricAlgebra.projToSpec k (Module.Dual k M) = 𝟙 _ := by
      rw [Category.assoc, projectiveOrbitMap_projToSpec, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext r
      simp
    have hpt : p (IsLocalRing.closedPoint k) =
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
      have h : Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k H : H →+* k))
          (IsLocalRing.closedPoint k) = AlgHom.kernelPoint (Bialgebra.counitAlgHom k H) := by
        apply PrimeSpectrum.ext
        change (PrimeSpectrum.comap _ (IsLocalRing.closedPoint k)).asIdeal = _
        rw [PrimeSpectrum.comap_asIdeal, AlgHom.kernelPoint_asIdeal]
        dsimp only [IsLocalRing.closedPoint]
        rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
        rfl
      rw [← h]
      rfl
    rw [← hpt]
    exact (pointEquivClosedPoint (TauCeti.SymmetricAlgebra.projToSpec k (Module.Dual k M))
      ⟨p, hp⟩).2

variable [Algebra.FiniteType k H]

/-- Rational orbit images are exactly the closed points in the full topological image of
the projective orbit morphism. -/
theorem range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints
    (m : M) (hm : Module.IsUnimodular k m) :
    Set.range (fun g : WithConv (H →ₐ[k] k) ↦
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)) =
        Set.range (projectiveOrbitMap (H := H) m hm) ∩
          closedPoints (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k
            (Module.Dual k M))) := by
  rw [← (projectiveOrbitMap (H := H) m hm).image_closedPoints_eq_range_inter_closedPoints,
    ← range_kernelPoint_eq_closedPoints (k := k) (A := H), ← Set.range_comp]
  exact (ofConv_surjective (A := H →ₐ[k] k)).range_comp
    (⇑(projectiveOrbitMap (H := H) m hm) ∘ AlgHom.kernelPoint)

end TauCeti.Comodule
