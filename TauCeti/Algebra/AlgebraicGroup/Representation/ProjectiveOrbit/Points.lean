/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic

/-!
# Rational fibers of projective orbit morphisms

The projective orbit morphism sends a rational group point to the line through its translate
of the chosen vector. Two such images coincide exactly when those translates span the same
line. In particular, its fiber over the identity image is the line stabilizer. This identifies
the rational fibers used in the construction of homogeneous spaces from projective orbits.

The result concerns points of the underlying projective spectrum. It does not identify
scheme-theoretic fibers or a quotient scheme. No smoothness or reducedness is required.

The construction uses `Comodule.projectiveOrbitMap`, its standard-open formulas, and
`Comodule.basePointsRepresentation`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.Comodule

universe u

section Coordinates

variable {R H M : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Evaluating orbit coordinates at a rational point evaluates homogeneous polynomials on
the translated vector. -/
@[simp]
theorem comp_orbitCoordinates (m : M) (g : WithConv (H →ₐ[R] R)) :
    g.ofConv.comp (orbitCoordinates (H := H) m) =
      SymmetricAlgebra.lift (Module.Dual.eval R M (basePointsRepresentation M g m)) := by
  ext φ
  simp

end Coordinates

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- A positive-degree homogeneous polynomial vanishes at the image of a rational group point
precisely when it vanishes on the translated vector. -/
theorem mem_projectiveOrbitMap_kernelPoint_iff (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) {s : SymmetricAlgebra k (Module.Dual k M)} {n : ℕ}
    (hn : 0 < n) (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M) n) :
    s ∈ (projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)).asHomogeneousIdeal ↔
      SymmetricAlgebra.lift (Module.Dual.eval k M (basePointsRepresentation M g m)) s = 0 := by
  have h := congrArg (fun U : (Spec (.of H)).Opens ↦ AlgHom.kernelPoint g.ofConv ∈ U)
    (projectiveOrbitMap_preimage_basicOpen m hm hn hs)
  rw [basicOpen_eq_of_affine] at h
  -- The scheme carriers use their own membership instances. Identify these with the
  -- spectrum ideals before applying the coordinate computation; the open lemmas cannot
  -- rewrite through those instances directly.
  change (s ∉ (projectiveOrbitMap (H := H) m hm
    (AlgHom.kernelPoint g.ofConv)).asHomogeneousIdeal) =
      ((orbitCoordinates (H := H) m s) ∉ (AlgHom.kernelPoint g.ofConv).asIdeal) at h
  simp only [AlgHom.kernelPoint_asIdeal, RingHom.mem_ker, AlgHom.coe_toRingHom,
    ← AlgHom.comp_apply, comp_orbitCoordinates] at h
  exact not_iff_not.mp (Iff.of_eq h)

/-- A linear homogeneous coordinate vanishes at a rational orbit image exactly when the
corresponding functional annihilates the translated vector. -/
@[simp]
theorem ι_mem_projectiveOrbitMap_kernelPoint_iff (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) (φ : Module.Dual k M) :
    SymmetricAlgebra.ι k (Module.Dual k M) φ ∈
        (projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)).asHomogeneousIdeal ↔
      φ (basePointsRepresentation M g m) = 0 := by
  simpa using mem_projectiveOrbitMap_kernelPoint_iff m hm g (by decide : 0 < 1)
    (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule k (Module.Dual k M) φ)

/-- Two rational projective orbit images coincide exactly when their translated vectors
generate the same line. The vectors may be chosen independently. -/
theorem projectiveOrbitMap_kernelPoint_eq_iff_span_eq
    (m : M) (hm : Module.IsUnimodular k m) (p : M) (hp : Module.IsUnimodular k p)
    (g h : WithConv (H →ₐ[k] k)) :
    projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) =
        projectiveOrbitMap (H := H) p hp (AlgHom.kernelPoint h.ofConv) ↔
      k ∙ basePointsRepresentation M g m = k ∙ basePointsRepresentation M h p := by
  constructor
  · intro heq
    apply Subspace.dualAnnihilator_inj.mp
    ext φ
    have hcoord := congrArg
      (fun x ↦ SymmetricAlgebra.ι k (Module.Dual k M) φ ∈ x.asHomogeneousIdeal) heq
    simp only [← SetLike.mem_coe, Submodule.coe_dualAnnihilator_span,
      Set.mem_ofPred_eq, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    simpa only [ι_mem_projectiveOrbitMap_kernelPoint_iff] using Iff.of_eq hcoord
  · intro hline
    obtain ⟨a, ha⟩ := Submodule.span_singleton_eq_span_singleton.mp hline
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext'
    intro n s hs
    rcases n with _ | n
    · obtain ⟨r, rfl⟩ : ∃ r : k, algebraMap k (SymmetricAlgebra k (Module.Dual k M)) r = s := by
        exact ⟨TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv k (Module.Dual k M)
          ⟨s, hs⟩, TauCeti.SymmetricAlgebra.algebraMap_homogeneousSubmoduleZeroEquiv_apply _ _ _⟩
      rcases eq_or_ne r 0 with rfl | hr
      · simp
      · have hu := (isUnit_iff_ne_zero.mpr hr).map
          (algebraMap k (SymmetricAlgebra k (Module.Dual k M)))
        have hnot (x : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k
            (Module.Dual k M))) :
            algebraMap k (SymmetricAlgebra k (Module.Dual k M)) r ∉ x.asHomogeneousIdeal :=
          fun hx ↦ x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
        exact iff_of_false (hnot _) (hnot _)
    · rw [mem_projectiveOrbitMap_kernelPoint_iff m hm g (Nat.succ_pos n) hs,
        mem_projectiveOrbitMap_kernelPoint_iff p hp h (Nat.succ_pos n) hs, ← ha]
      have heval : Module.Dual.eval k M (a • basePointsRepresentation M g m) =
          (a : k) • Module.Dual.eval k M (basePointsRepresentation M g m) := by
        ext φ
        simp [Units.smul_def]
      rw [heval, TauCeti.SymmetricAlgebra.lift_smul_of_mem_homogeneousSubmodule
        k (Module.Dual k M) _ (a : k) hs]
      simp [a.ne_zero]

/-- The rational fiber over the identity orbit image consists precisely of the points that
carry the chosen line onto itself. -/
theorem projectiveOrbitMap_kernelPoint_eq_one_iff (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) =
        projectiveOrbitMap (H := H) m hm
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ↔
      (k ∙ m).map (basePointsRepresentation M g) = k ∙ m := by
  have h := projectiveOrbitMap_kernelPoint_eq_iff_span_eq m hm m hm g 1
  have haction : basePointsRepresentation M (1 : WithConv (H →ₐ[k] k)) m = m := by simp
  rw [haction] at h
  simpa [Submodule.map_span, AlgHom.convOne_def] using h

end TauCeti.Comodule
