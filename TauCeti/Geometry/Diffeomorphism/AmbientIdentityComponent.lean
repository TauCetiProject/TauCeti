/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Naturality

/-!
# Diffeomorphisms ambient isotopic to the identity

This file packages the self-diffeomorphisms of a manifold whose underlying homeomorphisms are
ambient isotopic to the identity. They form a normal subgroup of the diffeomorphism group. This is
the relation-level precursor of the identity component of `Diff(M)`: once the geometric-topology
roadmap's C∞ topology on `Diff(M)` is available, this subgroup is the object compared with the
path component of the identity.

The construction deliberately reuses the general point-set relation `TauCeti.AmbientIsotopic`, as
required by the encoding conventions in `TauCetiRoadmap/GeometricTopology/README.md`. No topology
on the diffeomorphism group is assumed here.

## Main definitions

* `TauCeti.Diffeomorph.ambientIdentityComponent`: the normal subgroup of self-diffeomorphisms
  ambient isotopic to the identity.

## Main results

* `TauCeti.Diffeomorph.mem_ambientIdentityComponent_iff`: membership is ambient isotopy of the
  underlying continuous self-map from the identity.
* `TauCeti.Diffeomorph.ambientIsotopic_iff_mul_inv_mem`: two diffeomorphisms differ by ambient
  isotopy exactly when their quotient belongs to the identity subgroup.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

private def continuousMap (f : M ≃ₘ^n⟮I, I⟯ M) : C(M, M) := f.toHomeomorph

private theorem continuousMap_one :
    continuousMap (I := I) (n := n) (1 : M ≃ₘ^n⟮I, I⟯ M) = ContinuousMap.id M := rfl

private theorem continuousMap_mul (f g : M ≃ₘ^n⟮I, I⟯ M) :
    continuousMap (f * g) = (continuousMap f).comp (continuousMap g) := rfl

private theorem continuousMap_inv (f : M ≃ₘ^n⟮I, I⟯ M) :
    continuousMap f⁻¹ = (f.toHomeomorph.symm : C(M, M)) := rfl

/-- The self-diffeomorphisms whose underlying continuous maps are ambient isotopic to the
identity. This is a normal subgroup: ambient isotopies compose, invert, and are invariant under
changes of ambient coordinates. -/
def ambientIdentityComponent : Subgroup (M ≃ₘ^n⟮I, I⟯ M) where
  carrier := {f | AmbientIsotopic (ContinuousMap.id M) (continuousMap f)}
  one_mem' := by
    dsimp only [Set.mem_setOf_eq]
    rw [continuousMap_one]
  mul_mem' := by
    intro f g hf hg
    dsimp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [continuousMap_mul]
    exact hf.trans (hg.postcomp_homeomorph f.toHomeomorph)
  inv_mem' := by
    intro f hf
    dsimp only [Set.mem_setOf_eq] at hf ⊢
    rw [continuousMap_inv]
    have hleft : (f.toHomeomorph.symm : C(M, M)).comp (continuousMap f) =
        ContinuousMap.id M := by
      ext x
      simp [continuousMap]
    rw [← hleft]
    exact hf.symm.postcomp_homeomorph f.toHomeomorph.symm

/-- Membership in the ambient identity component means that the underlying continuous map is
ambient isotopic to the identity map. -/
theorem mem_ambientIdentityComponent_iff {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ ambientIdentityComponent (I := I) (n := n) ↔
      AmbientIsotopic (ContinuousMap.id M) (f.toHomeomorph : C(M, M)) := Iff.rfl

/-- The ambient identity component is a normal subgroup of the diffeomorphism group. -/
instance ambientIdentityComponent_isNormal :
    (ambientIdentityComponent (I := I) (M := M) (n := n)).Normal where
  conj_mem f hf g := by
    rw [mem_ambientIdentityComponent_iff] at hf ⊢
    have htarget : ((g * f * g⁻¹).toHomeomorph : C(M, M)) =
        continuousMap (g * f * g⁻¹) := rfl
    rw [htarget]
    rw [continuousMap_mul, continuousMap_mul, continuousMap_inv]
    simpa [continuousMap] using
      (hf.precomp (g.toHomeomorph.symm : C(M, M))).postcomp_homeomorph g.toHomeomorph

/-- A diffeomorphism ambient isotopic to the identity remains so after conjugation. -/
theorem conj_mem_ambientIdentityComponent {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ ambientIdentityComponent (I := I) (n := n)) (g : M ≃ₘ^n⟮I, I⟯ M) :
    g * f * g⁻¹ ∈ ambientIdentityComponent (I := I) (n := n) :=
  (inferInstance : (ambientIdentityComponent (I := I) (M := M) (n := n)).Normal).conj_mem f hf g

/-- Two self-diffeomorphisms are ambient isotopic exactly when their quotient belongs to the
ambient identity component. The quotient is `g * f⁻¹`, since multiplication acts as function
composition. -/
theorem ambientIsotopic_iff_mul_inv_mem (f g : M ≃ₘ^n⟮I, I⟯ M) :
    AmbientIsotopic (f.toHomeomorph : C(M, M)) (g.toHomeomorph : C(M, M)) ↔
      g * f⁻¹ ∈ ambientIdentityComponent (I := I) (n := n) := by
  rw [mem_ambientIdentityComponent_iff]
  constructor
  · intro h
    have h' := h.precomp (f.toHomeomorph.symm : C(M, M))
    convert h' using 1 <;> ext x <;> simp
  · intro h
    have h' := h.precomp (f.toHomeomorph : C(M, M))
    convert h' using 1 <;> ext x <;> simp

end Diffeomorph

end TauCeti
