/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.Grassmannian.Map

/-!
# Rank-one Grassmannians and projective spaces

Mathlib's `Projectivization.equivSubmodule` identifies projective points with one-dimensional
subspaces. For finite coordinate spaces this equivalence is a homeomorphism onto the
rank-one Grassmannian with its frame-quotient topology: a one-vector frame is precisely a
nonzero vector, with the same coordinate topology. Thus the projective and Grassmannian
constructions give the same finite real and complex projective spaces, not merely equivalent
sets. The comparison commutes with injective linear maps, in particular ambient coordinate
inclusions. Compactness and Hausdorffness transfer from the projective model.

The algebraic comparison is Mathlib's `Projectivization.equivSubmodule`; the quotient topology
and affine charts on projective space come from `TauCeti.Topology.Algebra.Projectivization`.
-/

public section

open Set
open scoped LinearAlgebra.Projectivization

namespace TauCeti.finiteGrassmannian

variable {𝕜 : Type*} [Field 𝕜] {N M : ℕ}

private theorem equivSubmodule_mk_frame (v : finiteFullRankFrame 𝕜 1 N) :
    Projectivization.equivSubmodule 𝕜 (Fin N → 𝕜)
      (Projectivization.mk 𝕜 (v.1 0) (v.2.ne_zero 0)) = frameSpan v := by
  apply Subtype.ext
  simp only [Projectivization.coe_equivSubmodule, Projectivization.submodule_mk,
    coe_frameSpan, Set.range_unique, Fin.default_eq_zero]

variable [TopologicalSpace 𝕜]

/-- Projective space is the rank-one finite Grassmannian, with its frame-quotient topology.
The underlying equivalence is Mathlib's `Projectivization.equivSubmodule`. -/
noncomputable def projectivizationHomeomorph (𝕜 : Type*) [Field 𝕜] [TopologicalSpace 𝕜]
    (N : ℕ) : ℙ 𝕜 (Fin N → 𝕜) ≃ₜ finiteGrassmannian 𝕜 1 N where
  toEquiv := Projectivization.equivSubmodule 𝕜 (Fin N → 𝕜)
  continuous_toFun := by
    apply Projectivization.continuous_iff.2
    refine (continuous_frameSpan.comp
      (finiteFullRankFrame.continuous_ofNeZero (𝕜 := 𝕜) (N := N))).congr fun v ↦ ?_
    simpa only [Function.comp_apply, Equiv.toFun_as_coe, Projectivization.mk'_eq_mk,
      finiteFullRankFrame.coe_ofNeZero] using
      (equivSubmodule_mk_frame (finiteFullRankFrame.ofNeZero v)).symm
  continuous_invFun := by
    apply isQuotientMap_frameSpan.continuous_iff.2
    have hc := Projectivization.continuous_mk (K := 𝕜)
      ((continuous_apply 0).comp (continuous_subtype_val (p :=
        fun v : Fin 1 → Fin N → 𝕜 ↦ LinearIndependent 𝕜 v)))
      (fun v ↦ v.2.ne_zero 0)
    exact hc.congr fun v ↦
      ((Projectivization.equivSubmodule 𝕜 (Fin N → 𝕜)).symm_apply_eq.2
        (equivSubmodule_mk_frame v).symm).symm

/-- The comparison retains the actual line as a submodule of the coordinate space. -/
@[simp]
theorem coe_projectivizationHomeomorph (p : ℙ 𝕜 (Fin N → 𝕜)) :
    (projectivizationHomeomorph 𝕜 N p).1 = p.submodule :=
  Projectivization.coe_equivSubmodule 𝕜 p

/-- The inverse comparison also retains the underlying line. -/
@[simp]
theorem submodule_projectivizationHomeomorph_symm (V : finiteGrassmannian 𝕜 1 N) :
    ((projectivizationHomeomorph 𝕜 N).symm V).submodule = V.1 :=
  congrArg Subtype.val ((projectivizationHomeomorph 𝕜 N).apply_symm_apply V)

/-- The projective point of a one-vector frame corresponds to its span. -/
@[simp]
theorem projectivizationHomeomorph_mk_frame (v : finiteFullRankFrame 𝕜 1 N) :
    projectivizationHomeomorph 𝕜 N (Projectivization.mk 𝕜 (v.1 0) (v.2.ne_zero 0)) =
      frameSpan v :=
  equivSubmodule_mk_frame v

/-- The comparison is natural for injective linear maps, including the finite-stage
coordinate inclusions used for projective spaces. -/
@[simp]
theorem projectivizationHomeomorph_map
    (f : (Fin N → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hf : Function.Injective f)
    (p : ℙ 𝕜 (Fin N → 𝕜)) :
    projectivizationHomeomorph 𝕜 M (Projectivization.map f hf p) =
      map f hf (projectivizationHomeomorph 𝕜 N p) := by
  apply Subtype.ext
  simpa only [coe_projectivizationHomeomorph, coe_map] using
    Projectivization.submodule_map f hf p

/-- Hausdorffness of projective space transfers to the rank-one Grassmannian.
In particular, this applies over the real and complex numbers. -/
instance [T2Space (ℙ 𝕜 (Fin N → 𝕜))] : T2Space (finiteGrassmannian 𝕜 1 N) :=
  (projectivizationHomeomorph 𝕜 N).symm.isEmbedding.t2Space

/-- Compactness of projective space transfers to the rank-one Grassmannian.
In particular, finite real and complex rank-one Grassmannians are compact. -/
instance [CompactSpace (ℙ 𝕜 (Fin N → 𝕜))] : CompactSpace (finiteGrassmannian 𝕜 1 N) :=
  (projectivizationHomeomorph 𝕜 N).surjective.compactSpace
    (projectivizationHomeomorph 𝕜 N).continuous

end TauCeti.finiteGrassmannian
