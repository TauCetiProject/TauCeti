/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Symmetric continuous bilinear maps

Symmetric continuous bilinear maps form a closed linear subspace. Simultaneous change of
variables preserves this subspace. These restricted coordinate changes provide the model
fibres and gluing maps for bundles of symmetric bilinear tensors.

`ContinuousLinearEquiv.symmetricBilinearMapsCongr` restricts Mathlib's iterated `arrowCongr`
using `ContinuousLinearEquiv.ofSubmodules`. It needs only the topology of the original
spaces, so it applies to bundle fibres without choosing fibre norms. The identity, inverse
and composition laws give consistent coordinates on overlaps. In finite dimensions these
equivalences also identify the dimensions of the symmetric fibres.

On a normed model fibre, `ContinuousLinearMap.symmetrize` is the continuous linear retraction
`b ↦ (b + bᵀ) / 2` when two is nonzero. It commutes with changes of variables, so its image
is independent of the chosen fibre coordinates. Taking real-valued maps on tangent spaces
gives the fibre model for symmetric covariant two-tensors, the ambient tensors for metrics.
-/

public section

noncomputable section

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type*) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The linear subspace of symmetric continuous bilinear maps. -/
def symmetricBilinearMaps : Submodule 𝕜 (E →L[𝕜] E →L[𝕜] G) where
  carrier := {b | ∀ v w, b v w = b w v}
  zero_mem' := by simp
  add_mem' hb hc v w := by simp [hb v w, hc v w]
  smul_mem' a b hb v w := by simp [hb v w]

@[simp]
theorem mem_symmetricBilinearMaps (b : E →L[𝕜] E →L[𝕜] G) :
    b ∈ symmetricBilinearMaps 𝕜 E G ↔ ∀ v w, b v w = b w v :=
  Iff.rfl

/-- Symmetry is closed in the topology of continuous bilinear maps. -/
theorem isClosed_symmetricBilinearMaps [IsNormableSpace 𝕜 E] :
    IsClosed (symmetricBilinearMaps 𝕜 E G : Set (E →L[𝕜] E →L[𝕜] G)) := by
  have heq : (symmetricBilinearMaps 𝕜 E G : Set (E →L[𝕜] E →L[𝕜] G)) =
      ⋂ v, ⋂ w, {b | b v w = b w v} := by ext b; simp
  rw [heq]
  exact isClosed_iInter fun v ↦ isClosed_iInter fun w ↦
    isClosed_eq ((ContinuousLinearMap.apply 𝕜 G w).continuous.comp
      (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] G) v).continuous)
      ((ContinuousLinearMap.apply 𝕜 G v).continuous.comp
        (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] G) w).continuous)

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A change of variables identifies the spaces of symmetric bilinear maps. -/
def symmetricBilinearMapsCongr (e : E ≃L[𝕜] F) :
    symmetricBilinearMaps 𝕜 E G ≃L[𝕜] symmetricBilinearMaps 𝕜 F G := by
  let a := e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G))
  refine a.ofSubmodules _ _ ?_
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩ v w
    exact hc (e.symm v) (e.symm w)
  · intro hb
    refine ⟨a.symm b, ?_, a.apply_symm_apply b⟩
    intro v w
    exact hb (e v) (e w)

@[simp]
theorem symmetricBilinearMapsCongr_apply (e : E ≃L[𝕜] F)
    (b : symmetricBilinearMaps 𝕜 E G) (v w : F) :
    (symmetricBilinearMapsCongr e b : F →L[𝕜] F →L[𝕜] G) v w =
      b.val (e.symm v) (e.symm w) :=
  (rfl)

/-- The identity change of variables gives the identity symmetric coordinates. -/
@[simp]
theorem symmetricBilinearMapsCongr_refl :
    symmetricBilinearMapsCongr (G := G) (ContinuousLinearEquiv.refl 𝕜 E) =
      ContinuousLinearEquiv.refl 𝕜 (symmetricBilinearMaps 𝕜 E G) := by
  ext b v w
  rfl

/-- Reversing a change of variables reverses the induced symmetric coordinates. -/
@[simp]
theorem symmetricBilinearMapsCongr_symm (e : E ≃L[𝕜] F) :
    (symmetricBilinearMapsCongr (G := G) e).symm = symmetricBilinearMapsCongr e.symm := by
  ext b v w
  rfl

/-- Symmetric coordinates respect composition, giving the overlap cocycle law. -/
@[simp]
theorem symmetricBilinearMapsCongr_trans
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
    (e : E ≃L[𝕜] F) (f : F ≃L[𝕜] W) :
    symmetricBilinearMapsCongr (G := G) (e.trans f) =
      (symmetricBilinearMapsCongr e).trans (symmetricBilinearMapsCongr f) := by
  ext b v w
  rfl

end ContinuousLinearEquiv

namespace ContinuousLinearMap

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Averaging a bilinear map with its transpose, with codomain the symmetric subspace. -/
def symmetrize :
    (V →L[𝕜] V →L[𝕜] G) →L[𝕜] symmetricBilinearMaps 𝕜 V G :=
  { toFun b := ⟨(2 : 𝕜)⁻¹ • (b + b.flip), fun v w ↦ by simp [add_comm]⟩
    map_add' b c := by ext v w; simp; module
    map_smul' a b := by ext v w; simp [smul_add, smul_smul, mul_comm]
    cont := by
      apply Continuous.subtype_mk
      -- The unbundled bound works with the intrinsic topology on iterated hom spaces,
      -- without identifying its normed and seminormed instances.
      have hf : IsBoundedLinearMap 𝕜
          (fun b : V →L[𝕜] V →L[𝕜] G ↦ b.flip) :=
        { map_add := fun b c ↦ by ext v w; simp
          map_smul := fun a b ↦ by ext v w; simp
          bound := ⟨1, by norm_num, fun b ↦ by simp⟩ }
      exact (continuous_const (y := (2 : 𝕜)⁻¹)).smul (continuous_id.add hf.continuous) }

@[simp]
theorem symmetrize_apply (b : V →L[𝕜] V →L[𝕜] G) (v w : V) :
    (symmetrize b).val v w = (2 : 𝕜)⁻¹ • (b v w + b w v) :=
  (rfl)

/-- Symmetrization is the identity on symmetric bilinear maps. -/
@[simp]
theorem symmetrize_coe [NeZero (2 : 𝕜)] (b : symmetricBilinearMaps 𝕜 V G) :
    symmetrize b.val = b := by
  apply Subtype.ext
  ext v w
  rw [symmetrize_apply, b.property v w, ← two_smul 𝕜,
    inv_smul_smul₀ (NeZero.ne (2 : 𝕜))]

/-- Symmetrization commutes with simultaneous pullback of its two arguments. -/
theorem symmetrize_bilinearComp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (b : V →L[𝕜] V →L[𝕜] G) (A : W →L[𝕜] V) :
    (symmetrize (b.bilinearComp A A)).val =
      (symmetrize b).val.bilinearComp A A := by
  ext v w
  simp

end Normed

end ContinuousLinearMap
