/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
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

On a normed model fibre, `ContinuousLinearMap.symmetrizeBilinear` is the continuous linear
retraction `b ↦ (b + bᵀ) / 2` when two is nonzero. It commutes with changes of variables, so its
image is independent of the chosen fibre coordinates. Taking real-valued maps on tangent spaces
gives the fibre model for symmetric covariant two-tensors, the ambient tensors for metrics.
-/

public section

noncomputable section

namespace TauCeti

variable (𝕜 : Type*) [NormedField 𝕜]
  (E : Type*) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  (G : Type*) [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

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
theorem isClosed_symmetricBilinearMaps [ContinuousSMul 𝕜 E] [T2Space G] :
    IsClosed (symmetricBilinearMaps 𝕜 E G : Set (E →L[𝕜] E →L[𝕜] G)) := by
  have heq : (symmetricBilinearMaps 𝕜 E G : Set (E →L[𝕜] E →L[𝕜] G)) =
      ⋂ v, ⋂ w, {b | b v w = b w v} := by ext b; simp
  rw [heq]
  exact isClosed_iInter fun v ↦ isClosed_iInter fun w ↦
    isClosed_eq ((continuous_eval_const v).eval_const w)
      ((continuous_eval_const w).eval_const v)

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti

variable {𝕜 : Type*} [NormedField 𝕜]
  {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

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
def symmetrizeBilinear :
    (V →L[𝕜] V →L[𝕜] G) →L[𝕜] symmetricBilinearMaps 𝕜 V G :=
  ContinuousLinearMap.codRestrict
    ((2 : 𝕜)⁻¹ • (ContinuousLinearMap.id 𝕜 _ +
      ((flipₗᵢ 𝕜 V V G).toContinuousLinearEquiv : _ →L[𝕜] _)))
    (symmetricBilinearMaps 𝕜 V G) (fun b v w ↦ by simp [add_comm])

@[simp]
theorem symmetrizeBilinear_apply (b : V →L[𝕜] V →L[𝕜] G) (v w : V) :
    (symmetrizeBilinear b).val v w = (2 : 𝕜)⁻¹ • (b v w + b w v) :=
  (rfl)

/-- Symmetrization is the identity on symmetric bilinear maps. -/
@[simp]
theorem symmetrizeBilinear_coe [NeZero (2 : 𝕜)] (b : symmetricBilinearMaps 𝕜 V G) :
    symmetrizeBilinear b.val = b := by
  apply Subtype.ext
  ext v w
  simp [symmetrizeBilinear_apply, b.property v w, ← two_smul 𝕜, NeZero.ne (2 : 𝕜)]

/-- Symmetrization commutes with simultaneous pullback of its two arguments. -/
theorem symmetrizeBilinear_bilinearComp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (b : V →L[𝕜] V →L[𝕜] G) (A : W →L[𝕜] V) :
    (symmetrizeBilinear (b.bilinearComp A A)).val =
      (symmetrizeBilinear b).val.bilinearComp A A := by
  ext v w
  simp

end Normed

end ContinuousLinearMap
