/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# Linear isometries between Stiefel manifolds

A real linear isometry `f : E →ₗᵢ[ℝ] F` preserves inner products, so applying `f` vector by vector
maps orthonormal `k`-frames of `E` to orthonormal `k`-frames of `F`, giving a topological
embedding `f.stiefelMap k : C(stiefel E k, stiefel F k)` (`LinearIsometry.stiefelMap`,
`LinearIsometry.isEmbedding_stiefelMap`). For a linear isometric equivalence `e : E ≃ₗᵢ[ℝ] F`, the
induced map is a homeomorphism `e.stiefelHomeomorph k : stiefel E k ≃ₜ stiefel F k`
(`LinearIsometryEquiv.stiefelHomeomorph`), compatible with the sphere projections
(`LinearIsometryEquiv.stiefelProj_stiefelHomeomorph`).

## Main declarations

* `LinearIsometry.stiefelMap`: the continuous map `stiefel E k → stiefel F k` induced by a linear
  isometry, an embedding by `LinearIsometry.isEmbedding_stiefelMap`.
* `LinearIsometryEquiv.stiefelHomeomorph`: the homeomorphism `stiefel E k ≃ₜ stiefel F k` induced
  by a linear isometric equivalence.
-/

public section

open TauCeti Topology

namespace LinearIsometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : E →ₗᵢ[ℝ] F) (k : ℕ)

/-- A real linear isometry maps orthonormal `k`-frames to orthonormal `k`-frames, vector by
vector. -/
def stiefelMap : C(stiefel E k, stiefel F k) where
  toFun v := ⟨f ∘ v.val, mem_stiefel_iff.2 ((mem_stiefel_iff.1 v.property).comp_linearIsometry f)⟩
  continuous_toFun := continuous_induced_rng.2 <| continuous_pi fun i ↦
    f.continuous.comp ((continuous_apply i).comp continuous_subtypeVal)

@[simp]
theorem coe_stiefelMap_apply (v : stiefel E k) (i : Fin k) :
    ((f.stiefelMap k v : stiefel F k) : Fin k → F) i = f ((v : Fin k → E) i) :=
  (rfl)

/-- Projecting a mapped frame to its `i`-th vector applies `f.unitSphereMap` to the `i`-th vector of
the original frame. -/
@[simp]
theorem stiefelProj_stiefelMap (i : Fin k) (v : stiefel E k) :
    stiefelProj F k i (f.stiefelMap k v) = f.unitSphereMap (stiefelProj E k i v) :=
  Subtype.ext (by simp)

/-- The map on Stiefel manifolds induced by a linear isometry is a topological embedding. -/
theorem isEmbedding_stiefelMap : IsEmbedding (f.stiefelMap k) := by
  refine IsEmbedding.subtypeVal.of_comp_iff.1 ?_
  exact (IsEmbedding.piMap fun _ ↦ f.isometry.isEmbedding).comp IsEmbedding.subtypeVal

/-- The identity linear isometry induces the identity map on `V_k(E)`. -/
@[simp]
theorem stiefelMap_id : (LinearIsometry.id : E →ₗᵢ[ℝ] E).stiefelMap k = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ ↦ rfl

/-- Composition of linear isometries maps to composition on Stiefel manifolds. -/
theorem stiefelMap_comp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (g : F →ₗᵢ[ℝ] G) :
    (g.comp f).stiefelMap k = (g.stiefelMap k).comp (f.stiefelMap k) :=
  ContinuousMap.ext fun _ ↦ rfl

end LinearIsometry

namespace LinearIsometryEquiv

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- A real linear isometric equivalence induces a homeomorphism between Stiefel manifolds, acting
vector by vector. -/
def stiefelHomeomorph (e : E ≃ₗᵢ[ℝ] F) (k : ℕ) : stiefel E k ≃ₜ stiefel F k where
  toFun := e.toLinearIsometry.stiefelMap k
  invFun := e.symm.toLinearIsometry.stiefelMap k
  left_inv v := Subtype.ext <| funext fun i ↦ e.symm_apply_apply (v.val i)
  right_inv w := Subtype.ext <| funext fun i ↦ e.apply_symm_apply (w.val i)
  continuous_toFun := (e.toLinearIsometry.stiefelMap k).continuous
  continuous_invFun := (e.symm.toLinearIsometry.stiefelMap k).continuous

@[simp]
theorem coe_stiefelHomeomorph_apply (e : E ≃ₗᵢ[ℝ] F) (k : ℕ) (v : stiefel E k) (i : Fin k) :
    ((e.stiefelHomeomorph k v : stiefel F k) : Fin k → F) i = e ((v : Fin k → E) i) :=
  (rfl)

@[simp]
theorem stiefelHomeomorph_symm (e : E ≃ₗᵢ[ℝ] F) (k : ℕ) :
    (e.stiefelHomeomorph k).symm = e.symm.stiefelHomeomorph k :=
  (rfl)

@[simp]
theorem stiefelHomeomorph_refl (k : ℕ) :
    (LinearIsometryEquiv.refl ℝ E).stiefelHomeomorph k = Homeomorph.refl (stiefel E k) :=
  Homeomorph.ext fun _ ↦ rfl

@[simp]
theorem stiefelHomeomorph_trans (e₁ : E ≃ₗᵢ[ℝ] F) (e₂ : F ≃ₗᵢ[ℝ] G) (k : ℕ) :
    (e₁.trans e₂).stiefelHomeomorph k = (e₁.stiefelHomeomorph k).trans (e₂.stiefelHomeomorph k) :=
  Homeomorph.ext fun _ ↦ rfl

/-- The Stiefel homeomorphism induced by a linear isometric equivalence intertwines the projections
to the unit spheres with `unitSphereIsometryEquiv`. -/
@[simp]
theorem stiefelProj_stiefelHomeomorph (e : E ≃ₗᵢ[ℝ] F) (k : ℕ) (i : Fin k) (v : stiefel E k) :
    stiefelProj F k i (e.stiefelHomeomorph k v) =
      e.unitSphereIsometryEquiv (stiefelProj E k i v) :=
  Subtype.ext (by simp)

end LinearIsometryEquiv
