/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Transporting Hilbert bases by linear isometric equivalences

This file adds the Hilbert-basis analogue of `Basis.map`: a Hilbert basis of a Hilbert space
can be transported across a linear isometric equivalence. It follows Mathlib's
`OrthonormalBasis.map` API for transporting orthonormal bases. A typical use is moving a weighted
orthogonal-polynomial basis across the isometry between the weighted and unweighted `L²` spaces.

The API is intentionally small: the representation equality and pointwise simp lemmas expose the
transport, while Mathlib's existing Hilbert-basis coordinate and Parseval lemmas supply the derived
coordinate identities after rewriting through the inverse isometry.
-/

public section

variable {ι 𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

/-- Transport a Hilbert basis along a linear isometric equivalence. -/
protected noncomputable def mapₗᵢ (b : HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    HilbertBasis ι 𝕜 F :=
  ofRepr (e.symm.trans b.repr)

/-- The coordinate representation of `b.mapₗᵢ e` is `b.repr` after applying `e.symm`. -/
@[simp]
theorem repr_mapₗᵢ (b : HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e).repr = e.symm.trans b.repr :=
  (rfl)

/-- The `i`th vector of the transported basis is the image of the `i`th vector. -/
@[simp]
theorem mapₗᵢ_apply (b : HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (i : ι) :
    b.mapₗᵢ e i = e (b i) := by
  classical
  simp only [← HilbertBasis.repr_symm_single, repr_mapₗᵢ, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_symm]

/-- Function-level form of `HilbertBasis.mapₗᵢ_apply`. -/
@[simp]
theorem coe_mapₗᵢ (b : HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    ⇑(b.mapₗᵢ e) = e ∘ b :=
  funext (b.mapₗᵢ_apply e)

/-- Transport along the identity isometry leaves a Hilbert basis unchanged. -/
@[simp]
theorem mapₗᵢ_refl (b : HilbertBasis ι 𝕜 E) :
    b.mapₗᵢ (LinearIsometryEquiv.refl 𝕜 E) = b :=
  DFunLike.ext _ _ fun _ => by simp

/-- Transporting along two linear isometric equivalences is the same as transporting along their
composition. -/
@[simp]
theorem mapₗᵢ_trans {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (f : F ≃ₗᵢ[𝕜] G) :
    (b.mapₗᵢ e).mapₗᵢ f = b.mapₗᵢ (e.trans f) :=
  DFunLike.ext _ _ fun _ => by simp

/-- Transporting a Hilbert basis across an isometry and then back across the inverse isometry
recovers the original basis. -/
theorem mapₗᵢ_symm (b : HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e).mapₗᵢ e.symm = b := by
  simp

/-- Transporting a Hilbert basis back across an inverse isometry and then forward again recovers
the original basis. -/
theorem mapₗᵢ_symm_self (b : HilbertBasis ι 𝕜 F) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e.symm).mapₗᵢ e = b := by
  simp

end HilbertBasis
