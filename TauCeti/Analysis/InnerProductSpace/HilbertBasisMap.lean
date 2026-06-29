/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Transporting Hilbert bases by linear isometric equivalences

This file adds the Hilbert-basis analogue of `Basis.map`: a Hilbert basis of a Hilbert space
can be transported across a linear isometric equivalence.  The construction is the Part 0
`HilbertBasis.mapₗᵢ` primitive from the `OrthogonalL2Bases` roadmap, used later to move weighted
orthogonal-polynomial bases across the weight-change isometry.
-/

namespace TauCeti

open scoped BigOperators

variable {ι : Type*} {𝕜 : Type*} {E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Transport a Hilbert basis along a linear isometric equivalence. -/
protected noncomputable def _root_.HilbertBasis.mapₗᵢ
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    _root_.HilbertBasis ι 𝕜 F :=
  _root_.HilbertBasis.ofRepr (e.symm.trans b.repr)

/-- The coordinate representation of `b.mapₗᵢ e` is `b.repr` after applying `e.symm`. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_repr
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e).repr = e.symm.trans b.repr :=
  rfl

/-- The `i`th vector of the transported basis is the image of the `i`th vector. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_apply
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (i : ι) :
    b.mapₗᵢ e i = e (b i) :=
  rfl

/-- Function-level form of `HilbertBasis.mapₗᵢ_apply`. -/
@[simp]
theorem _root_.HilbertBasis.coe_mapₗᵢ
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    ⇑(b.mapₗᵢ e) = e ∘ b :=
  rfl

/-- Transporting a Hilbert basis along a linear isometric equivalence gives an orthonormal
family. -/
theorem _root_.HilbertBasis.mapₗᵢ_orthonormal
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    Orthonormal 𝕜 (e ∘ b) := by
  simpa using (b.mapₗᵢ e).orthonormal

/-- Parseval's identity as a `HasSum` statement for the transported basis vectors. -/
theorem _root_.HilbertBasis.mapₗᵢ_hasSum_inner_mul_inner (b : _root_.HilbertBasis ι 𝕜 E)
    (e : E ≃ₗᵢ[𝕜] F) (x y : F) :
    HasSum (fun i => inner 𝕜 x (e (b i)) * inner 𝕜 (e (b i)) y) (inner 𝕜 x y) := by
  simpa using (b.mapₗᵢ e).hasSum_inner_mul_inner x y

/-- Parseval's identity as a `tsum` statement for the transported basis vectors. -/
theorem _root_.HilbertBasis.mapₗᵢ_tsum_inner_mul_inner (b : _root_.HilbertBasis ι 𝕜 E)
    (e : E ≃ₗᵢ[𝕜] F) (x y : F) :
    ∑' i, inner 𝕜 x (e (b i)) * inner 𝕜 (e (b i)) y = inner 𝕜 x y := by
  simpa using (b.mapₗᵢ e).tsum_inner_mul_inner x y

/-- Transport along the identity isometry leaves a Hilbert basis unchanged. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_refl (b : _root_.HilbertBasis ι 𝕜 E) :
    b.mapₗᵢ (LinearIsometryEquiv.refl 𝕜 E) = b := by
  cases b
  rfl

/-- Transporting along two linear isometric equivalences is the same as transporting along their
composition. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_trans {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (f : F ≃ₗᵢ[𝕜] G) :
    (b.mapₗᵢ e).mapₗᵢ f = b.mapₗᵢ (e.trans f) := by
  cases b
  rfl

end TauCeti
