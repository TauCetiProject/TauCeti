module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Transporting Hilbert bases by linear isometric equivalences

This file adds the Hilbert-basis analogue of `Basis.map`: a Hilbert basis of a Hilbert space
can be transported across a linear isometric equivalence.  It also follows Mathlib's
`OrthonormalBasis.map` API for transporting orthonormal bases.  The construction is the Part 0
`HilbertBasis.mapₗᵢ` primitive from the `OrthogonalL2Bases` roadmap, used later to move weighted
orthogonal-polynomial bases across the weight-change isometry.
-/

public section

namespace TauCeti

open scoped BigOperators

variable {ι : Type*} {𝕜 : Type*} {E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Transport a Hilbert basis along a linear isometric equivalence. -/
protected noncomputable def _root_.HilbertBasis.mapₗᵢ
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    _root_.HilbertBasis ι 𝕜 F :=
  _root_.HilbertBasis.ofRepr (e.symm.trans b.repr)

/-- The coordinate representation of `b.mapₗᵢ e` is `b.repr` after applying `e.symm`. -/
@[simp]
theorem _root_.HilbertBasis.repr_mapₗᵢ
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e).repr = e.symm.trans b.repr :=
  congrArg _root_.HilbertBasis.repr (_root_.HilbertBasis.mapₗᵢ.eq_1 b e)

/-- Coordinates in the transported Hilbert basis are the original coordinates after applying
the inverse isometry. -/
@[simp]
theorem _root_.HilbertBasis.repr_mapₗᵢ_apply
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (x : F) :
    (b.mapₗᵢ e).repr x = b.repr (e.symm x) := by
  rw [_root_.HilbertBasis.repr_mapₗᵢ]
  rfl

/-- The `i`th coordinate in the transported Hilbert basis is the inner product against the
corresponding original basis vector after applying the inverse isometry. -/
@[simp]
theorem _root_.HilbertBasis.repr_mapₗᵢ_apply_apply
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (x : F) (i : ι) :
    ((b.mapₗᵢ e).repr x) i = ⟪b i, e.symm x⟫ := by
  rw [_root_.HilbertBasis.repr_mapₗᵢ_apply, b.repr_apply_apply]

/-- The `i`th vector of the transported basis is the image of the `i`th vector. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_apply
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (i : ι) :
    b.mapₗᵢ e i = e (b i) :=
  by
    rw [_root_.HilbertBasis.mapₗᵢ.eq_1]
    rfl

/-- Function-level form of `HilbertBasis.mapₗᵢ_apply`. -/
@[simp]
theorem _root_.HilbertBasis.coe_mapₗᵢ
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    ⇑(b.mapₗᵢ e) = e ∘ b :=
  funext (b.mapₗᵢ_apply e)

/-- The image family of a Hilbert basis under a linear isometric equivalence is orthonormal. -/
theorem _root_.HilbertBasis.orthonormal_mapₗᵢ
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    Orthonormal 𝕜 (e ∘ b) := by
  rw [← _root_.HilbertBasis.coe_mapₗᵢ b e]
  exact (b.mapₗᵢ e).orthonormal

/-- Parseval for a transported Hilbert basis, stated using the original basis vectors and the
transporting isometry. -/
protected theorem _root_.HilbertBasis.hasSum_inner_mapₗᵢ_mul_inner
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (x y : F) :
    HasSum (fun i => ⟪x, e (b i)⟫ * ⟪e (b i), y⟫) ⟪x, y⟫ := by
  simpa using (b.mapₗᵢ e).hasSum_inner_mul_inner x y

/-- Summability of the Parseval series for a transported Hilbert basis. -/
protected theorem _root_.HilbertBasis.summable_inner_mapₗᵢ_mul_inner
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (x y : F) :
    Summable (fun i => ⟪x, e (b i)⟫ * ⟪e (b i), y⟫) :=
  (b.hasSum_inner_mapₗᵢ_mul_inner e x y).summable

/-- The `tsum` form of Parseval for a transported Hilbert basis. -/
protected theorem _root_.HilbertBasis.tsum_inner_mapₗᵢ_mul_inner
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (x y : F) :
    ∑' i, ⟪x, e (b i)⟫ * ⟪e (b i), y⟫ = ⟪x, y⟫ :=
  (b.hasSum_inner_mapₗᵢ_mul_inner e x y).tsum_eq

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
