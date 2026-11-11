/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic
public import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# Primitive embeddings of integral lattices

A primitive embedding is an injective rational linear map preserving the bilinear forms,
carrying the source lattice into the target, with saturated image in the target lattice.
The saturation condition is equivalent to a torsion-free integral cokernel, and hence to
being a direct summand of the target carrier. The complement in this criterion is an
integral-module complement, not necessarily an orthogonal complement.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1, 5°.
-/

public section

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} {W : Type v} {X : Type w}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  [AddCommGroup X] [Module ℚ X]
  {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice X}

/-- An injective form-preserving rational linear map is a primitive embedding when it maps
one carrier into the other and its image is saturated in the target carrier. -/
structure IsPrimitiveEmbedding (L : IntegralLattice V) (M : IntegralLattice W)
    (f : V →ₗ[ℚ] W) : Prop where
  /-- Injectivity on the rational ambient spaces. -/
  injective : Function.Injective f
  /-- Preservation of the rational bilinear forms. -/
  map_form : ∀ x y, M.form (f x) (f y) = L.form x y
  /-- The integral image lies in the target carrier. -/
  map_carrier : L.carrier.map (f.restrictScalars ℤ) ≤ M.carrier
  /-- The integral image is saturated in the target carrier. -/
  saturated : ∀ y ∈ M.carrier, ∀ k : ℤ, k ≠ 0 →
    k • y ∈ L.carrier.map (f.restrictScalars ℤ) →
      y ∈ L.carrier.map (f.restrictScalars ℤ)

/-- Every integral-lattice isometry is a primitive embedding. -/
@[simp]
theorem Isometry.isPrimitiveEmbedding (e : Isometry L M) :
    IsPrimitiveEmbedding L M (e : V ≃ₗ[ℚ] W).toLinearMap where
  injective := e.injective
  map_form := e.map_app
  map_carrier := e.map_carrier.le
  saturated y hy _ _ _ := by
    rwa [← LinearEquiv.restrictScalars_toLinearMap, e.map_carrier]

namespace IsPrimitiveEmbedding

variable {f : V →ₗ[ℚ] W} {g : W →ₗ[ℚ] X}

/-- The identity is a primitive embedding, including for degenerate lattices. -/
@[simp]
theorem id (L : IntegralLattice V) : IsPrimitiveEmbedding L L LinearMap.id := by
  convert (Isometry.refl L).isPrimitiveEmbedding using 1
  ext x
  simp

/-- Composites of primitive embeddings are primitive. -/
theorem comp (hg : IsPrimitiveEmbedding M N g) (hf : IsPrimitiveEmbedding L M f) :
    IsPrimitiveEmbedding L N (g.comp f) where
  injective := hg.injective.comp hf.injective
  map_form x y := (hg.map_form _ _).trans (hf.map_form x y)
  map_carrier := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg.map_carrier ⟨f x, hf.map_carrier ⟨x, hx, rfl⟩, rfl⟩
  saturated y hy k hk hky := by
    obtain ⟨x, hx, hxy⟩ := hky
    have hgm : k • y ∈ M.carrier.map (g.restrictScalars ℤ) :=
      ⟨f x, hf.map_carrier ⟨x, hx, rfl⟩, hxy⟩
    obtain ⟨z, hz, rfl⟩ := hg.saturated y hy k hk hgm
    have hfx : f x = k • z := hg.injective (by simpa using hxy)
    obtain ⟨a, ha, haz⟩ := hf.saturated z hz k hk ⟨x, hx, hfx⟩
    exact ⟨a, ha, by simp [LinearMap.comp_apply, haz]⟩

/-- A primitive embedding has torsion-free integral cokernel. The submodule in the quotient
is its image viewed inside the target carrier. -/
theorem isTorsionFree_quotient (hf : IsPrimitiveEmbedding L M f) :
    Module.IsTorsionFree ℤ
      (M ⧸ (L.carrier.map (f.restrictScalars ℤ)).comap M.carrier.subtype) := by
  apply Submodule.isTorsionFree_quotient_of_smul_mem
  intro k y hk hy
  exact hf.saturated y y.property k hk hy

end IsPrimitiveEmbedding

/-- Postcomposition with a lattice isometry preserves and reflects primitivity. -/
@[simp]
theorem Isometry.isPrimitiveEmbedding_comp_iff (e : Isometry M N) (f : V →ₗ[ℚ] W) :
    IsPrimitiveEmbedding L N ((e : W ≃ₗ[ℚ] X).toLinearMap.comp f) ↔
      IsPrimitiveEmbedding L M f := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.isPrimitiveEmbedding.comp h⟩
  convert e.symm.isPrimitiveEmbedding.comp h using 1
  ext x
  simp

/-- Precomposition with a lattice isometry preserves and reflects primitivity. -/
@[simp]
theorem Isometry.isPrimitiveEmbedding_comp_right_iff (e : Isometry L M) (g : W →ₗ[ℚ] X) :
    IsPrimitiveEmbedding L N (g.comp (e : V ≃ₗ[ℚ] W).toLinearMap) ↔
      IsPrimitiveEmbedding M N g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp e.isPrimitiveEmbedding⟩
  convert h.comp e.symm.isPrimitiveEmbedding using 1
  ext x
  simp

/-- For an injective form-preserving map carrying one lattice into another, primitivity is
exactly torsion-freeness of its integral cokernel. -/
theorem isPrimitiveEmbedding_iff_isTorsionFree_quotient (f : V →ₗ[ℚ] W)
    (hi : Function.Injective f) (hB : ∀ x y, M.form (f x) (f y) = L.form x y)
    (hL : L.carrier.map (f.restrictScalars ℤ) ≤ M.carrier) :
    IsPrimitiveEmbedding L M f ↔ Module.IsTorsionFree ℤ
      (M ⧸ (L.carrier.map (f.restrictScalars ℤ)).comap M.carrier.subtype) := by
  refine ⟨fun hf ↦ hf.isTorsionFree_quotient, fun h ↦ ⟨hi, hB, hL, ?_⟩⟩
  have := h
  intro y hy k hk hky
  exact Submodule.mem_of_smul_mem_of_isTorsionFree_quotient
    ((L.carrier.map (f.restrictScalars ℤ)).comap M.carrier.subtype) (z := ⟨y, hy⟩) hk hky

/-- The integral image of a form-preserving injection is saturated exactly when it has an
integral-module complement. This does not assert an orthogonal splitting. -/
theorem isPrimitiveEmbedding_iff_exists_isCompl (f : V →ₗ[ℚ] W)
    (hi : Function.Injective f) (hB : ∀ x y, M.form (f x) (f y) = L.form x y)
    (hL : L.carrier.map (f.restrictScalars ℤ) ≤ M.carrier) :
    IsPrimitiveEmbedding L M f ↔ ∃ T : Submodule ℤ M,
      IsCompl ((L.carrier.map (f.restrictScalars ℤ)).comap M.carrier.subtype) T := by
  rw [isPrimitiveEmbedding_iff_isTorsionFree_quotient f hi hB hL,
    Submodule.exists_isCompl_iff_isTorsionFree_quotient]

end TauCeti.IntegralLattice
