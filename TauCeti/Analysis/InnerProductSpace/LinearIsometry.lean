/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Linear isometries, orthogonal complements, and product decompositions

A linear isometry `f : E →ₗᵢ[ℝ] F` into a finite-dimensional inner product space identifies `F`
with the product of `E` and the orthogonal complement of the range of `f`, by
`(u, w) ↦ f u + w`. Read through this identification, `f` itself is the inclusion `u ↦ (u, 0)` of
the first factor. This is the normal form in which Mathlib's `Manifold.IsImmersionAt` asks for a
map to be written in charts, so this decomposition is what exhibits a linear isometry, and the maps
of spheres and balls it induces, as immersions.

A linear isometry also carries the orthogonal complement of a vector into the orthogonal
complement of its image; this is how it transports the stereographic charts of unit spheres. For
Euclidean spaces, a linear isometry matching a pair of standard basis vectors matches the
corresponding coordinates; this is how it transports the half-space charts of closed balls.

An isometry between the orthogonal complements of two unit vectors extends uniquely to
an ambient isometry sending one vector to the other. This extension works over both real
and complex inner product spaces, without completeness or dimension assumptions.

## Main definitions

* `LinearIsometry.prodOrthogonalRangeEquiv`: the continuous linear equivalence
  `E × (range f)ᗮ ≃L[ℝ] F` given by `(u, w) ↦ f u + w`.
* `LinearIsometry.orthogonalComplementSingletonMap`: the restriction of a linear isometry to a map
  `(ℝ ∙ v)ᗮ →ₗᵢ[ℝ] (ℝ ∙ w)ᗮ`, where `w` is the image of `v`.

* `LinearIsometryEquiv.extendOrthogonalComplement`: extend an isometry of orthogonal
  complements by its prescribed action on the radial line.

## Main results

* `LinearIsometry.apply_eq_of_map_single`: a linear isometry of Euclidean spaces sending the `i`-th
  standard basis vector to the `j`-th one reads the `i`-th coordinate off as the `j`-th coordinate
  of the image.
* `LinearMap.eq_of_apply_eq_of_eqOn_orthogonal`: linear maps agreeing on a vector and
  its orthogonal complement are equal, without a unit-norm assumption.
* `LinearIsometryEquiv.eq_extendOrthogonalComplement`: a linear isometry equals the
  extension if it agrees on the unit vector and its orthogonal complement.
-/

public section

noncomputable section

namespace LinearIsometry

open Module

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- A linear isometry `f` maps the orthogonal complement of `v` into the orthogonal complement of
`f v`. -/
theorem map_mem_orthogonal_singleton (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w) {y : E}
    (hy : y ∈ (ℝ ∙ v)ᗮ) : f y ∈ (ℝ ∙ w)ᗮ := by
  subst hw
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy ⊢
  rwa [f.inner_map_map]

/-- The restriction of a linear isometry `f` to a linear isometry from the orthogonal complement
of `v` to the orthogonal complement of its image `w`. -/
def orthogonalComplementSingletonMap (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w) :
    (ℝ ∙ v)ᗮ →ₗᵢ[ℝ] (ℝ ∙ w)ᗮ where
  toLinearMap := (f.toLinearMap.domRestrict (ℝ ∙ v)ᗮ).codRestrict (ℝ ∙ w)ᗮ fun y ↦
    f.map_mem_orthogonal_singleton hw y.2
  norm_map' y := f.norm_map y

@[simp]
theorem coe_orthogonalComplementSingletonMap_apply (f : E →ₗᵢ[ℝ] F) {v : E} {w : F} (hw : f v = w)
    (y : (ℝ ∙ v)ᗮ) : (f.orthogonalComplementSingletonMap hw y : F) = f y :=
  (rfl)

variable [FiniteDimensional ℝ F]

/-- A linear isometry `f : E →ₗᵢ[ℝ] F` into a finite-dimensional space identifies the product of
`E` with the orthogonal complement of the range of `f` with `F`, by `(u, w) ↦ f u + w`. -/
def prodOrthogonalRangeEquiv (f : E →ₗᵢ[ℝ] F) :
    (E × (LinearMap.range f.toLinearMap)ᗮ) ≃L[ℝ] F :=
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_injective f.toLinearMap f.injective
  ((f.equivRange.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ _)).trans
    (Submodule.prodEquivOfIsCompl _ _
      (Submodule.isCompl_orthogonal _))).toContinuousLinearEquiv

@[simp]
theorem prodOrthogonalRangeEquiv_apply (f : E →ₗᵢ[ℝ] F) (u : E)
    (w : (LinearMap.range f.toLinearMap)ᗮ) : f.prodOrthogonalRangeEquiv (u, w) = f u + w := by
  rfl

/-- Through `LinearIsometry.prodOrthogonalRangeEquiv`, the linear isometry `f` is the inclusion of
the first factor. -/
theorem prodOrthogonalRangeEquiv_apply_zero (f : E →ₗᵢ[ℝ] F) (u : E) :
    f.prodOrthogonalRangeEquiv (u, 0) = f u := by
  simp

section EuclideanSpace

variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A linear isometry of Euclidean spaces sending the `i`-th standard basis vector to the `j`-th
one reads the `i`-th coordinate of its argument off as the `j`-th coordinate of the image. -/
theorem apply_eq_of_map_single {L : EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] EuclideanSpace 𝕜 κ} {i : ι} {j : κ}
    (hL : L (EuclideanSpace.single i 1) = EuclideanSpace.single j 1) (u : EuclideanSpace 𝕜 ι) :
    L u j = u i := by
  have h := L.inner_map_map (EuclideanSpace.single i 1) u
  rw [hL] at h
  simpa [EuclideanSpace.inner_single_left] using h

end EuclideanSpace

end LinearIsometry

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] {x : E}

/-- Linear maps are determined by their value on a vector and their restriction to its
orthogonal complement. The vector need not be a unit vector or even nonzero. -/
theorem eq_of_apply_eq_of_eqOn_orthogonal {f g : E →ₗ[𝕜] F} (hx : f x = g x)
    (h : ∀ v : (𝕜 ∙ x)ᗮ, f v = g v) : f = g := by
  apply ext_on_codisjoint (𝕜 ∙ x).isCompl_orthogonal.codisjoint
  · exact eqOn_span' (by simpa only [Set.eqOn_singleton] using hx)
  · intro v hv
    exact h ⟨v, hv⟩

end LinearMap

namespace LinearIsometryEquiv

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {x : E} {y : F}

/-- Extend an isometry between the orthogonal complements of two unit vectors by sending
one unit vector to the other. The extension uses Mathlib's
`Submodule.orthogonalDecomposition` and `LinearIsometryEquiv.toSpanUnitSingleton`. -/
noncomputable def extendOrthogonalComplement
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    E ≃ₗᵢ[𝕜] F :=
  (𝕜 ∙ x).orthogonalDecomposition.trans
    (((toSpanUnitSingleton x hx).symm.trans (toSpanUnitSingleton y hy)).withLpProdCongr 2 e |>.trans
      (𝕜 ∙ y).orthogonalDecomposition.symm)

/-- On the orthogonal direct sum, the extension acts on the radial and transverse
components separately. -/
@[simp]
theorem extendOrthogonalComplement_apply_smul_add
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (r : 𝕜) (v : (𝕜 ∙ x)ᗮ) :
    e.extendOrthogonalComplement hx hy (r • x + v) = r • y + e v := by
  have h := (𝕜 ∙ x).orthogonalDecomposition.apply_symm_apply
    (WithLp.toLp 2 (toSpanUnitSingleton x hx r, v))
  conv_lhs at h =>
    simp only [Submodule.orthogonalDecomposition_symm_apply, WithLp.toLp_fst,
      WithLp.toLp_snd, toSpanUnitSingleton_apply]
  simp only [extendOrthogonalComplement, trans_apply, h, withLpProdCongr_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, symm_apply_apply]
  simp only [Submodule.orthogonalDecomposition_symm_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, toSpanUnitSingleton_apply]

/-- The extension sends the distinguished unit vector to the distinguished target vector. -/
@[simp]
theorem extendOrthogonalComplement_apply_self
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    e.extendOrthogonalComplement hx hy x = y := by
  simpa using e.extendOrthogonalComplement_apply_smul_add hx hy 1 0

/-- The extension agrees with the original isometry on the orthogonal complement. -/
@[simp]
theorem extendOrthogonalComplement_apply_coe
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (v : (𝕜 ∙ x)ᗮ) : e.extendOrthogonalComplement hx hy v = e v := by
  simpa using e.extendOrthogonalComplement_apply_smul_add hx hy 0 v

/-- An ambient linear isometry is uniquely determined by its value on a unit vector and
its restriction to the orthogonal complement. -/
theorem eq_extendOrthogonalComplement
    (e : (𝕜 ∙ x)ᗮ ≃ₗᵢ[𝕜] (𝕜 ∙ y)ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (f : E →ₗᵢ[𝕜] F) (hfx : f x = y)
    (hf : ∀ v : (𝕜 ∙ x)ᗮ, f v = e v) :
    f = (e.extendOrthogonalComplement hx hy).toLinearIsometry := by
  apply LinearIsometry.toLinearMap_injective
  apply LinearMap.eq_of_apply_eq_of_eqOn_orthogonal (x := x)
  · simpa only [LinearIsometry.coe_toLinearMap, coe_toLinearIsometry,
      extendOrthogonalComplement_apply_self] using hfx
  · intro v
    simpa only [LinearIsometry.coe_toLinearMap, coe_toLinearIsometry,
      extendOrthogonalComplement_apply_coe] using hf v

end LinearIsometryEquiv
