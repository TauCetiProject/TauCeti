/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
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

Orthogonal line coordinates associated with a unit vector identify the ambient space with
the product of its orthogonal hyperplane and the scalar line. The `L²` product version is
isometric; the ordinary product version is a continuous linear equivalence used for line
sections and product integration.

An isometric inclusion also identifies the operator algebra of its source isometrically with
an orthogonal corner in the target's operator algebra: extend by zero using `e T e†`.
Compression is its inverse on this corner, and extension preserves composition and adjoints.

Along a smooth family of linear isometries of a finite-dimensional real inner product space, the
inverses again depend smoothly on the parameter: expanding in an orthonormal basis `bᵢ`,
`(R p)⁻¹ x = ∑ i, ⟪R p bᵢ, x⟫ bᵢ`. So a smooth path of linear isometries moves the unit sphere by
diffeomorphisms.

## Main definitions

* `TauCeti.orthogonalLineIsometry` and `TauCeti.orthogonalLineEquiv`: orthogonal line coordinates.
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
* `LinearIsometryEquiv.eq_refl_or_eq_neg`: the only real linear isometry equivalences of `ℝ`
  are the identity and negation.
* `ContDiff.linearIsometryEquiv_symm_apply`: the inverses along a smooth family of linear
  isometries of a finite-dimensional space form a smooth family.
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

/-- The only real linear isometry equivalences of the real line are the identity and negation. -/
theorem eq_refl_or_eq_neg (A : ℝ ≃ₗᵢ[ℝ] ℝ) : A = .refl ℝ ℝ ∨ A = .neg ℝ := by
  have hsq : (A 1) ^ 2 = 1 := by
    simpa only [RCLike.inner_apply, conj_trivial, mul_one, one_mul, pow_two]
      using A.inner_map_map (1 : ℝ) 1
  -- By linearity, `A` is multiplication by `A 1`.
  have hA (x : ℝ) : A x = x * A 1 := by simpa using _root_.map_smul A x (1 : ℝ)
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact .inl (ext fun x ↦ by simp [hA x, h])
  · exact .inr (ext fun x ↦ by simp [hA x, h])

end LinearIsometryEquiv

namespace TauCeti

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The isometric form of orthogonal line coordinates, using the `L²` norm on the product.
Constructed from Mathlib's `Submodule.orthogonalDecomposition` and
`LinearIsometryEquiv.toSpanUnitSingleton`. -/
def orthogonalLineIsometry (e : E) (he : ‖e‖ = 1) :
    WithLp 2 ((ℝ ∙ e)ᗮ × ℝ) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2 (.refl ℝ _) (.toSpanUnitSingleton e he)).trans
    ((LinearIsometryEquiv.withLpProdComm 2 ℝ _ _).trans
      (ℝ ∙ e).orthogonalDecomposition.symm)

@[simp]
theorem orthogonalLineIsometry_apply (e : E) (he : ‖e‖ = 1)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    orthogonalLineIsometry e he (WithLp.toLp 2 (y, t)) = (y : E) + t • e := by
  simp [orthogonalLineIsometry, add_comm]

/-- Orthogonal line coordinates: the transverse coordinate lies in `eᗮ` and the longitudinal
coordinate is real. This version uses the ordinary product norm;
`orthogonalLineIsometry` supplies the isometric version on the `L²` product. -/
def orthogonalLineEquiv (e : E) (he : ‖e‖ = 1) : ((ℝ ∙ e)ᗮ × ℝ) ≃L[ℝ] E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ ∙ e)ᗮ ℝ).symm.trans
    (orthogonalLineIsometry e he).toContinuousLinearEquiv

/-- The ordinary product coordinates are the isometric coordinates after changing the
product norm to the `L²` norm. -/
theorem orthogonalLineEquiv_def (e : E) (he : ‖e‖ = 1) :
    orthogonalLineEquiv e he =
      (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ ∙ e)ᗮ ℝ).symm.trans
        (orthogonalLineIsometry e he).toContinuousLinearEquiv := (rfl)

@[simp]
theorem orthogonalLineEquiv_apply (e : E) (he : ‖e‖ = 1)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    orthogonalLineEquiv e he (y, t) = (y : E) + t • e :=
  orthogonalLineIsometry_apply e he y t

/-- The longitudinal inverse coordinate is the inner product with the unit direction. -/
@[simp]
theorem orthogonalLineEquiv_symm_snd (e : E) (he : ‖e‖ = 1) (x : E) :
    ((orthogonalLineEquiv e he).symm x).2 = ⟪e, x⟫ := by
  obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
  have hy : ⟪e, (y : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
  rw [ContinuousLinearEquiv.symm_apply_apply, orthogonalLineEquiv_apply]
  simp [inner_add_right, inner_smul_right, hy, inner_self_eq_norm_sq_to_K, he]

/-- The transverse inverse coordinate is obtained by subtracting the longitudinal component. -/
@[simp]
theorem orthogonalLineEquiv_symm_fst (e : E) (he : ‖e‖ = 1) (x : E) :
    (((orthogonalLineEquiv e he).symm x).1 : E) = x - ⟪e, x⟫ • e := by
  have h := (orthogonalLineEquiv e he).apply_symm_apply x
  rw [← Prod.eta (p := (orthogonalLineEquiv e he).symm x),
    orthogonalLineEquiv_apply, orthogonalLineEquiv_symm_snd] at h
  exact eq_sub_iff_add_eq.mpr h

/-- Pythagoras in orthogonal line coordinates. -/
theorem norm_add_smul_sq (e : E) (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    ‖(y : E) + t • e‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  rw [← orthogonalLineIsometry_apply e he y t,
    (orthogonalLineIsometry e he).norm_map, WithLp.prod_norm_sq_eq_of_L2]
  simp

/-- A point `y + t • e` in orthogonal line coordinates lies at height `t` along `e`. -/
theorem inner_add_smul (e : E) (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    ⟪e, (y : E) + t • e⟫ = t := by
  rw [← orthogonalLineEquiv_apply e he, ← orthogonalLineEquiv_symm_snd e he,
    ContinuousLinearEquiv.symm_apply_apply]

end TauCeti

/-! ### Operator corners -/

namespace LinearIsometry

open ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Extend an operator along an isometric inclusion by zero on the orthogonal complement.
This is an isometric embedding of operator spaces, preserving composition and adjoints.
Its image is the corner supported on the range of the inclusion. -/
def cornerEmbedding (e : E →ₗᵢ[𝕜] F) : (E →L[𝕜] E) →ₗᵢ[𝕜] (F →L[𝕜] F) where
  toLinearMap := ((compL 𝕜 F E F e.toContinuousLinearMap).comp
    ((compL 𝕜 F E E).flip e.toContinuousLinearMap.adjoint)).toLinearMap
  norm_map' T := by
    simp only [coe_coe, comp_apply, flip_apply, compL_apply]
    rw [e.norm_toContinuousLinearMap_comp,
      ← adjoint.norm_map (T ∘L e.toContinuousLinearMap.adjoint), adjoint_comp,
      adjoint_adjoint, e.norm_toContinuousLinearMap_comp, adjoint.norm_map]

/-- The operator extended by zero is `e T e†`. -/
theorem cornerEmbedding_apply (e : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    e.cornerEmbedding T = e.toContinuousLinearMap ∘L T ∘L e.toContinuousLinearMap.adjoint :=
  (rfl)

/-- Evaluation of the extension by zero. -/
@[simp]
theorem cornerEmbedding_apply_apply (e : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) (x : F) :
    e.cornerEmbedding T x = e (T (e.toContinuousLinearMap.adjoint x)) :=
  (rfl)

/-- Compression to the included space is a left inverse of extension by zero. -/
@[simp]
theorem adjoint_comp_cornerEmbedding_comp (e : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    e.toContinuousLinearMap.adjoint ∘L e.cornerEmbedding T ∘L e.toContinuousLinearMap = T := by
  calc
    _ = (e.toContinuousLinearMap.adjoint ∘L e.toContinuousLinearMap) ∘L T ∘L
        (e.toContinuousLinearMap.adjoint ∘L e.toContinuousLinearMap) := by
      simp only [cornerEmbedding_apply, ContinuousLinearMap.comp_assoc]
    _ = T := by simp [e.adjoint_comp_self, ContinuousLinearMap.one_def]

/-- Extension by zero commutes with adjoints. -/
@[simp]
theorem adjoint_cornerEmbedding (e : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    (e.cornerEmbedding T).adjoint = e.cornerEmbedding T.adjoint := by
  simp [cornerEmbedding_apply, adjoint_comp, ContinuousLinearMap.comp_assoc]

/-- Extension by zero preserves composition. -/
@[simp]
theorem cornerEmbedding_comp (e : E →ₗᵢ[𝕜] F) (T S : E →L[𝕜] E) :
    e.cornerEmbedding (T ∘L S) = e.cornerEmbedding T ∘L e.cornerEmbedding S := by
  ext x
  have he (y : E) : e.toContinuousLinearMap.adjoint (e y) = y :=
    DFunLike.congr_fun e.adjoint_comp_self y
  simp [cornerEmbedding_apply_apply, he]

/-- The identity extends to the orthogonal projection onto the included space, not in general
 to the ambient identity. -/
@[simp]
theorem cornerEmbedding_id (e : E →ₗᵢ[𝕜] F) :
    e.cornerEmbedding (ContinuousLinearMap.id 𝕜 E) =
      e.toContinuousLinearMap ∘L e.toContinuousLinearMap.adjoint := by
  simp [cornerEmbedding_apply]

/-- Compressing and extending an ambient operator gives its two-sided corner compression. -/
theorem cornerEmbedding_adjoint_comp (e : E →ₗᵢ[𝕜] F) (T : F →L[𝕜] F) :
    e.cornerEmbedding (e.toContinuousLinearMap.adjoint ∘L T ∘L e.toContinuousLinearMap) =
      (e.toContinuousLinearMap ∘L e.toContinuousLinearMap.adjoint) ∘L T ∘L
        (e.toContinuousLinearMap ∘L e.toContinuousLinearMap.adjoint) := by
  simp only [cornerEmbedding_apply, ContinuousLinearMap.comp_assoc]

/-- An operator is an extension by zero exactly when it is supported on the inclusion's
orthogonal corner. This characterizes the image without choosing a preimage. -/
theorem mem_range_cornerEmbedding_iff (e : E →ₗᵢ[𝕜] F) (T : F →L[𝕜] F) :
    T ∈ Set.range e.cornerEmbedding ↔
      (e.toContinuousLinearMap ∘L e.toContinuousLinearMap.adjoint) ∘L T ∘L
        (e.toContinuousLinearMap ∘L e.toContinuousLinearMap.adjoint) = T := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [← cornerEmbedding_adjoint_comp, adjoint_comp_cornerEmbedding_comp]
  · intro h
    exact ⟨e.toContinuousLinearMap.adjoint ∘L T ∘L e.toContinuousLinearMap,
      (e.cornerEmbedding_adjoint_comp T).trans h⟩

end LinearIsometry

/-! ### Smooth paths of linear isometries -/

open scoped InnerProductSpace in
/-- Along a smooth family of linear isometries of a finite-dimensional real inner product space,
the inverses also depend smoothly on the parameter: expanding in an orthonormal basis `bᵢ`,
`(R p)⁻¹ x = ∑ i, ⟪R p bᵢ, x⟫ bᵢ`. -/
theorem ContDiff.linearIsometryEquiv_symm_apply {F G : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : WithTop ℕ∞} {R : G → F ≃ₗᵢ[ℝ] F} (hR : ContDiff ℝ m fun p : G × F => R p.1 p.2) :
    ContDiff ℝ m fun p : G × F => (R p.1).symm p.2 := by
  let b := stdOrthonormalBasis ℝ F
  have hexp : (fun p : G × F => (R p.1).symm p.2) =
      fun p => ∑ i, ⟪R p.1 (b i), p.2⟫_ℝ • b i := by
    funext p
    conv_lhs => rw [← b.sum_repr' ((R p.1).symm p.2)]
    simp only [LinearIsometryEquiv.inner_map_eq_flip]
  rw [hexp]
  exact ContDiff.sum fun i _ =>
    ((hR.comp (contDiff_fst.prodMk contDiff_const)).inner ℝ contDiff_snd).smul contDiff_const
