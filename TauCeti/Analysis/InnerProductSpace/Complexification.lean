/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Module.Complexification
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Hilbert-space complexification of a real inner product space

For a real inner product space `X`, the complexification `X_ℂ = X ⊕ i X`
(`TauCeti.Complexification X`) carries the complex inner product

`⟪x + i y, u + i v⟫ = (⟪x, u⟫ + ⟪y, v⟫) + i (⟪x, v⟫ - ⟪y, u⟫)`,

whose norm is the `L²` norm `‖x + i y‖ = √(‖x‖² + ‖y‖²)`. This is not the Taylor norm that
`TauCeti.Analysis.Normed.Module.Complexification` puts on `Complexification X`: the two norms are
equivalent but differ in general (for orthogonal unit vectors `x` and `y`, the Taylor norm of
`x + i y` is `1` and its `L²` norm is `√2`). The Hilbert structure therefore lives on the type
synonym `WithLp 2 (Complexification X)`, just as Mathlib's `L²` product of two inner product
spaces lives on `WithLp 2 (E × F)`. As a real normed space, `X_ℂ` is isometric to the `L²`
product `WithLp 2 (X × X)`, so it is complete whenever `X` is.

A bounded real operator `T : X →L[ℝ] Y` complexifies to the bounded complex operator
`T_ℂ (x + i y) = T x + i T y`, the `WithLp` lift of `ContinuousLinearMap.complexify`. For the
`L²` norm, complexification is isometric and commutes with composition and with adjoints. For a
real Hilbert space `X`, it is therefore an isometric `⋆`-algebra embedding of the real
`C⋆`-algebra `X →L[ℝ] X` into the complex `C⋆`-algebra `X_ℂ →L[ℂ] X_ℂ`. This is the standard
device for transferring complex spectral theory, such as the continuous functional calculus of a
self-adjoint operator, to operators on real Hilbert spaces.

## Main declarations

* `WithLp.instComplexificationInnerProductSpace`: the complex inner product space
  `WithLp 2 (Complexification X)`, with `WithLp.complexification_re_inner` and
  `WithLp.complexification_im_inner` computing the inner product from real and imaginary parts.
* `WithLp.complexification_norm_sq_eq`: `‖x + i y‖² = ‖x‖² + ‖y‖²`.
* `WithLp.complexificationEquivProd`: the real-linear isometric equivalence
  `WithLp 2 (Complexification X) ≃ₗᵢ[ℝ] WithLp 2 (X × X)`,
  `WithLp.complexificationOfRealₗᵢ`: the real-linear isometric inclusion
  `X →ₗᵢ[ℝ] WithLp 2 (Complexification X)`, and
  `WithLp.instComplexificationCompleteSpace` as a consequence.
* `WithLp.finrank_complexification`: the complexification of a finite-dimensional space has
  complex dimension the real dimension of `X`.
* `ContinuousLinearMap.complexifyL2`: the complexification of a bounded real operator, with
  `ContinuousLinearMap.eq_complexifyL2_iff` (it is the unique complex-linear extension),
  `ContinuousLinearMap.norm_complexifyL2`, `ContinuousLinearMap.complexifyL2_comp` and
  `ContinuousLinearMap.adjoint_complexifyL2`.
* `ContinuousLinearMap.complexifyL2ₗᵢ`: complexification as a real-linear isometry of operator
  spaces.
* `ContinuousLinearMap.complexifyL2StarAlgHom`: complexification of the bounded operators on a
  real Hilbert space, as a `⋆`-algebra homomorphism over `ℝ`.
* `ContinuousLinearMap.isClosedEmbedding_complexifyL2StarAlgHom`: complexification of bounded
  operators is a closed embedding.
* `ContinuousLinearMap.isSelfAdjoint_complexifyL2_iff`: complexification preserves and reflects
  self-adjointness.

Orthogonal complementation, orthogonal projections and the projection gap also
commute with Hilbert complexification, without ambient completeness.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33, for the norms a
  complexification can carry.

## Acknowledgements

Copyright (c) 2026 Kitware, Inc. All rights reserved. The adapted projection
transport below retains its original Apache-2.0 licence.

The Hilbert-space complexification, the complexification of bounded operators and its
compatibility with adjoints also appear in `ForTauCeti/Analysis/InnerProductSpace/Complexification/`
of the [AIQ DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0), on the carrier `WithLp 2 (E × E)`. This file builds the same
structure on top of Tau Ceti's algebraic `Complexification`. The orthogonal
projection transport is adapted from DKPS
`DavisKahan/SpectralTheory/Complexification/Subspace.lean`
(Jon Crall and Claude Opus 5; Kitware 2026, Apache-2.0).
-/

public section

noncomputable section

open TauCeti
open scoped InnerProductSpace

namespace WithLp

section Norm

variable {X : Type*} [NormedAddCommGroup X]

/-- The `L²` norm `‖x + i y‖ = √(‖x‖² + ‖y‖²)` on the complexification, induced from the `L²`
product `WithLp 2 (X × X)` along the coordinates `z ↦ (re z, im z)`. -/
instance instComplexificationNormedAddCommGroup :
    NormedAddCommGroup (WithLp 2 (Complexification X)) :=
  NormedAddCommGroup.induced _ _
    ({ toFun z := toLp 2 (z.ofLp.re, z.ofLp.im)
       map_zero' := (rfl)
       map_add' _ _ := (rfl) } : WithLp 2 (Complexification X) →+ WithLp 2 (X × X))
    fun _ _ h ↦ ofLp_injective 2 (Complexification.ext (congrArg (fun p ↦ p.ofLp.1) h)
      (congrArg (fun p ↦ p.ofLp.2) h))

/-- The `L²` norm of `x + i y` is the norm of `(x, y)` in the `L²` product. -/
theorem complexification_norm_eq (z : WithLp 2 (Complexification X)) :
    ‖z‖ = ‖toLp 2 (z.ofLp.re, z.ofLp.im)‖ := (rfl)

/-- The squared `L²` norm of `x + i y` is `‖x‖² + ‖y‖²`. -/
theorem complexification_norm_sq_eq (z : WithLp 2 (Complexification X)) :
    ‖z‖ ^ 2 = ‖z.ofLp.re‖ ^ 2 + ‖z.ofLp.im‖ ^ 2 := by
  simp [complexification_norm_eq, prod_norm_sq_eq_of_L2]

/-- The real embedding `x ↦ x + i 0` is isometric for the `L²` norm. -/
@[simp]
theorem complexification_norm_toLp_ofReal (x : X) :
    ‖toLp 2 (Complexification.ofReal x)‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), complexification_norm_sq_eq]
  simp

variable [NormedSpace ℝ X]

variable (X) in
/-- As a real normed space, the `L²` complexification of `X` is the `L²` product `X × X`, via
`x + i y ↦ (x, y)`. Real scalars act on the complexification by restricting the complex ones. -/
def complexificationEquivProd : WithLp 2 (Complexification X) ≃ₗᵢ[ℝ] WithLp 2 (X × X) where
  toFun z := toLp 2 (z.ofLp.re, z.ofLp.im)
  invFun p := toLp 2 ⟨p.ofLp.1, p.ofLp.2⟩
  map_add' _ _ := (rfl)
  map_smul' r z := by simp [← toLp_smul]
  left_inv _ := (rfl)
  right_inv _ := (rfl)
  norm_map' z := (complexification_norm_eq z).symm

@[simp]
theorem complexificationEquivProd_apply (z : WithLp 2 (Complexification X)) :
    complexificationEquivProd X z = toLp 2 (z.ofLp.re, z.ofLp.im) := (rfl)

@[simp]
theorem complexificationEquivProd_symm_apply (p : WithLp 2 (X × X)) :
    (complexificationEquivProd X).symm p = toLp 2 ⟨p.ofLp.1, p.ofLp.2⟩ := (rfl)

/-- The `L²` complexification of a real Banach space is complete. -/
instance instComplexificationCompleteSpace [CompleteSpace X] :
    CompleteSpace (WithLp 2 (Complexification X)) :=
  (complexificationEquivProd X).toIsometryEquiv.completeSpace

variable (X) in
/-- The real-linear isometric inclusion `x ↦ x + i 0` of a real normed space `X` into its `L²`
complexification `WithLp 2 (Complexification X)`. -/
def complexificationOfRealₗᵢ : X →ₗᵢ[ℝ] WithLp 2 (Complexification X) where
  toFun x := toLp 2 (Complexification.ofReal x)
  map_add' x y := by
    apply ofLp_injective 2
    ext <;> simp
  map_smul' r x := by
    apply ofLp_injective 2
    ext <;> simp
  norm_map' := complexification_norm_toLp_ofReal

@[simp]
theorem complexificationOfRealₗᵢ_apply (x : X) :
    complexificationOfRealₗᵢ X x = toLp 2 (Complexification.ofReal x) := (rfl)

/-- The complex dimension of the complexification of `X` is the real dimension of `X`. -/
@[simp]
theorem finrank_complexification [FiniteDimensional ℝ X] :
    Module.finrank ℂ (WithLp 2 (Complexification X)) = Module.finrank ℝ X := by
  have h := Module.finrank_mul_finrank ℝ ℂ (WithLp 2 (Complexification X))
  rw [(complexificationEquivProd X).toLinearEquiv.finrank_eq,
    (WithLp.linearEquiv 2 ℝ (X × X)).finrank_eq, Module.finrank_prod,
    Complex.finrank_real_complex] at h
  omega

end Norm

section InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Complex scaling multiplies the `L²` norm of the complexification by the modulus. -/
theorem complexification_norm_smul (c : ℂ) (z : WithLp 2 (Complexification X)) :
    ‖c • z‖ = ‖c‖ * ‖z‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, complexification_norm_sq_eq,
    complexification_norm_sq_eq, Complex.sq_norm, Complex.normSq_apply]
  simp only [ofLp_smul, Complexification.smul_re, Complexification.smul_im]
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [norm_smul, real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

/-- The complex inner product `⟪x + i y, u + i v⟫ = (⟪x, u⟫ + ⟪y, v⟫) + i (⟪x, v⟫ - ⟪y, u⟫)` on
the complexification of a real inner product space, whose norm is the `L²` norm. -/
instance instComplexificationInnerProductSpace :
    InnerProductSpace ℂ (WithLp 2 (Complexification X)) where
  norm_smul_le c z := (complexification_norm_smul c z).le
  inner z w := ⟨⟪z.ofLp.re, w.ofLp.re⟫_ℝ + ⟪z.ofLp.im, w.ofLp.im⟫_ℝ,
    ⟪z.ofLp.re, w.ofLp.im⟫_ℝ - ⟪z.ofLp.im, w.ofLp.re⟫_ℝ⟩
  norm_sq_eq_re_inner z := by
    rw [complexification_norm_sq_eq]
    simp
  conj_inner_symm z w := by
    apply Complex.ext <;> simp [real_inner_comm]
  add_left z w u := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring
  smul_left z w c := by
    apply Complex.ext <;>
      simp [inner_add_left, inner_sub_left, real_inner_smul_left, Complex.mul_re,
        Complex.mul_im] <;> ring

/-- The real part of the inner product on the complexification. -/
@[simp]
theorem complexification_re_inner (z w : WithLp 2 (Complexification X)) :
    (⟪z, w⟫_ℂ).re = ⟪z.ofLp.re, w.ofLp.re⟫_ℝ + ⟪z.ofLp.im, w.ofLp.im⟫_ℝ := (rfl)

/-- The imaginary part of the inner product on the complexification. -/
@[simp]
theorem complexification_im_inner (z w : WithLp 2 (Complexification X)) :
    (⟪z, w⟫_ℂ).im = ⟪z.ofLp.re, w.ofLp.im⟫_ℝ - ⟪z.ofLp.im, w.ofLp.re⟫_ℝ := (rfl)

/-- The complex inner product of two real vectors in the `L²` complexification is their real inner
product. -/
@[simp]
theorem complexification_inner_toLp_ofReal (x y : X) :
    ⟪toLp 2 (Complexification.ofReal x), toLp 2 (Complexification.ofReal y)⟫_ℂ =
      (⟪x, y⟫_ℝ : ℂ) := by
  apply Complex.ext <;> simp

/-- `complexificationOfRealₗᵢ` preserves inner products, sending the real inner product to the
complex inner product. -/
theorem inner_complexificationOfRealₗᵢ (x y : X) :
    ⟪complexificationOfRealₗᵢ X x, complexificationOfRealₗᵢ X y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) :=
  complexification_inner_toLp_ofReal x y

end InnerProductSpace

end WithLp

namespace Submodule

open WithLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complex subspace whose real and imaginary parts lie in a given real subspace,
on the Hilbert-norm complexification. -/
def complexifyL2 (S : Submodule ℝ E) : Submodule ℂ (WithLp 2 (Complexification E)) where
  carrier := {z | z.ofLp.re ∈ S ∧ z.ofLp.im ∈ S}
  zero_mem' := ⟨S.zero_mem, S.zero_mem⟩
  add_mem' hx hy := ⟨S.add_mem hx.1 hy.1, S.add_mem hx.2 hy.2⟩
  smul_mem' c _ hz := ⟨S.sub_mem (S.smul_mem c.re hz.1) (S.smul_mem c.im hz.2),
    S.add_mem (S.smul_mem c.im hz.1) (S.smul_mem c.re hz.2)⟩

@[simp]
theorem mem_complexifyL2 (S : Submodule ℝ E) (z : WithLp 2 (Complexification E)) :
    z ∈ S.complexifyL2 ↔ z.ofLp.re ∈ S ∧ z.ofLp.im ∈ S := Iff.rfl

/-- Complexifying a real subspace preserves and reflects density. -/
@[simp]
theorem dense_complexifyL2_iff (S : Submodule ℝ E) :
    Dense (S.complexifyL2 : Set (WithLp 2 (Complexification E))) ↔ Dense (S : Set E) := by
  let e := (complexificationEquivProd E).toHomeomorph.trans
    (prodContinuousLinearEquiv 2 ℝ E E).toHomeomorph
  have he_apply (w : WithLp 2 (Complexification E)) : e w = (w.ofLp.re, w.ofLp.im) := by
    simp [e, complexificationEquivProd_apply]
  have he : e '' (S.complexifyL2 : Set (WithLp 2 (Complexification E))) =
      (S : Set E) ×ˢ (S : Set E) := by
    ext z
    simp only [Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [he_apply] using (mem_complexifyL2 S w).1 hw
    · intro hz
      exact ⟨toLp 2 ⟨z.1, z.2⟩, hz, by simp [he_apply]⟩
  rw [← e.isDenseEmbedding.dense_image, he]
  exact ⟨fun h ↦ (Prod.fst_surjective : Function.Surjective (Prod.fst : E × E → E)).denseRange
    |>.dense_of_mapsTo continuous_fst h (fun _ hx ↦ hx.1), fun h ↦ h.prod h⟩

end Submodule

namespace ContinuousLinearMap

open Complexification WithLp

section NormedSpace

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The complexification `T_ℂ (x + i y) = T x + i T y` of a bounded real operator, as a bounded
complex-linear operator between the `L²` complexifications. -/
def complexifyL2 (T : X →L[ℝ] Y) :
    WithLp 2 (Complexification X) →L[ℂ] WithLp 2 (Complexification Y) :=
  (LinearMap.withLpMap 2 (T.complexify : Complexification X →ₗ[ℂ] Complexification Y)).mkContinuous
    ‖T‖ fun z ↦ by
      have h (x : X) : ‖T x‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖x‖ ^ 2 := by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 2
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow,
        WithLp.complexification_norm_sq_eq, WithLp.complexification_norm_sq_eq, mul_add]
      simpa using add_le_add (h z.ofLp.re) (h z.ofLp.im)

/-- The complexification acts on the underlying vector of `WithLp 2 (Complexification X)` by
`ContinuousLinearMap.complexify`. -/
@[simp]
theorem ofLp_complexifyL2_apply (T : X →L[ℝ] Y) (z : WithLp 2 (Complexification X)) :
    (T.complexifyL2 z).ofLp = T.complexify z.ofLp := (rfl)

/-- The complexification agrees with `T` on real vectors. -/
@[simp]
theorem complexifyL2_toLp_ofReal (T : X →L[ℝ] Y) (x : X) :
    T.complexifyL2 (toLp 2 (ofReal x)) = toLp 2 (ofReal (T x)) := by
  apply ofLp_injective 2
  simp

/-- The complexification is the unique complex-linear extension of `T`. -/
theorem eq_complexifyL2_iff (T : X →L[ℝ] Y)
    (S : WithLp 2 (Complexification X) →L[ℂ] WithLp 2 (Complexification Y)) :
    S = T.complexifyL2 ↔ ∀ x, S (toLp 2 (ofReal x)) = toLp 2 (ofReal (T x)) := by
  refine ⟨fun h x ↦ h ▸ complexifyL2_toLp_ofReal T x, fun h ↦ ?_⟩
  ext1 z
  have hz : z = toLp 2 (ofReal z.ofLp.re) + Complex.I • toLp 2 (ofReal z.ofLp.im) := by
    rw [← toLp_smul, ← toLp_add, re_add_I_smul_im, toLp_ofLp]
  rw [hz, map_add, map_smul, map_add, map_smul, h, h, complexifyL2_toLp_ofReal,
    complexifyL2_toLp_ofReal]

/-- Complexification sends the zero operator to zero. -/
@[simp]
theorem complexifyL2_zero : (0 : X →L[ℝ] Y).complexifyL2 = 0 := by
  ext1 z
  apply ofLp_injective 2
  ext <;> simp

/-- Complexification is additive. -/
@[simp]
theorem complexifyL2_add (S T : X →L[ℝ] Y) :
    (S + T).complexifyL2 = S.complexifyL2 + T.complexifyL2 := by
  ext1 z
  apply ofLp_injective 2
  ext <;> simp

/-- Complexification preserves identity maps. -/
@[simp]
theorem complexifyL2_id :
    (ContinuousLinearMap.id ℝ X).complexifyL2 = ContinuousLinearMap.id ℂ _ := by
  ext1 z
  apply ofLp_injective 2
  simp

/-- Complexification preserves composition of bounded operators. -/
@[simp]
theorem complexifyL2_comp (T : Y →L[ℝ] Z) (S : X →L[ℝ] Y) :
    (T.comp S).complexifyL2 = T.complexifyL2.comp S.complexifyL2 := by
  ext1 z
  apply ofLp_injective 2
  simp

end NormedSpace

section InnerProductSpace

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Y]
  [InnerProductSpace ℝ Y]

/-- Complexification preserves the operator norm. -/
@[simp]
theorem norm_complexifyL2 (T : X →L[ℝ] Y) : ‖T.complexifyL2‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) ?_
  refine T.opNorm_le_bound (norm_nonneg T.complexifyL2) fun x ↦ ?_
  simpa using T.complexifyL2.le_opNorm (toLp 2 (ofReal x))

/-- The adjoint of a complexification is the complexification of the adjoint. -/
@[simp]
theorem adjoint_complexifyL2 [CompleteSpace X] [CompleteSpace Y] (T : X →L[ℝ] Y) :
    adjoint T.complexifyL2 = (adjoint T).complexifyL2 := by
  refine ((eq_adjoint_iff _ _).2 fun y x ↦ ?_).symm
  apply Complex.ext <;> simp [adjoint_inner_left]

/-- Complexification is real-homogeneous. -/
@[simp]
theorem complexifyL2_smul (r : ℝ) (T : X →L[ℝ] Y) :
    (r • T).complexifyL2 = r • T.complexifyL2 := by
  ext1 z
  apply ofLp_injective 2
  ext <;> simp

variable (X Y)

/-- Complexification of bounded operators, as a real-linear isometry. -/
def complexifyL2ₗᵢ :
    (X →L[ℝ] Y) →ₗᵢ[ℝ] (WithLp 2 (Complexification X) →L[ℂ] WithLp 2 (Complexification Y)) where
  toFun := complexifyL2
  map_add' := complexifyL2_add
  map_smul' := complexifyL2_smul
  norm_map' := norm_complexifyL2

/-- Complexification of the bounded operators on a real Hilbert space, as a homomorphism of
real `⋆`-algebras. -/
def complexifyL2StarAlgHom [CompleteSpace X] :
    (X →L[ℝ] X) →⋆ₐ[ℝ]
      (WithLp 2 (Complexification X) →L[ℂ] WithLp 2 (Complexification X)) where
  toFun := complexifyL2
  map_one' := complexifyL2_id
  map_mul' := complexifyL2_comp
  map_zero' := complexifyL2_zero
  map_add' := complexifyL2_add
  commutes' r := by
    ext1 z; apply ofLp_injective 2; ext <;> simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := (adjoint_complexifyL2 T).symm

variable {X Y}

@[simp]
theorem complexifyL2ₗᵢ_apply (T : X →L[ℝ] Y) : complexifyL2ₗᵢ X Y T = T.complexifyL2 := (rfl)

@[simp]
theorem complexifyL2StarAlgHom_apply [CompleteSpace X] (T : X →L[ℝ] X) :
    complexifyL2StarAlgHom X T = T.complexifyL2 := (rfl)

variable (X) in
/-- Complexification of the bounded operators on a real Hilbert space is a closed embedding. -/
theorem isClosedEmbedding_complexifyL2StarAlgHom [CompleteSpace X] :
    Topology.IsClosedEmbedding (complexifyL2StarAlgHom X) := by
  have : ⇑(complexifyL2StarAlgHom X) = complexifyL2ₗᵢ X X := funext fun _ ↦ by simp
  -- Naming the codomain lets its metric instance be synthesized before unification.
  exact this ▸ (complexifyL2ₗᵢ X X).isometry.isClosedEmbedding
    (γ := WithLp 2 (Complexification X) →L[ℂ] WithLp 2 (Complexification X))

/-- A bounded operator on a real Hilbert space is self-adjoint exactly when its complexification
is. -/
@[simp]
theorem isSelfAdjoint_complexifyL2_iff [CompleteSpace X] {T : X →L[ℝ] X} :
    IsSelfAdjoint T.complexifyL2 ↔ IsSelfAdjoint T := by
  simpa using (complexifyL2ₗᵢ X X).injective.isSelfAdjoint_apply_iff (complexifyL2StarAlgHom X)

end InnerProductSpace

end ContinuousLinearMap

section RealComplexification

open TauCeti WithLp
open scoped InnerProductSpace

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hilbert complexification commutes with orthogonal complementation. -/
@[simp]
theorem complexifyL2_orthogonal (U : Submodule ℝ E) :
    Uᗮ.complexifyL2 = U.complexifyL2ᗮ := by
  ext z
  constructor
  · intro hz
    rw [mem_complexifyL2] at hz
    rw [mem_orthogonal]
    intro w hw
    rw [mem_complexifyL2] at hw
    -- Expose the two coordinate formulas for the native complex inner product.
    apply Complex.ext
    · change ⟪w.ofLp.re, z.ofLp.re⟫_ℝ + ⟪w.ofLp.im, z.ofLp.im⟫_ℝ = 0
      simp [inner_right_of_mem_orthogonal hw.1 hz.1,
        inner_right_of_mem_orthogonal hw.2 hz.2]
    · change ⟪w.ofLp.re, z.ofLp.im⟫_ℝ - ⟪w.ofLp.im, z.ofLp.re⟫_ℝ = 0
      simp [inner_right_of_mem_orthogonal hw.1 hz.2,
        inner_right_of_mem_orthogonal hw.2 hz.1]
  · intro hz
    have h (u : E) (hu : u ∈ U) :
        ⟪toLp 2 (Complexification.ofReal u), z⟫_ℂ = 0 :=
      hz _ (by simpa only [mem_complexifyL2, ofLp_toLp,
        Complexification.ofReal_re, Complexification.ofReal_im] using And.intro hu U.zero_mem)
    rw [mem_complexifyL2]
    constructor
    · rw [mem_orthogonal]
      intro u hu
      simpa using congrArg Complex.re (h u hu)
    · rw [mem_orthogonal]
      intro u hu
      simpa using congrArg Complex.im (h u hu)

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

/-- The complexified projection takes values in the complexified subspace. -/
theorem complexifyL2_starProjection_mem (z : WithLp 2 (Complexification E)) :
    U.starProjection.complexifyL2 z ∈ U.complexifyL2 := by
  rw [mem_complexifyL2]
  simpa only [ContinuousLinearMap.ofLp_complexifyL2_apply,
    ContinuousLinearMap.complexify_apply_re, ContinuousLinearMap.complexify_apply_im] using
    And.intro (U.starProjection_apply_mem z.ofLp.re) (U.starProjection_apply_mem z.ofLp.im)

/-- The residual from the complexified projection is orthogonal to its range. -/
theorem sub_complexifyL2_starProjection_mem_orthogonal
    (z : WithLp 2 (Complexification E)) :
    z - U.starProjection.complexifyL2 z ∈ U.complexifyL2ᗮ := by
  rw [← complexifyL2_orthogonal, mem_complexifyL2]
  simp

/-- An orthogonally complemented real subspace remains complemented after complexification. -/
instance instHasOrthogonalProjectionComplexifyL2 : U.complexifyL2.HasOrthogonalProjection where
  exists_orthogonal z := ⟨_, U.complexifyL2_starProjection_mem z,
    U.sub_complexifyL2_starProjection_mem_orthogonal z⟩

/-- Orthogonal projection commutes with Hilbert complexification. -/
@[simp]
theorem starProjection_complexifyL2 :
    U.complexifyL2.starProjection = U.starProjection.complexifyL2 := by
  ext z
  exact U.complexifyL2.eq_starProjection_of_mem_orthogonal
    (U.complexifyL2_starProjection_mem z)
    (U.sub_complexifyL2_starProjection_mem_orthogonal z)

/-- Hilbert complexification preserves the gap between two orthogonally complemented subspaces. -/
@[simp]
theorem projectionGap_complexifyL2 (V : Submodule ℝ E) [V.HasOrthogonalProjection] :
    U.complexifyL2.projectionGap V.complexifyL2 = U.projectionGap V := by
  have hsub : (U.starProjection - V.starProjection).complexifyL2 =
      U.starProjection.complexifyL2 - V.starProjection.complexifyL2 :=
    by simpa only [LinearIsometry.coe_toLinearMap,
      ContinuousLinearMap.complexifyL2ₗᵢ_apply] using
      map_sub (ContinuousLinearMap.complexifyL2ₗᵢ E E).toLinearMap
        U.starProjection V.starProjection
  rw [projectionGap_def, projectionGap_def, starProjection_complexifyL2,
    starProjection_complexifyL2, ← hsub, ContinuousLinearMap.norm_complexifyL2]

end Submodule

end RealComplexification
