/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Hermitian vector bundles over the ring of integers

Let `K` be a number field. A hermitian vector bundle over `Spec 𝓞 K` is a finitely generated
projective `𝓞 K`-module `E` together with, for every field embedding `σ : K →+* ℂ`, a positive
definite hermitian inner product `h_σ` on the complex vector space `E_σ = ℂ ⊗[𝓞 K, σ] E`, such
that `h_{conj σ}(1 ⊗ x, 1 ⊗ y)` is the complex conjugate of `h_σ(1 ⊗ x, 1 ⊗ y)` for `x y : E`.

The complex fibre `ComplexFiber σ E` is `ComplexAlong σ ⊗[𝓞 K] E`, where `ComplexAlong σ` is a
type synonym of `ℂ` carrying the `𝓞 K`-algebra structure given by `σ`; it is a complex vector
space through the left factor.

## Main definitions

The structure is `TauCeti.HermitianVectorBundle`; the other names are in its namespace.

* `ComplexAlong σ`: the complex numbers as an `𝓞 K`-algebra through `σ : K →+* ℂ`.
* `Metric K E`: a family of positive definite hermitian inner products on the complex fibres
  of `E`, compatible with complex conjugation of embeddings.
* `HermitianVectorBundle K`: a finitely generated projective `𝓞 K`-module with a
  hermitian metric.
* `rank`: the rank `finrank K (K ⊗[𝓞 K] E)`.
* `trivial`: the trivial bundle `Ō_K`, with `h_σ(1, 1) = 1`.
* `rescale`: the bundle `Ē(c)` with norms `e^{-c} ‖·‖_σ`.
* `Isometry`: `𝓞 K`-linear isomorphisms whose complexifications
  are unitary at every embedding.
* `sectionDegree`: the expression `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ` attached to a section `s`.
  For a nonzero section of a bundle of rank one it is the Arakelov degree of the bundle; for other
  bundles or sections it is only this expression, not a degree of the bundle.

## References

* P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616
  (1983/84), §1.1, pp. 25–26.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.2, p. 13.
* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795 (1994/95), Appendice A.1–A.2.
-/

public noncomputable section

open NumberField ComplexConjugate TensorProduct Module

namespace TauCeti

variable {K : Type*} [Field K]

namespace HermitianVectorBundle

/-- The complex numbers, viewed as an algebra over `𝓞 K` through the field embedding
`σ : K →+* ℂ`. The complex fibre of an `𝓞 K`-module `E` at `σ` is
`ComplexAlong σ ⊗[𝓞 K] E`. -/
@[expose] def ComplexAlong (_σ : K →+* ℂ) : Type := ℂ

namespace ComplexAlong

variable (σ : K →+* ℂ)

/-- The commutative ring structure of `ℂ` on `ComplexAlong σ`. -/
instance instCommRing : CommRing (ComplexAlong σ) := inferInstanceAs (CommRing ℂ)

/-- The `ℂ`-algebra structure of `ℂ` on `ComplexAlong σ`. -/
instance instAlgebraComplex : Algebra ℂ (ComplexAlong σ) := inferInstanceAs (Algebra ℂ ℂ)

/-- The `𝓞 K`-algebra structure on `ComplexAlong σ` given by the embedding `σ`. -/
instance instAlgebraRingOfIntegers : Algebra (𝓞 K) (ComplexAlong σ) :=
  RingHom.toAlgebra ((σ.comp (algebraMap (𝓞 K) K) : 𝓞 K →+* ℂ) : 𝓞 K →+* ComplexAlong σ)

/-- Integers of `K` and complex numbers act on `ComplexAlong σ` by commuting multiplications. -/
instance instSMulCommClass : SMulCommClass (𝓞 K) ℂ (ComplexAlong σ) where
  smul_comm a c z := by
    rw [Algebra.smul_def a, Algebra.smul_def a]
    exact mul_smul_comm c _ z

/-- The identification of `ComplexAlong σ` with `ℂ`. -/
@[expose] def toComplex : ComplexAlong σ ≃ₗ[ℂ] ℂ := LinearEquiv.refl ℂ ℂ

/-- An integer `a` of `K` acts on `ComplexAlong σ` as the complex number `σ(a)`. -/
theorem toComplex_algebraMap (a : 𝓞 K) :
    toComplex σ (algebraMap (𝓞 K) (ComplexAlong σ) a) = σ (algebraMap (𝓞 K) K a) :=
  (rfl)

/-- The image of an integer `a` of `K` in `ComplexAlong σ` is that of the complex number `σ(a)`. -/
theorem algebraMap_ringOfIntegers_eq (a : 𝓞 K) :
    algebraMap (𝓞 K) (ComplexAlong σ) a =
      algebraMap ℂ (ComplexAlong σ) (σ (algebraMap (𝓞 K) K a)) :=
  (rfl)

end ComplexAlong

/-- The complex fibre `E_σ = ℂ ⊗[𝓞 K, σ] E` of an `𝓞 K`-module at a field embedding `σ`. -/
abbrev ComplexFiber (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] : Type _ :=
  ComplexAlong σ ⊗[𝓞 K] E

variable (K) in
/-- A hermitian metric on an `𝓞 K`-module `E`: for every embedding `σ : K →+* ℂ` a positive
definite hermitian inner product on the complex fibre `E_σ`, such that
`h_{conj σ}(1 ⊗ x, 1 ⊗ y) = conj (h_σ(1 ⊗ x, 1 ⊗ y))` for `x y : E`. Inner products are conjugate
linear in the first argument, as in Mathlib. -/
@[ext]
structure Metric (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] where
  /-- The inner product on the complex fibre at `σ`. -/
  core (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber σ E)
  /-- The inner products at conjugate embeddings are conjugate on the integral elements. -/
  inner_conjugate (σ : K →+* ℂ) (x y : E) :
    (core (ComplexEmbedding.conjugate σ)).inner (1 ⊗ₜ x) (1 ⊗ₜ y) =
      conj ((core σ).inner (1 ⊗ₜ x) (1 ⊗ₜ y))

end HermitianVectorBundle

open HermitianVectorBundle in
variable (K) in
/-- A hermitian vector bundle over `Spec 𝓞 K`: a finitely generated projective `𝓞 K`-module
with a hermitian metric. A hermitian line bundle is one of rank one. -/
structure HermitianVectorBundle where
  /-- The underlying `𝓞 K`-module. -/
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [module : Module (𝓞 K) carrier]
  [finite : Module.Finite (𝓞 K) carrier]
  [projective : Module.Projective (𝓞 K) carrier]
  /-- The hermitian metric. -/
  metric : Metric K carrier

namespace HermitianVectorBundle

attribute [instance] addCommGroup module finite projective

instance instCoeSort : CoeSort (HermitianVectorBundle K) (Type _) := ⟨carrier⟩

variable (E F : HermitianVectorBundle K)

/-- The inner product `h_σ` on the complex fibre `E_σ`. -/
def inner (σ : K →+* ℂ) (v w : ComplexFiber σ E) : ℂ := (E.metric.core σ).inner v w

/-- The norm `‖x‖_σ = h_σ(1 ⊗ x, 1 ⊗ x) ^ (1 / 2)` of an element `x : E` at an embedding `σ`. -/
def norm (σ : K →+* ℂ) (x : E) : ℝ :=
  Real.sqrt (RCLike.re (E.inner σ (1 ⊗ₜ x) (1 ⊗ₜ x)))

/-- The rank of a hermitian vector bundle: the dimension of its generic fibre `K ⊗[𝓞 K] E`. -/
def rank : ℕ := finrank K (K ⊗[𝓞 K] E)

/-- The inner product of `E` at `σ` is the one of its metric. -/
theorem inner_def (σ : K →+* ℂ) (v w : ComplexFiber σ E) :
    E.inner σ v w = (E.metric.core σ).inner v w :=
  (rfl)

/-- The norm of `x : E` at `σ` is `h_σ(1 ⊗ x, 1 ⊗ x) ^ (1 / 2)`. -/
theorem norm_def (σ : K →+* ℂ) (x : E) :
    E.norm σ x = Real.sqrt (RCLike.re (E.inner σ (1 ⊗ₜ x) (1 ⊗ₜ x))) :=
  (rfl)

/-- The rank of `E` is the dimension of its generic fibre `K ⊗[𝓞 K] E`. -/
theorem rank_def : E.rank = finrank K (K ⊗[𝓞 K] E) :=
  (rfl)

/-- The inner products at conjugate embeddings are conjugate on the integral elements. -/
theorem inner_conjugate (σ : K →+* ℂ) (x y : E) :
    E.inner (ComplexEmbedding.conjugate σ) (1 ⊗ₜ x) (1 ⊗ₜ y) =
      conj (E.inner σ (1 ⊗ₜ x) (1 ⊗ₜ y)) :=
  E.metric.inner_conjugate σ x y

/-- The norm of an element of `E` is the same at conjugate embeddings. -/
theorem norm_conjugate (σ : K →+* ℂ) (x : E) :
    E.norm (ComplexEmbedding.conjugate σ) x = E.norm σ x := by
  simp only [norm, inner_conjugate, RCLike.conj_re]

/-- An isometry of hermitian vector bundles: an `𝓞 K`-linear isomorphism whose
complexification is unitary at every embedding. -/
structure Isometry extends E ≃ₗ[𝓞 K] F where
  /-- The complexification at every embedding preserves the inner products. -/
  inner_baseChange (σ : K →+* ℂ) (v w : ComplexFiber σ E) :
    F.inner σ (toLinearEquiv.baseChange (𝓞 K) (ComplexAlong σ) _ _ v)
        (toLinearEquiv.baseChange (𝓞 K) (ComplexAlong σ) _ _ w) =
      E.inner σ v w

variable {E F}

/-- Two isometries with the same underlying `𝓞 K`-linear map are equal. -/
theorem Isometry.toLinearEquiv_injective :
    Function.Injective (Isometry.toLinearEquiv : Isometry E F → E ≃ₗ[𝓞 K] F) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ (rfl : f = g)
  rfl

/-- Two isometries with equal underlying maps are equal. -/
@[ext]
theorem Isometry.ext {f g : Isometry E F} (h : ∀ x, f.toLinearEquiv x = g.toLinearEquiv x) :
    f = g :=
  Isometry.toLinearEquiv_injective (LinearEquiv.ext h)

/-- An isometry preserves the inner products of elements at every embedding. -/
@[simp]
theorem Isometry.inner_one_tmul (f : Isometry E F) (σ : K →+* ℂ) (x y : E) :
    F.inner σ ((1 : ComplexAlong σ) ⊗ₜ f.toLinearEquiv x) (1 ⊗ₜ f.toLinearEquiv y) =
      E.inner σ (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  simpa using f.inner_baseChange σ (1 ⊗ₜ x) (1 ⊗ₜ y)

/-- An isometry preserves the norms of elements at every embedding. -/
@[simp]
theorem Isometry.norm_apply (f : Isometry E F) (σ : K →+* ℂ) (x : E) :
    F.norm σ (f.toLinearEquiv x) = E.norm σ x := by
  rw [norm, norm, f.inner_one_tmul]

variable (E) in
/-- A nonzero element of a hermitian vector bundle stays nonzero in every complex fibre, since
`E` is flat and `𝓞 K → ℂ` is injective. -/
theorem one_tmul_ne_zero (σ : K →+* ℂ) {x : E} (hx : x ≠ 0) :
    (1 : ComplexAlong σ) ⊗ₜ[𝓞 K] x ≠ 0 := by
  have : FaithfulSMul (𝓞 K) (ComplexAlong σ) :=
    (faithfulSMul_iff_algebraMap_injective (𝓞 K) (ComplexAlong σ)).mpr
      ((RingHom.injective σ).comp (FaithfulSMul.algebraMap_injective (𝓞 K) K))
  intro h
  exact hx (Module.Flat.tensorProduct_mk_injective (𝓞 K) E (ComplexAlong σ) (by simpa using h))

variable (E) in
/-- The norm of a nonzero element of a hermitian vector bundle is positive at every
embedding. -/
theorem norm_pos (σ : K →+* ℂ) {x : E} (hx : x ≠ 0) : 0 < E.norm σ x := by
  let := E.metric.core σ
  refine Real.sqrt_pos.2 (lt_of_le_of_ne InnerProductSpace.Core.inner_self_nonneg (Ne.symm ?_))
  exact fun h => E.one_tmul_ne_zero σ hx (InnerProductSpace.Core.normSq_eq_zero.1 h)

variable (E) in
/-- An integer `a` of `K` scales the norm at `σ` by `|σ(a)|`: `‖a • x‖_σ = |σ(a)| ‖x‖_σ`. -/
theorem norm_smul (σ : K →+* ℂ) (a : 𝓞 K) (x : E) :
    E.norm σ (a • x) = ‖σ (algebraMap (𝓞 K) K a)‖ * E.norm σ x := by
  set c : ℂ := σ (algebraMap (𝓞 K) K a)
  -- In the fibre, `a` acts on `1 ⊗ x` as the complex number `σ(a)`.
  have h : (1 : ComplexAlong σ) ⊗ₜ[𝓞 K] (a • x) = c • ((1 : ComplexAlong σ) ⊗ₜ x) := by
    rw [← smul_tmul, smul_tmul', Algebra.smul_def, Algebra.smul_def, mul_one, mul_one,
      ComplexAlong.algebraMap_ringOfIntegers_eq]
  have hr : (E.metric.core σ).inner (1 ⊗ₜ x) (c • (1 ⊗ₜ x)) =
      c * (E.metric.core σ).inner (1 ⊗ₜ x) (1 ⊗ₜ x) :=
    InnerProductSpace.Core.inner_smul_right (c := (E.metric.core σ).toCore) _ _
  rw [norm, norm, inner, inner, h, (E.metric.core σ).smul_left, hr, ← mul_assoc, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
  simp [Real.sqrt_mul (sq_nonneg _)]

section Trivial

variable (σ : K →+* ℂ)

/-- The identification `z ⊗ a ↦ σ(a) z` of the complex fibre of `𝓞 K` at `σ` with `ℂ`. -/
def trivialFiberEquiv : ComplexFiber σ (𝓞 K) ≃ₗ[ℂ] ℂ :=
  ((AlgebraTensorModule.rid (𝓞 K) (ComplexAlong σ) (ComplexAlong σ)).restrictScalars ℂ).trans
    (ComplexAlong.toComplex σ)

/-- `trivialFiberEquiv σ` sends `1 ⊗ a` to `σ(a)`. -/
@[simp]
theorem trivialFiberEquiv_one_tmul (a : 𝓞 K) :
    trivialFiberEquiv σ ((1 : ComplexAlong σ) ⊗ₜ a) = σ (algebraMap (𝓞 K) K a) :=
  mul_one _

/-- The standard inner product `h_σ(v, w) = conj (v) * w` on the complex fibre of `𝓞 K`: the
inner product of `ℂ` pulled back along `trivialFiberEquiv σ`. -/
@[instance_reducible]
def trivialCore : InnerProductSpace.Core ℂ (ComplexFiber σ (𝓞 K)) :=
  letI := NormedAddCommGroup.induced _ ℂ (trivialFiberEquiv σ) (trivialFiberEquiv σ).injective
  letI := InnerProductSpace.induced (𝕜 := ℂ) (trivialFiberEquiv σ)
  InnerProductSpace.toCore

/-- The standard inner product on the complex fibre of `𝓞 K` is `conj (v) * w`. -/
theorem trivialCore_inner (v w : ComplexFiber σ (𝓞 K)) :
    (trivialCore σ).inner v w = conj (trivialFiberEquiv σ v) * trivialFiberEquiv σ w :=
  RCLike.inner_apply' _ _

variable (K) in
/-- The trivial hermitian line bundle `Ō_K = (𝓞 K, |·|_σ)`, with `h_σ(1, 1) = 1` for every
embedding `σ`. -/
abbrev trivial : HermitianVectorBundle K where
  carrier := 𝓞 K
  metric :=
    { core := trivialCore
      inner_conjugate σ x y := by
        simp [trivialCore_inner, ComplexEmbedding.conjugate_coe_eq] }

/-- The inner product of `Ō_K` at `σ` on integral elements is `conj (σ x) * σ y`. -/
@[simp]
theorem trivial_inner (x y : 𝓞 K) :
    (trivial K).inner σ ((1 : ComplexAlong σ) ⊗ₜ[𝓞 K] x) (1 ⊗ₜ y) =
      conj (σ (algebraMap (𝓞 K) K x)) * σ (algebraMap (𝓞 K) K y) := by
  rw [inner, trivialCore_inner, trivialFiberEquiv_one_tmul, trivialFiberEquiv_one_tmul]

/-- The norm on `Ō_K` at `σ` is the absolute value `|σ(x)|`. -/
@[simp]
theorem trivial_norm (x : 𝓞 K) : (trivial K).norm σ x = ‖σ (algebraMap (𝓞 K) K x)‖ := by
  rw [norm, trivial_inner, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re,
    Real.sqrt_sq (norm_nonneg _)]

/-- The section `1` of `Ō_K` has norm one at every embedding. -/
theorem trivial_norm_one : (trivial K).norm σ 1 = 1 := by
  simp [trivial_norm]

/-- The trivial bundle has rank one. -/
@[simp]
theorem rank_trivial : (trivial K).rank = 1 := by
  rw [rank, Module.finrank_baseChange, Module.finrank_self]

end Trivial

section Rescale

/-- The inner products of `Ē(c)`: those of `Ē` pulled back along multiplication by `e^{-c}`,
that is, multiplied by `e^{-2c}`. -/
@[instance_reducible]
def rescaleCore (c : ℝ) (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber σ E) :=
  let f := LinearEquiv.smulOfNeZero ℂ (ComplexFiber σ E) (Real.exp (-c) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
  letI : NormedAddCommGroup (ComplexFiber σ E) := (E.metric.core σ).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (ComplexFiber σ E) := .ofCore (E.metric.core σ).toCore
  @InnerProductSpace.toCore ℂ _ _ (NormedAddCommGroup.induced _ _ f f.injective)
    (InnerProductSpace.induced (𝕜 := ℂ) f)

/-- The inner products of `Ē(c)` are those of `Ē` multiplied by `e^{-2c}`. -/
theorem rescaleCore_inner (c : ℝ) (σ : K →+* ℂ) (v w : ComplexFiber σ E) :
    (E.rescaleCore c σ).inner v w = ((Real.exp (-c) ^ 2 : ℝ) : ℂ) * E.inner σ v w := by
  set a : ℂ := ((Real.exp (-c) : ℝ) : ℂ)
  have h : (E.rescaleCore c σ).inner v w = (E.metric.core σ).inner (a • v) (a • w) := rfl
  have hr : (E.metric.core σ).inner v (a • w) = a * (E.metric.core σ).inner v w :=
    InnerProductSpace.Core.inner_smul_right (c := (E.metric.core σ).toCore) v w
  rw [h, (E.metric.core σ).smul_left, hr, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    ← sq, inner]

/-- The rescaled bundle `Ē(c)`: the same module, with every norm multiplied by `e^{-c}`, so
that every inner product is multiplied by `e^{-2c}`. -/
@[expose]
def rescale (c : ℝ) : HermitianVectorBundle K where
  carrier := E
  metric :=
    { core := E.rescaleCore c
      inner_conjugate σ x y := by
        rw [rescaleCore_inner, rescaleCore_inner, map_mul, Complex.conj_ofReal,
          E.inner_conjugate] }

/-- The inner products of `Ē(c)` are those of `Ē` multiplied by `e^{-2c}`. -/
@[simp]
theorem rescale_inner (c : ℝ) (σ : K →+* ℂ) (v w : ComplexFiber σ E) :
    (E.rescale c).inner σ v w = ((Real.exp (-c) ^ 2 : ℝ) : ℂ) * E.inner σ v w :=
  E.rescaleCore_inner c σ v w

/-- Rescaling multiplies every norm by `e^{-c}`. -/
@[simp]
theorem rescale_norm (c : ℝ) (σ : K →+* ℂ) (x : E) :
    (E.rescale c).norm σ x = Real.exp (-c) * E.norm σ x := by
  have h : (E.rescale c).inner σ (1 ⊗ₜ x) (1 ⊗ₜ x) =
      ((Real.exp (-c) ^ 2 : ℝ) : ℂ) * E.inner σ (1 ⊗ₜ x) (1 ⊗ₜ x) :=
    E.rescale_inner c σ _ _
  unfold norm
  simp only [h, RCLike.re_to_complex]
  rw [Complex.re_ofReal_mul, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]

/-- Rescaling does not change the rank. -/
@[simp]
theorem rank_rescale (c : ℝ) : (E.rescale c).rank = E.rank :=
  (rfl)

end Rescale

section SectionDegree

variable [NumberField K]

/-- The expression `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ` attached to a section `s`, the sum
running over all field embeddings `σ : K →+* ℂ`. For a nonzero section of a hermitian vector
bundle of rank one this is the Arakelov degree of the bundle; its independence of the section is
the product formula. For other bundles or sections it is only this expression. -/
def sectionDegree (s : E) : ℝ :=
  Real.log (Submodule.span (𝓞 K) {s}).cardQuot - ∑ σ : K →+* ℂ, Real.log (E.norm σ s)

/-- The degree computed with `s` is `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ`. -/
theorem sectionDegree_def (s : E) :
    E.sectionDegree s =
      Real.log (Submodule.span (𝓞 K) {s}).cardQuot - ∑ σ : K →+* ℂ, Real.log (E.norm σ s) :=
  (rfl)

/-- The degree of `Ō_K` computed with the section `1` is zero. -/
@[simp]
theorem sectionDegree_trivial_one : (trivial K).sectionDegree 1 = 0 := by
  simp [sectionDegree, Ideal.span_singleton_one, Submodule.cardQuot_top]

/-- Rescaling the metric by `e^{-c}` adds `[K : ℚ] c` to the degree computed with a nonzero
section. -/
theorem sectionDegree_rescale (c : ℝ) {s : E} (hs : s ≠ 0) :
    (E.rescale c).sectionDegree s = E.sectionDegree s + finrank ℚ K * c := by
  have h σ : Real.log ((E.rescale c).norm σ s) = -c + Real.log (E.norm σ s) := by
    rw [rescale_norm, Real.log_mul (by positivity) (E.norm_pos σ hs).ne', Real.log_exp]
  simp only [sectionDegree, h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul]
  -- `E.rescale c` is `E` with a new metric: its carrier is `E` by definition, but the module
  -- instance on the span differs syntactically, so `rw` cannot identify the two `cardQuot` terms
  -- and `change` restates the left one over `E`.
  change Real.log (Submodule.span (𝓞 K) {s}).cardQuot - _ = _
  ring

end SectionDegree

end HermitianVectorBundle

end TauCeti
