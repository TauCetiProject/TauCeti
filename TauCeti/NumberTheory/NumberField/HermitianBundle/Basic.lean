/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.RingTheory.FractionalIdeal.BaseChange

import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Hermitian vector bundles over the ring of integers of a number field

Let `K` be a number field with ring of integers `O_K`. A hermitian vector bundle over `Spec O_K`
is a finitely generated projective `O_K`-module `E` together with, for every complex embedding
`σ : K → ℂ`, a positive definite hermitian form `h_σ` on the complex fibre `E ⊗_{O_K,σ} ℂ`, such
that `h_{conj σ}(1 ⊗ x, 1 ⊗ y)` is the complex conjugate of `h_σ(1 ⊗ x, 1 ⊗ y)` for `x, y ∈ E`,
where `conj σ` is the complex conjugate embedding. At a real embedding this says that `h_σ` is the
complexification of a real inner product. These are
the objects whose Arakelov degree is the archimedean part of the height of a point, and the
Hodge line of an abelian variety with its Faltings metric is one of them.

To form the fibre `E ⊗_{O_K,σ} ℂ` for every `σ` at once, `NumberField.ComplexEmbedding.Codomain σ`
is a copy of `ℂ` carrying the `K`-algebra structure given by `σ`; the fibre at `σ` is the scalar
extension `Codomain σ ⊗[𝓞 K] E`, a complex vector space. The hermitian forms are complex
sesquilinear forms on these fibres, conjugate-linear in the first argument as in Mathlib.

## Main definitions

* `TauCeti.HermitianMetric K E`: a hermitian metric on an `𝓞 K`-module `E`, a family of positive
  definite hermitian forms on the complex fibres compatible with complex conjugation of the
  embeddings.
* `TauCeti.HermitianMetric.norm`: the norm `‖u‖_σ` of a vector in the complex fibre at `σ`.
* `TauCeti.HermitianMetric.placeNorm`: the norm `‖x‖_v` of `x ∈ E` at an infinite place `v`,
  computed at either complex embedding inducing `v` (`TauCeti.HermitianMetric.placeNorm_mk`).
* `TauCeti.HermitianMetric.rescale`: the metric `Ē(c)` with all norms multiplied by `e^{-c}`.
* `TauCeti.HermitianMetric.Isometry`: an `𝓞 K`-linear isomorphism whose complexifications are
  unitary at every embedding.
* `TauCeti.HermitianMetric.ofIsBaseChange`: the metric `‖x‖_σ = e^{-λ_v} |σ(ι x)|` on an
  `𝓞 K`-module `E` whose scalar extension to `K` is identified with `K` by `ι`, for real weights
  `λ_v` indexed by the infinite places.
* `TauCeti.HermitianMetric.trivial`: the trivial hermitian line `Ō_K = (O_K, |·|)`.
* `TauCeti.HermitianMetric.fractionalIdeal`: the hermitian line `(𝔞, e^{-λ_v} |·|_v)` of a
  nonzero fractional ideal `𝔞`.
* `TauCeti.HermitianBundle K`: a finitely generated projective `𝓞 K`-module with a hermitian
  metric, with its `TauCeti.HermitianBundle.rank`.

## References

* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §1.1.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.2.
* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.1–A.2.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate ComplexOrder nonZeroDivisors

namespace NumberField.ComplexEmbedding

variable {K : Type*} [Field K]

/-- The field `ℂ`, regarded as an algebra over `K` (and over its ring of integers) through the
complex embedding `σ`. The complex fibre of an `𝓞 K`-module `E` at `σ` is the scalar extension
`Codomain σ ⊗[𝓞 K] E`, a complex vector space. -/
@[expose] def Codomain (_σ : K →+* ℂ) : Type := ℂ

namespace Codomain

variable (σ : K →+* ℂ)

instance : Field (Codomain σ) := inferInstanceAs (Field ℂ)

instance : Algebra ℂ (Codomain σ) := inferInstanceAs (Algebra ℂ ℂ)

instance : Algebra K (Codomain σ) := σ.toAlgebra

instance : Algebra (𝓞 K) (Codomain σ) := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra

instance : IsScalarTower (𝓞 K) K (Codomain σ) := .of_algebraMap_eq fun _ ↦ rfl

instance : SMulCommClass (𝓞 K) ℂ (Codomain σ) where
  smul_comm a c z := mul_left_comm (G := ℂ) (σ (algebraMap (𝓞 K) K a)) c z

/-- The identification of `Codomain σ` with `ℂ`, as `ℂ`-algebras. -/
def equiv : Codomain σ ≃ₐ[ℂ] ℂ := AlgEquiv.refl

@[simp]
theorem equiv_algebraMap (x : K) : equiv σ (algebraMap K (Codomain σ) x) = σ x := (rfl)

@[simp]
theorem equiv_algebraMap_ringOfIntegers (x : 𝓞 K) :
    equiv σ (algebraMap (𝓞 K) (Codomain σ) x) = σ x := (rfl)

/-- In the complex fibre `Codomain σ ⊗[𝓞 K] E`, a pure tensor `c ⊗ x` is the complex multiple
`c • (1 ⊗ x)`. -/
theorem tmul_eq_smul {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (c : Codomain σ) (x : E) :
    c ⊗ₜ[𝓞 K] x = equiv σ c • (1 ⊗ₜ[𝓞 K] x : Codomain σ ⊗[𝓞 K] E) := by
  -- `equiv σ` is the identity of `ℂ`, and `ℂ` acts on `Codomain σ` by multiplication.
  rw [TensorProduct.smul_tmul']
  exact congrArg (· ⊗ₜ[𝓞 K] x) (mul_one (M := ℂ) c).symm

end Codomain

end NumberField.ComplexEmbedding

namespace TauCeti

open NumberField NumberField.ComplexEmbedding

variable (K : Type*) [Field K] (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

/-- A **hermitian metric** on an `𝓞 K`-module `E`: for every complex embedding `σ` of `K`, a
positive definite hermitian form on the complex fibre `E ⊗_{O_K,σ} ℂ`, conjugate-linear in the
first argument, such that `h_{conj σ}(1 ⊗ x, 1 ⊗ y) = conj (h_σ(1 ⊗ x, 1 ⊗ y))` for `x, y ∈ E`,
where `conj σ` is the complex conjugate embedding `NumberField.ComplexEmbedding.conjugate σ`.
A finitely generated projective `𝓞 K`-module with such a metric is a hermitian vector bundle
over `Spec 𝓞 K` (`TauCeti.HermitianBundle`). -/
@[ext]
structure HermitianMetric where
  /-- The hermitian form `h_σ` on the complex fibre at `σ`. -/
  form (σ : K →+* ℂ) : Codomain σ ⊗[𝓞 K] E →ₗ⋆[ℂ] Codomain σ ⊗[𝓞 K] E →ₗ[ℂ] ℂ
  /-- Each form is hermitian. -/
  isSymm_form (σ : K →+* ℂ) : (form σ).IsSymm
  /-- Each form is positive definite. -/
  form_self_pos (σ : K →+* ℂ) {u : Codomain σ ⊗[𝓞 K] E} : u ≠ 0 → 0 < form σ u u
  /-- The forms at complex conjugate embeddings are complex conjugate on `E`. -/
  form_conjugate_tmul (σ : K →+* ℂ) (x y : E) :
    form (conjugate σ) (1 ⊗ₜ x) (1 ⊗ₜ y) = conj (form σ (1 ⊗ₜ x) (1 ⊗ₜ y))

namespace HermitianMetric

variable {K E}
variable (h : HermitianMetric K E)

theorem conj_form (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    conj (h.form σ u v) = h.form σ v u :=
  (h.isSymm_form σ).eq u v

theorem form_self_nonneg (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) : 0 ≤ h.form σ u u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · exact (h.form_self_pos σ hu).le

@[simp]
theorem form_self_eq_zero_iff {σ : K →+* ℂ} {u : Codomain σ ⊗[𝓞 K] E} :
    h.form σ u u = 0 ↔ u = 0 :=
  ⟨fun h0 ↦ by_contra fun hu ↦ (h.form_self_pos σ hu).ne' h0, fun hu ↦ by simp [hu]⟩

/-- The norm `‖u‖_σ = h_σ(u, u)^{1/2}` of a vector in the complex fibre at `σ`. -/
protected def norm (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) : ℝ :=
  √(h.form σ u u).re

theorem norm_nonneg (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) : 0 ≤ h.norm σ u :=
  Real.sqrt_nonneg _

theorem form_self_eq_norm_sq (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.form σ u u = ((h.norm σ u ^ 2 : ℝ) : ℂ) := by
  have hnn := Complex.nonneg_iff.mp (h.form_self_nonneg σ u)
  rw [HermitianMetric.norm, Real.sq_sqrt hnn.1]
  exact Complex.ext (by simp) (by simpa using hnn.2.symm)

theorem norm_sq (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.norm σ u ^ 2 = (h.form σ u u).re := by
  rw [h.form_self_eq_norm_sq, Complex.ofReal_re]

@[simp]
theorem norm_eq_zero_iff {σ : K →+* ℂ} {u : Codomain σ ⊗[𝓞 K] E} : h.norm σ u = 0 ↔ u = 0 := by
  rw [← h.form_self_eq_zero_iff, h.form_self_eq_norm_sq, Complex.ofReal_eq_zero,
    pow_eq_zero_iff two_ne_zero]

theorem norm_pos {σ : K →+* ℂ} {u : Codomain σ ⊗[𝓞 K] E} (hu : u ≠ 0) : 0 < h.norm σ u :=
  (h.norm_nonneg σ u).lt_of_ne' (by simpa using hu)

@[simp]
theorem norm_zero (σ : K →+* ℂ) : h.norm σ 0 = 0 := by simp

theorem norm_smul (σ : K →+* ℂ) (c : ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.norm σ (c • u) = ‖c‖ * h.norm σ u := by
  rw [HermitianMetric.norm, HermitianMetric.norm, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (_root_.norm_nonneg c)]

/-- At the complex conjugate embedding, vectors of `E` have the same norm. -/
@[simp]
theorem norm_conjugate_tmul (σ : K →+* ℂ) (x : E) :
    h.norm (conjugate σ) (1 ⊗ₜ x) = h.norm σ (1 ⊗ₜ x) := by
  rw [HermitianMetric.norm, HermitianMetric.norm, h.form_conjugate_tmul, Complex.conj_re]

/-- At a real embedding, the form takes real values on vectors of `E`: it is the
complexification of a real inner product on `E ⊗_σ ℝ`. -/
theorem conj_form_tmul_of_isReal {σ : K →+* ℂ} (hσ : IsReal σ) (x y : E) :
    conj (h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y)) = h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  rw [← h.form_conjugate_tmul]
  have hc : conjugate σ = σ := isReal_iff.mp hσ
  generalize conjugate σ = τ at hc ⊢
  subst hc
  rfl

/-- The norm `‖x‖_v` of `x ∈ E` at an infinite place `v` of `K`, computed at a complex embedding
inducing `v`; it does not depend on the choice of embedding (`placeNorm_mk`). -/
def placeNorm (v : InfinitePlace K) (x : E) : ℝ :=
  h.norm v.embedding (1 ⊗ₜ x)

/-- The norm at the place induced by `σ` is the norm at `σ`. -/
@[simp]
theorem placeNorm_mk (σ : K →+* ℂ) (x : E) :
    h.placeNorm (InfinitePlace.mk σ) x = h.norm σ (1 ⊗ₜ x) := by
  rcases InfinitePlace.embedding_mk_eq σ with hσ | hσ
  · rw [placeNorm, hσ]
  · rw [placeNorm, hσ, norm_conjugate_tmul]

theorem placeNorm_nonneg (v : InfinitePlace K) (x : E) : 0 ≤ h.placeNorm v x :=
  h.norm_nonneg _ _

/-- The zero module carries exactly one hermitian metric, the empty family of forms on the zero
fibres. -/
instance [Subsingleton E] : Unique (HermitianMetric K E) where
  default :=
    { form _ := 0
      isSymm_form _ := LinearMap.isSymm_def.mpr fun _ _ ↦ by simp
      form_self_pos _ u hu := (hu (Subsingleton.elim _ _)).elim
      form_conjugate_tmul _ _ _ := by simp }
  uniq h := by
    ext σ u v
    simp [Subsingleton.elim u 0]

/-! ### Rescaling -/

/-- The metric `Ē(c)`: every form multiplied by `e^{-2c}`, so that every norm is multiplied by
`e^{-c}`. -/
def rescale (c : ℝ) : HermitianMetric K E where
  form σ := ((Real.exp (-2 * c) : ℝ) : ℂ) • h.form σ
  isSymm_form σ := LinearMap.isSymm_def.mpr fun u v ↦ by
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, h.conj_form]
  form_self_pos σ u hu := by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using
      mul_pos (Complex.zero_lt_real.mpr (Real.exp_pos _)) (h.form_self_pos σ hu)
  form_conjugate_tmul σ x y := by
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal,
      h.form_conjugate_tmul]

@[simp]
theorem rescale_form_apply (c : ℝ) (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    (h.rescale c).form σ u v = Real.exp (-2 * c) * h.form σ u v := (rfl)

@[simp]
theorem norm_rescale (c : ℝ) (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    (h.rescale c).norm σ u = Real.exp (-c) * h.norm σ u := by
  have hexp : Real.exp (-2 * c) = Real.exp (-c) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [HermitianMetric.norm, HermitianMetric.norm, rescale_form_apply, Complex.re_ofReal_mul,
    hexp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

@[simp]
theorem placeNorm_rescale (c : ℝ) (v : InfinitePlace K) (x : E) :
    (h.rescale c).placeNorm v x = Real.exp (-c) * h.placeNorm v x :=
  h.norm_rescale c _ _

@[simp]
theorem rescale_zero : h.rescale 0 = h := by
  ext σ u v
  simp

@[simp]
theorem rescale_rescale (c d : ℝ) : (h.rescale c).rescale d = h.rescale (c + d) := by
  ext σ u v
  simp only [rescale_form_apply, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf

/-! ### Isometries -/

variable {F G : Type*} [AddCommGroup F] [Module (𝓞 K) F] [AddCommGroup G] [Module (𝓞 K) G]

/-- An **isometry** between hermitian metrics: an `𝓞 K`-linear isomorphism `E ≃ F` whose
complexification is unitary at every complex embedding. Unitarity is tested on vectors of `E`;
`HermitianMetric.Isometry.form_baseChange` gives it on the whole complex fibre. -/
structure Isometry (h : HermitianMetric K E) (h' : HermitianMetric K F) extends E ≃ₗ[𝓞 K] F where
  /-- The linear isomorphism preserves the hermitian forms. -/
  form_tmul (σ : K →+* ℂ) (x y : E) :
    h'.form σ (1 ⊗ₜ toLinearEquiv x) (1 ⊗ₜ toLinearEquiv y) = h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y)

namespace Isometry

variable {h} {h' : HermitianMetric K F} {h'' : HermitianMetric K G}

instance : EquivLike (Isometry h h') E F where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' e e' he _ := by
    obtain ⟨e, _⟩ := e
    obtain ⟨e', _⟩ := e'
    congr
    exact LinearEquiv.coe_injective he

@[simp]
theorem coe_toLinearEquiv (e : Isometry h h') : ⇑e.toLinearEquiv = e := rfl

/-- Two isometries with the same underlying map are equal. -/
@[ext]
theorem ext {e e' : Isometry h h'} (he : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ he

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : Isometry h h' → E ≃ₗ[𝓞 K] F) := fun _ _ he ↦
  ext fun x ↦ congr($he x)

/-- An isometry preserves the hermitian forms on the whole complex fibre. -/
theorem form_baseChange (e : Isometry h h') (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    h'.form σ (e.toLinearMap.baseChange (Codomain σ) u)
        (e.toLinearMap.baseChange (Codomain σ) v) = h.form σ u v := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul c x =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul d y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Codomain.tmul_eq_smul σ c,
        Codomain.tmul_eq_smul σ d, Codomain.tmul_eq_smul σ c x, Codomain.tmul_eq_smul σ d y,
        LinearMap.map_smulₛₗ₂, map_smul, LinearMap.map_smulₛₗ₂, map_smul]
      exact congrArg _ (congrArg _ (e.form_tmul σ x y))

theorem norm_baseChange (e : Isometry h h') (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h'.norm σ (e.toLinearMap.baseChange (Codomain σ) u) = h.norm σ u := by
  rw [HermitianMetric.norm, HermitianMetric.norm, e.form_baseChange]

@[simp]
theorem form_tmul_apply (e : Isometry h h') (σ : K →+* ℂ) (x y : E) :
    h'.form σ (1 ⊗ₜ e x) (1 ⊗ₜ e y) = h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y) :=
  e.form_tmul σ x y

@[simp]
theorem norm_tmul_apply (e : Isometry h h') (σ : K →+* ℂ) (x : E) :
    h'.norm σ (1 ⊗ₜ e x) = h.norm σ (1 ⊗ₜ x) := by
  rw [HermitianMetric.norm, HermitianMetric.norm, e.form_tmul_apply]

@[simp]
theorem placeNorm_apply (e : Isometry h h') (v : InfinitePlace K) (x : E) :
    h'.placeNorm v (e x) = h.placeNorm v x :=
  e.norm_tmul_apply _ x

variable (h) in
/-- The identity isometry. -/
@[refl]
def refl : Isometry h h where
  toLinearEquiv := LinearEquiv.refl (𝓞 K) E
  form_tmul _ _ _ := rfl

/-- The inverse of an isometry. -/
@[symm]
def symm (e : Isometry h h') : Isometry h' h where
  toLinearEquiv := e.toLinearEquiv.symm
  form_tmul σ x y := by
    rw [← e.form_tmul σ]
    simp

/-- The composite of two isometries. -/
@[trans]
def trans (e : Isometry h h') (e' : Isometry h' h'') : Isometry h h'' where
  toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
  form_tmul σ x y := by
    simp only [LinearEquiv.trans_apply]
    rw [e'.form_tmul, e.form_tmul]

@[simp]
theorem refl_apply (x : E) : refl h x = x := (rfl)

@[simp]
theorem symm_apply_apply (e : Isometry h h') (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (e : Isometry h h') (x : F) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

@[simp]
theorem trans_apply (e : Isometry h h') (e' : Isometry h' h'') (x : E) :
    e.trans e' x = e' (e x) := (rfl)

end Isometry

/-! ### Hermitian lines inside `K` -/

section OfIsBaseChange

variable {ι : E →ₗ[𝓞 K] K} (hι : IsBaseChange K ι)

/-- For `ι : E → K` identifying the scalar extension of `E` to `K` with `K`, the complex fibre of
`E` at `σ` is `ℂ`, through `c ⊗ x ↦ c σ(ι x)`. -/
def fibreEquiv (σ : K →+* ℂ) : Codomain σ ⊗[𝓞 K] E ≃ₗ[ℂ] ℂ :=
  ((hι.comp (IsBaseChange.linearMap K (Codomain σ))).equiv.restrictScalars ℂ).trans
    (Codomain.equiv σ).toLinearEquiv

@[simp]
theorem fibreEquiv_tmul (σ : K →+* ℂ) (c : Codomain σ) (x : E) :
    fibreEquiv hι σ (c ⊗ₜ x) = Codomain.equiv σ c * σ (ι x) := by
  rw [fibreEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    IsBaseChange.equiv_tmul]
  simp

/-- The hermitian metric `‖x‖_σ = e^{-λ_v} |σ(ι x)|`, where `v` is the place induced by `σ`, on an
`𝓞 K`-module `E` whose scalar extension to `K` is identified with `K` by `ι`. -/
def ofIsBaseChange (w : InfinitePlace K → ℝ) : HermitianMetric K E where
  form σ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun u v ↦ (Real.exp (-2 * w (InfinitePlace.mk σ)) : ℂ) *
      (conj (fibreEquiv hι σ u) * fibreEquiv hι σ v))
    (fun _ _ _ ↦ by simp only [map_add]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, smul_eq_mul, map_mul]; ring)
    (fun _ _ _ ↦ by simp only [map_add]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring)
  isSymm_form σ := LinearMap.isSymm_def.mpr fun u v ↦ by
    simp only [LinearMap.mk₂'ₛₗ_apply, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  form_self_pos σ u hu := by
    have hne : fibreEquiv hι σ u ≠ 0 :=
      fun h0 ↦ hu (((fibreEquiv hι σ).injective).eq_iff.mp (h0.trans (map_zero _).symm))
    rw [LinearMap.mk₂'ₛₗ_apply, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact Complex.zero_lt_real.mpr (mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.mpr hne) 2))
  form_conjugate_tmul σ x y := by
    simp only [LinearMap.mk₂'ₛₗ_apply, fibreEquiv_tmul, map_one, one_mul,
      conjugate_coe_eq, InfinitePlace.mk_conjugate_eq, map_mul, Complex.conj_ofReal]

variable (w : InfinitePlace K → ℝ)

theorem ofIsBaseChange_form_tmul (σ : K →+* ℂ) (x y : E) :
    (ofIsBaseChange hι w).form σ (1 ⊗ₜ x) (1 ⊗ₜ y) =
      Real.exp (-2 * w (InfinitePlace.mk σ)) * (conj (σ (ι x)) * σ (ι y)) := by
  simp [ofIsBaseChange]

/-- In the metric `ofIsBaseChange hι w`, `‖x‖_σ = e^{-λ_v} |σ(ι x)|`. -/
@[simp]
theorem norm_ofIsBaseChange_tmul (σ : K →+* ℂ) (x : E) :
    (ofIsBaseChange hι w).norm σ (1 ⊗ₜ x) =
      Real.exp (-w (InfinitePlace.mk σ)) * ‖σ (ι x)‖ := by
  have hexp : Real.exp (-2 * w (InfinitePlace.mk σ)) = Real.exp (-w (InfinitePlace.mk σ)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [HermitianMetric.norm, ofIsBaseChange_form_tmul, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re, hexp, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le (_root_.norm_nonneg _))]

@[simp]
theorem placeNorm_ofIsBaseChange (v : InfinitePlace K) (x : E) :
    (ofIsBaseChange hι w).placeNorm v x = Real.exp (-w v) * v (ι x) := by
  rw [placeNorm, norm_ofIsBaseChange_tmul, InfinitePlace.mk_embedding,
    InfinitePlace.norm_embedding_eq]

theorem rescale_ofIsBaseChange (c : ℝ) :
    (ofIsBaseChange hι w).rescale c = ofIsBaseChange hι (w + fun _ ↦ c) := by
  ext σ u v
  simp only [rescale_form_apply, ofIsBaseChange, LinearMap.mk₂'ₛₗ_apply, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, Pi.add_apply]
  ring_nf

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] {ι' : F →ₗ[𝓞 K] K}
  (hι' : IsBaseChange K ι')

/-- A linear isomorphism compatible with the embeddings into `K` is an isometry between the
metrics `ofIsBaseChange` with the same weights. -/
def isometryOfIsBaseChange (e : E ≃ₗ[𝓞 K] F) (he : ∀ x, ι' (e x) = ι x) :
    Isometry (ofIsBaseChange hι w) (ofIsBaseChange hι' w) where
  toLinearEquiv := e
  form_tmul σ x y := by rw [ofIsBaseChange_form_tmul, ofIsBaseChange_form_tmul, he, he]

@[simp]
theorem isometryOfIsBaseChange_apply (e : E ≃ₗ[𝓞 K] F) (he : ∀ x, ι' (e x) = ι x) (x : E) :
    isometryOfIsBaseChange hι w hι' e he x = e x := (rfl)

end OfIsBaseChange

section NumberField

variable (K) [NumberField K]

/-- The **trivial hermitian line** `Ō_K = (O_K, |·|)`: `‖x‖_σ = |σ(x)|` at every embedding. -/
@[expose] def trivial : HermitianMetric K (𝓞 K) :=
  ofIsBaseChange (IsLocalizedModule.isBaseChange (𝓞 K)⁰ K (Algebra.linearMap (𝓞 K) K)) 0

variable {K}

theorem trivial_form_tmul (σ : K →+* ℂ) (x y : 𝓞 K) :
    (trivial K).form σ (1 ⊗ₜ x) (1 ⊗ₜ y) = conj (σ x) * σ y := by
  simp [trivial, ofIsBaseChange_form_tmul]

/-- The trivial line has `h_σ(1, 1) = 1` at every embedding. -/
@[simp]
theorem trivial_form_one (σ : K →+* ℂ) :
    (trivial K).form σ (1 ⊗ₜ 1) (1 ⊗ₜ 1) = 1 := by
  simp [trivial_form_tmul]

@[simp]
theorem norm_trivial_tmul (σ : K →+* ℂ) (x : 𝓞 K) :
    (trivial K).norm σ (1 ⊗ₜ x) = ‖σ x‖ := by
  simp [trivial]

@[simp]
theorem placeNorm_trivial (v : InfinitePlace K) (x : 𝓞 K) :
    (trivial K).placeNorm v x = v x := by
  simp [trivial]

/-- The **hermitian line of a nonzero fractional ideal** `𝔞` with weights `λ_v` at the infinite
places: `‖x‖_σ = e^{-λ_v} |σ(x)|` for `x ∈ 𝔞`, where `v` is the place induced by `σ`. -/
@[expose] def fractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (w : InfinitePlace K → ℝ) : HermitianMetric K I :=
  ofIsBaseChange (FractionalIdeal.isBaseChange_subtype hI) w

@[simp]
theorem norm_fractionalIdeal_tmul {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (w : InfinitePlace K → ℝ) (σ : K →+* ℂ) (x : I) :
    (fractionalIdeal I hI w).norm σ (1 ⊗ₜ x) =
      Real.exp (-w (InfinitePlace.mk σ)) * ‖σ x‖ := by
  simp [fractionalIdeal]

@[simp]
theorem placeNorm_fractionalIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (w : InfinitePlace K → ℝ) (v : InfinitePlace K) (x : I) :
    (fractionalIdeal I hI w).placeNorm v x = Real.exp (-w v) * v x := by
  simp [fractionalIdeal]

end NumberField

end HermitianMetric

universe u v

/-- A **hermitian vector bundle** over `Spec 𝓞 K`: a finitely generated projective `𝓞 K`-module
with a hermitian metric. -/
structure HermitianBundle (K : Type u) [Field K] where
  /-- The underlying `𝓞 K`-module. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module (𝓞 K) carrier]
  [isFinite : Module.Finite (𝓞 K) carrier]
  [isProjective : Module.Projective (𝓞 K) carrier]
  /-- The hermitian metric. -/
  metric : HermitianMetric K carrier

namespace HermitianBundle

attribute [instance] isAddCommGroup isModule isFinite isProjective

variable {K : Type u} [Field K]

instance : CoeSort (HermitianBundle.{u, v} K) (Type v) := ⟨carrier⟩

/-- The rank of a hermitian vector bundle: the rank of its underlying `𝓞 K`-module. -/
def rank (Ē : HermitianBundle K) : ℕ := Module.finrank (𝓞 K) Ē

/-- The rank of a hermitian vector bundle is the dimension of its generic fibre `Ē ⊗ K`. -/
theorem rank_eq_finrank_tensorProduct [NumberField K] (Ē : HermitianBundle K) :
    Ē.rank = Module.finrank K (K ⊗[𝓞 K] Ē) := by
  have : IsLocalizedModule (𝓞 K)⁰ (TensorProduct.mk (𝓞 K) K Ē 1) :=
    (isLocalizedModule_iff_isBaseChange (𝓞 K)⁰ K _).mpr (TensorProduct.isBaseChange _ _ _)
  rw [rank, IsFractionRing.finrank_right_eq (R := 𝓞 K) (S := K),
    IsLocalizedModule.finrank_eq (𝓞 K)⁰ (TensorProduct.mk (𝓞 K) K Ē 1) le_rfl]

variable (K)

/-- The **trivial hermitian line bundle** `Ō_K = (O_K, |·|)`. -/
@[expose] def trivial [NumberField K] : HermitianBundle.{u, u} K where
  carrier := 𝓞 K
  metric := HermitianMetric.trivial K

@[simp]
theorem rank_trivial [NumberField K] : (trivial K).rank = 1 :=
  Module.finrank_self (𝓞 K)

/-- The **zero hermitian vector bundle**, the zero module with the empty family of forms. -/
@[expose] def zero : HermitianBundle.{u, v} K where
  carrier := PUnit
  metric := default

@[simp]
theorem rank_zero : (zero.{u, v} K).rank = 0 :=
  Module.finrank_zero_of_subsingleton (M := PUnit.{v + 1})

end HermitianBundle

end TauCeti
