/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.NumberTheory.NumberField.ComplexEmbedding.Codomain
public import TauCeti.RingTheory.FractionalIdeal.BaseChange
public import TauCeti.RingTheory.FractionalIdeal.LinearEquiv

import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Hermitian vector bundles over the ring of integers of a number field

Let `K` be a number field with ring of integers `O_K`. A hermitian vector bundle over `Spec O_K`
is a finitely generated projective `O_K`-module `E` together with, for every complex embedding
`σ : K → ℂ`, a positive definite hermitian form `h_σ` on the complex fibre `E ⊗_{O_K,σ} ℂ`, such
that `h_{conj σ}(1 ⊗ x, 1 ⊗ y)` is the complex conjugate of `h_σ(1 ⊗ x, 1 ⊗ y)` for `x, y ∈ E`,
where `conj σ` is the complex conjugate embedding. At a real embedding this says that `h_σ` is the
complexification of a real inner product. The Arakelov degree of these objects computes
heights of points, and the Hodge line of an abelian variety with its Faltings metric is one of
them.

To form the fibre `E ⊗_{O_K,σ} ℂ` for every `σ` at once, the fibre at `σ` is the scalar
extension `Codomain σ ⊗[𝓞 K] E`, a complex vector space, where
`NumberField.ComplexEmbedding.Codomain σ` is a copy of `ℂ` carrying the `K`-algebra structure
given by `σ`. The hermitian forms are complex sesquilinear forms on these fibres,
conjugate-linear in the first argument as in Mathlib.

## Main definitions

* `TauCeti.HermitianMetric K E`: a hermitian metric on an `𝓞 K`-module `E`, a family of positive
  definite hermitian forms on the complex fibres compatible with complex conjugation of the
  embeddings.
* `TauCeti.HermitianMetric.toCore`: the form at `σ` as an inner product core on the complex
  fibre at `σ`.
* `TauCeti.HermitianMetric.norm`: the norm `‖u‖_σ` of a vector in the complex fibre at `σ`.
* `TauCeti.HermitianMetric.fiberConj`: complex conjugation `c ⊗ x ↦ conj c ⊗ x` from the complex
  fibre at `σ` to the one at `conj σ`; it is antiunitary
  (`TauCeti.HermitianMetric.form_fiberConj`).
* `TauCeti.HermitianMetric.placeNorm`: the norm `‖x‖_v` of `x ∈ E` at an infinite place `v`,
  computed at either complex embedding inducing `v` (`TauCeti.HermitianMetric.placeNorm_mk`).
* `TauCeti.HermitianMetric.rescale`: the metric `Ē(c)` with all norms multiplied by `e^{-c}`.
* `TauCeti.HermitianMetric.IsometryEquiv`: an `𝓞 K`-linear isomorphism whose complexifications
  are unitary at every embedding.
* `TauCeti.HermitianMetric.ofIsBaseChange`: the metric `‖x‖_σ = e^{-λ_v} |σ(ι x)|` on an
  `𝓞 K`-module `E` whose scalar extension to `K` is identified with `K` by `ι`, for real weights
  `λ_v` indexed by the infinite places.
* `TauCeti.HermitianMetric.trivial`: the trivial hermitian line `Ō_K = (O_K, |·|)`.
* `TauCeti.HermitianMetric.fractionalIdeal`: the hermitian line `(𝔞, e^{-λ_v} |·|_v)` of a
  nonzero fractional ideal `𝔞`; `TauCeti.HermitianMetric.isometryEquivTrivialFractionalIdealOne`
  identifies the line of `(1)` with zero weights with `Ō_K`.
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

/-- The hermitian form `h_σ` as an inner product core on the complex fibre at `σ`. Its norm is
`HermitianMetric.norm`, whose basic properties come from this core. -/
@[instance_reducible]
def toCore (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (Codomain σ ⊗[𝓞 K] E) where
  inner u v := h.form σ u v
  conj_inner_symm u v := h.conj_form σ v u
  re_inner_nonneg u := (Complex.nonneg_iff.mp (h.form_self_nonneg σ u)).1
  add_left u v w := by simp only [map_add, LinearMap.add_apply]
  smul_left u v r := by simp only [LinearMap.map_smulₛₗ₂, smul_eq_mul]
  definite _ hu := h.form_self_eq_zero_iff.mp hu

/-- The inner product of the core `h.toCore σ` is the form `h_σ`. -/
@[simp]
theorem inner_toCore (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    @inner ℂ _ (h.toCore σ).toInner u v = h.form σ u v :=
  (rfl)

/-- The norm `‖u‖_σ = h_σ(u, u)^{1/2}` of a vector in the complex fibre at `σ`, the norm of the
inner product core `h.toCore σ`. -/
protected def norm (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) : ℝ :=
  letI := h.toCore σ
  (InnerProductSpace.Core.toNorm (𝕜 := ℂ)).norm u

theorem norm_def (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.norm σ u = √(h.form σ u u).re := (rfl)

/-- Complex scalars come out of the form on pure tensors: conjugate-linearly on the left and
linearly on the right. -/
theorem form_tmul_tmul (σ : K →+* ℂ) (c d : Codomain σ) (x y : E) :
    h.form σ (c ⊗ₜ x) (d ⊗ₜ y) =
      conj (Codomain.equiv σ c) * Codomain.equiv σ d * h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  rw [Codomain.tmul_eq_smul σ c, Codomain.tmul_eq_smul σ d, LinearMap.map_smulₛₗ₂, map_smul,
    smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The normed group structure on the complex fibre at `σ` given by the core `h.toCore σ`, whose
norm is `HermitianMetric.norm`; used locally to read off the norm axioms. -/
private abbrev normedAddCommGroup (σ : K →+* ℂ) : NormedAddCommGroup (Codomain σ ⊗[𝓞 K] E) :=
  letI := h.toCore σ
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The norm at `σ` is the norm of `h.normedAddCommGroup σ`. This holds by definition: Mathlib
builds `InnerProductSpace.Core.toNormedAddCommGroup` from the same square root `√(re ⟪u, u⟫)` that
defines `InnerProductSpace.Core.toNorm`. The norm axioms below are read off through this bridge. -/
private theorem norm_eq_normedAddCommGroup (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.norm σ u = (h.normedAddCommGroup σ).norm u :=
  rfl

theorem norm_nonneg (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) : 0 ≤ h.norm σ u := by
  let := h.normedAddCommGroup σ
  rw [norm_eq_normedAddCommGroup]
  exact (h.toCore σ).toNormedSpaceCore.norm_nonneg u

theorem form_self_eq_norm_sq (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.form σ u u = ((h.norm σ u ^ 2 : ℝ) : ℂ) := by
  have hnn := Complex.nonneg_iff.mp (h.form_self_nonneg σ u)
  rw [norm_def, Real.sq_sqrt hnn.1]
  exact Complex.ext (by simp) (by simpa using hnn.2.symm)

theorem norm_sq (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.norm σ u ^ 2 = (h.form σ u u).re := by
  rw [h.form_self_eq_norm_sq, Complex.ofReal_re]

/-- Orthogonality for the form at `σ` is symmetric. -/
theorem form_eq_zero_symm {σ : K →+* ℂ} {u v : Codomain σ ⊗[𝓞 K] E} :
    h.form σ u v = 0 ↔ h.form σ v u = 0 := by
  rw [← h.conj_form σ v u, map_eq_zero]

/-- **Pythagoras' theorem** for vectors orthogonal for the form at `σ`. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_form_eq_zero {σ : K →+* ℂ}
    {u v : Codomain σ ⊗[𝓞 K] E} (huv : h.form σ u v = 0) :
    h.norm σ (u + v) ^ 2 = h.norm σ u ^ 2 + h.norm σ v ^ 2 := by
  simp only [norm_sq, map_add, LinearMap.add_apply, huv, h.form_eq_zero_symm.mp huv, add_zero,
    zero_add, Complex.add_re]

@[simp]
theorem norm_eq_zero_iff {σ : K →+* ℂ} {u : Codomain σ ⊗[𝓞 K] E} : h.norm σ u = 0 ↔ u = 0 := by
  let := h.normedAddCommGroup σ
  rw [norm_eq_normedAddCommGroup]
  exact (h.toCore σ).toNormedSpaceCore.norm_eq_zero_iff u

theorem norm_pos {σ : K →+* ℂ} {u : Codomain σ ⊗[𝓞 K] E} (hu : u ≠ 0) : 0 < h.norm σ u :=
  (h.norm_nonneg σ u).lt_of_ne' (by simpa using hu)

@[simp]
theorem norm_zero (σ : K →+* ℂ) : h.norm σ 0 = 0 := by simp

theorem norm_smul (σ : K →+* ℂ) (c : ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    h.norm σ (c • u) = ‖c‖ * h.norm σ u := by
  let := h.normedAddCommGroup σ
  rw [norm_eq_normedAddCommGroup, norm_eq_normedAddCommGroup]
  exact (h.toCore σ).toNormedSpaceCore.norm_smul c u

/-- The triangle inequality for the norm at `σ`. -/
theorem norm_add_le (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    h.norm σ (u + v) ≤ h.norm σ u + h.norm σ v := by
  let := h.normedAddCommGroup σ
  simp only [norm_eq_normedAddCommGroup]
  exact (h.toCore σ).toNormedSpaceCore.norm_triangle u v

/-- The Cauchy–Schwarz inequality for the form at `σ`. -/
theorem norm_form_le (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    ‖h.form σ u v‖ ≤ h.norm σ u * h.norm σ v :=
  letI := h.toCore σ
  InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) u v

/-- At the complex conjugate embedding, vectors of `E` have the same norm. -/
@[simp]
theorem norm_conjugate_tmul (σ : K →+* ℂ) (x : E) :
    h.norm (conjugate σ) (1 ⊗ₜ x) = h.norm σ (1 ⊗ₜ x) := by
  rw [norm_def, norm_def, h.form_conjugate_tmul, Complex.conj_re]

/-- At a real embedding, the form takes real values on vectors of `E`: it is the
complexification of a real inner product on `E ⊗_σ ℝ`. -/
theorem conj_form_tmul_of_isReal {σ : K →+* ℂ} (hσ : IsReal σ) (x y : E) :
    conj (h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y)) = h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  rw [← h.form_conjugate_tmul]
  have hc : conjugate σ = σ := isReal_iff.mp hσ
  -- The type of `h.form τ` depends on `τ`, so `rw [hc]` cannot rewrite `conjugate σ` to `σ`;
  -- generalizing `conjugate σ` and substituting rewrites the form and its type together.
  generalize conjugate σ = τ at hc ⊢
  subst hc
  rfl

/-! ### Complex conjugation of fibres -/

section FiberConj

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F]

variable (E) in
/-- Complex conjugation `c ⊗ x ↦ conj c ⊗ x` from the complex fibre `E_σ` to `E_{conj σ}`: it
fixes the vectors `1 ⊗ x` of `E` and is conjugate-linear (`fiberConj_smul`). -/
def fiberConj (σ : K →+* ℂ) :
    Codomain σ ⊗[𝓞 K] E →ₗ[𝓞 K] Codomain (conjugate σ) ⊗[𝓞 K] E :=
  (Codomain.conj σ).rTensor E

@[simp]
theorem fiberConj_tmul (σ : K →+* ℂ) (c : Codomain σ) (x : E) :
    fiberConj E σ (c ⊗ₜ x) = Codomain.conj σ c ⊗ₜ x :=
  LinearMap.rTensor_tmul _ _ _ _

theorem fiberConj_one_tmul (σ : K →+* ℂ) (x : E) :
    fiberConj E σ ((1 : Codomain σ) ⊗ₜ x) = 1 ⊗ₜ x := by
  simp

/-- Complex conjugation of fibres is conjugate-linear. -/
@[simp]
theorem fiberConj_smul (σ : K →+* ℂ) (c : ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    fiberConj E σ (c • u) = conj c • fiberConj E σ u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => rw [smul_add, map_add, hu, hv, map_add, smul_add]
  | tmul d x =>
    rw [TensorProduct.smul_tmul', fiberConj_tmul, fiberConj_tmul, TensorProduct.smul_tmul']
    congr 1
    apply (Codomain.equiv (conjugate σ)).injective
    simp

/-- Complex conjugation of fibres commutes with the complexification of linear maps. -/
theorem fiberConj_baseChange (σ : K →+* ℂ) (f : F →ₗ[𝓞 K] E) (u : Codomain σ ⊗[𝓞 K] F) :
    fiberConj E σ (f.baseChange (Codomain σ) u) =
      f.baseChange (Codomain (conjugate σ)) (fiberConj F σ u) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul d x => simp

/-- Complex conjugation of fibres is antiunitary: the form at `conj σ` of the conjugates
of `u, v` is `conj h_σ(u, v)`. -/
theorem form_fiberConj (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    h.form (conjugate σ) (fiberConj E σ u) (fiberConj E σ v) = conj (h.form σ u v) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul c x =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul d y =>
      simp [h.form_tmul_tmul σ c d, h.form_tmul_tmul (conjugate σ) (Codomain.conj σ c),
        h.form_conjugate_tmul]

end FiberConj

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

/-- The zero module carries exactly one hermitian metric, the zero form on every (zero) fibre. -/
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

/-- `√(e^{-2c} a) = e^{-c} √a`: multiplying a form by `e^{-2c}` multiplies its norm by `e^{-c}`. -/
private theorem sqrt_exp_neg_two_mul_mul (c a : ℝ) :
    √(Real.exp (-2 * c) * a) = Real.exp (-c) * √a := by
  rw [Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half, show -2 * c / 2 = -c by ring]

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
  rw [norm_def, norm_def, rescale_form_apply, Complex.re_ofReal_mul, sqrt_exp_neg_two_mul_mul]

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
  rw [show -2 * d + -2 * c = -2 * (c + d) by ring]

/-! ### Isometries -/

variable {F G : Type*} [AddCommGroup F] [Module (𝓞 K) F] [AddCommGroup G] [Module (𝓞 K) G]

/-- An **isometry** between hermitian metrics: an `𝓞 K`-linear isomorphism `E ≃ F` whose
complexification is unitary at every complex embedding. Unitarity is tested on vectors of `E`;
`HermitianMetric.IsometryEquiv.form_toLinearMap_baseChange` gives it on the whole complex
fibre. -/
structure IsometryEquiv (h : HermitianMetric K E) (h' : HermitianMetric K F)
    extends E ≃ₗ[𝓞 K] F where
  /-- The linear isomorphism preserves the hermitian forms. -/
  form_tmul (σ : K →+* ℂ) (x y : E) :
    h'.form σ (1 ⊗ₜ toLinearEquiv x) (1 ⊗ₜ toLinearEquiv y) = h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y)

namespace IsometryEquiv

variable {h} {h' : HermitianMetric K F} {h'' : HermitianMetric K G}

instance : EquivLike (IsometryEquiv h h') E F where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' e e' he _ := by
    obtain ⟨e, _⟩ := e
    obtain ⟨e', _⟩ := e'
    congr
    exact LinearEquiv.coe_injective he

instance : LinearEquivClass (IsometryEquiv h h') (𝓞 K) E F where
  map_add e := map_add e.toLinearEquiv
  map_smulₛₗ e := map_smulₛₗ e.toLinearEquiv

@[simp]
theorem coe_toLinearEquiv (e : IsometryEquiv h h') : ⇑e.toLinearEquiv = e := rfl

/-- Two isometries with the same underlying map are equal. -/
@[ext]
theorem ext {e e' : IsometryEquiv h h'} (he : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ he

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : IsometryEquiv h h' → E ≃ₗ[𝓞 K] F) := fun _ _ he ↦
  ext fun x ↦ congr($he x)

/-- An isometry preserves the hermitian forms on the whole complex fibre. -/
theorem form_toLinearMap_baseChange (e : IsometryEquiv h h') (σ : K →+* ℂ)
    (u v : Codomain σ ⊗[𝓞 K] E) :
    h'.form σ (e.toLinearMap.baseChange (Codomain σ) u)
        (e.toLinearMap.baseChange (Codomain σ) v) = h.form σ u v := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul c x =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul d y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h'.form_tmul_tmul,
        h.form_tmul_tmul, LinearEquiv.coe_coe, e.form_tmul]

theorem norm_toLinearMap_baseChange (e : IsometryEquiv h h') (σ : K →+* ℂ)
    (u : Codomain σ ⊗[𝓞 K] E) :
    h'.norm σ (e.toLinearMap.baseChange (Codomain σ) u) = h.norm σ u := by
  rw [norm_def, norm_def, e.form_toLinearMap_baseChange]

@[simp]
theorem form_tmul_map (e : IsometryEquiv h h') (σ : K →+* ℂ) (x y : E) :
    h'.form σ (1 ⊗ₜ e x) (1 ⊗ₜ e y) = h.form σ (1 ⊗ₜ x) (1 ⊗ₜ y) :=
  e.form_tmul σ x y

@[simp]
theorem norm_tmul_map (e : IsometryEquiv h h') (σ : K →+* ℂ) (x : E) :
    h'.norm σ (1 ⊗ₜ e x) = h.norm σ (1 ⊗ₜ x) := by
  rw [norm_def, norm_def, e.form_tmul_map]

@[simp]
theorem placeNorm_map (e : IsometryEquiv h h') (v : InfinitePlace K) (x : E) :
    h'.placeNorm v (e x) = h.placeNorm v x :=
  e.norm_tmul_map _ x

variable (h) in
/-- The identity isometry. -/
@[refl]
def refl : IsometryEquiv h h where
  toLinearEquiv := LinearEquiv.refl (𝓞 K) E
  form_tmul _ _ _ := rfl

/-- The inverse of an isometry. -/
@[symm]
def symm (e : IsometryEquiv h h') : IsometryEquiv h' h where
  toLinearEquiv := e.toLinearEquiv.symm
  form_tmul σ x y := by
    rw [← e.form_tmul σ]
    simp

/-- The composite of two isometries. -/
@[trans]
def trans (e : IsometryEquiv h h') (e' : IsometryEquiv h' h'') : IsometryEquiv h h'' where
  toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
  form_tmul σ x y := by
    simp only [LinearEquiv.trans_apply]
    rw [e'.form_tmul, e.form_tmul]

@[simp]
theorem refl_apply (x : E) : refl h x = x := (rfl)

@[simp]
theorem symm_apply_apply (e : IsometryEquiv h h') (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (e : IsometryEquiv h h') (x : F) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

@[simp]
theorem trans_apply (e : IsometryEquiv h h') (e' : IsometryEquiv h' h'') (x : E) :
    e.trans e' x = e' (e x) := (rfl)

@[simp]
theorem toLinearEquiv_refl : (refl h).toLinearEquiv = LinearEquiv.refl (𝓞 K) E := (rfl)

@[simp]
theorem toLinearEquiv_symm (e : IsometryEquiv h h') : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  (rfl)

@[simp]
theorem toLinearEquiv_trans (e : IsometryEquiv h h') (e' : IsometryEquiv h' h'') :
    (e.trans e').toLinearEquiv = e.toLinearEquiv.trans e'.toLinearEquiv := (rfl)

end IsometryEquiv

/-! ### Hermitian lines inside `K` -/

section OfIsBaseChange

variable {ι : E →ₗ[𝓞 K] K} (hι : IsBaseChange K ι)

/-- For `ι : E → K` identifying the scalar extension of `E` to `K` with `K`, the complex fibre of
`E` at `σ` is `ℂ`, through `c ⊗ x ↦ c σ(ι x)`. -/
def fiberEquiv (σ : K →+* ℂ) : Codomain σ ⊗[𝓞 K] E ≃ₗ[ℂ] ℂ :=
  ((hι.comp (IsBaseChange.linearMap K (Codomain σ))).equiv.restrictScalars ℂ).trans
    (Codomain.equiv σ).toLinearEquiv

@[simp]
theorem fiberEquiv_tmul (σ : K →+* ℂ) (c : Codomain σ) (x : E) :
    fiberEquiv hι σ (c ⊗ₜ x) = Codomain.equiv σ c * σ (ι x) := by
  rw [fiberEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    IsBaseChange.equiv_tmul]
  simp

/-- The hermitian metric `‖x‖_σ = e^{-λ_v} |σ(ι x)|`, where `v` is the place induced by `σ`, on an
`𝓞 K`-module `E` whose scalar extension to `K` is identified with `K` by `ι`. -/
def ofIsBaseChange (w : InfinitePlace K → ℝ) : HermitianMetric K E where
  form σ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun u v ↦ (Real.exp (-2 * w (InfinitePlace.mk σ)) : ℂ) *
      (conj (fiberEquiv hι σ u) * fiberEquiv hι σ v))
    (fun _ _ _ ↦ by simp only [map_add]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, smul_eq_mul, map_mul]; ring)
    (fun _ _ _ ↦ by simp only [map_add]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring)
  isSymm_form σ := LinearMap.isSymm_def.mpr fun u v ↦ by
    simp only [LinearMap.mk₂'ₛₗ_apply, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  form_self_pos σ u hu := by
    have hne := (fiberEquiv hι σ).map_ne_zero_iff.mpr hu
    rw [LinearMap.mk₂'ₛₗ_apply, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact Complex.zero_lt_real.mpr (mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.mpr hne) 2))
  form_conjugate_tmul σ x y := by
    simp only [LinearMap.mk₂'ₛₗ_apply, fiberEquiv_tmul, map_one, one_mul,
      conjugate_coe_eq, InfinitePlace.mk_conjugate_eq, map_mul, Complex.conj_ofReal]

variable (w : InfinitePlace K → ℝ)

@[simp]
theorem ofIsBaseChange_form_apply (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] E) :
    (ofIsBaseChange hι w).form σ u v =
      Real.exp (-2 * w (InfinitePlace.mk σ)) * (conj (fiberEquiv hι σ u) * fiberEquiv hι σ v) :=
  (rfl)

/-- The form of `ofIsBaseChange hι w` on vectors of `E`. This is not `@[simp]`: `simp` proves it
from `ofIsBaseChange_form_apply` and `fiberEquiv_tmul`. -/
theorem ofIsBaseChange_form_tmul (σ : K →+* ℂ) (x y : E) :
    (ofIsBaseChange hι w).form σ (1 ⊗ₜ x) (1 ⊗ₜ y) =
      Real.exp (-2 * w (InfinitePlace.mk σ)) * (conj (σ (ι x)) * σ (ι y)) := by
  simp

/-- In the metric `ofIsBaseChange hι w`, `‖x‖_σ = e^{-λ_v} |σ(ι x)|`. -/
@[simp]
theorem norm_ofIsBaseChange_tmul (σ : K →+* ℂ) (x : E) :
    (ofIsBaseChange hι w).norm σ (1 ⊗ₜ x) =
      Real.exp (-w (InfinitePlace.mk σ)) * ‖σ (ι x)‖ := by
  rw [norm_def, ofIsBaseChange_form_tmul]
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re,
    sqrt_exp_neg_two_mul_mul, Real.sqrt_sq (_root_.norm_nonneg _)]

@[simp]
theorem placeNorm_ofIsBaseChange (v : InfinitePlace K) (x : E) :
    (ofIsBaseChange hι w).placeNorm v x = Real.exp (-w v) * v (ι x) := by
  rw [placeNorm, norm_ofIsBaseChange_tmul, InfinitePlace.mk_embedding,
    InfinitePlace.norm_embedding_eq]

theorem rescale_ofIsBaseChange (c : ℝ) :
    (ofIsBaseChange hι w).rescale c = ofIsBaseChange hι (w + fun _ ↦ c) := by
  ext σ u v
  simp only [rescale_form_apply, ofIsBaseChange_form_apply, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add, Pi.add_apply]
  rw [show -2 * c + -2 * w (InfinitePlace.mk σ) = -2 * (w (InfinitePlace.mk σ) + c) by ring]

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] {ι' : F →ₗ[𝓞 K] K}
  (hι' : IsBaseChange K ι')

/-- A linear isomorphism compatible with the embeddings into `K` is an isometry between the
metrics `ofIsBaseChange` with the same weights. -/
def isometryEquivOfIsBaseChange (e : E ≃ₗ[𝓞 K] F) (he : ∀ x, ι' (e x) = ι x) :
    IsometryEquiv (ofIsBaseChange hι w) (ofIsBaseChange hι' w) where
  toLinearEquiv := e
  form_tmul σ x y := by rw [ofIsBaseChange_form_tmul, ofIsBaseChange_form_tmul, he, he]

@[simp]
theorem isometryEquivOfIsBaseChange_apply (e : E ≃ₗ[𝓞 K] F) (he : ∀ x, ι' (e x) = ι x) (x : E) :
    isometryEquivOfIsBaseChange hι w hι' e he x = e x := (rfl)

end OfIsBaseChange

section NumberField

variable (K) [NumberField K]

/-- The **trivial hermitian line** `Ō_K = (O_K, |·|)`: `‖x‖_σ = |σ(x)|` at every embedding. -/
def trivial : HermitianMetric K (𝓞 K) :=
  ofIsBaseChange (IsLocalizedModule.isBaseChange (𝓞 K)⁰ K (Algebra.linearMap (𝓞 K) K)) 0

theorem trivial_def :
    trivial K =
      ofIsBaseChange (IsLocalizedModule.isBaseChange (𝓞 K)⁰ K (Algebra.linearMap (𝓞 K) K)) 0 :=
  (rfl)

variable {K}

@[simp]
theorem trivial_form_tmul (σ : K →+* ℂ) (x y : 𝓞 K) :
    (trivial K).form σ (1 ⊗ₜ x) (1 ⊗ₜ y) = conj (σ x) * σ y := by
  simp [trivial]

/-- The trivial line has `h_σ(1, 1) = 1` at every embedding. -/
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
def fractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (w : InfinitePlace K → ℝ) : HermitianMetric K I :=
  ofIsBaseChange (FractionalIdeal.isBaseChange_subtype hI) w

theorem fractionalIdeal_def (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (w : InfinitePlace K → ℝ) :
    fractionalIdeal I hI w = ofIsBaseChange (FractionalIdeal.isBaseChange_subtype hI) w :=
  (rfl)

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

variable (K) in
/-- The hermitian line of the unit ideal `(1)` with all weights zero is isometric to `Ō_K`, through
the identification of `O_K` with `(1)`. -/
def isometryEquivTrivialFractionalIdealOne :
    IsometryEquiv (trivial K) (fractionalIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) one_ne_zero 0) :=
  isometryEquivOfIsBaseChange _ 0 _ (FractionalIdeal.linearEquivOne (𝓞 K)⁰ K) fun x ↦ by
    rw [Submodule.subtype_apply, FractionalIdeal.coe_linearEquivOne_apply,
      Algebra.linearMap_apply]

@[simp]
theorem isometryEquivTrivialFractionalIdealOne_apply (x : 𝓞 K) :
    (isometryEquivTrivialFractionalIdealOne K x : K) = x :=
  (congrArg Subtype.val (isometryEquivOfIsBaseChange_apply _ _ _ _ _ x)).trans
    (FractionalIdeal.coe_linearEquivOne_apply x)

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

theorem rank_def (Ē : HermitianBundle K) : Ē.rank = Module.finrank (𝓞 K) Ē := (rfl)

/-- The rank of a hermitian vector bundle is the dimension of its generic fibre `Ē ⊗ K`. -/
theorem rank_eq_finrank_tensorProduct (Ē : HermitianBundle K) :
    Ē.rank = Module.finrank K (K ⊗[𝓞 K] Ē) :=
  (TensorProduct.isBaseChange (𝓞 K) Ē K).finrank_eq.symm

variable (K)

/-- The **trivial hermitian line bundle** `Ō_K = (O_K, |·|)`. -/
@[expose] def trivial [NumberField K] : HermitianBundle.{u, u} K where
  carrier := 𝓞 K
  metric := HermitianMetric.trivial K

@[simp]
theorem rank_trivial [NumberField K] : (trivial K).rank = 1 :=
  Module.finrank_self (𝓞 K)

/-- The **zero hermitian vector bundle**, the zero module with the zero form on every (zero)
fibre. -/
@[expose] def zero : HermitianBundle.{u, v} K where
  carrier := PUnit
  metric := default

@[simp]
theorem rank_zero : (zero.{u, v} K).rank = 0 :=
  Module.finrank_zero_of_subsingleton (M := PUnit.{v + 1})

end HermitianBundle

end TauCeti
