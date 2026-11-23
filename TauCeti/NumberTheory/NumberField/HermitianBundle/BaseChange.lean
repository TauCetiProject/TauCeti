/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic

/-!
# Base change of hermitian vector bundles along a field extension

Let `L/K` be an extension of fields and `Ē = (E, (h_σ)_σ)` a hermitian vector bundle over
`Spec 𝓞 K`. Its base change `Ē_{𝓞 L}` is the `𝓞 L`-module `𝓞 L ⊗_{𝓞 K} E` with, at a complex
embedding `τ : L → ℂ`, the form `h_{τ|K}` of the restriction `τ|K = τ ∘ (K → L)`. This uses the
identification of the complex fibres

`ℂ ⊗_{𝓞 L, τ} (𝓞 L ⊗_{𝓞 K} E) ≅ ℂ ⊗_{𝓞 K, τ|K} E`, `c ⊗ (a ⊗ x) ↦ c τ(a) ⊗ x`,

which is Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange`. The conjugation
condition holds because the conjugate of `τ|K` is the restriction of the conjugate of `τ`.

## Main declarations

* `TauCeti.HermitianMetric.baseChangeFiberEquiv`: the fibre identification above.
* `TauCeti.HermitianMetric.baseChange`: the base-changed metric `(h_{τ|K})_τ` on
  `𝓞 L ⊗_{𝓞 K} E`.
* `TauCeti.HermitianMetric.baseChangeSelf`: base change along the identity of `K` is isometric to
  the original metric, through `𝓞 K ⊗_{𝓞 K} E ≅ E`.
* `TauCeti.HermitianMetric.baseChangeBaseChange`: base change along `K → L → M` is isometric to
  base change along `K → M`, through `𝓞 M ⊗_{𝓞 L} (𝓞 L ⊗_{𝓞 K} E) ≅ 𝓞 M ⊗_{𝓞 K} E`.
* `TauCeti.HermitianBundle.baseChange`: the hermitian vector bundle `Ē_{𝓞 L}`, with
  `TauCeti.HermitianBundle.rank_baseChange`: base change preserves the rank.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2–A.3, p. 147.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate

namespace TauCeti

open NumberField NumberField.ComplexEmbedding

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]

namespace HermitianMetric

variable (K E) in
/-- The complex fibre at `τ : L → ℂ` of the base change `𝓞 L ⊗_{𝓞 K} E` is the complex fibre of
`E` at the restriction `τ|K`, through `c ⊗ (a ⊗ x) ↦ c τ(a) ⊗ x`. -/
def baseChangeFiberEquiv (τ : L →+* ℂ) :
    Codomain τ ⊗[𝓞 L] (𝓞 L ⊗[𝓞 K] E) ≃ₗ[ℂ] Codomain (τ.comp (algebraMap K L)) ⊗[𝓞 K] E :=
  letI : Algebra (𝓞 K) (Codomain τ) :=
    inferInstanceAs (Algebra (𝓞 K) (Codomain (τ.comp (algebraMap K L))))
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (Codomain τ) := .of_algebraMap_eq fun _ ↦ rfl
  (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (𝓞 L) (Codomain τ) (Codomain τ)
    E).restrictScalars ℂ

/-- The fibre identification sends `1 ⊗ (a ⊗ x)` to `τ(a) (1 ⊗ x)`. -/
@[simp]
theorem baseChangeFiberEquiv_one_tmul_tmul (τ : L →+* ℂ) (a : 𝓞 L) (x : E) :
    baseChangeFiberEquiv K E τ (1 ⊗ₜ (a ⊗ₜ x)) = τ a • (1 ⊗ₜ x) := by
  -- `cancelBaseChange` sends `1 ⊗ (a ⊗ x)` to `(a • 1) ⊗ x`, and `a • 1 = τ(a) • 1` in `ℂ`.
  change ((τ a : ℂ) • (1 : Codomain (τ.comp (algebraMap K L)))) ⊗ₜ[𝓞 K] x = _
  exact (TensorProduct.smul_tmul' _ _ _).symm

variable (h : HermitianMetric K E)

/-- The **base change** of a hermitian metric along `K → L`: on `𝓞 L ⊗_{𝓞 K} E`, the form at a
complex embedding `τ` of `L` is the form `h_{τ|K}` of `E` at the restriction of `τ` to `K`, through
`TauCeti.HermitianMetric.baseChangeFiberEquiv`. -/
def baseChange : HermitianMetric L (𝓞 L ⊗[𝓞 K] E) where
  form τ := ((h.form (τ.comp (algebraMap K L))).comp
    (baseChangeFiberEquiv K E τ).toLinearMap).compl₂ (baseChangeFiberEquiv K E τ).toLinearMap
  isSymm_form τ := LinearMap.isSymm_def.mpr fun u v ↦ by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h.conj_form]
  form_self_pos τ u hu := by
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] using
      h.form_self_pos _ ((baseChangeFiberEquiv K E τ).map_ne_zero_iff.mpr hu)
  form_conjugate_tmul τ x y := by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h₁, h₂]
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      | tmul b y =>
        simp only [baseChangeFiberEquiv_one_tmul_tmul, LinearMap.map_smulₛₗ₂, map_smul,
          smul_eq_mul, conjugate_coe_eq, map_mul, Complex.conj_conj]
        rw [show (conjugate τ).comp (algebraMap K L) = conjugate (τ.comp (algebraMap K L)) from
          rfl, h.form_conjugate_tmul]

@[simp]
theorem baseChange_form_apply (τ : L →+* ℂ) (u v : Codomain τ ⊗[𝓞 L] (𝓞 L ⊗[𝓞 K] E)) :
    h.baseChange.form τ u v =
      h.form (τ.comp (algebraMap K L)) (baseChangeFiberEquiv K E τ u)
        (baseChangeFiberEquiv K E τ v) :=
  (rfl)

/-- On pure tensors, `h_{𝓞 L}(a ⊗ x, b ⊗ y)` at `τ` is `conj (τ a) τ(b) h_{τ|K}(x, y)`. -/
theorem baseChange_form_tmul_tmul (τ : L →+* ℂ) (a b : 𝓞 L) (x y : E) :
    h.baseChange.form τ (1 ⊗ₜ (a ⊗ₜ x)) (1 ⊗ₜ (b ⊗ₜ y)) =
      conj (τ a) * τ b * h.form (τ.comp (algebraMap K L)) (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  simp only [baseChange_form_apply, baseChangeFiberEquiv_one_tmul_tmul, LinearMap.map_smulₛₗ₂,
    map_smul, smul_eq_mul]
  ring

/-- `‖a ⊗ x‖_τ = |τ(a)| ‖x‖_{τ|K}` in the base-changed metric. -/
@[simp]
theorem norm_baseChange_tmul_tmul (τ : L →+* ℂ) (a : 𝓞 L) (x : E) :
    h.baseChange.norm τ (1 ⊗ₜ (a ⊗ₜ x)) =
      ‖τ a‖ * h.norm (τ.comp (algebraMap K L)) (1 ⊗ₜ x) := by
  rw [norm_def, baseChange_form_apply, baseChangeFiberEquiv_one_tmul_tmul, ← norm_def,
    norm_smul]

/-- `1 ⊗ (a • x) = σ(a) (1 ⊗ x)` in the complex fibre at `σ`. -/
theorem one_tmul_smul (σ : K →+* ℂ) (a : 𝓞 K) (x : E) :
    (1 : Codomain σ) ⊗ₜ[𝓞 K] (a • x) = σ a • (1 ⊗ₜ[𝓞 K] x) := by
  rw [← TensorProduct.smul_tmul, Codomain.tmul_eq_smul, Algebra.smul_def, mul_one,
    Codomain.equiv_algebraMap_ringOfIntegers]

/-- Along the identity of `K`, the fibre identification sends `1 ⊗ z` to `1 ⊗ z'`, where `z'` is
the image of `z` under `𝓞 K ⊗_{𝓞 K} E ≅ E`. -/
private theorem baseChangeFiberEquiv_self_one_tmul (σ : K →+* ℂ) :
    ∀ z, baseChangeFiberEquiv K E (L := K) σ (1 ⊗ₜ z) = 1 ⊗ₜ TensorProduct.lid (𝓞 K) E z := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ =>
    erw [TensorProduct.tmul_add, map_add, h₁, h₂, map_add, TensorProduct.tmul_add]
  | tmul a x =>
    erw [baseChangeFiberEquiv_one_tmul_tmul, TensorProduct.lid_tmul, one_tmul_smul]
    rfl

/-- Base change along the identity of `K` is isometric to the original metric, through
`𝓞 K ⊗_{𝓞 K} E ≅ E`. -/
def baseChangeSelf : IsometryEquiv (h.baseChange (L := K)) h where
  toLinearEquiv := TensorProduct.lid (𝓞 K) E
  form_tmul σ x y := by
    rw [baseChange_form_apply, baseChangeFiberEquiv_self_one_tmul,
      baseChangeFiberEquiv_self_one_tmul]
    rfl

@[simp]
theorem baseChangeSelf_apply (x : 𝓞 K ⊗[𝓞 K] E) :
    h.baseChangeSelf x = TensorProduct.lid (𝓞 K) E x :=
  (rfl)

section Composite

variable {M : Type*} [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/-- The identification of the complex fibres of `E` at two equal embeddings. -/
private def fiberCongr {σ σ' : K →+* ℂ} (hσ : σ = σ') :
    Codomain σ ⊗[𝓞 K] E ≃ₗ[ℂ] Codomain σ' ⊗[𝓞 K] E :=
  hσ ▸ LinearEquiv.refl ℂ _

private theorem fiberCongr_smul_one_tmul {σ σ' : K →+* ℂ} (hσ : σ = σ') (c : ℂ) (x : E) :
    fiberCongr hσ (c • (1 ⊗ₜ[𝓞 K] x)) = c • (1 ⊗ₜ[𝓞 K] x) := by
  subst hσ
  rfl

private theorem form_fiberCongr {σ σ' : K →+* ℂ} (hσ : σ = σ') (u v : Codomain σ ⊗[𝓞 K] E) :
    h.form σ' (fiberCongr hσ u) (fiberCongr hσ v) = h.form σ u v := by
  subst hσ
  rfl

private theorem comp_algebraMap_comp_algebraMap (μ : M →+* ℂ) :
    (μ.comp (algebraMap L M)).comp (algebraMap K L) = μ.comp (algebraMap K M) := by
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

/-- The fibre identifications of an iterated base change agree with that of the direct base
change, through `𝓞 M ⊗_{𝓞 L} (𝓞 L ⊗_{𝓞 K} E) ≅ 𝓞 M ⊗_{𝓞 K} E`. -/
private theorem baseChangeFiberEquiv_baseChangeFiberEquiv_one_tmul (μ : M →+* ℂ)
    (z : 𝓞 M ⊗[𝓞 L] (𝓞 L ⊗[𝓞 K] E)) :
    fiberCongr (comp_algebraMap_comp_algebraMap μ)
        (baseChangeFiberEquiv K E (μ.comp (algebraMap L M))
          (baseChangeFiberEquiv L (𝓞 L ⊗[𝓞 K] E) μ (1 ⊗ₜ z))) =
      baseChangeFiberEquiv K E μ
        (1 ⊗ₜ TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (𝓞 L) (𝓞 M) (𝓞 M) E z) := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | tmul c w =>
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    | tmul a x =>
      rw [baseChangeFiberEquiv_one_tmul_tmul, map_smul, baseChangeFiberEquiv_one_tmul_tmul,
        smul_smul, fiberCongr_smul_one_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        baseChangeFiberEquiv_one_tmul_tmul]
      congr 1
      simp only [Algebra.smul_def, map_mul, RingHom.comp_apply]
      rw [mul_comm, ← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 M) M,
        IsScalarTower.algebraMap_apply (𝓞 L) L M]

/-- Base change along `K → L → M` agrees with base change along `K → M` up to canonical isometry,
through `𝓞 M ⊗_{𝓞 L} (𝓞 L ⊗_{𝓞 K} E) ≅ 𝓞 M ⊗_{𝓞 K} E`. -/
def baseChangeBaseChange :
    IsometryEquiv (h.baseChange (L := L)).baseChange (h.baseChange (L := M)) where
  toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (𝓞 L) (𝓞 M) (𝓞 M) E
  form_tmul μ z w := by
    rw [baseChange_form_apply, baseChange_form_apply, baseChange_form_apply,
      ← baseChangeFiberEquiv_baseChangeFiberEquiv_one_tmul,
      ← baseChangeFiberEquiv_baseChangeFiberEquiv_one_tmul, form_fiberCongr]

@[simp]
theorem baseChangeBaseChange_tmul (c : 𝓞 M) (a : 𝓞 L) (x : E) :
    h.baseChangeBaseChange (L := L) (M := M) (c ⊗ₜ (a ⊗ₜ x)) = (a • c) ⊗ₜ x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul _ _ _ _ _ _

end Composite

end HermitianMetric

namespace HermitianBundle

universe u v

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The **base change** `Ē_{𝓞 L}` of a hermitian vector bundle along `K → L`: the module
`𝓞 L ⊗_{𝓞 K} E` with the metric `(h_{τ|K})_τ` of `TauCeti.HermitianMetric.baseChange`. -/
@[expose] def baseChange (Ē : HermitianBundle.{u, v} K) : HermitianBundle.{u, max u v} L where
  carrier := 𝓞 L ⊗[𝓞 K] Ē
  metric := Ē.metric.baseChange

/-- Base change along an extension of fields preserves the rank: `rank Ē_{𝓞 L} = rank Ē`. -/
@[simp]
theorem rank_baseChange (Ē : HermitianBundle.{u, v} K) :
    (Ē.baseChange (L := L)).rank = Ē.rank := by
  rw [rank_def, rank_def]
  exact (TensorProduct.isBaseChange (𝓞 K) Ē (𝓞 L)).finrank_eq

end HermitianBundle

end TauCeti
