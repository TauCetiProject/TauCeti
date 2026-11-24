/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic

import TauCeti.LinearAlgebra.SesquilinearForm.Separating

/-!
# The dual of a hermitian vector bundle

Let `Ē = (E, (h_σ)_σ)` be a hermitian vector bundle over `Spec O_K`. Its dual is
`Ē^∨ = (Hom_{O_K}(E, O_K), (h^∨_σ)_σ)`, where `h^∨_σ` is the dual hermitian form on the complex
fibre of `E^∨` at `σ`.

For a finitely generated projective `𝓞 K`-module `E`, the complex fibre
`Codomain σ ⊗[𝓞 K] E^∨` of the dual is identified with the complex dual of the fibre
`Codomain σ ⊗[𝓞 K] E` by `c ⊗ f ↦ (d ⊗ x ↦ c d σ(f x))`
(`TauCeti.Module.Dual.baseChangeEvaluationEquiv`). The form `h_σ` is nondegenerate on the
finite-dimensional fibre, so every complex linear functional `φ` on the fibre is `h_σ(u_φ, ·)` for
a unique vector `u_φ` (the Riesz vector, `TauCeti.HermitianMetric.dualVector`). The dual form is
`h^∨_σ(a, b) = h_σ(u_b, u_a)`, so that the Riesz correspondence is antiunitary. Complex
conjugation `c ⊗ x ↦ conj c ⊗ x` from the fibre at `σ` to the fibre at `conj σ` carries the Riesz
vector of `1 ⊗ f` at `σ` to that at `conj σ`, which gives the conjugation condition of the dual
metric.

## Main definitions

* `TauCeti.HermitianMetric.dualPairing σ`: the scalar-extended evaluation
  `TauCeti.Module.Dual.baseChangeEvaluation`, viewed as a complex linear map from the fibre of
  `E^∨` at `σ` to the complex dual of the fibre of `E` at `σ`.
* `TauCeti.HermitianMetric.dualPairingEquiv σ`: `dualPairing σ` as a complex linear equivalence,
  for finitely generated projective `E`.
* `TauCeti.HermitianMetric.dualVector`: the Riesz vector `u_a` of an element `a` of the fibre of
  `E^∨`, characterized by `h_σ(u_a, w) = a(w)` (`TauCeti.HermitianMetric.form_dualVector`).
* `TauCeti.HermitianMetric.dual`: the dual hermitian metric on `Module.Dual (𝓞 K) E`.
* `TauCeti.HermitianMetric.isometryEquivDualDual`: the isometry `Ē ≅ Ē^∨∨` given by evaluation.
* `TauCeti.HermitianMetric.isometryEquivDualTrivial`: the isometry `Ō_K^∨ ≅ Ō_K`, `f ↦ f 1`.
* `TauCeti.HermitianBundle.dual`: the dual hermitian vector bundle.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2–A.3.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate

open NumberField NumberField.ComplexEmbedding

namespace TauCeti

namespace HermitianMetric

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (σ : K →+* ℂ)

/-! ### The fibre of the dual module -/

variable (E) in
/-- The scalar-extended evaluation `TauCeti.Module.Dual.baseChangeEvaluation` from the complex
fibre `Codomain σ ⊗[𝓞 K] E^∨` of the dual module to the complex dual of the fibre
`Codomain σ ⊗[𝓞 K] E`, viewed as a complex linear map through `Codomain.equiv σ`:
`c ⊗ f ↦ (d ⊗ x ↦ c d σ(f x))` (`TauCeti.HermitianMetric.dualPairing_tmul_tmul`). For finitely
generated projective `E` it is an equivalence (`TauCeti.HermitianMetric.dualPairingEquiv`). -/
def dualPairing :
    Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E →ₗ[ℂ] Module.Dual ℂ (Codomain σ ⊗[𝓞 K] E) :=
  LinearMap.compRight ℂ (Codomain.equiv σ).toLinearMap ∘ₗ
    LinearMap.restrictScalarsₗ ℂ (Codomain σ) (Codomain σ ⊗[𝓞 K] E) (Codomain σ) ℂ ∘ₗ
    (TauCeti.Module.Dual.baseChangeEvaluation (R := 𝓞 K) (M := E)
      (A := Codomain σ)).restrictScalars ℂ

theorem dualPairing_apply (a : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E)
    (w : Codomain σ ⊗[𝓞 K] E) :
    dualPairing E σ a w = Codomain.equiv σ (TauCeti.Module.Dual.baseChangeEvaluation a w) :=
  (rfl)

@[simp]
theorem dualPairing_tmul_tmul (c d : Codomain σ) (f : Module.Dual (𝓞 K) E) (x : E) :
    dualPairing E σ (c ⊗ₜ f) (d ⊗ₜ x) =
      Codomain.equiv σ c * (Codomain.equiv σ d * σ (f x)) := by
  rw [dualPairing_apply, TauCeti.Module.Dual.baseChangeEvaluation_tmul, map_mul, map_mul,
    Codomain.equiv_algebraMap_ringOfIntegers, mul_assoc]

/-- For finitely generated projective `E`, `dualPairing` identifies the complex fibre of `E^∨`
with the complex dual of the fibre of `E`; it is
`TauCeti.Module.Dual.baseChangeEvaluationEquiv` followed by `Codomain.equiv σ`. -/
def dualPairingEquiv [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] :
    Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E ≃ₗ[ℂ] Module.Dual ℂ (Codomain σ ⊗[𝓞 K] E) :=
  LinearEquiv.ofBijective (dualPairing E σ) <| by
    have hc (c : Codomain σ) : algebraMap ℂ (Codomain σ) (Codomain.equiv σ c) = c := by
      rw [← (Codomain.equiv σ).symm.commutes, Algebra.algebraMap_self_apply,
        AlgEquiv.symm_apply_apply]
    refine ⟨fun a b hab ↦ (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := 𝓞 K) (M := E)
      (A := Codomain σ)).injective (LinearMap.ext fun w ↦ ?_), fun φ ↦ ?_⟩
    · simpa only [TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply, dualPairing_apply,
        EmbeddingLike.apply_eq_iff_eq] using LinearMap.congr_fun hab w
    let ψ : Module.Dual (Codomain σ) (Codomain σ ⊗[𝓞 K] E) :=
      { toFun w := (Codomain.equiv σ).symm (φ w)
        map_add' _ _ := by simp only [map_add]
        map_smul' c w := by
          rw [← hc c, RingHom.id_apply, algebraMap_smul (Codomain σ) _ w, map_smul, map_smul,
            algebraMap_smul (Codomain σ)] }
    refine ⟨(TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := 𝓞 K) (M := E)
      (A := Codomain σ)).symm ψ, LinearMap.ext fun w ↦ ?_⟩
    rw [dualPairing_apply, ← TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
      LinearEquiv.apply_symm_apply]
    exact AlgEquiv.apply_symm_apply _ _

@[simp]
theorem dualPairingEquiv_apply [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
    (a : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E) : dualPairingEquiv σ a = dualPairing E σ a :=
  (rfl)

/-- Pairing the element `1 ⊗ eval x` of the fibre of the double dual with an element `b` of the
fibre of the dual is pairing `b` with `1 ⊗ x`. -/
theorem dualPairing_one_tmul_eval (x : E) (b : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E) :
    dualPairing (Module.Dual (𝓞 K) E) σ (1 ⊗ₜ Module.Dual.eval (𝓞 K) E x) b =
      dualPairing E σ b (1 ⊗ₜ x) := by
  induction b using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul z f =>
    rw [dualPairing_tmul_tmul, dualPairing_tmul_tmul, Module.Dual.eval_apply]
    simp only [map_one, one_mul]

/-! ### Complex conjugation of fibres -/

/-- Complex conjugation `Codomain σ → Codomain (conjugate σ)`, which is `𝓞 K`-linear because
`conj (σ a) = (conjugate σ) a`. -/
private def codomainConj : Codomain σ →ₗ[𝓞 K] Codomain (conjugate σ) where
  toFun z := (Codomain.equiv (conjugate σ)).symm (conj (Codomain.equiv σ z))
  map_add' _ _ := by simp only [map_add]
  map_smul' a z := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
    apply (Codomain.equiv (conjugate σ)).injective
    simp only [map_mul, AlgEquiv.apply_symm_apply, Codomain.equiv_algebraMap_ringOfIntegers,
      conjugate_coe_eq]

private theorem equiv_codomainConj (z : Codomain σ) :
    Codomain.equiv (conjugate σ) (codomainConj σ z) = conj (Codomain.equiv σ z) :=
  AlgEquiv.apply_symm_apply _ _

variable (E) in
/-- Complex conjugation `c ⊗ x ↦ conj c ⊗ x` from the complex fibre at `σ` to the complex fibre
at the conjugate embedding. -/
private def conjFiber : Codomain σ ⊗[𝓞 K] E →ₗ[𝓞 K] Codomain (conjugate σ) ⊗[𝓞 K] E :=
  (codomainConj σ).rTensor E

private theorem conjFiber_tmul (z : Codomain σ) (x : E) :
    conjFiber E σ (z ⊗ₜ x) = codomainConj σ z ⊗ₜ x :=
  (rfl)

private theorem conjFiber_surjective : Function.Surjective (conjFiber E σ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro u -
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => exact add_mem ha hb
  | tmul z x =>
    refine ⟨(Codomain.equiv σ).symm (conj (Codomain.equiv (conjugate σ) z)) ⊗ₜ x, ?_⟩
    rw [conjFiber_tmul]
    congr 1
    apply (Codomain.equiv (conjugate σ)).injective
    rw [equiv_codomainConj, AlgEquiv.apply_symm_apply, Complex.conj_conj]

private theorem dualPairing_conjFiber (f : Module.Dual (𝓞 K) E) (w : Codomain σ ⊗[𝓞 K] E) :
    dualPairing E (conjugate σ) (1 ⊗ₜ f) (conjFiber E σ w) =
      conj (dualPairing E σ (1 ⊗ₜ f) w) := by
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul z x =>
    rw [conjFiber_tmul, dualPairing_tmul_tmul, dualPairing_tmul_tmul, conjugate_coe_eq,
      equiv_codomainConj]
    simp only [map_one, one_mul, map_mul]

variable (h : HermitianMetric K E)

/-- The forms at `σ` and at the conjugate embedding are complex conjugate under conjugation of
fibres, on the whole fibre. -/
private theorem form_conjFiber (u v : Codomain σ ⊗[𝓞 K] E) :
    h.form (conjugate σ) (conjFiber E σ u) (conjFiber E σ v) = conj (h.form σ u v) := by
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul z x =>
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul w y =>
      rw [conjFiber_tmul, conjFiber_tmul, h.form_tmul_tmul (conjugate σ), h.form_tmul_tmul σ,
        form_conjugate_tmul]
      simp only [equiv_codomainConj, map_mul, Complex.conj_conj]

/-! ### Riesz vectors -/

/-- On a finite-dimensional complex fibre, the positive definite form `h_σ` identifies the fibre
conjugate-linearly with its complex dual, `u ↦ h_σ(u, ·)`. -/
theorem form_bijective [Module.Finite (𝓞 K) E] : Function.Bijective (h.form σ) := by
  have : Module.Finite ℂ (Codomain σ) := inferInstanceAs (Module.Finite ℂ ℂ)
  have : Module.Finite ℂ (Codomain σ ⊗[𝓞 K] E) := Module.Finite.trans (Codomain σ) _
  exact LinearMap.bijective_of_apply_self_ne_zero fun _ hu h0 ↦ hu (h.form_self_eq_zero_iff.1 h0)

variable [Module.Finite (𝓞 K) E]

/-- The **Riesz vector** `u_a` of an element `a` of the complex fibre of `E^∨` at `σ`: the unique
vector of the fibre of `E` with `h_σ(u_a, w) = a(w)` for every `w`
(`TauCeti.HermitianMetric.form_dualVector`, `TauCeti.HermitianMetric.dualVector_eq_iff`). It is
conjugate-linear in `a`. -/
def dualVector :
    Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E →ₗ⋆[ℂ] Codomain σ ⊗[𝓞 K] E :=
  (LinearEquiv.ofBijective (h.form σ) (h.form_bijective σ)).symm.toLinearMap.comp
    (dualPairing E σ)

theorem dualVector_def :
    h.dualVector σ = (LinearEquiv.ofBijective (h.form σ) (h.form_bijective σ)).symm.toLinearMap.comp
      (dualPairing E σ) :=
  (rfl)

theorem dualVector_eq_iff {a : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E}
    {x : Codomain σ ⊗[𝓞 K] E} : h.dualVector σ a = x ↔ h.form σ x = dualPairing E σ a := by
  rw [dualVector, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  exact eq_comm

@[simp]
theorem form_dualVector (a : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E)
    (w : Codomain σ ⊗[𝓞 K] E) : h.form σ (h.dualVector σ a) w = dualPairing E σ a w :=
  congrArg (· w) ((h.dualVector_eq_iff σ).1 rfl)

theorem dualVector_injective [Module.Projective (𝓞 K) E] :
    Function.Injective (h.dualVector σ) :=
  (LinearEquiv.ofBijective (h.form σ) (h.form_bijective σ)).symm.injective.comp
    (dualPairingEquiv σ).injective

/-- Conjugation of fibres carries the Riesz vector of `1 ⊗ f` at `σ` to the Riesz vector of
`1 ⊗ f` at the conjugate embedding. -/
private theorem dualVector_conjugate (f : Module.Dual (𝓞 K) E) :
    h.dualVector (conjugate σ) (1 ⊗ₜ f) = conjFiber E σ (h.dualVector σ (1 ⊗ₜ f)) := by
  rw [dualVector_eq_iff]
  ext w'
  obtain ⟨w, rfl⟩ := conjFiber_surjective σ w'
  rw [h.form_conjFiber, form_dualVector, dualPairing_conjFiber]

/-! ### The dual metric -/

variable [Module.Projective (𝓞 K) E]

/-- The **dual hermitian metric** on `E^∨ = Module.Dual (𝓞 K) E` of a hermitian metric on a
finitely generated projective `𝓞 K`-module: `h^∨_σ(a, b) = h_σ(u_b, u_a)` for the Riesz vectors
`u_a, u_b` (`TauCeti.HermitianMetric.dual_form_apply`), so that `a ↦ u_a` is antiunitary. -/
def dual : HermitianMetric K (Module.Dual (𝓞 K) E) where
  form σ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun a b ↦ h.form σ (h.dualVector σ b) (h.dualVector σ a))
    (fun _ _ _ ↦ by simp only [map_add])
    (fun _ _ _ ↦ by simp only [map_smulₛₗ, smul_eq_mul, RingHom.id_apply])
    (fun _ _ _ ↦ by simp only [map_add, LinearMap.add_apply])
    (fun _ _ _ ↦ by
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
        Complex.conj_conj])
  isSymm_form σ := LinearMap.isSymm_def.mpr fun a b ↦ by
    simp only [LinearMap.mk₂'ₛₗ_apply, conj_form]
  form_self_pos σ a ha := by
    simpa only [LinearMap.mk₂'ₛₗ_apply] using
      h.form_self_pos σ ((map_ne_zero_iff _ (h.dualVector_injective σ)).2 ha)
  form_conjugate_tmul σ f g := by
    simp only [LinearMap.mk₂'ₛₗ_apply, dualVector_conjugate, form_conjFiber]

@[simp]
theorem dual_form_apply (a b : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E) :
    h.dual.form σ a b = h.form σ (h.dualVector σ b) (h.dualVector σ a) :=
  (rfl)

/-- The Riesz vector, for `h`, of the element of the fibre of `E^∨` corresponding to the
functional `h_σ(u, ·)` is `u`. -/
theorem dualVector_symm_form (u : Codomain σ ⊗[𝓞 K] E) :
    h.dualVector σ ((dualPairingEquiv σ).symm (h.form σ u)) = u := by
  rw [dualVector_eq_iff, ← dualPairingEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The Riesz vector, for the dual metric, of `1 ⊗ eval x` is the element of the fibre of `E^∨`
corresponding to the functional `h_σ(1 ⊗ x, ·)`. -/
theorem dualVector_dual_one_tmul_eval (x : E) :
    h.dual.dualVector σ (1 ⊗ₜ Module.Dual.eval (𝓞 K) E x) =
      (dualPairingEquiv σ).symm (h.form σ (1 ⊗ₜ x)) := by
  have ha := h.dualVector_symm_form σ (1 ⊗ₜ x)
  rw [dualVector_eq_iff]
  ext b
  rw [dual_form_apply, ha, form_dualVector, dualPairing_one_tmul_eval]

/-- **`Ē ≅ Ē^∨∨` isometrically**: evaluation `E ≃ E^∨∨` is an isometry from a hermitian metric to
its double dual. -/
def isometryEquivDualDual : IsometryEquiv h h.dual.dual where
  toLinearEquiv := Module.evalEquiv (𝓞 K) E
  form_tmul σ x y := by
    simp only [Module.evalEquiv_apply, dual_form_apply, dualVector_dual_one_tmul_eval,
      dualVector_symm_form]

@[simp]
theorem isometryEquivDualDual_apply (x : E) :
    h.isometryEquivDualDual x = Module.Dual.eval (𝓞 K) E x :=
  (rfl)

/-! ### The dual of the trivial line -/

section NumberField

variable [NumberField K]

/-- The Riesz vector of `1 ⊗ f` for the trivial line is `conj (σ (f 1)) ⊗ 1`. -/
theorem trivial_dualVector_one_tmul (f : Module.Dual (𝓞 K) (𝓞 K)) :
    (trivial K).dualVector σ (1 ⊗ₜ f) = (Codomain.equiv σ).symm (conj (σ (f 1))) ⊗ₜ 1 := by
  rw [dualVector_eq_iff]
  ext w
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul d e =>
    have hf : f e = e * f 1 := by simpa using map_smul f e 1
    rw [form_tmul_tmul, trivial_form_tmul, dualPairing_tmul_tmul, hf]
    simp only [AlgEquiv.apply_symm_apply, Complex.conj_conj, map_mul, map_one, one_mul]
    ring

variable (K) in
/-- **The dual of `Ō_K` is `Ō_K`**: `f ↦ f 1` is an isometry from the dual of the trivial
hermitian line to the trivial line. -/
def isometryEquivDualTrivial : IsometryEquiv (trivial K).dual (trivial K) where
  toLinearEquiv := LinearMap.ringLmapEquivSelf (𝓞 K) (𝓞 K) (𝓞 K)
  form_tmul σ f g := by
    rw [dual_form_apply, trivial_dualVector_one_tmul, trivial_dualVector_one_tmul,
      form_tmul_tmul _ σ ((Codomain.equiv σ).symm _)]
    simp [trivial_form_tmul, mul_comm]

@[simp]
theorem isometryEquivDualTrivial_apply (f : Module.Dual (𝓞 K) (𝓞 K)) :
    isometryEquivDualTrivial K f = f 1 :=
  (rfl)

end NumberField

end HermitianMetric

namespace HermitianBundle

universe u v

variable {K : Type u} [Field K]

/-- The **dual hermitian vector bundle** `Ē^∨ = (Hom_{O_K}(E, O_K), h^∨)`. -/
@[expose] def dual (Ē : HermitianBundle.{u, v} K) : HermitianBundle.{u, max u v} K where
  carrier := Module.Dual (𝓞 K) Ē
  metric := Ē.metric.dual

end HermitianBundle

end TauCeti
