/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic

import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dual of a hermitian vector bundle

Let `Ē = (E, (h_σ)_σ)` be a hermitian vector bundle over `Spec O_K`. Its dual is
`Ē^∨ = (Hom_{O_K}(E, O_K), (h^∨_σ)_σ)`, where `h^∨_σ` is the dual hermitian form on the complex
fibre of `E^∨` at `σ`.

For a finitely generated projective `𝓞 K`-module `E`, the complex fibre
`Codomain σ ⊗[𝓞 K] E^∨` of the dual is identified with the complex dual of the fibre
`Codomain σ ⊗[𝓞 K] E` by `c ⊗ f ↦ (d ⊗ x ↦ c d σ(f x))`
(`TauCeti.HermitianMetric.bijective_dualPairing`). The form `h_σ` is nondegenerate on the
finite-dimensional fibre, so every complex linear functional `φ` on the fibre is `h_σ(u_φ, ·)` for
a unique vector `u_φ` (the Riesz vector, `TauCeti.HermitianMetric.dualVector`). The dual form is
`h^∨_σ(a, b) = h_σ(u_b, u_a)`, so that the Riesz correspondence is antiunitary. Complex
conjugation `c ⊗ x ↦ conj c ⊗ x` from the fibre at `σ` to the fibre at `conj σ` carries the Riesz
vector of `1 ⊗ f` at `σ` to that at `conj σ`, which gives the conjugation condition of the dual
metric.

## Main definitions

* `TauCeti.HermitianMetric.dualPairing σ`: the complex linear map from the fibre of `E^∨` at `σ`
  to the complex dual of the fibre of `E` at `σ`; it is bijective for finitely generated
  projective `E`.
* `TauCeti.HermitianMetric.dualVector`: the Riesz vector `u_a` of an element `a` of the fibre of
  `E^∨`, characterized by `h_σ(u_a, w) = a(w)` (`TauCeti.HermitianMetric.form_dualVector`).
* `TauCeti.HermitianMetric.dual`: the dual hermitian metric on `Module.Dual (𝓞 K) E`.
* `TauCeti.HermitianMetric.dualDualIsometryEquiv`: the isometry `Ē ≅ Ē^∨∨` given by evaluation.
* `TauCeti.HermitianMetric.dualTrivialIsometryEquiv`: the isometry `Ō_K^∨ ≅ Ō_K`, `f ↦ f 1`.
* `TauCeti.HermitianBundle.dual`: the dual hermitian vector bundle.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2–A.3.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate

open NumberField NumberField.ComplexEmbedding

namespace NumberField.ComplexEmbedding.Codomain

variable {K : Type*} [Field K] (σ : K →+* ℂ)

/-- Complex conjugation `Codomain σ → Codomain (conjugate σ)`, which is `𝓞 K`-linear because
`conj (σ a) = (conjugate σ) a`. -/
def conjL : Codomain σ →ₗ[𝓞 K] Codomain (conjugate σ) where
  toFun z := (equiv (conjugate σ)).symm (conj (equiv σ z))
  map_add' _ _ := by simp only [map_add]
  map_smul' a z := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
    apply (equiv (conjugate σ)).injective
    simp only [map_mul, AlgEquiv.apply_symm_apply, equiv_algebraMap_ringOfIntegers,
      conjugate_coe_eq]

/-- `Codomain.equiv σ` is the identity of `ℂ`. -/
theorem equiv_apply (z : Codomain σ) : equiv σ z = (z : ℂ) :=
  (equiv σ).commutes z

@[simp]
theorem equiv_conjL (z : Codomain σ) : equiv (conjugate σ) (conjL σ z) = conj (equiv σ z) :=
  AlgEquiv.apply_symm_apply _ _

end NumberField.ComplexEmbedding.Codomain

namespace TauCeti

namespace HermitianMetric

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (σ : K →+* ℂ)

/-! ### The fibre of the dual module -/

variable (E) in
/-- The complex linear map from the complex fibre `Codomain σ ⊗[𝓞 K] E^∨` of the dual module to
the complex dual of the fibre `Codomain σ ⊗[𝓞 K] E`, `c ⊗ f ↦ (d ⊗ x ↦ c d σ(f x))`
(`TauCeti.HermitianMetric.dualPairing_tmul_tmul`). It is bijective for finitely generated
projective `E` (`TauCeti.HermitianMetric.bijective_dualPairing`). -/
def dualPairing :
    Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E →ₗ[ℂ] Module.Dual ℂ (Codomain σ ⊗[𝓞 K] E) :=
  ((Module.Dual.baseChange (Codomain σ)).liftBaseChange (Codomain σ)).restrictScalars ℂ

theorem dualPairing_def :
    dualPairing E σ =
      ((Module.Dual.baseChange (Codomain σ)).liftBaseChange (Codomain σ)).restrictScalars ℂ :=
  (rfl)

theorem dualPairing_tmul_tmul (c d : Codomain σ) (f : Module.Dual (𝓞 K) E) (x : E) :
    dualPairing E σ (c ⊗ₜ f) (d ⊗ₜ x) =
      Codomain.equiv σ c * (Codomain.equiv σ d * σ (f x)) := by
  change c * (algebraMap (𝓞 K) (Codomain σ) (f x) * d) = _
  rw [Codomain.equiv_apply, Codomain.equiv_apply, mul_comm (algebraMap _ _ _)]
  rfl

/-- For finitely generated projective `E`, taking duals commutes with the scalar extension to
the complex fibre: `dualPairing E σ` is bijective. It agrees with the composite of Mathlib's
`dualTensorHomEquiv` and `LinearMap.liftBaseChangeEquiv`. -/
theorem bijective_dualPairing [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] :
    Function.Bijective (dualPairing E σ) := by
  let e := ((TensorProduct.comm (𝓞 K) (Codomain σ) (Module.Dual (𝓞 K) E)).trans
    (dualTensorHomEquiv (𝓞 K) E (Codomain σ))).trans
    ((LinearMap.liftBaseChangeEquiv (Codomain σ)).restrictScalars (𝓞 K))
  have he : ∀ u, ((e u : Codomain σ ⊗[𝓞 K] E →ₗ[Codomain σ] Codomain σ) : _ → _) =
      dualPairing E σ u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | add a b ha hb => ext v; simp only [map_add, LinearMap.add_apply]; rw [← ha, ← hb]; rfl
    | tmul c f =>
      funext v
      induction v using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add] at *; rw [ha, hb]; rfl
      | tmul d x =>
        rw [dualPairing_tmul_tmul]
        simp only [e, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
          LinearEquiv.restrictScalars_apply]
        rw [LinearMap.liftBaseChange_tmul, dualTensorHomEquiv_tmul, smul_eq_mul,
          Algebra.smul_def]
        rw [Codomain.equiv_apply, Codomain.equiv_apply]
        exact (by intros; ring : ∀ a b d : ℂ, d * (a * b) = b * (d * a)) _ _ _
  refine ⟨fun u u' huu' ↦ e.injective (LinearMap.ext fun v ↦ ?_), fun g ↦ ?_⟩
  · exact (congrFun (he u) v).trans
      ((congrArg (· v) huu').trans (congrFun (he u') v).symm)
  · let g' : Codomain σ ⊗[𝓞 K] E →ₗ[Codomain σ] Codomain σ :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c v ↦ g.map_smul (c : ℂ) v }
    obtain ⟨u, hu⟩ := e.surjective g'
    exact ⟨u, LinearMap.ext fun v ↦ (congrFun (he u) v).symm.trans (by rw [hu]; rfl)⟩

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

variable (E) in
/-- Complex conjugation `c ⊗ x ↦ conj c ⊗ x` from the complex fibre at `σ` to the complex fibre
at the conjugate embedding; it is conjugate-linear (`TauCeti.HermitianMetric.fiberConj_smul`). -/
def fiberConj : Codomain σ ⊗[𝓞 K] E →ₗ[𝓞 K] Codomain (conjugate σ) ⊗[𝓞 K] E :=
  (Codomain.conjL σ).rTensor E

@[simp]
theorem fiberConj_tmul (z : Codomain σ) (x : E) :
    fiberConj E σ (z ⊗ₜ x) = Codomain.conjL σ z ⊗ₜ x :=
  (rfl)

theorem fiberConj_smul (c : ℂ) (u : Codomain σ ⊗[𝓞 K] E) :
    fiberConj E σ (c • u) = conj c • fiberConj E σ u := by
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul z x =>
    rw [TensorProduct.smul_tmul', fiberConj_tmul, fiberConj_tmul, TensorProduct.smul_tmul']
    congr 1
    apply (Codomain.equiv (conjugate σ)).injective
    rw [map_smul (Codomain.equiv (conjugate σ)), Codomain.equiv_conjL, Codomain.equiv_conjL,
      map_smul (Codomain.equiv σ), smul_eq_mul, smul_eq_mul, map_mul]

theorem fiberConj_surjective : Function.Surjective (fiberConj E σ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro u -
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => exact add_mem ha hb
  | tmul z x =>
    refine ⟨(Codomain.equiv σ).symm (conj (Codomain.equiv (conjugate σ) z)) ⊗ₜ x, ?_⟩
    rw [fiberConj_tmul]
    congr 1
    apply (Codomain.equiv (conjugate σ)).injective
    rw [Codomain.equiv_conjL, AlgEquiv.apply_symm_apply, Complex.conj_conj]

theorem dualPairing_fiberConj (f : Module.Dual (𝓞 K) E) (w : Codomain σ ⊗[𝓞 K] E) :
    dualPairing E (conjugate σ) (1 ⊗ₜ f) (fiberConj E σ w) =
      conj (dualPairing E σ (1 ⊗ₜ f) w) := by
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul z x =>
    rw [fiberConj_tmul, dualPairing_tmul_tmul, dualPairing_tmul_tmul, conjugate_coe_eq,
      Codomain.equiv_conjL]
    simp only [map_one, one_mul, map_mul]

variable (h : HermitianMetric K E)

/-- The forms at `σ` and at the conjugate embedding are complex conjugate under conjugation of
fibres, on the whole fibre. -/
theorem form_fiberConj (u v : Codomain σ ⊗[𝓞 K] E) :
    h.form (conjugate σ) (fiberConj E σ u) (fiberConj E σ v) = conj (h.form σ u v) := by
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul z x =>
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul w y =>
      rw [fiberConj_tmul, fiberConj_tmul, h.form_tmul_tmul (conjugate σ), h.form_tmul_tmul σ,
        form_conjugate_tmul]
      simp only [Codomain.equiv_conjL, map_mul, Complex.conj_conj]

/-! ### Riesz vectors -/

/-- On a finite-dimensional complex fibre, the positive definite form `h_σ` identifies the fibre
conjugate-linearly with its complex dual, `u ↦ h_σ(u, ·)`. -/
theorem bijective_form [Module.Finite (𝓞 K) E] : Function.Bijective (h.form σ) := by
  have : Module.Finite ℂ (Codomain σ) := inferInstanceAs (Module.Finite ℂ ℂ)
  have : Module.Finite ℂ (Codomain σ ⊗[𝓞 K] E) := Module.Finite.trans (Codomain σ) _
  refine ⟨(injective_iff_map_eq_zero (h.form σ)).2 fun u hu ↦
    h.form_self_eq_zero_iff.1 (congrArg (· u) hu), LinearMap.range_eq_top.1 ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hW := Subspace.finrank_add_finrank_dualCoannihilator_eq (LinearMap.range (h.form σ))
  have hbot : (LinearMap.range (h.form σ)).dualCoannihilator = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun u hu ↦ h.form_self_eq_zero_iff.1
      ((Submodule.mem_dualCoannihilator u).1 hu _ ⟨u, rfl⟩)
  rw [hbot, finrank_bot, add_zero] at hW
  rw [hW, Subspace.dual_finrank_eq]

variable [Module.Finite (𝓞 K) E]

/-- The **Riesz vector** `u_a` of an element `a` of the complex fibre of `E^∨` at `σ`: the unique
vector of the fibre of `E` with `h_σ(u_a, w) = a(w)` for every `w`
(`TauCeti.HermitianMetric.form_dualVector`, `TauCeti.HermitianMetric.dualVector_eq_iff`). It is
conjugate-linear in `a`. -/
def dualVector :
    Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E →ₗ⋆[ℂ] Codomain σ ⊗[𝓞 K] E :=
  (LinearEquiv.ofBijective (h.form σ) (h.bijective_form σ)).symm.toLinearMap.comp
    (dualPairing E σ)

theorem dualVector_def :
    h.dualVector σ = (LinearEquiv.ofBijective (h.form σ) (h.bijective_form σ)).symm.toLinearMap.comp
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
  (LinearEquiv.ofBijective (h.form σ) (h.bijective_form σ)).symm.injective.comp
    (bijective_dualPairing σ).1

/-- Conjugation of fibres carries the Riesz vector of `1 ⊗ f` at `σ` to the Riesz vector of
`1 ⊗ f` at the conjugate embedding. -/
theorem dualVector_conjugate (f : Module.Dual (𝓞 K) E) :
    h.dualVector (conjugate σ) (1 ⊗ₜ f) = fiberConj E σ (h.dualVector σ (1 ⊗ₜ f)) := by
  rw [dualVector_eq_iff]
  ext w'
  obtain ⟨w, rfl⟩ := fiberConj_surjective σ w'
  rw [h.form_fiberConj, form_dualVector, dualPairing_fiberConj]

/-! ### The dual metric -/

variable [Module.Projective (𝓞 K) E]

/-- The **dual hermitian metric** on `E^∨ = Module.Dual (𝓞 K) E` of a hermitian metric on a
finitely generated projective `𝓞 K`-module: `h^∨_σ(a, b) = h_σ(u_b, u_a)` for the Riesz vectors
`u_a, u_b` (`TauCeti.HermitianMetric.dual_form_apply`), so that `a ↦ u_a` is antiunitary. -/
def dual : HermitianMetric K (Module.Dual (𝓞 K) E) where
  form σ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun a b ↦ h.form σ (h.dualVector σ b) (h.dualVector σ a))
    (fun _ _ _ ↦ by simp only [map_add])
    (fun _ _ _ ↦ by simp only [map_smulₛₗ, smul_eq_mul]; rfl)
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
    simp only [LinearMap.mk₂'ₛₗ_apply, dualVector_conjugate, form_fiberConj]

theorem dual_form_apply (a b : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E) :
    h.dual.form σ a b = h.form σ (h.dualVector σ b) (h.dualVector σ a) :=
  (rfl)

/-- The Riesz vector, for `h`, of the element of the fibre of `E^∨` corresponding to the
functional `h_σ(u, ·)` is `u`. -/
theorem dualVector_symm_form (u : Codomain σ ⊗[𝓞 K] E) :
    h.dualVector σ
      ((LinearEquiv.ofBijective _ (bijective_dualPairing (E := E) σ)).symm (h.form σ u)) = u := by
  rw [dualVector_eq_iff]
  exact ((LinearEquiv.ofBijective _ (bijective_dualPairing (E := E) σ)).apply_symm_apply _).symm

/-- The Riesz vector, for the dual metric, of `1 ⊗ eval x` is the element of the fibre of `E^∨`
corresponding to the functional `h_σ(1 ⊗ x, ·)`. -/
theorem dualVector_dual_one_tmul_eval (x : E) :
    h.dual.dualVector σ (1 ⊗ₜ Module.Dual.eval (𝓞 K) E x) =
      (LinearEquiv.ofBijective _ (bijective_dualPairing (E := E) σ)).symm
        (h.form σ (1 ⊗ₜ x)) := by
  have ha := h.dualVector_symm_form σ (1 ⊗ₜ x)
  rw [dualVector_eq_iff]
  ext b
  rw [dual_form_apply, ha, form_dualVector, dualPairing_one_tmul_eval]

/-- **`Ē ≅ Ē^∨∨` isometrically**: evaluation `E ≃ E^∨∨` is an isometry from a hermitian metric to
its double dual. -/
def dualDualIsometryEquiv : IsometryEquiv h h.dual.dual where
  toLinearEquiv := Module.evalEquiv (𝓞 K) E
  form_tmul σ x y := by
    rw [Module.evalEquiv_apply, Module.evalEquiv_apply, dual_form_apply,
      dualVector_dual_one_tmul_eval, dualVector_dual_one_tmul_eval, dual_form_apply,
      dualVector_symm_form, dualVector_symm_form]

@[simp]
theorem dualDualIsometryEquiv_apply (x : E) :
    h.dualDualIsometryEquiv x = Module.Dual.eval (𝓞 K) E x :=
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
    rw [form_tmul_tmul, trivial_form_tmul, dualPairing_tmul_tmul, AlgEquiv.apply_symm_apply,
      Complex.conj_conj]
    have hf : f e = e * f 1 := by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [hf]
    simp only [map_mul, map_one, one_mul]
    ring

variable (K) in
/-- **The dual of `Ō_K` is `Ō_K`**: `f ↦ f 1` is an isometry from the dual of the trivial
hermitian line to the trivial line. -/
def dualTrivialIsometryEquiv : IsometryEquiv (trivial K).dual (trivial K) where
  toLinearEquiv := LinearMap.ringLmapEquivSelf (𝓞 K) (𝓞 K) (𝓞 K)
  form_tmul σ f g := by
    rw [dual_form_apply, trivial_dualVector_one_tmul, trivial_dualVector_one_tmul]
    conv_rhs => rw [form_tmul_tmul]
    rw [trivial_form_one, trivial_form_tmul, LinearMap.ringLmapEquivSelf_apply,
      LinearMap.ringLmapEquivSelf_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      Complex.conj_conj, mul_one, mul_comm]

@[simp]
theorem dualTrivialIsometryEquiv_apply (f : Module.Dual (𝓞 K) (𝓞 K)) :
    dualTrivialIsometryEquiv K f = f 1 :=
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
