/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Localization

/-!
# Sub-bundles and quotients of hermitian vector bundles

Let `K` be a number field and `h` a hermitian metric on an `𝓞 K`-module `E`. For an `𝓞 K`-submodule
`F ⊂ E`:

* `F` carries the **restricted metric**, `h_σ` on the complex fibre `F_σ ⊂ E_σ`. More generally,
  `h` pulls back along any injective `𝓞 K`-linear map `f : F → E`, since its complexifications
  `f_σ` stay injective (`ℂ` is flat over `𝓞 K`).
* `E ⧸ F` carries the **quotient metric**: its complex fibre `(E ⧸ F)_σ = E_σ ⧸ F_σ` is identified
  with the orthogonal complement of `F_σ` in `E_σ`, and `h_σ` is restricted to it. The norm of a
  class is the smallest norm of its lifts (`norm_quotient_baseChange_mkQ_le`).

When `E` is a hermitian vector bundle, `F` is finitely generated projective, and so is `E ⧸ F` when
`F` is saturated, that is, `E ⧸ F` is torsion-free; both are then hermitian vector bundles.

## Main definitions

* `TauCeti.HermitianMetric.fiberConj`: complex conjugation `c ⊗ x ↦ conj c ⊗ x` from the complex
  fibre at `σ` to the one at `conj σ`; it is antiunitary (`form_fiberConj`).
* `TauCeti.HermitianMetric.comap`: the pullback of a metric along an injective linear map.
* `TauCeti.HermitianMetric.quotientLift`: the identification of the complex fibre of `E ⧸ F` with
  the orthogonal complement of the fibre of `F`, as a section of the projection.
* `TauCeti.HermitianMetric.quotient`: the quotient metric on `E ⧸ F`.
* `TauCeti.HermitianBundle.sub`, `TauCeti.HermitianBundle.quotient`: the hermitian vector bundles
  on a submodule, and on the quotient by a saturated submodule.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.2–A.3.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.2.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate

namespace TauCeti

open NumberField NumberField.ComplexEmbedding

variable {K : Type*} [Field K]
variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F]

namespace HermitianMetric

/-! ### Complex conjugation of fibres -/

/-- Complex conjugation `ℂ → ℂ` from `Codomain σ` to `Codomain (conj σ)`; it is `𝓞 K`-linear
since `conj (σ a * z) = (conj σ) a * conj z`. -/
def codomainConj (σ : K →+* ℂ) : Codomain σ →ₗ[𝓞 K] Codomain (conjugate σ) where
  toFun z := (Codomain.equiv (conjugate σ)).symm (conj (Codomain.equiv σ z))
  map_add' z w := by simp only [map_add]
  map_smul' a z := by
    apply (Codomain.equiv (conjugate σ)).injective
    simp only [AlgEquiv.apply_symm_apply, Algebra.smul_def, map_mul, RingHom.id_apply,
      Codomain.equiv_algebraMap_ringOfIntegers, conjugate_coe_eq]

/-- `codomainConj σ` is complex conjugation. -/
@[simp]
theorem equiv_codomainConj (σ : K →+* ℂ) (z : Codomain σ) :
    Codomain.equiv (conjugate σ) (codomainConj σ z) = conj (Codomain.equiv σ z) :=
  AlgEquiv.apply_symm_apply _ _

variable (E) in
/-- Complex conjugation `c ⊗ x ↦ conj c ⊗ x` from the complex fibre `E_σ` to `E_{conj σ}`: it
fixes the vectors `1 ⊗ x` of `E` and is conjugate-linear (`fiberConj_smul`). -/
def fiberConj (σ : K →+* ℂ) :
    Codomain σ ⊗[𝓞 K] E →ₗ[𝓞 K] Codomain (conjugate σ) ⊗[𝓞 K] E :=
  (codomainConj σ).rTensor E

@[simp]
theorem fiberConj_tmul (σ : K →+* ℂ) (c : Codomain σ) (x : E) :
    fiberConj E σ (c ⊗ₜ x) = codomainConj σ c ⊗ₜ x :=
  (rfl)

theorem fiberConj_one_tmul (σ : K →+* ℂ) (x : E) :
    fiberConj E σ ((1 : Codomain σ) ⊗ₜ x) = 1 ⊗ₜ x := by
  rw [fiberConj_tmul]
  congr 1
  apply (Codomain.equiv (conjugate σ)).injective
  simp

/-- Complex conjugation of fibres is conjugate-linear. -/
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

variable (h : HermitianMetric K E)

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
      rw [fiberConj_tmul, fiberConj_tmul, h.form_tmul_tmul, h.form_tmul_tmul σ c d,
        equiv_codomainConj, equiv_codomainConj, h.form_conjugate_tmul, map_mul, map_mul,
        Complex.conj_conj]

/-! ### Pulling back along injective maps -/

/-- The complexification `f_σ` of an injective `𝓞 K`-linear map is injective, since `ℂ` is flat
over `𝓞 K`. -/
theorem baseChange_injective [NumberField K] (σ : K →+* ℂ) {f : F →ₗ[𝓞 K] E}
    (hf : Function.Injective f) : Function.Injective (f.baseChange (Codomain σ)) := by
  have : Module.Flat (𝓞 K) (Codomain σ) := Module.Flat.trans (𝓞 K) K (Codomain σ)
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- The **pullback** of a hermitian metric `h` on `E` along an injective `𝓞 K`-linear map
`f : F → E`: the form at `σ` is `h_σ(f_σ u, f_σ v)`, where `f_σ` is the complexification of `f`.
For the inclusion of a submodule this is the restricted metric. -/
def comap [NumberField K] (f : F →ₗ[𝓞 K] E) (hf : Function.Injective f) :
    HermitianMetric K F where
  form σ := ((h.form σ).comp ((f.baseChange (Codomain σ)).restrictScalars ℂ)).compl₂
    ((f.baseChange (Codomain σ)).restrictScalars ℂ)
  isSymm_form σ := LinearMap.isSymm_def.mpr fun u v ↦ (h.isSymm_form σ).eq _ _
  form_self_pos σ u hu := by
    refine h.form_self_pos σ (u := f.baseChange (Codomain σ) u) fun h0 ↦ hu ?_
    exact baseChange_injective σ hf (h0.trans (map_zero _).symm)
  form_conjugate_tmul σ x y := by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.baseChange_tmul, h.form_conjugate_tmul]

@[simp]
theorem comap_form_apply [NumberField K] (f : F →ₗ[𝓞 K] E) (hf : Function.Injective f)
    (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] F) :
    (h.comap f hf).form σ u v =
      h.form σ (f.baseChange (Codomain σ) u) (f.baseChange (Codomain σ) v) :=
  (rfl)

/-- The pullback metric agrees with `h` on vectors of `F`. -/
theorem comap_form_tmul [NumberField K] (f : F →ₗ[𝓞 K] E) (hf : Function.Injective f)
    (σ : K →+* ℂ) (x y : F) :
    (h.comap f hf).form σ (1 ⊗ₜ x) (1 ⊗ₜ y) = h.form σ (1 ⊗ₜ f x) (1 ⊗ₜ f y) :=
  (rfl)

/-- The norms of the pullback metric are those of `h`. -/
@[simp]
theorem norm_comap [NumberField K] (f : F →ₗ[𝓞 K] E) (hf : Function.Injective f)
    (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] F) :
    (h.comap f hf).norm σ u = h.norm σ (f.baseChange (Codomain σ) u) := by
  rw [norm_def, norm_def]
  rfl

/-! ### The quotient metric -/

variable (F' : Submodule (𝓞 K) E)

/-- The complexification of `E → E ⧸ F` is surjective with kernel the image of the complexified
fibre of `F`. -/
private theorem exact_baseChange (σ : K →+* ℂ) :
    Function.Exact (F'.subtype.baseChange (Codomain σ)) (F'.mkQ.baseChange (Codomain σ)) := by
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
  exact lTensor_exact _ (LinearMap.exact_subtype_mkQ F') (Submodule.mkQ_surjective F')

private theorem baseChange_mkQ_surjective (σ : K →+* ℂ) :
    Function.Surjective (F'.mkQ.baseChange (Codomain σ)) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective F')

/-- A vector `v` of `E_σ` is `h_σ`-orthogonal to the fibre `F_σ` of a submodule. -/
@[expose] def IsOrthogonalFiber (σ : K →+* ℂ) (v : Codomain σ ⊗[𝓞 K] E) : Prop :=
  ∀ w : Codomain σ ⊗[𝓞 K] F', h.form σ (F'.subtype.baseChange (Codomain σ) w) v = 0

/-- Vectors orthogonal to `F_σ` with the same image in `(E ⧸ F)_σ` are equal. -/
theorem eq_of_isOrthogonalFiber {σ : K →+* ℂ} {v v' : Codomain σ ⊗[𝓞 K] E}
    (hv : h.IsOrthogonalFiber F' σ v) (hv' : h.IsOrthogonalFiber F' σ v')
    (he : F'.mkQ.baseChange (Codomain σ) v = F'.mkQ.baseChange (Codomain σ) v') : v = v' := by
  obtain ⟨w, hw⟩ := (exact_baseChange F' σ (v - v')).1 (by rw [map_sub, he, sub_self])
  rw [← sub_eq_zero, ← h.form_self_eq_zero_iff (σ := σ)]
  nth_rewrite 1 [← hw]
  rw [map_sub, hv w, hv' w, sub_zero]

/-- Every vector of `(E ⧸ F)_σ` lifts to a vector of `E_σ` orthogonal to `F_σ`: subtract from any
lift its orthogonal projection onto `F_σ`. -/
private theorem exists_isOrthogonalFiber [Module.Finite (𝓞 K) E] (σ : K →+* ℂ)
    (u : Codomain σ ⊗[𝓞 K] (E ⧸ F')) :
    ∃ v, F'.mkQ.baseChange (Codomain σ) v = u ∧ h.IsOrthogonalFiber F' σ v := by
  obtain ⟨v₀, rfl⟩ := baseChange_mkQ_surjective F' σ u
  let : NormedAddCommGroup (Codomain σ ⊗[𝓞 K] E) := (h.toCore σ).toNormedAddCommGroup
  let : InnerProductSpace ℂ (Codomain σ ⊗[𝓞 K] E) := .ofCore (h.toCore σ).toCore
  have : Module.Finite ℂ (Codomain σ) := Module.Finite.self ℂ
  have : FiniteDimensional ℂ (Codomain σ ⊗[𝓞 K] E) := Module.Finite.trans (Codomain σ) _
  let W := LinearMap.range ((F'.subtype.baseChange (Codomain σ)).restrictScalars ℂ)
  refine ⟨v₀ - W.starProjection v₀, ?_, fun w ↦ ?_⟩
  · obtain ⟨w, hw⟩ : W.starProjection v₀ ∈ W := W.starProjection_apply_mem v₀
    rw [map_sub, ← hw, LinearMap.restrictScalars_apply,
      (exact_baseChange F' σ).apply_apply_eq_zero, sub_zero]
  · have key := Submodule.inner_right_of_mem_orthogonal (K := W) ⟨w, rfl⟩
      (W.sub_starProjection_mem_orthogonal v₀)
    rw [← h.inner_toCore]
    exact key

/-- The lift of a vector of `(E ⧸ F)_σ` to the orthogonal complement of `F_σ` in `E_σ`. Together
with the projection it identifies `(E ⧸ F)_σ` with that orthogonal complement: it is a section of
the projection (`baseChange_mkQ_quotientLift`) with values orthogonal to `F_σ`
(`isOrthogonalFiber_quotientLift`), and these characterize it (`quotientLift_eq`). -/
def quotientLift [Module.Finite (𝓞 K) E] (σ : K →+* ℂ) :
    Codomain σ ⊗[𝓞 K] (E ⧸ F') →ₗ[ℂ] Codomain σ ⊗[𝓞 K] E :=
  have hex := h.exists_isOrthogonalFiber F' σ
  have hu := fun u ↦ (hex u).choose_spec
  { toFun u := (hex u).choose
    map_add' u u' := h.eq_of_isOrthogonalFiber F' (hu _).2
      (fun w ↦ by rw [map_add, (hu u).2 w, (hu u').2 w, add_zero])
      (by rw [map_add, (hu _).1, (hu u).1, (hu u').1])
    map_smul' c u := h.eq_of_isOrthogonalFiber F' (hu _).2
      (fun w ↦ by rw [LinearMap.map_smul, (hu u).2 w, smul_zero])
      (by rw [RingHom.id_apply, LinearMap.map_smul_of_tower, (hu _).1, (hu u).1]) }

variable [Module.Finite (𝓞 K) E]

@[simp]
theorem baseChange_mkQ_quotientLift (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] (E ⧸ F')) :
    F'.mkQ.baseChange (Codomain σ) (h.quotientLift F' σ u) = u :=
  (h.exists_isOrthogonalFiber F' σ u).choose_spec.1

theorem isOrthogonalFiber_quotientLift (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] (E ⧸ F')) :
    h.IsOrthogonalFiber F' σ (h.quotientLift F' σ u) :=
  (h.exists_isOrthogonalFiber F' σ u).choose_spec.2

/-- `quotientLift` is the unique lift orthogonal to `F_σ`. -/
theorem quotientLift_eq {σ : K →+* ℂ} {v : Codomain σ ⊗[𝓞 K] E}
    (hv : h.IsOrthogonalFiber F' σ v) :
    h.quotientLift F' σ (F'.mkQ.baseChange (Codomain σ) v) = v :=
  h.eq_of_isOrthogonalFiber F' (h.isOrthogonalFiber_quotientLift F' σ _) hv
    (h.baseChange_mkQ_quotientLift F' σ _)

omit [Module.Finite (𝓞 K) E] in
/-- Complex conjugation of fibres maps vectors orthogonal to `F_σ` to vectors orthogonal to
`F_{conj σ}`. -/
theorem IsOrthogonalFiber.fiberConj {σ : K →+* ℂ} {v : Codomain σ ⊗[𝓞 K] E}
    (hv : h.IsOrthogonalFiber F' σ v) :
    h.IsOrthogonalFiber F' (conjugate σ) (fiberConj E σ v) := by
  intro w
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ h₁ h₂ => rw [map_add, LinearMap.map_add₂, h₁, h₂, add_zero]
  | tmul c x =>
    rw [Codomain.tmul_eq_smul, LinearMap.map_smul_of_tower, LinearMap.map_smulₛₗ₂,
      ← fiberConj_one_tmul σ x, ← fiberConj_baseChange, form_fiberConj, hv, map_zero, smul_zero]

/-- The lifts at conjugate embeddings are exchanged by complex conjugation of fibres. -/
theorem quotientLift_fiberConj (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] (E ⧸ F')) :
    h.quotientLift F' (conjugate σ) (fiberConj (E ⧸ F') σ u) =
      fiberConj E σ (h.quotientLift F' σ u) := by
  conv_lhs => rw [← h.baseChange_mkQ_quotientLift F' σ u, fiberConj_baseChange]
  exact h.quotientLift_eq F' ((h.isOrthogonalFiber_quotientLift F' σ u).fiberConj h F')

/-- The **quotient metric** on `E ⧸ F`: the complex fibre `(E ⧸ F)_σ` is identified with the
orthogonal complement of `F_σ` in `E_σ` by `quotientLift`, and carries the restriction of `h_σ`.
The norm of a class is the smallest norm of its lifts (`norm_quotient_baseChange_mkQ_le`). -/
def quotient : HermitianMetric K (E ⧸ F') where
  form σ := ((h.form σ).comp (h.quotientLift F' σ)).compl₂ (h.quotientLift F' σ)
  isSymm_form σ := LinearMap.isSymm_def.mpr fun u v ↦ (h.isSymm_form σ).eq _ _
  form_self_pos σ u hu := h.form_self_pos σ fun h0 ↦
    hu (by rw [← h.baseChange_mkQ_quotientLift F' σ u, h0, map_zero])
  form_conjugate_tmul σ x y := by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
    rw [← fiberConj_one_tmul σ x, ← fiberConj_one_tmul σ y, h.quotientLift_fiberConj,
      h.quotientLift_fiberConj, form_fiberConj]

@[simp]
theorem quotient_form_apply (σ : K →+* ℂ) (u v : Codomain σ ⊗[𝓞 K] (E ⧸ F')) :
    (h.quotient F').form σ u v = h.form σ (h.quotientLift F' σ u) (h.quotientLift F' σ v) :=
  (rfl)

/-- On vectors orthogonal to `F_σ`, the quotient metric is `h_σ`. -/
theorem quotient_form_baseChange_mkQ {σ : K →+* ℂ} {v v' : Codomain σ ⊗[𝓞 K] E}
    (hv : h.IsOrthogonalFiber F' σ v) (hv' : h.IsOrthogonalFiber F' σ v') :
    (h.quotient F').form σ (F'.mkQ.baseChange (Codomain σ) v)
      (F'.mkQ.baseChange (Codomain σ) v') = h.form σ v v' := by
  rw [quotient_form_apply, h.quotientLift_eq F' hv, h.quotientLift_eq F' hv']

/-- The quotient norm of the class of `v` is at most the norm of `v`, with equality for `v`
orthogonal to `F_σ`: the quotient norm is the distance from `v` to `F_σ`. -/
theorem norm_quotient_baseChange_mkQ_le (σ : K →+* ℂ) (v : Codomain σ ⊗[𝓞 K] E) :
    (h.quotient F').norm σ (F'.mkQ.baseChange (Codomain σ) v) ≤ h.norm σ v := by
  set u := h.quotientLift F' σ (F'.mkQ.baseChange (Codomain σ) v)
  obtain ⟨w, hw⟩ := (exact_baseChange F' σ (v - u)).1
    (by rw [map_sub, h.baseChange_mkQ_quotientLift, sub_self])
  have horth : h.form σ (F'.subtype.baseChange (Codomain σ) w) u = 0 :=
    h.isOrthogonalFiber_quotientLift F' σ (F'.mkQ.baseChange (Codomain σ) v) w
  have horth' : h.form σ u (F'.subtype.baseChange (Codomain σ) w) = 0 := by
    rw [← h.conj_form, horth, map_zero]
  have hv : v = u + F'.subtype.baseChange (Codomain σ) w := by rw [hw, add_sub_cancel]
  have key : (h.norm σ v) ^ 2 =
      (h.norm σ u) ^ 2 + (h.norm σ (F'.subtype.baseChange (Codomain σ) w)) ^ 2 := by
    rw [h.norm_sq, h.norm_sq, h.norm_sq, hv]
    simp only [map_add, LinearMap.add_apply, horth, horth', add_zero, zero_add, Complex.add_re]
  rw [norm_def, quotient_form_apply, ← norm_def]
  refine (pow_le_pow_iff_left₀ (h.norm_nonneg σ u) (h.norm_nonneg σ v) two_ne_zero).mp ?_
  rw [key]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem norm_quotient_baseChange_mkQ {σ : K →+* ℂ} {v : Codomain σ ⊗[𝓞 K] E}
    (hv : h.IsOrthogonalFiber F' σ v) :
    (h.quotient F').norm σ (F'.mkQ.baseChange (Codomain σ) v) = h.norm σ v := by
  rw [norm_def, norm_def, quotient_form_baseChange_mkQ h F' hv hv]

end HermitianMetric

namespace HermitianBundle

variable [NumberField K] (Ē : HermitianBundle K) (F : Submodule (𝓞 K) Ē)

/-- The **sub-bundle** of a hermitian vector bundle `Ē` on an `𝓞 K`-submodule `F`, with the
restricted metric. It is a hermitian vector bundle: `F` is finitely generated since `𝓞 K` is
Noetherian, and projective since it is torsion-free over the Dedekind domain `𝓞 K`. -/
@[expose] def sub : HermitianBundle K where
  carrier := F
  isProjective :=
    have : Module.FinitePresentation (𝓞 K) F := Module.finitePresentation_of_finite _ _
    Module.Flat.projective_of_finitePresentation
  metric := Ē.metric.comap F.subtype F.injective_subtype

theorem sub_metric : (Ē.sub F).metric = Ē.metric.comap F.subtype F.injective_subtype :=
  (rfl)

/-- The **quotient bundle** `Ē ⧸ F` of a hermitian vector bundle by a saturated submodule `F`
(`Ē ⧸ F` torsion-free), with the quotient metric. Saturation makes `Ē ⧸ F` projective. -/
@[expose] def quotient [Module.IsTorsionFree (𝓞 K) (Ē ⧸ F)] : HermitianBundle K where
  carrier := Ē ⧸ F
  isProjective :=
    have : Module.FinitePresentation (𝓞 K) (Ē ⧸ F) := Module.finitePresentation_of_finite _ _
    Module.Flat.projective_of_finitePresentation
  metric := Ē.metric.quotient F

theorem quotient_metric [Module.IsTorsionFree (𝓞 K) (Ē ⧸ F)] :
    (Ē.quotient F).metric = Ē.metric.quotient F :=
  (rfl)

end HermitianBundle

end TauCeti
