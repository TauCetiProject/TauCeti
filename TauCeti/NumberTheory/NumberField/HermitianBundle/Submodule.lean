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

/-!
# Sub-bundles and quotients of hermitian vector bundles

Let `K` be a number field and `h` a hermitian metric on an `𝓞 K`-module `E`. For an `𝓞 K`-submodule
`F ⊂ E`:

* `F` carries the **restricted metric**, `h_σ` on the complex fibre `F_σ ⊂ E_σ`. More generally,
  `h` pulls back along any injective `𝓞 K`-linear map `f : F → E`, since its complexifications
  `f_σ` stay injective (`ℂ` is flat over `𝓞 K`).
* `E ⧸ F` carries the **quotient metric**: its complex fibre `(E ⧸ F)_σ = E_σ ⧸ F_σ` is identified
  with the orthogonal complement of `F_σ` in `E_σ`, and `h_σ` is restricted to it. The norm of a
  class is the norm of its orthogonal lift (`norm_quotient_baseChange_mkQ`), and at most the norm
  of any lift (`norm_quotient_baseChange_mkQ_le`).

When `E` is a hermitian vector bundle, `F` is finitely generated projective, and so is `E ⧸ F` when
`F` is saturated, that is, `E ⧸ F` is torsion-free; both are then hermitian vector bundles.

## Main definitions

* `TauCeti.HermitianMetric.comap`: the pullback of a metric along an injective linear map.
* `TauCeti.HermitianMetric.isometryEquivComap`: a metric is isometric to its pullback along a
  linear isomorphism.
* `TauCeti.HermitianMetric.quotientLift`: the identification of the complex fibre of `E ⧸ F` with
  the orthogonal complement of the fibre of `F`, as a section of the projection.
* `TauCeti.HermitianMetric.quotient`: the quotient metric on `E ⧸ F`.
* `TauCeti.HermitianBundle.ofSubmodule`, `TauCeti.HermitianBundle.quotient`: the hermitian vector
  bundles on a submodule, and on the quotient by a saturated submodule.

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

variable (h : HermitianMetric K E)

/-! ### Pulling back along injective maps -/

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
    exact Codomain.baseChange_injective σ hf (h0.trans (map_zero _).symm)
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
    (h.comap f hf).form σ (1 ⊗ₜ x) (1 ⊗ₜ y) = h.form σ (1 ⊗ₜ f x) (1 ⊗ₜ f y) := by
  rw [comap_form_apply, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]

/-- The norms of the pullback metric are those of `h`. -/
@[simp]
theorem norm_comap [NumberField K] (f : F →ₗ[𝓞 K] E) (hf : Function.Injective f)
    (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] F) :
    (h.comap f hf).norm σ u = h.norm σ (f.baseChange (Codomain σ) u) := by
  rw [norm_def, norm_def, comap_form_apply]

@[simp]
theorem placeNorm_comap [NumberField K] (f : F →ₗ[𝓞 K] E) (hf : Function.Injective f)
    (v : InfinitePlace K) (x : F) :
    (h.comap f hf).placeNorm v x = h.placeNorm v (f x) := by
  rw [← v.mk_embedding, placeNorm_mk, placeNorm_mk, norm_comap, LinearMap.baseChange_tmul]

/-- A hermitian metric `h` on `E` is isometric, by `e⁻¹`, to its pullback along a linear
isomorphism `e : F ≃ E`. -/
def isometryEquivComap [NumberField K] (e : F ≃ₗ[𝓞 K] E) :
    IsometryEquiv h (h.comap e.toLinearMap e.injective) where
  toLinearEquiv := e.symm
  form_tmul σ x y := by simp

@[simp]
theorem isometryEquivComap_apply [NumberField K] (e : F ≃ₗ[𝓞 K] E) (x : E) :
    h.isometryEquivComap e x = e.symm x :=
  (rfl)

@[simp]
theorem toLinearEquiv_isometryEquivComap [NumberField K] (e : F ≃ₗ[𝓞 K] E) :
    (h.isometryEquivComap e).toLinearEquiv = e.symm :=
  (rfl)

@[simp]
theorem isometryEquivComap_symm_apply [NumberField K] (e : F ≃ₗ[𝓞 K] E) (x : F) :
    (h.isometryEquivComap e).symm x = e x := by
  simpa using (h.isometryEquivComap e).symm_apply_apply (e x)

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
def IsOrthogonalFiber (σ : K →+* ℂ) (v : Codomain σ ⊗[𝓞 K] E) : Prop :=
  ∀ w : Codomain σ ⊗[𝓞 K] F', h.form σ (F'.subtype.baseChange (Codomain σ) w) v = 0

theorem isOrthogonalFiber_iff {σ : K →+* ℂ} {v : Codomain σ ⊗[𝓞 K] E} :
    h.IsOrthogonalFiber F' σ v ↔
      ∀ w : Codomain σ ⊗[𝓞 K] F', h.form σ (F'.subtype.baseChange (Codomain σ) w) v = 0 :=
  Iff.rfl

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
    have := congrArg conj (hv (1 ⊗ₜ x))
    rw [← form_fiberConj, fiberConj_baseChange] at this
    simp only [fiberConj_tmul, Codomain.conj_one, LinearMap.baseChange_tmul,
      Submodule.subtype_apply, map_zero] at this
    simp [Codomain.tmul_eq_smul _ c, this]

/-- The lifts at conjugate embeddings are exchanged by complex conjugation of fibres. -/
theorem quotientLift_fiberConj (σ : K →+* ℂ) (u : Codomain σ ⊗[𝓞 K] (E ⧸ F')) :
    h.quotientLift F' (conjugate σ) (fiberConj (E ⧸ F') σ u) =
      fiberConj E σ (h.quotientLift F' σ u) := by
  conv_lhs => rw [← h.baseChange_mkQ_quotientLift F' σ u, fiberConj_baseChange]
  exact h.quotientLift_eq F' ((h.isOrthogonalFiber_quotientLift F' σ u).fiberConj h F')

/-- The **quotient metric** on `E ⧸ F`: the complex fibre `(E ⧸ F)_σ` is identified with the
orthogonal complement of `F_σ` in `E_σ` by `quotientLift`, and carries the restriction of `h_σ`.
The norm of a class is the smallest norm of its lifts (`norm_quotient_baseChange_mkQ`,
`norm_quotient_baseChange_mkQ_le`). -/
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

/-- The quotient norm of the class of `v` is at most the norm of `v`. The lifts orthogonal to
`F_σ` attain it (`norm_quotient_baseChange_mkQ`). -/
theorem norm_quotient_baseChange_mkQ_le (σ : K →+* ℂ) (v : Codomain σ ⊗[𝓞 K] E) :
    (h.quotient F').norm σ (F'.mkQ.baseChange (Codomain σ) v) ≤ h.norm σ v := by
  set u := h.quotientLift F' σ (F'.mkQ.baseChange (Codomain σ) v)
  obtain ⟨w, hw⟩ := (exact_baseChange F' σ (v - u)).1
    (by rw [map_sub, h.baseChange_mkQ_quotientLift, sub_self])
  have horth : h.form σ u (F'.subtype.baseChange (Codomain σ) w) = 0 :=
    h.form_eq_zero_symm.mp (h.isOrthogonalFiber_quotientLift F' σ _ w)
  have hv : v = u + F'.subtype.baseChange (Codomain σ) w := by rw [hw, add_sub_cancel]
  rw [norm_def, quotient_form_apply, ← norm_def]
  refine (pow_le_pow_iff_left₀ (h.norm_nonneg σ u) (h.norm_nonneg σ v) two_ne_zero).mp ?_
  rw [hv, h.norm_add_sq_eq_norm_sq_add_norm_sq_of_form_eq_zero horth]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The quotient norm of the class of `x` at a place is at most the norm of `x` there. -/
theorem placeNorm_quotient_mk_le (v : InfinitePlace K) (x : E) :
    (h.quotient F').placeNorm v (Submodule.Quotient.mk x) ≤ h.placeNorm v x := by
  rw [← v.mk_embedding, placeNorm_mk, placeNorm_mk, ← Submodule.mkQ_apply,
    ← LinearMap.baseChange_tmul]
  exact h.norm_quotient_baseChange_mkQ_le F' _ _

/-- On a lift `v` orthogonal to `F_σ`, the quotient norm of its class is `‖v‖_σ`. -/
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
@[expose] def ofSubmodule : HermitianBundle K where
  carrier := F
  isProjective :=
    have : Module.FinitePresentation (𝓞 K) F := Module.finitePresentation_of_finite _ _
    Module.Flat.projective_of_finitePresentation
  metric := Ē.metric.comap F.subtype F.injective_subtype

theorem ofSubmodule_metric :
    (Ē.ofSubmodule F).metric = Ē.metric.comap F.subtype F.injective_subtype :=
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
