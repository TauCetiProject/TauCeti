/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# The Hodge star of differential forms on an oriented Riemannian manifold

On an oriented Riemannian manifold `M` of dimension `m = k + l`, the Hodge star of the tangent
spaces, `Orientation.formHodgeStar`, applied fibrewise sends real `k`-forms to real `l`-forms.
At a single point `x` it is packaged as a continuous linear equivalence `TauCeti.formHodgeStarCLE`
with underlying continuous linear map `TauCeti.formHodgeStarCLM`, and on rough sections it gives
`TauCeti.RoughForm.hodgeStar`. Fibrewise it satisfies `α ∧ ⋆β = ⟨α, β⟩ vol`, with `vol` the
Riemannian volume form, `⋆⋆ = (-1) ^ (k l)`, and it changes sign with the orientation. On functions
it is `⋆f = f vol`, with inverse `⋆(f vol) = f`, and on differentials of functions it is
`⋆df = ι_(grad f) vol`; these identities express the codifferential of `df` through the divergence
of the gradient.

For a `C^n` metric on a `C^(n+1)` manifold the star preserves `C^n` regularity at each point
(`TauCeti.RoughForm.contMDiffAt_hodgeStar`) and globally (`TauCeti.IsSmoothForm.hodgeStar`), so it
restricts to a linear map of smooth forms, `TauCeti.SmoothForm.hodgeStar`, defines a `C^n` section
of the `Hom` bundle between exterior form bundles (`TauCeti.contMDiff_formHodgeStarCLM`), and
induces a `C^n` diffeomorphism between their total spaces (`TauCeti.formHodgeStarDiffeomorph`). In
the frame `(∂ᵢ)` of a tangent trivialization the star is computed by
`(⋆α)(w) = ∑ α(∂_{i₁}, …, ∂_{iₖ}) vol(gⁱ¹ʲ∂ⱼ, …, gⁱᵏʲ∂ⱼ, w)` through the inverse metric `gⁱʲ`
(`Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum`), and the inverse metric, the volume form
and the coefficients of `α` are all `C^n`. Smoothness is tested on the values on fixed tuples of
model vectors (`TauCeti.contMDiffAt_continuousAlternatingMap_apply`).

## Main definitions

* `TauCeti.formHodgeStarCLE`, `TauCeti.formHodgeStarCLM`: the fibrewise Hodge star on exterior
  form fibres as a continuous linear equivalence and continuous linear map.
* `TauCeti.formHodgeStarDiffeomorph`: the `C^n` diffeomorphism between the total spaces of real
  `k`-forms and `l`-forms induced by the Hodge star.
* `TauCeti.RoughForm.hodgeStar`: the Hodge star of rough real forms.
* `TauCeti.SmoothForm.hodgeStar`: the Hodge star of smooth real forms.
* `TauCeti.SmoothForm.innerZeroForm`: the smooth zero-form `⋆(α ∧ ⋆β)` representing `⟨α, β⟩`.

## Main results

* `TauCeti.RoughForm.contMDiffAt_hodgeStar`, `TauCeti.IsSmoothForm.hodgeStar`: the Hodge star
  preserves `C^n` regularity of forms locally and globally.
* `TauCeti.contMDiff_formHodgeStarCLM`, `TauCeti.contMDiff_formHodgeStar_totalSpace`: `C^n`
  regularity of the Hodge star as a `Hom`-bundle section and on total spaces.
* `TauCeti.RoughForm.wedge_hodgeStar_apply`: `α ∧ ⋆β = ⟨α, β⟩ vol`, and its smooth-form version
  `TauCeti.SmoothForm.inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar`.
* `TauCeti.SmoothForm.innerZeroForm_apply`, `TauCeti.SmoothForm.hodgeStar_wedge_zero_right`:
  pointwise evaluation of `innerZeroForm` and right `C^∞(M)`-linearity of `SmoothForm.hodgeStar`.
* `TauCeti.RoughForm.hodgeStar_hodgeStar`: `⋆⋆α = (-1) ^ (k l) α`.
* `TauCeti.RoughForm.hodgeStar_ofFunction`, `TauCeti.RoughForm.hodgeStar_smul_riemannianVolumeForm`:
  `⋆f = f vol` and `⋆(f vol) = f`.
* `TauCeti.RoughForm.hodgeStar_mextDeriv_ofFunction`: `⋆df = ι_(grad f) vol`.
* `TauCeti.RoughForm.hodgeStar_hodgeStar_of_even`,
  `TauCeti.RoughForm.alternatingFormInner_hodgeStar_left`: in an even middle degree the star is
  an involution and is pointwise self-adjoint.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E]

section Main

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

namespace RoughForm

/-- The Hodge star of rough real `k`-forms on an oriented Riemannian manifold of dimension
`m = k + l`: at each point, the Hodge star `Orientation.formHodgeStar` of the tangent space for
the metric and the orientation. -/
def hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    RoughForm I M ℝ k →ₗ[ℝ] RoughForm I M ℝ l :=
  LinearMap.pi fun x ↦
    letI := o.fact_finrank_tangentSpace x
    ((o.orientationAt x).formHodgeStar
      (hkl.trans (o.fact_finrank_tangentSpace x).out.symm)).toLinearMap ∘ₗ LinearMap.proj x

/-- The Hodge star of a form at a point is the Hodge star of the tangent space. -/
@[simp]
theorem hodgeStar_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (φ : RoughForm I M ℝ k) (x : M) :
    hodgeStar o hkl φ x =
      (letI := o.fact_finrank_tangentSpace x
       (o.orientationAt x).formHodgeStar
         (hkl.trans (o.fact_finrank_tangentSpace x).out.symm) (φ x)) :=
  (rfl)

/-- **The wedge characterization of the Hodge star**: `α ∧ ⋆β = ⟨α, β⟩ vol` at every point, where
`⟨·, ·⟩` is the pointwise inner product of forms and `vol` the Riemannian volume form, read in
degree `k + l = m`. -/
theorem wedge_hodgeStar_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α β : RoughForm I M ℝ k) (x : M) (v : Fin (k + l) → TangentSpace I x) :
    (α x).wedge (hodgeStar o hkl β x) v =
      alternatingFormInner (TangentSpace I x) k (α x) (β x) *
        riemannianVolumeForm o x (v ∘ finCongr hkl.symm) := by
  let := o.fact_finrank_tangentSpace x
  rw [hodgeStar_apply, Orientation.wedge_formHodgeStar_apply, riemannianVolumeForm_apply]

/-- **The square of the Hodge star**: `⋆⋆α = (-1) ^ (k l) α` for a `k`-form `α`. -/
theorem hodgeStar_hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (hlk : l + k = m) (α : RoughForm I M ℝ k) :
    hodgeStar o hlk (hodgeStar o hkl α) = (-1 : ℝ) ^ (k * l) • α := by
  funext x
  let := o.fact_finrank_tangentSpace x
  rw [hodgeStar_apply, hodgeStar_apply, Orientation.formHodgeStar_formHodgeStar, Pi.smul_apply]

/-- In an even middle degree the Hodge star of forms is an involution, `⋆⋆α = α`. -/
@[simp]
theorem hodgeStar_hodgeStar_of_even (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (α : RoughForm I M ℝ k) : hodgeStar o rfl (hodgeStar o rfl α) = α := by
  rw [hodgeStar_hodgeStar, (hk.mul_right k).neg_one_pow, one_smul]

/-- In an even middle degree the Hodge star of forms is pointwise self-adjoint:
`⟨⋆α, β⟩ = ⟨α, ⋆β⟩` at every point. -/
theorem alternatingFormInner_hodgeStar_left (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (α β : RoughForm I M ℝ k) (x : M) :
    alternatingFormInner (TangentSpace I x) k (hodgeStar o rfl α x) (β x) =
      alternatingFormInner (TangentSpace I x) k (α x) (hodgeStar o rfl β x) := by
  let := o.fact_finrank_tangentSpace x
  rw [hodgeStar_apply, hodgeStar_apply]
  exact (o.orientationAt x).alternatingFormInner_formHodgeStar_left hk _ (α x) (β x)

/-- Reversing the orientation negates the Hodge star. -/
@[simp]
theorem hodgeStar_neg_orientation (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α : RoughForm I M ℝ k) : hodgeStar (-o) hkl α = -hodgeStar o hkl α := by
  funext x
  let := o.fact_finrank_tangentSpace x
  rw [hodgeStar_apply, Pi.neg_apply, hodgeStar_apply, Manifold.Orientation.orientationAt_neg,
    Orientation.formHodgeStar_neg_orientation]

/-- The Hodge star of a function is the function times the volume form, `⋆f = f vol`. -/
@[simp]
theorem hodgeStar_ofFunction (o : Manifold.Orientation I M (Fin m)) (hm : 0 + m = m)
    (f : M → ℝ) :
    hodgeStar o hm (ofFunction I f) = fun x ↦ f x • riemannianVolumeForm o x := by
  funext x
  let := o.fact_finrank_tangentSpace x
  rw [hodgeStar_apply, ofFunction_apply_eq_constOfIsEmpty,
    Orientation.formHodgeStar_constOfIsEmpty, riemannianVolumeForm_def]

/-- The Hodge star of a function times the volume form is the function, `⋆(f vol) = f`. -/
@[simp]
theorem hodgeStar_smul_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m))
    (hm : m + 0 = m) (f : M → ℝ) :
    hodgeStar o hm (fun x ↦ f x • riemannianVolumeForm o x) = ofFunction I f := by
  funext x
  let := o.fact_finrank_tangentSpace x
  rw [hodgeStar_apply, map_smul, riemannianVolumeForm_def,
    Orientation.formHodgeStar_volumeFormL, ofFunction_apply_eq_constOfIsEmpty]
  ext v
  simp

/-- **The Hodge star of a differential**: on an oriented Riemannian manifold of dimension
`l + 1`, the star of the differential of a function is the contraction of the volume form with the
gradient, `⋆df = ι_(grad f) vol`. -/
theorem hodgeStar_mextDeriv_ofFunction (o : Manifold.Orientation I M (Fin (l + 1)))
    (hl : 1 + l = l + 1) (f : M → ℝ) :
    hodgeStar o hl (mextDeriv (ofFunction I f)) =
      (riemannianVolumeForm o).interior (Manifold.mgradient I f) := by
  funext x
  let := o.fact_finrank_tangentSpace x
  -- The differential `df_x = ⟪grad f x, ·⟫` is the form dual to the vector `grad f x`.
  have hdf : mextDeriv (ofFunction I f) x = alternatingFormEquiv (TangentSpace I x) 1
      (exteriorPower.ιMulti ℝ 1 ![Manifold.mgradient I f x]) := by
    ext v
    rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
      alternatingFormEquiv_ιMulti_apply, Matrix.det_unique, Matrix.of_apply,
      Fin.default_eq_zero, Matrix.cons_val_zero, Manifold.inner_mgradient]
  ext w
  rw [hodgeStar_apply, hdf, Orientation.formHodgeStar_alternatingFormEquiv_ιMulti_apply,
    interior_apply, riemannianVolumeForm_apply, Fin.append_left_eq_cons]
  simp only [Function.comp_def, Fin.cast_cast, Fin.cast_eq_self, Matrix.cons_val_zero]
  -- `Matrix.vecCons`, used by the interior product, is by definition `Fin.cons`.
  rfl

/-- The Hodge star does not enlarge supports. -/
theorem tsupport_hodgeStar_subset (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (φ : RoughForm I M ℝ k) :
    _root_.tsupport (α := E [⋀^Fin l]→L[ℝ] ℝ) (hodgeStar o hkl φ) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ := by
  refine closure_mono fun x hx hφ ↦ hx ?_
  rw [hodgeStar_apply]
  exact (congrArg _ hφ).trans (map_zero _)

/-- The top form `⟨α, β⟩ vol` is supported in the support of `α`. -/
theorem tsupport_inner_smul_riemannianVolumeForm_subset (o : Manifold.Orientation I M (Fin m))
    (α β : RoughForm I M ℝ k) :
    _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ)
        (fun x ↦ alternatingFormInner (TangentSpace I x) k (α x) (β x) •
          riemannianVolumeForm o x) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α :=
  -- Supports are read in the model fibre; state the vanishing in the tangent fibre at `x`.
  closure_mono fun x hx hα ↦ hx
    (by simp [show α x = 0 from hα] :
      alternatingFormInner (TangentSpace I x) k (α x) (β x) • riemannianVolumeForm o x = 0)

/-- The top form `⟨α, β⟩ vol` is compactly supported when `α` is. -/
theorem isCompact_tsupport_inner_smul_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m))
    (α β : RoughForm I M ℝ k) (hα : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ)
      (fun x ↦ alternatingFormInner (TangentSpace I x) k (α x) (β x) •
        riemannianVolumeForm o x)) :=
  hα.of_isClosed_subset (_root_.isClosed_tsupport _)
    (tsupport_inner_smul_riemannianVolumeForm_subset o α β)

/-- The wedge `α ∧ ⋆β` is compactly supported when `α` or `β` is. -/
theorem isCompact_tsupport_wedge_hodgeStar {j : ℕ} (o : Manifold.Orientation I M (Fin m))
    (hjl : j + l = m) (α : RoughForm I M ℝ k) (β : RoughForm I M ℝ j)
    (h : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α) ∨
      IsCompact (_root_.tsupport (α := E [⋀^Fin j]→L[ℝ] ℝ) β)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin (k + l)]→L[ℝ] ℝ)
      (α.wedge (hodgeStar o hjl β))) := by
  rw [wedge_def]
  rcases h with h | h
  · exact h.of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin (k + l)]→L[ℝ] ℝ) _)
      (tsupport_wedgeWith_subset_left _ _ _)
  · exact h.of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin (k + l)]→L[ℝ] ℝ) _)
      ((tsupport_wedgeWith_subset_right _ _ _).trans (tsupport_hodgeStar_subset o hjl β))

end RoughForm

/-- The fibrewise Hodge star on real `k`-forms at `x`, as a continuous linear equivalence
`(TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ`. -/
def formHodgeStarCLE (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ :=
  letI := o.fact_finrank_tangentSpace x
  ((o.orientationAt x).formHodgeStar
    (hkl.trans (o.fact_finrank_tangentSpace x).out.symm)).toContinuousLinearEquiv

/-- The fibrewise Hodge star on real `k`-forms at `x`, as a continuous linear map
`(TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ`. -/
def formHodgeStarCLM (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ :=
  (formHodgeStarCLE o hkl x).toContinuousLinearMap

/-- Coercing `formHodgeStarCLE` to a continuous linear map gives `formHodgeStarCLM`. -/
@[simp]
theorem coe_formHodgeStarCLE (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (x : M) :
    (formHodgeStarCLE o hkl x :
      (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ) =
      formHodgeStarCLM o hkl x :=
  (rfl)

/-- `formHodgeStarCLE` evaluates as `Orientation.formHodgeStar` on the tangent space at `x`. -/
theorem formHodgeStarCLE_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    formHodgeStarCLE o hkl x α =
      (letI := o.fact_finrank_tangentSpace x
       (o.orientationAt x).formHodgeStar
         (hkl.trans (o.fact_finrank_tangentSpace x).out.symm) α) :=
  (rfl)

/-- `formHodgeStarCLM` evaluates as `Orientation.formHodgeStar` on the tangent space at `x`. -/
theorem formHodgeStarCLM_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    formHodgeStarCLM o hkl x α =
      (letI := o.fact_finrank_tangentSpace x
       (o.orientationAt x).formHodgeStar
         (hkl.trans (o.fact_finrank_tangentSpace x).out.symm) α) :=
  (rfl)

/-- `RoughForm.hodgeStar` at `x` applies `formHodgeStarCLM` to `φ x`. -/
theorem RoughForm.hodgeStar_eq_formHodgeStarCLM (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (φ : RoughForm I M ℝ k) (x : M) :
    RoughForm.hodgeStar o hkl φ x = formHodgeStarCLM o hkl x (φ x) :=
  (rfl)

/-- **The square of the fibrewise Hodge star**: `⋆ ∘ ⋆ = (-1) ^ (k l) • id`. -/
theorem formHodgeStarCLM_comp_formHodgeStarCLM (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (hlk : l + k = m) (x : M) :
    (formHodgeStarCLM o hlk x).comp (formHodgeStarCLM o hkl x) =
      (-1 : ℝ) ^ (k * l) • ContinuousLinearMap.id ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) := by
  ext α v
  let := o.fact_finrank_tangentSpace x
  simp [formHodgeStarCLM_apply, Orientation.formHodgeStar_formHodgeStar]

/-- The inverse of `formHodgeStarCLE` is `(-1) ^ (k l)` times the reverse-degree Hodge star. -/
theorem formHodgeStarCLE_symm_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (hlk : l + k = m) (x : M) (β : TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ) :
    (formHodgeStarCLE o hkl x).symm β = (-1 : ℝ) ^ (k * l) • formHodgeStarCLE o hlk x β := by
  apply (formHodgeStarCLE o hkl x).injective
  let := o.fact_finrank_tangentSpace x
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, formHodgeStarCLE_apply,
    formHodgeStarCLE_apply, Orientation.formHodgeStar_formHodgeStar, smul_smul,
    mul_comm l k, ← pow_add, ← two_mul, Even.neg_one_pow ⟨k * l, two_mul _⟩, one_smul]

/-- In an even middle degree, `formHodgeStarCLM` is an involution: `⋆ ∘ ⋆ = id`. -/
@[simp]
theorem formHodgeStarCLM_comp_self_of_even (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    (formHodgeStarCLM o rfl x).comp (formHodgeStarCLM o rfl x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) := by
  rw [formHodgeStarCLM_comp_formHodgeStarCLM o rfl rfl x, (hk.mul_right k).neg_one_pow, one_smul]

/-- In an even middle degree, `formHodgeStarCLE` is its own inverse. -/
@[simp]
theorem formHodgeStarCLE_symm_of_even (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    (formHodgeStarCLE o rfl x).symm = formHodgeStarCLE o rfl x := by
  ext α v
  rw [formHodgeStarCLE_symm_apply o rfl rfl x α, (hk.mul_right k).neg_one_pow, one_smul]

/-- Reversing the orientation negates `formHodgeStarCLM`. -/
@[simp]
theorem formHodgeStarCLM_neg_orientation (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (x : M) : formHodgeStarCLM (-o) hkl x = -formHodgeStarCLM o hkl x := by
  ext α v
  let := o.fact_finrank_tangentSpace x
  simp [formHodgeStarCLM_apply, Manifold.Orientation.orientationAt_neg]

/-- `formHodgeStarCLM` preserves the Gram inner product `alternatingFormInner` on every fibre. -/
theorem alternatingFormInner_formHodgeStarCLM (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (x : M) (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) l
        (formHodgeStarCLM o hkl x α) (formHodgeStarCLM o hkl x β) =
      alternatingFormInner (TangentSpace I x) k α β := by
  let := o.fact_finrank_tangentSpace x
  exact (o.orientationAt x).alternatingFormInner_formHodgeStar _ α β

/-- In an even middle degree, `formHodgeStarCLM` is self-adjoint for `alternatingFormInner`. -/
theorem alternatingFormInner_formHodgeStarCLM_left (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) k (formHodgeStarCLM o rfl x α) β =
      alternatingFormInner (TangentSpace I x) k α (formHodgeStarCLM o rfl x β) := by
  let := o.fact_finrank_tangentSpace x
  exact (o.orientationAt x).alternatingFormInner_formHodgeStar_left hk _ α β

/-- The Hodge star in the frame of a tangent trivialization: at a point `y` of the base set of the
trivialization at `x`, with frame `e.symmL y ∘ b` for `b` the standard basis of the model space,
`⋆φ` is computed from the values of `φ` on the frame, the volume of the frame and the inverse
chart Gram matrix. -/
private theorem hodgeStar_symmL_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (φ : RoughForm I M ℝ k) (σ : Fin (finrank ℝ E) ≃ Fin m) {x y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet) (v : Fin l → E) :
    RoughForm.hodgeStar o hkl φ y ((trivializationAt E (TangentSpace I) x).symmL ℝ y ∘ v) =
      riemannianVolumeForm o y (fun i ↦ (trivializationAt E (TangentSpace I) x).symmL ℝ y
        ((Module.finBasis ℝ E).reindex σ i)) *
      ∑ s : powersetCard (Fin m) k, φ y (fun i ↦ (trivializationAt E (TangentSpace I) x).symmL ℝ y
        ((Module.finBasis ℝ E).reindex σ (powersetCard.ofFinEmbEquiv.symm s i))) *
        ((Module.finBasis ℝ E).reindex σ).det (Fin.append (fun i ↦ ∑ j,
          (Riemannian.Tensor.chartInvGramMatrix (I := I) x y).submatrix σ.symm σ.symm
            (powersetCard.ofFinEmbEquiv.symm s i) j • (Module.finBasis ℝ E).reindex σ j) v ∘
          Fin.cast hkl.symm) := by
  set e := trivializationAt E (TangentSpace I) x
  set b := (Module.finBasis ℝ E).reindex σ
  let := o.fact_finrank_tangentSpace y
  let L := e.linearEquivAt ℝ y hy
  -- The frame `B = e.symmL y ∘ b` is the basis of the tangent space given by the trivialization.
  let B : Basis (Fin m) ℝ (TangentSpace I y) := e.basisAt b hy
  have hB : ⇑B = fun i ↦ e.symmL ℝ y (b i) := funext (Manifold.basisAt_apply b hy)
  have hL (w : E) : L (e.symmL ℝ y w) = w := by
    have : e.symmL ℝ y w = L.symm w := by
      rw [Trivialization.linearEquivAt_symm_apply, Trivialization.symmL_apply _ hy]
    rw [this, LinearEquiv.apply_symm_apply]
  -- Its Gram matrix is the reindexed chart Gram matrix, with the reindexed inverse.
  have hinv : (Matrix.gram ℝ B)⁻¹ =
      (Riemannian.Tensor.chartInvGramMatrix (I := I) x y).submatrix σ.symm σ.symm := by
    rw [Riemannian.Tensor.gram_basisAt_finBasis_reindex, Matrix.inv_submatrix_equiv,
      Riemannian.Tensor.chartInvGramMatrix_def]
  rw [RoughForm.hodgeStar_apply, Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum _ _ B,
    riemannianVolumeForm_apply, ← hB, hinv]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  · simp only [hB, Function.comp_def, e]
  -- Read the determinant in the frame back in the model space through the trivialization: by
  -- definition of `Trivialization.basisAt`, the frame `B` is the image of `b` under `L.symm`.
  have hBL : B = b.map L.symm := by simp only [B, L, Trivialization.basisAt]
  rw [hBL, Module.Basis.det_map, LinearEquiv.symm_symm]
  congr 1
  funext i
  simp only [Function.comp_apply]
  generalize Fin.cast _ i = j
  induction j using Fin.addCases with
  | left a => simp [map_sum, map_smul]
  | right a =>
    simp only [Fin.append_right, Function.comp_apply]
    exact hL _

section Smooth

variable {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- **Local regularity of the Hodge star**: if a rough `k`-form is `C^n` as an alternating-bundle
section at `x`, then its Hodge star is `C^n` at `x`, for a `C^n` metric on a `C^(n+1)` manifold. -/
theorem RoughForm.contMDiffAt_hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    {φ : RoughForm I M ℝ k} {x : M}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (φ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ) y (RoughForm.hodgeStar o hkl φ y)) x := by
  classical
  -- Read in the trivialization at `x`, it suffices that each value on a fixed tuple `v` of model
  -- vectors is `C^n` at `x`.
  simp only [contMDiffAt_section_iff,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    contMDiffAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply] at hφ ⊢
  intro v
  set e := trivializationAt E (TangentSpace I) x
  have hm : finrank ℝ E = m := by simpa using o.card_eq.symm
  let σ : Fin (finrank ℝ E) ≃ Fin m := finCongr hm
  let b : Basis (Fin m) ℝ E := (Module.finBasis ℝ E).reindex σ
  let D : E [⋀^Fin m]→L[ℝ] ℝ := AlternatingMap.toContinuousAlternatingMap b.det
  have hbase : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  -- Every ingredient of `hodgeStar_symmL_apply` is `C^n` at `x`: the coordinates of `φ` and of
  -- the volume form, and the inverse chart Gram matrix.
  have hvc := isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.1
    (isSmoothForm_riemannianVolumeForm (n := n) o) x b
  let G' : M → Matrix (Fin m) (Fin m) ℝ := fun y ↦
    (Riemannian.Tensor.chartInvGramMatrix (I := I) x y).submatrix σ.symm σ.symm
  have hG' (i j : Fin m) : ContMDiffAt I 𝓘(ℝ) n (fun y ↦ G' y i j) x :=
    (Riemannian.Tensor.contMDiffOn_chartInvGramMatrix_entry (I := I) (n := n) x _ _).contMDiffAt
      hbase
  let W : powersetCard (Fin m) k → M → Fin m → E := fun s y ↦
    Fin.append (fun i ↦ ∑ j, G' y (powersetCard.ofFinEmbEquiv.symm s i) j • b j) v ∘
      Fin.cast hkl.symm
  have hW (s : powersetCard (Fin m) k) : ContMDiffAt I 𝓘(ℝ) n (fun y ↦ D (W s y)) x := by
    refine D.toContinuousMultilinearMap.contDiff.comp_contMDiffAt
      (contMDiffAt_pi_module_iff.2 fun i ↦ ?_)
    simp only [W, Function.comp_apply]
    generalize Fin.cast hkl.symm i = j
    induction j using Fin.addCases with
    | left a =>
      simp only [Fin.append_left]
      exact contMDiffAt_finsetSum fun j _ ↦ (hG' _ _).smul contMDiffAt_const
    | right a =>
      simp only [Fin.append_right]
      exact contMDiffAt_const
  have hsum : ContMDiffAt I 𝓘(ℝ) n (fun y ↦
      riemannianVolumeForm o y (e.symmL ℝ y ∘ b) *
      ∑ s : powersetCard (Fin m) k, φ y (e.symmL ℝ y ∘ (b ∘ powersetCard.ofFinEmbEquiv.symm s)) *
        D (W s y)) x :=
    hvc.mul (contMDiffAt_finsetSum (t := Finset.univ) fun s _ ↦ (hφ _).mul (hW s))
  -- On the base set, the value of `⋆φ` is given by `hodgeStar_symmL_apply`.
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hbase] with y hy
  rw [hodgeStar_symmL_apply o hkl φ σ hy v]
  simp only [Function.comp_def, D, AlternatingMap.coe_toContinuousAlternatingMap, W, G', b, e]

/-- **The Hodge star of a `C^n` form is `C^n`**, for a `C^n` metric on a `C^(n+1)` manifold. -/
theorem IsSmoothForm.hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I n φ) :
    IsSmoothForm I n (RoughForm.hodgeStar o hkl φ) :=
  (isSmoothForm_def n _).2 fun x ↦ RoughForm.contMDiffAt_hodgeStar o hkl (hφ.contMDiff x)

/-- **The Hodge star is a `C^n` section of the `Hom` bundle** from real `k`-forms to real
`l`-forms, for a `C^n` metric on a `C^(n+1)` manifold. -/
theorem contMDiff_formHodgeStarCLM (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    ContMDiff I (I.prod 𝓘(ℝ, (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' ((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun y ↦ (TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
          TangentSpace I y [⋀^Fin l]→L[ℝ] ℝ)
        x (formHodgeStarCLM o hkl x)) := by
  intro x
  let Fk := E [⋀^Fin k]→L[ℝ] ℝ
  let Fl := E [⋀^Fin l]→L[ℝ] ℝ
  let Vk : M → Type _ := fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ
  let Vl : M → Type _ := fun y ↦ TangentSpace I y [⋀^Fin l]→L[ℝ] ℝ
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_clm_apply.2 fun α ↦ ?_⟩
  let ek := trivializationAt Fk Vk x
  let el := trivializationAt Fl Vl x
  have hxk : x ∈ ek.baseSet := FiberBundle.mem_baseSet_trivializationAt Fk Vk x
  have hxl : x ∈ el.baseSet := FiberBundle.mem_baseSet_trivializationAt Fl Vl x
  have hsec : ContMDiffAt I (I.prod 𝓘(ℝ, Fk)) n
      (fun y ↦ TotalSpace.mk' Fk (E := Vk) y (ek.symm y α)) x := by
    rw [contMDiffAt_section_iff]
    refine (contMDiffAt_const (c := α)).congr_of_eventuallyEq ?_
    filter_upwards [ek.open_baseSet.mem_nhds hxk] with y hy
    exact congr(Prod.snd $(ek.apply_mk_symm hy α))
  have hstar := (contMDiffAt_section_iff (x₀ := x)).1
    (RoughForm.contMDiffAt_hodgeStar o hkl (φ := fun y ↦ ek.symm y α) hsec)
  refine hstar.congr_of_eventuallyEq ?_
  filter_upwards [ek.open_baseSet.mem_nhds hxk, el.open_baseSet.mem_nhds hxl] with y hyk hyl
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [ek.symmL_apply hyk, Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hyl]
  rfl

/-- The Hodge star induces a `C^n` map between the total spaces of real `k`-forms and real
`l`-forms. -/
theorem contMDiff_formHodgeStar_totalSpace (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) :
    ContMDiff (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) n
      (fun p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) ↦
        TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ)
          p.proj (formHodgeStarCLM o hkl p.proj p.2)) :=
  (contMDiff_hom_bundle_iff (F₁ := E [⋀^Fin k]→L[ℝ] ℝ) (F₂ := E [⋀^Fin l]→L[ℝ] ℝ)
    (E₁ := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
    (E₂ := fun x : M ↦ TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ) (formHodgeStarCLM o hkl)).1
    (contMDiff_formHodgeStarCLM o hkl)

end Smooth

/-- The `C^n` diffeomorphism between the total spaces of real `k`-forms and real `l`-forms
induced by the Hodge star. -/
def formHodgeStarDiffeomorph (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
      ≃ₘ^n⟮I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ), I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)⟯
    TotalSpace (E [⋀^Fin l]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ) :=
  bundleDiffeomorph (IB := I) (n := n) (F₁ := E [⋀^Fin k]→L[ℝ] ℝ) (F₂ := E [⋀^Fin l]→L[ℝ] ℝ)
    (E₁ := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
    (E₂ := fun x : M ↦ TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ)
    (formHodgeStarCLE o hkl) (contMDiff_formHodgeStar_totalSpace o hkl)

/-- `formHodgeStarDiffeomorph` acts on `(x, α)` by `formHodgeStarCLE` in the fibre over `x`. -/
@[simp]
theorem formHodgeStarDiffeomorph_apply (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    formHodgeStarDiffeomorph n o hkl p = ⟨p.proj, formHodgeStarCLE o hkl p.proj p.2⟩ :=
  bundleDiffeomorph_apply _ _ p

/-- The inverse of `formHodgeStarDiffeomorph` acts in each fibre by `(formHodgeStarCLE o hkl x)⁻¹`.
-/
@[simp]
theorem formHodgeStarDiffeomorph_symm_apply (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (p : TotalSpace (E [⋀^Fin l]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ)) :
    (formHodgeStarDiffeomorph n o hkl).symm p =
      ⟨p.proj, (formHodgeStarCLE o hkl p.proj).symm p.2⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

namespace SmoothForm

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Hodge star of smooth real `k`-forms on an oriented manifold of dimension `m = k + l`
with a smooth Riemannian metric. -/
def hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l :=
  haveI : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  (RoughForm.hodgeStar o hkl).restrict fun φ hφ ↦
    ((SmoothForm.isSmoothForm ⟨φ, hφ⟩).hodgeStar o hkl).mem_smoothBundleForms

end SmoothForm

end Main

section Theorems

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}
  [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

namespace SmoothForm

/-- The Hodge star of a smooth form is the Hodge star of the underlying rough form. -/
@[simp]
theorem coe_hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (φ : SmoothForm I M ℝ k) :
    (hodgeStar o hkl φ : RoughForm I M ℝ l) = RoughForm.hodgeStar o hkl φ :=
  (rfl)

/-- **The square of the Hodge star of smooth forms**: `⋆⋆α = (-1) ^ (k l) α`. -/
theorem hodgeStar_hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (hlk : l + k = m) (α : SmoothForm I M ℝ k) :
    hodgeStar o hlk (hodgeStar o hkl α) = (-1 : ℝ) ^ (k * l) • α :=
  Subtype.ext (RoughForm.hodgeStar_hodgeStar o hkl hlk α)

/-- **The wedge characterization of the Hodge star of smooth forms**: the top form
`⟨α, β⟩ vol` is the degree transport of the smooth form `α ∧ ⋆β`. -/
theorem inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α β : SmoothForm I M ℝ k) :
    (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (β.1 x) •
        riemannianVolumeForm o x) =
      (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) hkl
        (wedge α (hodgeStar o hkl β)) : RoughForm I M ℝ m) := by
  funext x
  ext v
  rw [cast_apply, coe_wedge, coe_hodgeStar, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    ← ContinuousAlternatingMap.wedge_def, RoughForm.wedge_hodgeStar_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  simp only [Function.comp_def, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]

/-- The top form `⟨α, β⟩ vol` of two smooth forms is smooth. -/
theorem isSmoothForm_inner_smul_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α β : SmoothForm I M ℝ k) :
    IsSmoothForm I ∞ (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (β.1 x) •
      riemannianVolumeForm o x) := by
  rw [inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o hkl]
  exact SmoothForm.isSmoothForm _

/-- Reversing the orientation negates the Hodge star of smooth forms. -/
@[simp]
theorem hodgeStar_neg_orientation (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α : SmoothForm I M ℝ k) : hodgeStar (-o) hkl α = -hodgeStar o hkl α :=
  Subtype.ext (RoughForm.hodgeStar_neg_orientation o hkl α)

/-- The Hodge star of smooth forms commutes with multiplication by a smooth function,
`⋆(f α) = f ⋆α`. -/
@[simp]
theorem hodgeStar_funSMulₗ (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (f : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ k) :
    hodgeStar o hkl (funSMulₗ f α) = funSMulₗ f (hodgeStar o hkl α) :=
  Subtype.ext <| funext fun x ↦ by
    simp only [coe_hodgeStar, RoughForm.hodgeStar_apply, coe_funSMulₗ, map_smul]

/-- The smooth zero-form `⋆(α ∧ ⋆β)`, linear in `β`, representing the pointwise inner product
`⟨α, β⟩` of smooth `k`-forms on an oriented Riemannian `(k + l)`-manifold. -/
def innerZeroForm (o : Manifold.Orientation I M (Fin (k + l)))
    (α : SmoothForm I M ℝ k) : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ 0 :=
  hodgeStar o (Nat.add_zero (k + l)) ∘ₗ wedge α ∘ₗ hodgeStar o rfl

/-- Unfolding `innerZeroForm` as `⋆(α ∧ ⋆β)`. -/
theorem innerZeroForm_def (o : Manifold.Orientation I M (Fin (k + l)))
    (α β : SmoothForm I M ℝ k) :
    innerZeroForm o α β = hodgeStar o (Nat.add_zero (k + l)) (wedge α (hodgeStar o rfl β)) :=
  (rfl)

/-- Evaluating `innerZeroForm o α β` at `x : M` recovers `alternatingFormInner` of `α_x` and
`β_x`. -/
@[simp]
theorem innerZeroForm_apply (o : Manifold.Orientation I M (Fin (k + l)))
    (α β : SmoothForm I M ℝ k) (x : M) (u : Fin 0 → TangentSpace I x) :
    (innerZeroForm o α β).1 x u =
      alternatingFormInner (TangentSpace I x) k (α.1 x) (β.1 x) := by
  let _ := o.fact_finrank_tangentSpace x
  have hu : u = 0 := Subsingleton.elim _ _
  rw [hu, innerZeroForm, LinearMap.comp_apply, LinearMap.comp_apply, coe_hodgeStar,
    RoughForm.hodgeStar_apply]
  have hw : (wedge α (hodgeStar o rfl β)).1 x =
      (α.1 x).wedge ((o.orientationAt x).formHodgeStar
        (o.fact_finrank_tangentSpace x).out.symm (β.1 x)) := by
    ext w
    rw [coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
      ← ContinuousAlternatingMap.wedge_def, coe_hodgeStar, RoughForm.hodgeStar_apply]
  rw [hw]
  exact (o.orientationAt x).formHodgeStar_wedge_formHodgeStar_apply_zero _ _ (α.1 x) (β.1 x)

/-- The Hodge star commutes with right multiplication by a smooth zero-form. -/
theorem hodgeStar_wedge_zero_right (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (φ : SmoothForm I M ℝ k) (f : SmoothForm I M ℝ 0) :
    hodgeStar o hkl (wedge φ f) = wedge (hodgeStar o hkl φ) f := by
  apply Subtype.ext
  funext x
  let _ := o.fact_finrank_tangentSpace x
  ext v
  rw [wedge_apply_zero_right, coe_hodgeStar, RoughForm.hodgeStar_apply,
    wedge_zero_right_apply_eq_smul, map_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    mul_comm, coe_hodgeStar, RoughForm.hodgeStar_apply]

end SmoothForm

end Theorems

end TauCeti
