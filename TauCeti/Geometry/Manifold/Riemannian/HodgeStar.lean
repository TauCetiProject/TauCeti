/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The Hodge star of differential forms on an oriented Riemannian manifold

On an oriented Riemannian manifold `M` of dimension `m = k + l`, the Hodge star of the tangent
spaces, `Orientation.formHodgeStar`, applied fibrewise sends real `k`-forms to real `l`-forms.
This is `TauCeti.RoughForm.hodgeStar`. Fibrewise it satisfies `α ∧ ⋆β = ⟨α, β⟩ vol`, with `vol`
the Riemannian volume form, `⋆⋆ = (-1) ^ (k l)`, and it changes sign with the orientation.

For a `C^n` metric on a `C^(n+1)` manifold the star preserves `C^n` forms
(`TauCeti.IsSmoothForm.hodgeStar`), so it restricts to a linear map of smooth forms,
`TauCeti.SmoothForm.hodgeStar`. In the frame `(∂ᵢ)` of a tangent trivialization the star is
computed by `(⋆α)(w) = ∑ α(∂_{i₁}, …, ∂_{iₖ}) vol(gⁱ¹ʲ∂ⱼ, …, gⁱᵏʲ∂ⱼ, w)` through the inverse
metric `gⁱʲ` (`Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum`), and the inverse metric,
the volume form and the coefficients of `α` are all `C^n`. Smoothness is tested on the values on
fixed tuples of model vectors (`TauCeti.contMDiffAt_continuousAlternatingMap_apply`).

## Main definitions

* `TauCeti.RoughForm.hodgeStar`: the Hodge star of rough real forms.
* `TauCeti.SmoothForm.hodgeStar`: the Hodge star of smooth real forms.

## Main results

* `TauCeti.IsSmoothForm.hodgeStar`: the Hodge star of a `C^n` form is `C^n`.
* `TauCeti.RoughForm.wedge_hodgeStar_apply`: `α ∧ ⋆β = ⟨α, β⟩ vol`.
* `TauCeti.RoughForm.hodgeStar_hodgeStar`: `⋆⋆α = (-1) ^ (k l) α`.

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
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
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

/-- Reversing the orientation negates the Hodge star. -/
@[simp]
theorem hodgeStar_neg_orientation (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α : RoughForm I M ℝ k) : hodgeStar (-o) hkl α = -hodgeStar o hkl α := by
  funext x
  let := o.fact_finrank_tangentSpace x
  rw [hodgeStar_apply, Pi.neg_apply, hodgeStar_apply, Manifold.Orientation.orientationAt_neg,
    Orientation.formHodgeStar_neg_orientation]

end RoughForm

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
  -- The frame `B = e.symmL y ∘ b` is the image of `b` under the inverse trivialization.
  let B : Basis (Fin m) ℝ (TangentSpace I y) := b.map L.symm
  have hB : ⇑B = fun i ↦ e.symmL ℝ y (b i) := by
    funext i
    rw [Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply,
      Trivialization.symmL_apply _ hy]
  have hL (w : E) : L (e.symmL ℝ y w) = w := by
    have : e.symmL ℝ y w = L.symm w := by
      rw [Trivialization.linearEquivAt_symm_apply, Trivialization.symmL_apply _ hy]
    rw [this, LinearEquiv.apply_symm_apply]
  -- Its Gram matrix is the reindexed chart Gram matrix, with the reindexed inverse.
  have hinv : (Matrix.gram ℝ B)⁻¹ =
      (Riemannian.Tensor.chartInvGramMatrix (I := I) x y).submatrix σ.symm σ.symm := by
    have hgram : Matrix.gram ℝ B =
        (Riemannian.Tensor.chartGramMatrix (I := I) x y).submatrix σ.symm σ.symm := by
      rw [hB, Riemannian.Tensor.gram_symmL_finBasis_reindex]
    have hy' : y ∈ (chartAt H x).source := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hy
    rw [hgram]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.submatrix_mul_equiv,
      Riemannian.Tensor.chartInvGramMatrix_mul_chartGramMatrix _ hy', Matrix.submatrix_one_equiv]
  rw [RoughForm.hodgeStar_apply, Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum _ _ B,
    riemannianVolumeForm_apply, ← hB, hinv]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  · simp only [hB, Function.comp_def, e]
  -- Read the determinant in the frame back in the model space through the trivialization.
  rw [Module.Basis.det_map, LinearEquiv.symm_symm]
  congr 1
  funext i
  simp only [Function.comp_apply]
  generalize Fin.cast _ i = j
  induction j using Fin.addCases with
  | left a => simp [B, map_sum, map_smul]
  | right a =>
    simp only [Fin.append_right, Function.comp_apply]
    exact hL _

section Smooth

variable {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- **The Hodge star of a `C^n` form is `C^n`**, for a `C^n` metric on a `C^(n+1)` manifold. -/
theorem IsSmoothForm.hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I n φ) :
    IsSmoothForm I n (RoughForm.hodgeStar o hkl φ) := by
  classical
  -- Read in the trivialization at `x`, it suffices that each value on a fixed tuple `v` of model
  -- vectors is `C^n` at `x`.
  rw [isSmoothForm_def]
  intro x
  rw [contMDiffAt_section]
  simp_rw [RoughForm.trivializationAt_apply_snd]
  rw [contMDiffAt_continuousAlternatingMap_apply]
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
  have hφc := contMDiffAt_continuousAlternatingMap_apply.1 <| by
    simpa only [RoughForm.trivializationAt_apply_snd] using
      (contMDiffAt_section x).1 ((isSmoothForm_def n φ).1 hφ x)
  have hvc := contMDiffAt_continuousAlternatingMap_apply.1 (by
    simpa only [RoughForm.trivializationAt_apply_snd] using (contMDiffAt_section x).1
      ((isSmoothForm_def n _).1 (isSmoothForm_riemannianVolumeForm (n := n) o) x)) b
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
      (riemannianVolumeForm o y).compContinuousLinearMap (e.symmL ℝ y) b *
      ∑ s : powersetCard (Fin m) k, (φ y).compContinuousLinearMap (e.symmL ℝ y)
        (b ∘ powersetCard.ofFinEmbEquiv.symm s) * D (W s y)) x :=
    hvc.mul (contMDiffAt_finsetSum (t := Finset.univ) fun s _ ↦ (hφc _).mul (hW s))
  -- On the base set, the value of `⋆φ` is given by `hodgeStar_symmL_apply`.
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hbase] with y hy
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    hodgeStar_symmL_apply o hkl φ σ hy v]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, D,
    AlternatingMap.coe_toContinuousAlternatingMap, W, G', b, e]

end Smooth

namespace SmoothForm

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Hodge star of smooth real `k`-forms on an oriented manifold of dimension `m = k + l`
with a smooth Riemannian metric. -/
def hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l :=
  haveI : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  (RoughForm.hodgeStar o hkl).restrict fun φ hφ ↦
    ((SmoothForm.isSmoothForm ⟨φ, hφ⟩).hodgeStar o hkl).mem_smoothForms

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

end SmoothForm

end TauCeti
