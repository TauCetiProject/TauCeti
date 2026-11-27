/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.HilbertSchmidt
public import TauCeti.Analysis.Complex.OperatorNorm
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Representing chart covector fields by `(0,1)`-forms

Let `M` be a complex curve and `V → M` a real vector bundle with finite-dimensional model fibre
`F`, a complex vector space, with a finite bundle atlas `A`, and smooth metrics on `TM` and `V`.
In chart `i`, a `V`-valued one-form at the point read at `z` is read as a real linear map
`ℂ →L[ℝ] F`, and a complex antilinear one, `w ↦ conj w • v`, is determined by its value `v` at
`1` (`ContinuousLinearMap.antilinearOfOneL`).

The Hilbert–Schmidt inner product of the one-forms read as the antilinear maps with values `u` and
`v` at `1` is a bilinear form on `F`, the *chart Gram form*
(`TauCeti.FiniteBundleAtlas.chartZeroOneGram`). It is smooth in `z`
(`TauCeti.FiniteBundleAtlas.contDiffOn_chartZeroOneGram`) and nondegenerate on the chart image
(`TauCeti.FiniteBundleAtlas.isInvertible_chartZeroOneGram`), since the Hilbert–Schmidt inner
product is positive definite. Inverting it represents a smooth covector field `g` on `F` by a
smooth field `R` of values at `1`: the pairing of the one-form read as `antilinearOfOneL (R z)`
with every one-form read as an antilinear map `a` is `g z (a 1)`
(`TauCeti.FiniteBundleAtlas.exists_contDiffOn_hilbertSchmidtInner_eq`). This converts the chart
pairings `∫ g z (a z 1) dz` of `(0,1)`-forms into Hilbert–Schmidt pairings on `M`.

## Main definitions

* `TauCeti.FiniteBundleAtlas.chartZeroOneGram`: the chart Gram form.

## Main results

* `TauCeti.FiniteBundleAtlas.contDiffOn_chartZeroOneGram`: it is smooth on the chart image.
* `TauCeti.FiniteBundleAtlas.isInvertible_chartZeroOneGram`: it is invertible on the chart image.
* `TauCeti.FiniteBundleAtlas.exists_contDiffOn_hilbertSchmidtInner_eq`: smooth covector fields are
  represented through the Hilbert–Schmidt inner product.
-/

public section

noncomputable section

open Bundle Module Set
open ContinuousLinearMap (antilinearOfOneL)
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

namespace FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle V] [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  (A : FiniteBundleAtlas ℂ M F V) (i : Fin A.n)

/-- **The chart Gram form.** At `z` in chart `i`, the bilinear form `(u, v) ↦ ⟪αᵤ, αᵥ⟫_HS` on `F`,
where `αᵤ` is the one-form at the point read at `z` that reads as the antilinear map
`antilinearOfOneL u` with value `u` at `1`, and `⟪·, ·⟫_HS` is the Hilbert–Schmidt inner product
of the metrics on `TM` and `V` (`TauCeti.FiniteBundleAtlas.chartZeroOneGram_apply_apply`). -/
def chartZeroOneGram (z : ℂ) : F →L[ℝ] F →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap <|
    (LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] ℝ) ≃ₗ[ℝ] F →L[ℝ] ℝ).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun u v ↦
          ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z)
            (antilinearOfOneL F u)).hilbertSchmidtInner
              ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z) (antilinearOfOneL F v)))
        (fun u u' v ↦ by
          simp only [map_add, ContinuousLinearMap.hilbertSchmidtInner_add_left])
        (fun c u v ↦ by
          simp only [map_smul, ContinuousLinearMap.hilbertSchmidtInner_smul_left, smul_eq_mul])
        (fun u v v' ↦ by
          simp only [map_add, ContinuousLinearMap.hilbertSchmidtInner_add_right])
        (fun c u v ↦ by
          simp only [map_smul, ContinuousLinearMap.hilbertSchmidtInner_smul_right, smul_eq_mul])

/-- The chart Gram form is the Hilbert–Schmidt inner product of the one-forms read as the
antilinear maps with values `u` and `v` at `1`. -/
theorem chartZeroOneGram_apply_apply (z : ℂ) (u v : F) :
    A.chartZeroOneGram i z u v =
      ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z)
        (antilinearOfOneL F u)).hilbertSchmidtInner
          ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z) (antilinearOfOneL F v)) :=
  (rfl)

omit [FiniteDimensional ℝ F] in
/-- The antilinear map with value `u` at `1` has value `u` at `1`, so `antilinearOfOneL` is
injective. -/
private theorem antilinearOfOneL_injective : Function.Injective (antilinearOfOneL F) :=
  fun u v h ↦ by
    simpa only [ContinuousLinearMap.antilinearOfOneL_apply_apply_one] using
      congrArg (fun L : ℂ →L[ℝ] F ↦ L 1) h

/-- **The chart Gram form is invertible** at every point of the image of chart `i`. -/
theorem isInvertible_chartZeroOneGram {z : ℂ} (hz : z ∈ A.image i) :
    (A.chartZeroOneGram i z).IsInvertible := by
  have hb : (A.chart i).symm z ∈ (A.tangentHom.triv i).baseSet := by
    have := A.tangentHom.image_subset_target_inter_preimage_baseSet i
    rw [image_tangentHom] at this
    exact (this hz).2
  have hinj : Function.Injective (A.chartZeroOneGram i z) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu ↦ antilinearOfOneL_injective ?_
    have h0 := congrArg (fun L : F →L[ℝ] ℝ ↦ L u) hu
    simp only [chartZeroOneGram_apply_apply, zero_apply,
      ContinuousLinearMap.hilbertSchmidtInner_self_eq_zero_iff] at h0
    rw [map_zero, ← (A.tangentHom.triv i).continuousLinearMapAt_symmL (R := ℝ) hb
      (antilinearOfOneL F u), h0, map_zero]
  have hdim : finrank ℝ F = finrank ℝ (F →L[ℝ] ℝ) :=
    Subspace.dual_finrank_eq.symm.trans LinearMap.toContinuousLinearMap.finrank_eq
  exact ⟨(LinearMap.linearEquivOfInjective _ hinj hdim).toContinuousLinearEquiv, rfl⟩

variable [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x] in
/-- The one-form `y ↦ e.symm y L` that reads as the constant `L` in a trivialization `e` of the
bundle of `V`-valued one-forms is smooth on the base set of `e`. -/
private theorem contMDiffOn_symm_const
    (e : Trivialization (ℂ →L[ℝ] F)
      (π (ℂ →L[ℝ] F) (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)))
    [MemTrivializationAtlas e] (L : ℂ →L[ℝ] F) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) y
        (e.symm y L)) e.baseSet :=
  e.contMDiffOn_section_baseSet_iff.2 <|
    contMDiffOn_const.congr fun _ hy ↦ by rw [e.apply_mk_symm hy L]

/-- **The chart Gram form is smooth** on the image of chart `i`. -/
theorem contDiffOn_chartZeroOneGram :
    ContDiffOn ℝ ∞ (A.chartZeroOneGram i) (A.image i) := by
  set e := A.tangentHom.triv i
  refine contDiffOn_clm_apply.2 fun u ↦ contDiffOn_clm_apply.2 fun v ↦ ?_
  simp only [chartZeroOneGram_apply_apply]
  -- The Hilbert–Schmidt inner product of the two one-forms is smooth on the base set of `e`.
  have hφ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun y ↦ (e.symm y (antilinearOfOneL F u)).hilbertSchmidtInner
        (e.symm y (antilinearOfOneL F v))) e.baseSet := fun y hy ↦
    have hy' := e.open_baseSet.mem_nhds hy
    (((contMDiffOn_symm_const e _).contMDiffAt hy').hilbertSchmidtInner_bundle
      ((contMDiffOn_symm_const e _).contMDiffAt hy')).contMDiffWithinAt
  rw [← contMDiffOn_iff_contDiffOn]
  have himage := A.tangentHom.image_subset_target_inter_preimage_baseSet i
  rw [image_tangentHom] at himage
  refine (hφ.comp (contMDiffOn_chart_symm.mono fun z hz ↦ (himage hz).1)
    fun z hz ↦ (himage hz).2).congr fun z hz ↦ ?_
  have hb : (A.chart i).symm z ∈ e.baseSet := (himage hz).2
  exact congrArg₂ ContinuousLinearMap.hilbertSchmidtInner (Trivialization.symmL_apply _ hb _)
    (Trivialization.symmL_apply _ hb _)

/-- **Representing a chart covector field.** Let `W` be a subset of the image of chart `i` and `g`
a covector field on `F` that is smooth on `W`. There is a field `R : ℂ → F`, smooth on `W`, such
that at every `z ∈ W` the one-form read as the antilinear map `antilinearOfOneL (R z)` pairs with
every one-form read as a complex antilinear map `a` to `g z (a 1)`, under the Hilbert–Schmidt
inner product. -/
theorem exists_contDiffOn_hilbertSchmidtInner_eq {W : Set ℂ} (hW : W ⊆ A.image i)
    {g : ℂ → F →L[ℝ] ℝ} (hg : ContDiffOn ℝ ∞ g W) :
    ∃ R : ℂ → F, ContDiffOn ℝ ∞ R W ∧ ∀ z ∈ W, ∀ a : ℂ →L[ℝ] F,
      (∀ w, a (Complex.I • w) = -(Complex.I • a w)) →
        ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z)
          (antilinearOfOneL F (R z))).hilbertSchmidtInner
            ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z) a) = g z (a 1) := by
  refine ⟨fun z ↦ (A.chartZeroOneGram i z).inverse (g z), ?_, fun z hz a ha ↦ ?_⟩
  · refine ContDiffOn.clm_apply (fun z hz ↦ ?_) hg
    exact (isInvertible_chartZeroOneGram A i (hW hz)).contDiffAt_map_inverse.comp_contDiffWithinAt
      z ((contDiffOn_chartZeroOneGram A i).mono hW z hz)
  · rw [← ContinuousLinearMap.antilinearOfOneL_apply_eq_of_antilinear a ha,
      ← chartZeroOneGram_apply_apply,
      (isInvertible_chartZeroOneGram A i (hW hz)).self_apply_inverse,
      ContinuousLinearMap.antilinearOfOneL_apply_apply_one]

end FiniteBundleAtlas

end TauCeti
