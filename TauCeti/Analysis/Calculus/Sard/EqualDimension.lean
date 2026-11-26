/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Codex
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import TauCeti.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Lindelof

/-!
# Sard's lemma in equal dimensions

This file proves the equal-dimensional case of Sard's theorem for maps between two possibly
different finite-dimensional real normed spaces.  A differentiable map sends any set on which its
derivative is nowhere surjective to a set of additive Haar measure zero.  In particular, the
critical values of a differentiable map between spaces of equal dimension have measure zero, and
the regular values are dense. For Lipschitz maps, the totalized critical values are also null,
including images of nondifferentiability points. On the real line this says that the image of the
zero set of the totalized derivative is Lebesgue-null.

Mathlib proves the corresponding result for an endomorphism of one normed space in
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`.  We transport the codomain across a continuous
linear equivalence and use uniqueness of additive Haar measure to return to the original codomain.
Together with the lower-dimensional-source case, this reduces the remaining Morse--Sard argument
to maps whose source has strictly larger dimension, where higher regularity is needed.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_not_surjective_fderivWithin`: a map between equal-dimensional
  spaces sends a set of nonsurjective derivative points to a null set.
* `Differentiable.addHaar_image_criticalPoints_eq_zero`: the critical values of a globally
  differentiable map between equal-dimensional spaces form a null set.
* `LipschitzWith.addHaar_image_criticalPoints_eq_zero`: the same nullity for Lipschitz maps,
  including their nondifferentiability points in the totalized critical set.
* `TauCeti.dense_setOf_forall_surjective_fderiv`: the regular values of a map differentiable
  along a set, restricted to that set, are dense; `Differentiable.dense_compl_image_criticalPoints`
  is the case of a globally differentiable map.
* `TauCeti.countable_of_forall_injective_fderiv`: the points at which a map takes a value in a
  countable set and has injective derivative are countable.
* `TauCeti.exists_norm_lt_forall_det_one_sub_ne_zero`: arbitrarily small regular values of the
  displacement `z ↦ z - g z` of a self-map, at which `det (1 - g')` does not vanish.

The measure-theoretic input follows Sébastien Gouëzel's Mathlib formalization of the change of
variables theorem, itself based on Fremlin, *Measure Theory*, volume 2.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set
open scoped NNReal

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}
  (ν : Measure F) [IsAddHaarMeasure ν]

/-- **Sard's lemma in equal dimensions.** Let `E` and `F` be finite-dimensional real normed
spaces of equal dimension. If `f` is differentiable along `s` with derivative `f'`, and `f'` is
nowhere surjective on `s`, then `f '' s` has additive Haar measure zero in `F`.

Unlike the endomorphism version in Mathlib, the domain and codomain need not be the same normed
space and may carry unrelated norms and Haar measure normalizations. -/
theorem addHaar_image_eq_zero_of_not_surjective_fderivWithin
    (hdim : finrank ℝ E = finrank ℝ F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcrit : ∀ x ∈ s, ¬ Surjective (f' x)) : ν (f '' s) = 0 := by
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let g : E → E := fun x ↦ e (f x)
  let g' : E → E →L[ℝ] E := fun x ↦ (e : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x := by
    intro x hx
    exact e.hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hdet : ∀ x ∈ s, (g' x).det = 0 := by
    intro x hx
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    apply hcrit x hx
    intro y
    obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hinj (e y)
    refine ⟨z, e.injective ?_⟩
    simpa only [g', ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using hz
  have hnull : (addHaar : Measure E) (g '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero addHaar hg' hdet
  have hpreimage : ν (e ⁻¹' (g '' s)) = 0 :=
    by simpa only [ContinuousLinearEquiv.toContinuousAddEquiv_coe] using
      (e.toContinuousAddEquiv.quasiMeasurePreserving_addHaar ν addHaar).preimage_null hnull
  have himage : g '' s = e '' (f '' s) := by
    rw [image_image]
  rw [himage, Set.preimage_image_eq _ e.injective] at hpreimage
  exact hpreimage

/-- The critical values of a differentiable map between equal-dimensional finite-dimensional real
normed spaces have additive Haar measure zero. A point is critical here exactly when the Fréchet
derivative is not surjective. -/
theorem _root_.Differentiable.addHaar_image_criticalPoints_eq_zero
    (hf : Differentiable ℝ f) (hdim : finrank ℝ E = finrank ℝ F) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  apply addHaar_image_eq_zero_of_not_surjective_fderivWithin ν hdim
  · intro x _
    exact (hf x).hasFDerivAt.hasFDerivWithinAt
  · exact fun x hx ↦ hx

/-- The totalized critical values of a Lipschitz map between equal-dimensional real normed
spaces have additive Haar measure zero. This includes the images of nondifferentiability points,
where `fderiv` is zero by convention. No measurability hypothesis on the critical set is needed. -/
theorem _root_.LipschitzWith.addHaar_image_criticalPoints_eq_zero {K : ℝ≥0}
    (hf : LipschitzWith K f) (ν : Measure F) [IsAddHaarMeasure ν]
    (hdim : finrank ℝ E = finrank ℝ F) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  let D := {x | DifferentiableAt ℝ f x}
  have hD : (addHaar : Measure E) Dᶜ = 0 := by
    exact ae_iff.mp (hf.ae_differentiableAt (μ := addHaar))
  have hbad : ν (f '' Dᶜ) = 0 :=
    hf.lipschitzOnWith.addHaar_image_eq_zero addHaar ν hdim.le hD
  have hcrit : ν (f '' (D ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 := by
    apply addHaar_image_eq_zero_of_not_surjective_fderivWithin ν hdim
    · intro x hx
      exact hx.1.hasFDerivAt.hasFDerivWithinAt
    · exact fun x hx ↦ hx.2
  apply measure_mono_null (t := f '' Dᶜ ∪ f '' (D ∩ {x | ¬ Surjective (fderiv ℝ f x)}))
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hd : x ∈ D
    · exact Or.inr ⟨x, ⟨hd, hx⟩, rfl⟩
    · exact Or.inl ⟨x, hd, rfl⟩
  · exact measure_union_null hbad hcrit

/-- A Lipschitz function on the real line maps its totalized zero-derivative set to a
Lebesgue-null set, including the images of all nondifferentiability points. -/
theorem _root_.LipschitzWith.volume_image_setOf_deriv_eq_zero {K : ℝ≥0} {v : ℝ → ℝ}
    (hv : LipschitzWith K v) : volume (v '' {r | deriv v r = 0}) = 0 := by
  apply measure_mono_null (image_mono (t := {r | ¬ Surjective (fderiv ℝ v r)}) ?_)
    (hv.addHaar_image_criticalPoints_eq_zero volume rfl)
  intro r hr hsurj
  obtain ⟨t, ht⟩ := hsurj 1
  simp only [mem_ofPred_eq] at hr
  rw [fderiv_eq_deriv_mul, hr, zero_mul] at ht
  exact zero_ne_one ht

/-- **Regular values are dense.** Let `f` be a map between equal-dimensional finite-dimensional
real normed spaces that is differentiable at every point of a set `s`. Then the values `y` at
whose preimages in `s` the Fréchet derivative of `f` is surjective are dense. -/
theorem dense_setOf_forall_surjective_fderiv {s : Set E} (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hdim : finrank ℝ E = finrank ℝ F) :
    Dense {y | ∀ x ∈ s, f x = y → Surjective (fderiv ℝ f x)} := by
  have hnull : (addHaar : Measure F) (f '' {x | x ∈ s ∧ ¬ Surjective (fderiv ℝ f x)}) = 0 :=
    addHaar_image_eq_zero_of_not_surjective_fderivWithin addHaar hdim
      (fun x hx ↦ (hf x hx.1).hasFDerivAt.hasFDerivWithinAt) fun x hx ↦ hx.2
  refine (Measure.dense_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)).mono
    fun y hy x hx hxy ↦ ?_
  by_contra h
  exact hy ⟨x, ⟨hx, h⟩, hxy⟩

/-- The regular values of a differentiable map between equal-dimensional finite-dimensional real
normed spaces are dense. Here the regular values are expressed as the complement of the image of
the points where the Fréchet derivative is not surjective. -/
theorem _root_.Differentiable.dense_compl_image_criticalPoints
    (hf : Differentiable ℝ f) (hdim : finrank ℝ E = finrank ℝ F) :
    Dense (f '' {x | ¬ Surjective (fderiv ℝ f x)})ᶜ := by
  refine (dense_setOf_forall_surjective_fderiv (s := univ) (fun x _ ↦ hf x) hdim).mono ?_
  rintro _ hy ⟨x, hx, rfl⟩
  exact hx (hy x (mem_univ x) rfl)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F] in
/-- **Points of injective derivative over countably many values are countable.** Let `f` be a map
from a finite-dimensional real normed space. The points at which `f` takes a value in a countable
set `C` and has injective Fréchet derivative form a countable set, since near each of them `f`
takes the same value nowhere else; `TauCeti.countable_setOf_mem_and_deriv_ne_zero` is the case of
a map on a field. In equal dimensions an injective derivative is surjective, so together with
`TauCeti.dense_setOf_forall_surjective_fderiv` this yields countable sets of regular values with
countable preimages. -/
theorem countable_of_forall_injective_fderiv {C : Set F} {Z : Set E} (hC : C.Countable)
    (hZ : ∀ z ∈ Z, DifferentiableAt ℝ f z ∧ Injective (fderiv ℝ f z) ∧ f z ∈ C) :
    Z.Countable := by
  have hsub : Z ⊆ ⋃ c ∈ C, Z ∩ f ⁻¹' {c} := fun z hz ↦
    mem_iUnion₂.2 ⟨f z, (hZ z hz).2.2, hz, rfl⟩
  refine (hC.biUnion fun c _ ↦ ?_).mono hsub
  refine (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_iff_nhdsNE.2 fun z hz ↦ Filter.inf_principal_eq_bot.2 ?_)
  obtain ⟨hd, hinj, -⟩ := hZ z hz.1
  obtain ⟨K, -, hK⟩ :=
    (fderiv ℝ f z : E →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj)
  filter_upwards [hd.hasFDerivAt.eventually_ne ⟨K, hK⟩] with w hw hwZ
  exact hw (hwZ.2.trans hz.2.symm)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Regular values of `z ↦ z - g z` exist near `0`.** For a map `g` of a finite-dimensional real
normed space that has derivative `g' z` at every point `z` of a set `s`, there are vectors `v` of
arbitrarily small norm such that `1 - g' z` is invertible at every `z ∈ s` with `z - g z = v`.
This is `TauCeti.dense_setOf_forall_surjective_fderiv` for `z ↦ z - g z`. -/
theorem exists_norm_lt_forall_det_one_sub_ne_zero {s : Set E} {g : E → E}
    {g' : E → E →L[ℝ] E} (hg : ∀ z ∈ s, HasFDerivAt g (g' z) z) {η : ℝ} (hη : 0 < η) :
    ∃ v : E, ‖v‖ < η ∧ ∀ z ∈ s, z - g z = v → (1 - g' z).det ≠ 0 := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hD (z : E) (hz : z ∈ s) : HasFDerivAt (fun x ↦ x - g x) (1 - g' z) z :=
    (hasFDerivAt_id z).sub (hg z hz)
  obtain ⟨v, hv, hvη⟩ := (dense_setOf_forall_surjective_fderiv (f := fun x ↦ x - g x)
    (fun z hz ↦ (hD z hz).differentiableAt) rfl).exists_mem_open Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hη⟩
  refine ⟨v, mem_ball_zero_iff.1 hvη, fun z hz hzv ↦ ?_⟩
  have hs : Surjective ⇑(1 - g' z) := (hD z hz).fderiv ▸ hv z hz hzv
  exact (LinearMap.isUnit_det _ ((Module.End.isUnit_iff _).2
    ⟨LinearMap.injective_iff_surjective.2 hs, hs⟩)).ne_zero

end TauCeti
