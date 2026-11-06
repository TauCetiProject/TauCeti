/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth paths with prescribed Riemannian path length

For a `C¹` path on `[0, 1]`, there exists a globally `C¹` path that is constant near both
endpoints, has the same endpoints, and has exactly the same `Manifold.pathELength`. For two `C¹`
paths with a common endpoint, there likewise exists a globally `C¹` path between their outer
endpoints whose length is the sum of their lengths. These are the basic existential properties
needed to compare piecewise-`C¹` and `C¹` definitions of Riemannian distance.

The reparametrizations do not introduce new points: the smoothed path stays in the image of the
original path, and a smoothed concatenation stays in the union of the two original images. This
range control allows local length estimates to be applied after smoothing a path inside a fixed
open set.

A path on an arbitrary compact interval can first be reparametrized affinely onto `[0, 1]`
without changing its endpoints or length.

The construction uses Mathlib's `Real.smoothTransition` and
`Manifold.pathELength_comp_of_monotoneOn`. No new notion of path length is introduced.

## Main results

* `TauCeti.exists_contMDiff_pathELength_eq`: obtain a globally `C¹` path, constant near its
  endpoints, with the same endpoints, length, and image containment as a given `C¹` path.
* `TauCeti.Manifold.exists_contMDiff_pathELength_eq_of_le`: reparametrize a `C¹` path from an
  arbitrary compact interval onto `[0, 1]`, preserving its endpoints and length.
* `TauCeti.exists_contMDiff_pathELength_eq_add`: obtain a globally `C¹` path between the outer
  endpoints of two compatible `C¹` paths, with length equal to the sum of their lengths.
* `TauCeti.Manifold.pathELength_lineMap`: the straight segment between two points of an inner
  product space has length equal to the norm distance between them.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 1, Definition 2.9 and Chapter 7, Section 2.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Corner smoothing and the piecewise-`C¹` comparison".
-/

public section

open Filter Set
open scoped Bundle ContDiff Manifold Topology

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

/-- A `C¹` path on `[0, 1]` admits a globally `C¹` path which is constant near both endpoints,
has the same endpoints and length, and stays in the image of the original path. -/
theorem exists_contMDiff_pathELength_eq {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) :
    ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧
      η 0 = γ 0 ∧
      η 1 = γ 1 ∧
      Manifold.pathELength I η 0 1 = Manifold.pathELength I γ 0 1 ∧
      η =ᶠ[𝓝 0] (fun _ ↦ γ 0) ∧
      η =ᶠ[𝓝 1] (fun _ ↦ γ 1) ∧
      MapsTo η (Icc 0 1) (γ '' Icc 0 1) := by
  let f : ℝ → ℝ := fun t ↦ Real.smoothTransition (3 * t - 1)
  have hf_smooth : ContDiff ℝ 1 f := by
    apply Real.smoothTransition.contDiff.comp
    fun_prop
  have hf_range (t : ℝ) : f t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hf_zero : f 0 = 0 := by
    exact Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hf_one : f 1 = 1 := by
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  have hf_monotone : Monotone f := by
    apply Real.smoothTransition.monotone.comp
    intro s t hst
    dsimp only
    gcongr
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) I 1 (γ ∘ f) := by
    rw [← contMDiffOn_univ]
    exact hγ.comp hf_smooth.contMDiff.contMDiffOn fun t _ ↦ hf_range t
  refine ⟨γ ∘ f, hcomp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hf_zero]
  · simp [hf_one]
  · have hlength := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := γ) (f := f)
      zero_le_one (hf_monotone.monotoneOn _)
      (hf_smooth.differentiable one_ne_zero).differentiableOn
      (by simpa [hf_zero, hf_one] using hγ.mdifferentiableOn one_ne_zero)
    simpa [hf_zero, hf_one] using hlength
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t ht
    simp only [Function.comp_apply]
    rw [show f t = 0 by
      apply Real.smoothTransition.zero_of_nonpos
      norm_num at ht ⊢
      linarith]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t ht
    simp only [Function.comp_apply]
    rw [show f t = 1 by
      apply Real.smoothTransition.one_of_one_le
      norm_num at ht ⊢
      linarith]
  · intro t _
    exact ⟨f t, hf_range t, rfl⟩

namespace Manifold

/-- A `C¹` path on a compact interval admits a globally `C¹` path on `[0, 1]` with the same
endpoints and length, whose image stays in the original path's image. This is the single-piece
case of corner smoothing; the reparametrization is affine, so it changes neither the endpoints
nor the length. -/
theorem exists_contMDiff_pathELength_eq_of_le {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η 0 = γ a ∧ η 1 = γ b ∧
      Manifold.pathELength I η 0 1 = Manifold.pathELength I γ a b ∧
      MapsTo η (Icc 0 1) (γ '' Icc a b) := by
  set f := ContinuousAffineMap.lineMap (R := ℝ) a b with hf
  have hmaps : f '' Icc 0 1 ⊆ Icc a b := by
    rw [hf, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
    simp [hab, segment_eq_Icc]
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ f) (Icc 0 1) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact f.contDiff.contDiffOn
    · rw [← image_subset_iff]
      exact hmaps
  obtain ⟨η, hη, hη₀, hη₁, hlen, -, -, hηmaps⟩ :=
    TauCeti.exists_contMDiff_pathELength_eq hcomp
  refine ⟨η, hη, ?_, ?_, ?_, ?_⟩
  · simpa [hf, ContinuousAffineMap.coe_lineMap_eq] using hη₀
  · simpa [hf, ContinuousAffineMap.coe_lineMap_eq] using hη₁
  · rw [hlen, hf]
    have key := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := γ)
      (f := ContinuousAffineMap.lineMap (R := ℝ) a b) (a := 0) (b := 1) zero_le_one
      (by
        rw [ContinuousAffineMap.coe_lineMap_eq]
        exact (AffineMap.lineMap_mono hab).monotoneOn _)
      (ContinuousAffineMap.lineMap (R := ℝ) a b).differentiableOn
      (by
        simpa [ContinuousAffineMap.coe_lineMap_eq] using
          hγ.mdifferentiableOn one_ne_zero)
    simpa [ContinuousAffineMap.coe_lineMap_eq] using key
  · intro t ht
    obtain ⟨s, hs, hst⟩ := hηmaps ht
    exact ⟨f s, hmaps ⟨s, hs, rfl⟩, hst⟩

end Manifold

omit [∀ x : M, ENorm (TangentSpace I x)] [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)] in
/-- Gluing two paths after rescaling them to `[0, 1 / 2]` and `[1 / 2, 1]` gives a `C¹` path when
the first is constant near its right end and the second near its left end, with equal values. -/
private theorem contMDiff_piecewise_scale {α β : ℝ → M} {x y : M}
    (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α) (hβ : ContMDiff 𝓘(ℝ, ℝ) I 1 β)
    (hα₁ : α =ᶠ[𝓝 1] (fun _ ↦ x)) (hβ₀ : β =ᶠ[𝓝 0] (fun _ ↦ y)) (hxy : x = y) :
    ContMDiff 𝓘(ℝ, ℝ) I 1
      (piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1))) := by
  have hf : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun t : ℝ ↦ α (2 * t)) := by
    apply hα.comp
    simpa only [contMDiff_iff_contDiff] using
      (show ContDiff ℝ 1 (fun t : ℝ ↦ 2 * t) by fun_prop)
  have hg : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun t : ℝ ↦ β (2 * t - 1)) := by
    apply hβ.comp
    simpa only [contMDiff_iff_contDiff] using
      (show ContDiff ℝ 1 (fun t : ℝ ↦ 2 * t - 1) by fun_prop)
  have hf_const : (fun t : ℝ ↦ α (2 * t)) =ᶠ[𝓝 (1 / 2 : ℝ)] (fun _ ↦ x) := by
    apply hα₁.comp_tendsto
    have h : ContinuousAt (fun t : ℝ ↦ 2 * t) (1 / 2) := by fun_prop
    -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
    change Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 (1 / 2)) (𝓝 (2 * (1 / 2))) at h
    norm_num at h
    exact h
  have hg_const : (fun t : ℝ ↦ β (2 * t - 1)) =ᶠ[𝓝 (1 / 2 : ℝ)] (fun _ ↦ y) := by
    apply hβ₀.comp_tendsto
    have h : ContinuousAt (fun t : ℝ ↦ 2 * t - 1) (1 / 2) := by fun_prop
    -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
    change Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 (1 / 2))
      (𝓝 (2 * (1 / 2) - 1)) at h
    norm_num at h
    exact h
  exact hf.piecewise_Iic hg (hf_const.trans <| (hxy ▸ hg_const.symm))

/-- The path obtained by gluing `α` and `β`, rescaled to `[0, 1 / 2]` and `[1 / 2, 1]`, has length
the sum of the lengths of `α` and `β`, when both are `C¹`. -/
private theorem pathELength_piecewise_scale {α β : ℝ → M}
    (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α) (hβ : ContMDiff 𝓘(ℝ, ℝ) I 1 β) :
    Manifold.pathELength I
        (piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1))) 0 1 =
      Manifold.pathELength I α 0 1 + Manifold.pathELength I β 0 1 := by
  set f : ℝ → M := fun t ↦ α (2 * t) with hf
  set g : ℝ → M := fun t ↦ β (2 * t - 1) with hg
  set η : ℝ → M := piecewise (Iic (1 / 2 : ℝ)) f g with hη
  have hη_left : Manifold.pathELength I η 0 (1 / 2) =
      Manifold.pathELength I α 0 1 := by
    rw [Manifold.pathELength_congr (γ' := f) (fun t ht ↦ by
      exact (Iic (1 / 2 : ℝ)).piecewise_eq_of_mem f g ht.2)]
    rw [show f = α ∘ fun t : ℝ ↦ 2 * t by rfl]
    have hmono : Monotone (fun t : ℝ ↦ 2 * t) := fun _ _ hst ↦ by linarith
    have hlength := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := α)
      (f := fun t : ℝ ↦ 2 * t) (a := 0) (b := 1 / 2) (by norm_num)
      (hmono.monotoneOn _) (by fun_prop)
      (hα.mdifferentiable one_ne_zero).mdifferentiableOn
    norm_num at hlength
    exact hlength
  have hη_right : Manifold.pathELength I η (1 / 2) 1 =
      Manifold.pathELength I β 0 1 := by
    rw [Manifold.pathELength_congr_Ioo (γ' := g) (fun t ht ↦ by
      exact (Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem f g (not_le_of_gt ht.1))]
    rw [show g = β ∘ fun t : ℝ ↦ 2 * t - 1 by rfl]
    have hmono : Monotone (fun t : ℝ ↦ 2 * t - 1) := fun _ _ hst ↦ by linarith
    have hlength := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := β)
      (f := fun t : ℝ ↦ 2 * t - 1) (a := 1 / 2) (b := 1) (by norm_num)
      (hmono.monotoneOn _) (by fun_prop)
      (hβ.mdifferentiable one_ne_zero).mdifferentiableOn
    norm_num at hlength
    exact hlength
  rw [← Manifold.pathELength_add (I := I) (γ := η) (a := 0) (b := 1 / 2) (c := 1)
    (by norm_num) (by norm_num), hη_left, hη_right]

omit [TopologicalSpace M] in
/-- The path obtained by gluing `α` and `β`, rescaled to `[0, 1 / 2]` and `[1 / 2, 1]`, is constant
near `0` when `α` is. -/
private theorem piecewise_scale_eventuallyEq_nhds_zero {α β : ℝ → M} {x : M}
    (hα₀ : α =ᶠ[𝓝 0] (fun _ ↦ x)) :
    piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1)) =ᶠ[𝓝 0]
      (fun _ ↦ x) := by
  have hmap : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun t : ℝ ↦ 2 * t) 0 := by fun_prop
    -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
    change Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 (2 * 0)) at h
    norm_num at h
    exact h
  filter_upwards [hα₀.comp_tendsto hmap,
    Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with t htα ht
  have ht' : t < 1 / 2 := ht
  rw [(Iic (1 / 2 : ℝ)).piecewise_eq_of_mem _ _ ht'.le]
  exact htα

omit [TopologicalSpace M] in
/-- The path obtained by gluing `α` and `β`, rescaled to `[0, 1 / 2]` and `[1 / 2, 1]`, is constant
near `1` when `β` is. -/
private theorem piecewise_scale_eventuallyEq_nhds_one {α β : ℝ → M} {y : M}
    (hβ₁ : β =ᶠ[𝓝 1] (fun _ ↦ y)) :
    piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1)) =ᶠ[𝓝 1]
      (fun _ ↦ y) := by
  have hmap : Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 1) (𝓝 1) := by
    have h : ContinuousAt (fun t : ℝ ↦ 2 * t - 1) 1 := by fun_prop
    -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
    change Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 1) (𝓝 (2 * 1 - 1)) at h
    norm_num at h
    exact h
  filter_upwards [hβ₁.comp_tendsto hmap,
    Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with t htβ ht
  have ht' : 1 / 2 < t := ht
  rw [(Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem _ _ (not_le_of_gt ht')]
  exact htβ

omit [TopologicalSpace M] in
/-- The path obtained by gluing `α` and `β`, rescaled to `[0, 1 / 2]` and `[1 / 2, 1]`, maps
`[0, 1]` into the union of the sets into which `α` and `β` map `[0, 1]`. -/
private theorem mapsTo_piecewise_scale {α β : ℝ → M} {S T : Set M}
    (hα : MapsTo α (Icc 0 1) S) (hβ : MapsTo β (Icc 0 1) T) :
    MapsTo (piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1)))
      (Icc 0 1) (S ∪ T) := by
  intro t ht
  by_cases ht_half : t ≤ (1 / 2 : ℝ)
  · left
    rw [(Iic (1 / 2 : ℝ)).piecewise_eq_of_mem _ _ ht_half]
    exact hα ⟨by linarith [ht.1], by linarith⟩
  · right
    rw [(Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem _ _ ht_half]
    exact hβ ⟨by linarith, by linarith [ht.2]⟩

/-- Given two `C¹` paths on `[0, 1]` whose endpoints match, there is a globally `C¹` path with
their outer endpoints which is constant near those endpoints, whose length is the sum of the two
original lengths, and whose image stays in the union of the two original path images. -/
theorem exists_contMDiff_pathELength_eq_add {γ₁ γ₂ : ℝ → M}
    (hγ₁ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ₁ (Icc 0 1))
    (hγ₂ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ₂ (Icc 0 1)) (h₁₂ : γ₁ 1 = γ₂ 0) :
    ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧
      η 0 = γ₁ 0 ∧
      η 1 = γ₂ 1 ∧
      Manifold.pathELength I η 0 1 =
        Manifold.pathELength I γ₁ 0 1 + Manifold.pathELength I γ₂ 0 1 ∧
      η =ᶠ[𝓝 0] (fun _ ↦ γ₁ 0) ∧
      η =ᶠ[𝓝 1] (fun _ ↦ γ₂ 1) ∧
      MapsTo η (Icc 0 1) (γ₁ '' Icc 0 1 ∪ γ₂ '' Icc 0 1) := by
  obtain ⟨α, hα, hα₀, _, hαlen, hαconst₀, hαconst₁, hαmaps⟩ :=
    exists_contMDiff_pathELength_eq hγ₁
  obtain ⟨β, hβ, _, hβ₁, hβlen, hβconst₀, hβconst₁, hβmaps⟩ :=
    exists_contMDiff_pathELength_eq hγ₂
  refine ⟨piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1)),
    contMDiff_piecewise_scale hα hβ hαconst₁ hβconst₀ h₁₂, ?_, ?_, ?_,
    piecewise_scale_eventuallyEq_nhds_zero hαconst₀,
    piecewise_scale_eventuallyEq_nhds_one hβconst₁, mapsTo_piecewise_scale hαmaps hβmaps⟩
  · simp [hα₀]
  · rw [(Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem _ _ (by norm_num)]
    norm_num
    exact hβ₁
  · rw [pathELength_piecewise_scale hα hβ, hαlen, hβlen]

namespace Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The straight segment between two points of an inner product space has length equal to the
norm distance between them. -/
@[simp]
theorem pathELength_lineMap (x y : F) :
    Manifold.pathELength 𝓘(ℝ, F)
      (⇑(ContinuousAffineMap.lineMap (R := ℝ) x y)) 0 1 = ‖x - y‖ₑ := by
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
  exact lintegral_fderiv_lineMap_eq_edist .. |>.trans (edist_eq_enorm_sub ..)

end Manifold

end TauCeti
