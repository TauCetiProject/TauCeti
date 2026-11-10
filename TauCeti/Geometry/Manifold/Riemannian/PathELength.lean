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

For a `Cⁿ` path on `[0, 1]` with `n ≠ 0`, there exists a globally `Cⁿ` path that is constant near
both endpoints, has the same endpoints, and has exactly the same `Manifold.pathELength`. For two
`Cⁿ` paths with a common endpoint, there likewise exists a globally `Cⁿ` path between their outer
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

* `TauCeti.Manifold.exists_contMDiff_pathELength_eq`: obtain a globally `Cⁿ` path, constant near
  its endpoints, with the same endpoints, length, and image containment as a given `Cⁿ` path.
* `TauCeti.Manifold.exists_contMDiff_pathELength_eq_of_le`: the same for a `Cⁿ` path on an
  arbitrary compact interval, which is first reparametrized affinely onto `[0, 1]`.
* `TauCeti.Manifold.exists_contMDiff_pathELength_eq_add`: obtain a globally `Cⁿ` path between the
  outer endpoints of two compatible `Cⁿ` paths, with length equal to the sum of their lengths.
* `TauCeti.Manifold.pathELength_lineMap`: the straight segment between two points of an inner
  product space has length equal to the norm distance between them.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 1, Definition 2.9 and Chapter 7, Section 2.
-/

public section

open Filter Set
open scoped Bundle ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

/-- A `Cⁿ` path on `[0, 1]`, `n ≠ 0`, admits a globally `Cⁿ` path which is constant near both
endpoints, has the same endpoints and length, and stays in the image of the original path. -/
theorem exists_contMDiff_pathELength_eq {n : ℕ∞} {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc 0 1)) (hn : n ≠ 0) :
    ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I n η ∧
      η 0 = γ 0 ∧
      η 1 = γ 1 ∧
      Manifold.pathELength I η 0 1 = Manifold.pathELength I γ 0 1 ∧
      η =ᶠ[𝓝 0] (fun _ ↦ γ 0) ∧
      η =ᶠ[𝓝 1] (fun _ ↦ γ 1) ∧
      MapsTo η (Icc 0 1) (γ '' Icc 0 1) := by
  let f : ℝ → ℝ := fun t ↦ Real.smoothTransition (3 * t - 1)
  have hf_smooth {m : ℕ∞} : ContDiff ℝ m f := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hf_range (t : ℝ) : f t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hf_zero : f 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hf_one : f 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  have hf_mono : Monotone f :=
    Real.smoothTransition.monotone.comp fun s t hst ↦ by linarith
  refine ⟨γ ∘ f, contMDiffOn_univ.mp <|
      hγ.comp hf_smooth.contMDiff.contMDiffOn fun t _ ↦ hf_range t,
    by simp [hf_zero], by simp [hf_one], ?_, ?_, ?_, fun t _ ↦ ⟨f t, hf_range t, rfl⟩⟩
  · simpa [hf_zero, hf_one] using Manifold.pathELength_comp_of_monotoneOn zero_le_one
      (hf_mono.monotoneOn _) (hf_smooth (m := 1).differentiable one_ne_zero).differentiableOn
      (by simpa [hf_zero, hf_one] using hγ.mdifferentiableOn (mod_cast hn))
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t (ht : t < 1 / 3)
    simp only [Function.comp_apply,
      Real.smoothTransition.zero_of_nonpos (show 3 * t - 1 ≤ 0 by linarith), f]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t (ht : 2 / 3 < t)
    simp only [Function.comp_apply,
      Real.smoothTransition.one_of_one_le (show 1 ≤ 3 * t - 1 by linarith), f]

/-- A `Cⁿ` path on a compact interval `[a, b]`, `n ≠ 0`, admits a globally `Cⁿ` path on `[0, 1]`
which is constant near `0` and `1`, has the same endpoints and length, and stays in the image of
the original path. -/
theorem exists_contMDiff_pathELength_eq_of_le {n : ℕ∞} {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc a b)) (hn : n ≠ 0) :
    ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I n η ∧
      η 0 = γ a ∧
      η 1 = γ b ∧
      Manifold.pathELength I η 0 1 = Manifold.pathELength I γ a b ∧
      η =ᶠ[𝓝 0] (fun _ ↦ γ a) ∧
      η =ᶠ[𝓝 1] (fun _ ↦ γ b) ∧
      MapsTo η (Icc 0 1) (γ '' Icc a b) := by
  let f : ℝ → ℝ := AffineMap.lineMap a b
  have hf : ContDiff ℝ n f := (ContinuousAffineMap.lineMap (R := ℝ) a b).contDiff
  have hmaps : MapsTo f (Icc 0 1) (Icc a b) := by
    rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap, segment_eq_Icc hab]
  obtain ⟨η, hη, hη₀, hη₁, hlen, hη₀', hη₁', hηmaps⟩ :=
    exists_contMDiff_pathELength_eq (hγ.comp hf.contMDiff.contMDiffOn hmaps) hn
  have hf₀ : f 0 = a := AffineMap.lineMap_apply_zero a b
  have hf₁ : f 1 = b := AffineMap.lineMap_apply_one a b
  refine ⟨η, hη, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hf₀] using hη₀
  · simpa [hf₁] using hη₁
  · rw [hlen, ← hf₀, ← hf₁]
    exact Manifold.pathELength_comp_of_monotoneOn zero_le_one
      ((AffineMap.lineMap_mono hab).monotoneOn _)
      (hf.differentiable (mod_cast hn)).differentiableOn
      (by simpa [hf₀, hf₁] using hγ.mdifferentiableOn (mod_cast hn))
  · simpa [hf₀] using hη₀'
  · simpa [hf₁] using hη₁'
  · exact hηmaps.mono_right ((mapsTo_image γ _).comp hmaps).image_subset

omit [∀ x : M, ENorm (TangentSpace I x)] [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)] in
/-- Gluing two paths after rescaling them to `[0, 1 / 2]` and `[1 / 2, 1]` gives a `Cⁿ` path when
the first is constant near its right end and the second near its left end, with the same value. -/
private theorem contMDiff_piecewise_scale {n : WithTop ℕ∞} {α β : ℝ → M} {x : M}
    (hα : ContMDiff 𝓘(ℝ, ℝ) I n α) (hβ : ContMDiff 𝓘(ℝ, ℝ) I n β)
    (hα₁ : α =ᶠ[𝓝 1] (fun _ ↦ x)) (hβ₀ : β =ᶠ[𝓝 0] (fun _ ↦ x)) :
    ContMDiff 𝓘(ℝ, ℝ) I n
      (piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1))) := by
  have hf_const : (fun t : ℝ ↦ α (2 * t)) =ᶠ[𝓝 (1 / 2 : ℝ)] (fun _ ↦ x) :=
    hα₁.comp_tendsto ((by fun_prop : Continuous fun t : ℝ ↦ 2 * t).tendsto' _ _ (by norm_num))
  have hg_const : (fun t : ℝ ↦ β (2 * t - 1)) =ᶠ[𝓝 (1 / 2 : ℝ)] (fun _ ↦ x) :=
    hβ₀.comp_tendsto ((by fun_prop : Continuous fun t : ℝ ↦ 2 * t - 1).tendsto' _ _ (by norm_num))
  exact (hα.comp (contMDiff_iff_contDiff.mpr (by fun_prop))).piecewise_Iic
    (hβ.comp (contMDiff_iff_contDiff.mpr (by fun_prop))) (hf_const.trans hg_const.symm)

/-- The path obtained by gluing `α` and `β`, rescaled to `[0, 1 / 2]` and `[1 / 2, 1]`, has length
the sum of the lengths of `α` and `β`, when both are differentiable. -/
private theorem pathELength_piecewise_scale {α β : ℝ → M}
    (hα : MDifferentiable 𝓘(ℝ, ℝ) I α) (hβ : MDifferentiable 𝓘(ℝ, ℝ) I β) :
    Manifold.pathELength I
        (piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1))) 0 1 =
      Manifold.pathELength I α 0 1 + Manifold.pathELength I β 0 1 := by
  set f : ℝ → M := fun t ↦ α (2 * t)
  set g : ℝ → M := fun t ↦ β (2 * t - 1)
  set η : ℝ → M := piecewise (Iic (1 / 2 : ℝ)) f g
  have hη_left : Manifold.pathELength I η 0 (1 / 2) = Manifold.pathELength I α 0 1 := by
    rw [Manifold.pathELength_congr (γ' := f) fun t ht ↦ (Iic _).piecewise_eq_of_mem f g ht.2]
    have := Manifold.pathELength_comp_of_monotoneOn (γ := α) (f := fun t : ℝ ↦ 2 * t)
      (a := 0) (b := 1 / 2) (by norm_num) (fun _ _ _ _ h ↦ by linarith) (by fun_prop)
      hα.mdifferentiableOn
    norm_num at this
    exact this
  have hη_right : Manifold.pathELength I η (1 / 2) 1 = Manifold.pathELength I β 0 1 := by
    rw [Manifold.pathELength_congr_Ioo (γ' := g) fun t ht ↦
      (Iic _).piecewise_eq_of_notMem f g (not_le_of_gt ht.1)]
    have := Manifold.pathELength_comp_of_monotoneOn (γ := β) (f := fun t : ℝ ↦ 2 * t - 1)
      (a := 1 / 2) (b := 1) (by norm_num) (fun _ _ _ _ h ↦ by linarith) (by fun_prop)
      hβ.mdifferentiableOn
    norm_num at this
    exact this
  rw [← Manifold.pathELength_add (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1), hη_left,
    hη_right]

omit [TopologicalSpace M] in
/-- The path obtained by gluing `α` and `β`, rescaled to `[0, 1 / 2]` and `[1 / 2, 1]`, is constant
near `0` when `α` is. -/
private theorem piecewise_scale_eventuallyEq_nhds_zero {α β : ℝ → M} {x : M}
    (hα₀ : α =ᶠ[𝓝 0] (fun _ ↦ x)) :
    piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1)) =ᶠ[𝓝 0]
      (fun _ ↦ x) := by
  filter_upwards [hα₀.comp_tendsto
    ((by fun_prop : Continuous fun t : ℝ ↦ 2 * t).tendsto' _ _ (by norm_num)),
    Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with t htα (ht : t < 1 / 2)
  rwa [(Iic (1 / 2 : ℝ)).piecewise_eq_of_mem _ _ ht.le]

omit [TopologicalSpace M] in
/-- The path obtained by gluing `α` and `β`, rescaled to `[0, 1 / 2]` and `[1 / 2, 1]`, is constant
near `1` when `β` is. -/
private theorem piecewise_scale_eventuallyEq_nhds_one {α β : ℝ → M} {y : M}
    (hβ₁ : β =ᶠ[𝓝 1] (fun _ ↦ y)) :
    piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1)) =ᶠ[𝓝 1]
      (fun _ ↦ y) := by
  filter_upwards [hβ₁.comp_tendsto
    ((by fun_prop : Continuous fun t : ℝ ↦ 2 * t - 1).tendsto' _ _ (by norm_num)),
    Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with t htβ (ht : 1 / 2 < t)
  rwa [(Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem _ _ (not_le_of_gt ht)]

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

/-- Given two `Cⁿ` paths on `[0, 1]`, `n ≠ 0`, whose endpoints match, there is a globally `Cⁿ`
path with their outer endpoints which is constant near those endpoints, whose length is the sum of
the two original lengths, and whose image stays in the union of the two original path images. -/
theorem exists_contMDiff_pathELength_eq_add {n : ℕ∞} {γ₁ γ₂ : ℝ → M}
    (hγ₁ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ₁ (Icc 0 1))
    (hγ₂ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ₂ (Icc 0 1)) (h₁₂ : γ₁ 1 = γ₂ 0) (hn : n ≠ 0) :
    ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I n η ∧
      η 0 = γ₁ 0 ∧
      η 1 = γ₂ 1 ∧
      Manifold.pathELength I η 0 1 =
        Manifold.pathELength I γ₁ 0 1 + Manifold.pathELength I γ₂ 0 1 ∧
      η =ᶠ[𝓝 0] (fun _ ↦ γ₁ 0) ∧
      η =ᶠ[𝓝 1] (fun _ ↦ γ₂ 1) ∧
      MapsTo η (Icc 0 1) (γ₁ '' Icc 0 1 ∪ γ₂ '' Icc 0 1) := by
  obtain ⟨α, hα, hα₀, -, hαlen, hαconst₀, hαconst₁, hαmaps⟩ :=
    exists_contMDiff_pathELength_eq hγ₁ hn
  obtain ⟨β, hβ, -, hβ₁, hβlen, hβconst₀, hβconst₁, hβmaps⟩ :=
    exists_contMDiff_pathELength_eq hγ₂ hn
  refine ⟨piecewise (Iic (1 / 2 : ℝ)) (fun t ↦ α (2 * t)) (fun t ↦ β (2 * t - 1)),
    contMDiff_piecewise_scale hα hβ hαconst₁ (h₁₂ ▸ hβconst₀), by simp [hα₀], ?_, ?_,
    piecewise_scale_eventuallyEq_nhds_zero hαconst₀,
    piecewise_scale_eventuallyEq_nhds_one hβconst₁, mapsTo_piecewise_scale hαmaps hβmaps⟩
  · rw [(Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem _ _ (by norm_num)]
    norm_num [hβ₁]
  · rw [pathELength_piecewise_scale (hα.mdifferentiable (mod_cast hn))
      (hβ.mdifferentiable (mod_cast hn)), hαlen, hβlen]

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

end TauCeti.Manifold
