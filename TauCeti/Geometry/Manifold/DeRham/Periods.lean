/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.Poincare

/-!
# Exactness of closed one-forms with vanishing periods

A closed `1`-form `φ` on a preconnected manifold whose line integral around every smooth loop at
a base point `x₀` vanishes is exact: integrating `φ` along smooth paths from `x₀` defines a
primitive (`TauCeti.exists_mextDeriv_ofFunction_eq_of_forall_pathIntegral_eq_zero`). The manifold
may have boundary or corners, and the coefficients lie in any complete normed space.

The primitive at `y` is the line integral of `φ` along any smooth path from `x₀` to `y`; such paths
exist by smooth path connectedness, `TauCeti.Manifold.exists_contMDiff_path`. Two such paths give
the same value, because the first followed by the reversed second is a smooth loop at `x₀`
(`TauCeti.pathIntegral_eq_of_forall_pathIntegral_eq_zero`). Near each point `x`, the
Poincaré lemma `TauCeti.exists_mextDeriv_eq_nhds` gives a local primitive `p`. Joining `x` to
nearby points by short smooth paths inside the domain of `p` and applying the fundamental theorem
of calculus for line integrals shows that the global primitive differs from `p` by a constant near
`x`. Hence it is as regular as `φ`, and its differential is `φ`.

For real coefficients this says that a closed smooth `1`-form represents the zero class in de Rham
cohomology exactly when all its periods vanish
(`TauCeti.mem_exactForms_iff_forall_pathIntegral_eq_zero`). This is how `H¹_dR` is compared with
the fundamental group: forms whose periods vanish for homotopy reasons are exact.

## Main declarations

* `TauCeti.exists_mextDeriv_ofFunction_eq_of_forall_pathIntegral_eq_zero`: a closed `C^r`
  `1`-form whose periods vanish is the differential of a `C^r` function.
* `TauCeti.mem_exactForms_of_forall_pathIntegral_eq_zero`: a closed smooth real `1`-form whose
  periods vanish is exact.
* `TauCeti.mem_exactForms_iff_forall_pathIntegral_eq_zero`: a closed smooth real `1`-form is exact
  if and only if its periods vanish.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 11.42 and Theorem 17.17. Lee
  integrates along piecewise smooth curves; here they are replaced by smooth concatenations that
  are stationary near the joining times.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

section Coefficients

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Exactness by periods.** On a preconnected manifold, a closed `C^r` `1`-form, `r ≥ 1`, whose
line integral along every smooth loop `γ` at a base point `x₀`, parametrized by `[0, 1]`, vanishes
is the differential of a `C^r` function. The manifold may have boundary or corners.

The coefficient space is complete: the proof uses the Poincaré lemma, which fails for incomplete
coefficients. -/
theorem exists_mextDeriv_ofFunction_eq_of_forall_pathIntegral_eq_zero [PreconnectedSpace M]
    {r : ℕ∞} (hr : 1 ≤ r) {φ : RoughForm I M F 1} (hφ : IsSmoothForm I r φ)
    (hclosed : mextDeriv φ = 0) (x₀ : M)
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ → pathIntegral φ γ 0 1 = 0) :
    ∃ f : M → F, ContMDiff I 𝓘(ℝ, F) r f ∧ mextDeriv (RoughForm.ofFunction I f) = φ := by
  have hφ₀ : IsSmoothForm I 0 φ := hφ.of_le (by simp)
  -- the candidate primitive: line integrals along chosen smooth paths from the base point
  choose γ hγ hγ0 hγ1 using fun y ↦ Manifold.exists_contMDiff_path (I := I) (n := ⊤) x₀ y
  set f : M → F := fun y ↦ pathIntegral φ (γ y) 0 1
  -- the line integral along any smooth path from the base point to `y` is `f y`
  have hind (y : M) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I ∞ α) (hα0 : α 0 = x₀)
      (hα1 : α 1 = y) : pathIntegral φ α 0 1 = f y :=
    pathIntegral_eq_of_forall_pathIntegral_eq_zero hφ₀ h hα (hγ y) hα0 (hγ0 y)
      (hα1.trans (hγ1 y).symm)
  -- near each point, `f` differs by a constant from a local primitive given by the Poincaré lemma
  have hloc (x : M) : ∃ g : M → F, ContMDiffAt I 𝓘(ℝ, F) r g x ∧
      mextDeriv (RoughForm.ofFunction I g) x = φ x ∧ f =ᶠ[𝓝 x] g := by
    obtain ⟨U, hU, ψ, hψ, hdψ⟩ :=
      exists_mextDeriv_eq_nhds hr hφ (x := x) (Eventually.of_forall fun y ↦ congrFun hclosed y)
    rw [RoughForm.eq_ofFunction ψ] at hψ hdψ
    set p : M → F := fun y ↦ ψ y 0
    have hp : ContMDiff I 𝓘(ℝ, F) r p := isSmoothForm_ofFunction_iff.mp hψ
    have hp₁ : ContMDiff I 𝓘(ℝ, F) 1 p := hp.of_le (by exact_mod_cast hr)
    refine ⟨fun y ↦ p y + (f x - p x), (hp x).add contMDiffAt_const, ?_, ?_⟩
    · -- adding a constant does not change the differential
      have hd : mfderiv I 𝓘(ℝ, F) (fun y ↦ p y + (f x - p x)) x = mfderiv I 𝓘(ℝ, F) p x :=
        (((hp₁ x).mdifferentiableAt one_ne_zero).hasMFDerivAt.add
          (hasMFDerivAt_const (f x - p x) x)).mfderiv.trans (add_zero _)
      rw [← hdψ x (mem_of_mem_nhds hU), mextDeriv_ofFunction, mextDeriv_ofFunction]
      ext v
      simp only [ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv,
        ContinuousLinearMap.comp_apply, hd]
      rfl
    · filter_upwards [Manifold.eventually_exists_contMDiff_path (I := I) (n := ⊤) hU] with y hy
      obtain ⟨σ, hσ, hσ0, hσ1, hσU⟩ := hy
      have hγσ : γ x 1 = σ 0 := by rw [hγ1, hσ0]
      have hfy : f y = f x + pathIntegral φ σ 0 1 := by
        rw [← hind y _ ((hγ x).smoothTrans hσ hγσ) (by simp [hγ0]) (by simp [hσ1]),
          pathIntegral_smoothTrans hφ₀ ((hγ x).of_le (by simp)) (hσ.of_le (by simp)) hγσ]
      have hσp : pathIntegral φ σ 0 1 = p y - p x := by
        rw [pathIntegral_congr fun t _ ↦ (hdψ (σ t) (hσU t)).symm,
          pathIntegral_mextDeriv_ofFunction hp₁ (hσ.of_le (by simp)), hσ1, hσ0]
      rw [hfy, hσp]
      abel
  choose g hg hdg hfg using hloc
  refine ⟨f, fun x ↦ (hg x).congr_of_eventuallyEq (hfg x), funext fun x ↦ ?_⟩
  rw [mextDeriv_congr_of_eventuallyEq ((hfg x).mono fun y hy ↦ ?_), hdg x]
  ext v
  simp only [RoughForm.ofFunction_apply, hy]

end Coefficients

/-- **Exactness by periods**, for real coefficients. On a preconnected manifold, a closed smooth
`1`-form whose line integral along every smooth loop at a base point `x₀`, parametrized by
`[0, 1]`, vanishes is exact. -/
theorem mem_exactForms_of_forall_pathIntegral_eq_zero [PreconnectedSpace M]
    {φ : SmoothForm I M ℝ 1} (hφ : φ ∈ closedForms I M 1) (x₀ : M)
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      pathIntegral (φ : RoughForm I M ℝ 1) γ 0 1 = 0) :
    φ ∈ exactForms I M 1 := by
  obtain ⟨f, hf, hdf⟩ := exists_mextDeriv_ofFunction_eq_of_forall_pathIntegral_eq_zero
    (r := ⊤) le_top φ.isSmoothForm ((mem_closedForms I φ).mp hφ) x₀ h
  rw [exactForms_succ, LinearMap.mem_range]
  exact ⟨⟨RoughForm.ofFunction I f, (isSmoothForm_ofFunction_iff.mpr hf).mem_smoothForms⟩,
    Subtype.ext (by rw [mextDerivₗ_apply]; exact hdf)⟩

/-- On a preconnected manifold, a closed smooth real `1`-form is exact if and only if its line
integral along every smooth loop at a base point `x₀`, parametrized by `[0, 1]`, vanishes. -/
theorem mem_exactForms_iff_forall_pathIntegral_eq_zero [PreconnectedSpace M]
    {φ : SmoothForm I M ℝ 1} (hφ : φ ∈ closedForms I M 1) (x₀ : M) :
    φ ∈ exactForms I M 1 ↔ ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      pathIntegral (φ : RoughForm I M ℝ 1) γ 0 1 = 0 :=
  ⟨fun he _ hγ h0 h1 ↦ pathIntegral_eq_zero_of_mem_exactForms he (hγ.of_le (by simp))
    (h0.trans h1.symm), mem_exactForms_of_forall_pathIntegral_eq_zero hφ x₀⟩

end TauCeti
