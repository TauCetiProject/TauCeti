/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Curve
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.Poincare

/-!
# Exactness of `1`-forms through line integrals

A closed `1`-form on a connected manifold is exact as soon as its integral along every smooth
loop at a base point vanishes (`TauCeti.exists_mextDeriv_eq_of_forall_pathIntegral_eq_zero`).
Together with the vanishing of the integrals of exact forms around closed curves, this
characterizes the vanishing of de Rham classes in degree one
(`TauCeti.deRhamCohomology.mk_eq_zero_iff_forall_pathIntegral_eq_zero`), which is how line
integrals detect `H¹_dR`.

The primitive is the integral from the base point `x₀`: `f y = ∫_γ φ` along a smooth curve `γ`
from `x₀` to `y`. Smooth curves joining two points exist on a connected manifold
(`TauCeti.exists_contMDiff_curve`), and the value does not depend on the curve, because two such
curves concatenate, the second reversed, to a smooth loop at `x₀`. Near each point the closed form
has a primitive by the Poincaré lemma (`TauCeti.exists_mextDeriv_eq_nhds`), and integrating along
short curves shows that `f` differs from it by a constant. Hence `f` is smooth with `df = φ`.
The Poincaré lemma is where finite dimensionality, the Hausdorff property and completeness of the
coefficient space are used. Manifolds with boundary or corners are included.

## Main declarations

* `TauCeti.exists_mextDeriv_eq_of_forall_pathIntegral_eq_zero`: a closed `1`-form whose integrals
  along smooth loops at a base point vanish is exact.
* `TauCeti.mem_exactForms_one_iff_forall_pathIntegral_eq_zero`: a closed smooth real `1`-form is
  exact exactly when its integrals along smooth loops at a base point vanish.
* `TauCeti.deRhamCohomology.mk_eq_zero_iff_forall_pathIntegral_eq_zero`: the same criterion for
  the vanishing of a de Rham class in degree one.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*, and Chapter 17.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the integrals of `φ` along smooth loops at `x₀` vanish, then two smooth curves from `x₀` to
`y`, constant on `(-∞, 0]` and on `[1, ∞)`, have the same line integral: the first followed by the
reversed second is a smooth loop at `x₀`. -/
theorem pathIntegral_eq_of_forall_pathIntegral_eq_zero [IsManifold I 1 M]
    {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 0 φ) {x₀ y : M}
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      pathIntegral φ γ 0 1 = 0)
    {γ γ' : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hγ₀ : ∀ t ≤ 0, γ t = x₀)
    (hγ₁ : ∀ t, 1 ≤ t → γ t = y) (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ')
    (hγ'₀ : ∀ t ≤ 0, γ' t = x₀) (hγ'₁ : ∀ t, 1 ≤ t → γ' t = y) :
    pathIntegral φ γ 0 1 = pathIntegral φ γ' 0 1 := by
  have hrev : ContMDiff 𝓘(ℝ, ℝ) I ∞ fun t ↦ γ' (1 - t) :=
    hγ'.comp (by fun_prop : ContDiff ℝ ∞ fun t : ℝ ↦ 1 - t).contMDiff
  have h₂ : ∀ t ≤ 0, γ' (1 - t) = y := fun t ht ↦ hγ'₁ _ (by linarith)
  have hloop := h _ (hγ.curveConcat hrev hγ₁ h₂)
    (by rw [curveConcat_of_le (by norm_num), hγ₀ _ (by norm_num)])
    (by rw [curveConcat_of_lt (by norm_num)]; exact hγ'₀ _ (by norm_num))
  rw [pathIntegral_curveConcat hφ (hγ.of_le (by simp)) (hrev.of_le (by simp)) hγ₁ h₂,
    pathIntegral_comp_sub_left hφ (hγ'.of_le (by simp)), sub_self, sub_zero] at hloop
  exact sub_eq_zero.mp ((sub_eq_add_neg _ _).trans hloop)

variable [CompleteSpace F]

/-- **Line integrals detect exactness.** On a preconnected manifold, a closed `C^r` `1`-form
(`1 ≤ r`) whose integral along every smooth loop at a base point `x₀` vanishes is the exterior
derivative of a `C^r` function. The primitive is the integral along smooth curves from `x₀`. -/
theorem exists_mextDeriv_eq_of_forall_pathIntegral_eq_zero [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I ∞ M] [PreconnectedSpace M] {r : ℕ∞} (hr : 1 ≤ r) {φ : RoughForm I M F 1}
    (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) (x₀ : M)
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      pathIntegral φ γ 0 1 = 0) :
    ∃ ψ : RoughForm I M F 0, IsSmoothForm I r ψ ∧ mextDeriv ψ = φ := by
  have hφ₀ : IsSmoothForm I 0 φ := hφ.of_le (by simp)
  -- The primitive `f` is the integral along chosen smooth curves from `x₀`.
  choose γ hγ hγ₀ hγ₁ using fun y : M ↦ exists_contMDiff_curve (I := I) (n := ⊤) x₀ y
  set f : M → F := fun y ↦ pathIntegral φ (γ y) 0 1 with hf_def
  -- Near each point `x`, `f` differs by a constant from a local primitive `g` of `φ`.
  have hloc (x : M) : ∃ g : M → F, ContMDiff I 𝓘(ℝ, F) r g ∧
      (∀ᶠ y in 𝓝 x, f y = g y + (f x - g x)) ∧
      mextDeriv (RoughForm.ofFunction I g) x = φ x := by
    obtain ⟨U, hU, ψ, hψ, hdψ⟩ :=
      exists_mextDeriv_eq_nhds hr hφ (x := x) (Eventually.of_forall fun y ↦ congrFun hclosed y)
    have hψ' := hψ
    rw [RoughForm.eq_ofFunction ψ, isSmoothForm_ofFunction_iff] at hψ'
    refine ⟨fun y ↦ ψ y 0, hψ', ?_, ?_⟩
    · filter_upwards [eventually_exists_contMDiff_curve (I := I) (n := ⊤) hU] with y hy
      obtain ⟨c, hc, hc₀, hc₁, hcU⟩ := hy
      have hc' : ContMDiff 𝓘(ℝ, ℝ) I 1 c := hc.of_le (by simp)
      -- Integrate along the chosen curve to `x` followed by the short curve `c` from `x` to `y`.
      have hcat : f y = f x + pathIntegral φ c 0 1 := by
        simp only [hf_def]
        rw [pathIntegral_eq_of_forall_pathIntegral_eq_zero hφ₀ h (hγ y) (hγ₀ y) (hγ₁ y)
            ((hγ x).curveConcat hc (hγ₁ x) hc₀)
            (fun t ht ↦ by rw [curveConcat_of_le (by linarith), hγ₀ x _ (by linarith)])
            (fun t ht ↦ by rw [curveConcat_of_lt (by linarith), hc₁ _ (by linarith)]),
          pathIntegral_curveConcat hφ₀ ((hγ x).of_le (by simp)) hc' (hγ₁ x) hc₀]
      rw [hcat, pathIntegral_congr (ψ := mextDeriv ψ) fun t _ ↦ (hdψ _ (hcU t)).symm,
        pathIntegral_mextDeriv (hψ.of_le (by exact_mod_cast hr)) hc', hc₁ 1 le_rfl,
        hc₀ 0 le_rfl]
      abel
    · rw [← RoughForm.eq_ofFunction]
      exact hdψ x (mem_of_mem_nhds hU)
  refine ⟨RoughForm.ofFunction I f, isSmoothForm_ofFunction_iff.mpr fun x ↦ ?_, funext fun x ↦ ?_⟩
  · obtain ⟨g, hg, hfg, -⟩ := hloc x
    exact ((hg x).add contMDiffAt_const).congr_of_eventuallyEq hfg
  · obtain ⟨g, hg, hfg, hdg⟩ := hloc x
    rw [← hdg]
    exact mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      ((hg x).mdifferentiableAt (by simpa using (zero_lt_one.trans_le hr).ne')) hfg

/-- A closed smooth real `1`-form on a preconnected manifold is exact exactly when its integral
along every smooth loop at a base point `x₀` vanishes. -/
theorem mem_exactForms_one_iff_forall_pathIntegral_eq_zero [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I ∞ M] [PreconnectedSpace M] {φ : SmoothForm I M ℝ 1}
    (hφ : φ ∈ closedForms I M 1) (x₀ : M) :
    φ ∈ exactForms I M 1 ↔ ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      pathIntegral (φ : RoughForm I M ℝ 1) γ 0 1 = 0 := by
  refine ⟨fun he γ hγ h₀ h₁ ↦
    pathIntegral_eq_zero_of_mem_exactForms he (hγ.of_le (by simp)) (h₀.trans h₁.symm),
    fun h ↦ ?_⟩
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_forall_pathIntegral_eq_zero (r := ⊤) le_top
    φ.isSmoothForm ((mem_closedForms I φ).mp hφ) x₀ h
  rw [exactForms_succ]
  exact ⟨⟨ψ, hψ.mem_smoothForms⟩, Subtype.ext ((mextDerivₗ_apply I 0 _).trans hdψ)⟩

/-- A de Rham class of degree one on a preconnected manifold vanishes exactly when the integrals
of a representative along all smooth loops at a base point `x₀` vanish. -/
theorem deRhamCohomology.mk_eq_zero_iff_forall_pathIntegral_eq_zero [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I ∞ M] [PreconnectedSpace M] (φ : closedForms I M 1) (x₀ : M) :
    deRhamCohomology.mk I 1 φ = 0 ↔ ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ →
      γ 1 = x₀ → pathIntegral ((φ : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) γ 0 1 = 0 := by
  rw [deRhamCohomology.mk_eq_zero_iff, mem_exactForms_one_iff_forall_pathIntegral_eq_zero φ.2]

end TauCeti
