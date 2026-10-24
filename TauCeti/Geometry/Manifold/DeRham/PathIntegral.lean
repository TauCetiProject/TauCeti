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

/-- The line integral along a concatenation of two `C¹` curves, constant near the junction point,
is the sum of the line integrals. -/
private theorem pathIntegral_curveConcat [IsManifold I 1 M] {φ : RoughForm I M F 1}
    (hφ : IsSmoothForm I 0 φ) {γ₁ γ₂ : ℝ → M} {y : M} (hγ₁ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ₁)
    (hγ₂ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ₂) (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    pathIntegral φ (curveConcat γ₁ γ₂) 0 1 = pathIntegral φ γ₁ 0 1 + pathIntegral φ γ₂ 0 1 := by
  have hi := hφ.intervalIntegrable_apply_curveVelocity
    (ContMDiff.curveConcat (n := 1) hγ₁ hγ₂ h₁ h₂)
  rw [← pathIntegral_add_adjacent (hi 0 (1 / 3)) (hi (1 / 3) 1),
    ← pathIntegral_add_adjacent (hi (1 / 3) (2 / 3)) (hi (2 / 3) 1)]
  -- The concatenation runs through `γ₁` on `[0, 1/3]`, rests on `[1/3, 2/3]`, and runs through
  -- `γ₂` on `[2/3, 1]`.
  have hl : pathIntegral φ (curveConcat γ₁ γ₂) 0 (1 / 3) = pathIntegral φ γ₁ 0 1 := by
    rw [pathIntegral_congr_of_eqOn_uIoo ((eqOn_curveConcat_left h₁ h₂).mono fun t ht ↦ by
        rw [uIoo_of_le (by norm_num)] at ht; exact lt_trans ht.2 (by norm_num)),
      show (fun t ↦ γ₁ (3 * t)) = γ₁ ∘ fun t ↦ 3 * t from rfl,
      pathIntegral_comp hφ hγ₁ (σ' := fun _ ↦ 3) (fun t _ ↦ by
        simpa using (hasDerivAt_id t).const_mul (3 : ℝ)) continuousOn_const]
    norm_num
  have hm : pathIntegral φ (curveConcat γ₁ γ₂) (1 / 3) (2 / 3) = 0 := by
    rw [pathIntegral_congr_of_eqOn_uIoo (γ' := fun _ ↦ y) fun t ht ↦
        curveConcat_eq_of_mem_Icc h₁ h₂ (by
          rw [uIoo_of_le (by norm_num)] at ht; exact Ioo_subset_Icc_self ht),
      pathIntegral_const_curve]
  have hr : pathIntegral φ (curveConcat γ₁ γ₂) (2 / 3) 1 = pathIntegral φ γ₂ 0 1 := by
    rw [pathIntegral_congr_of_eqOn_uIoo ((eqOn_curveConcat_right h₁ h₂).mono fun t ht ↦ by
        rw [uIoo_of_le (by norm_num)] at ht; exact lt_trans (by norm_num) ht.1),
      show (fun t ↦ γ₂ (3 * t - 2)) = γ₂ ∘ fun t ↦ 3 * t - 2 from rfl,
      pathIntegral_comp hφ hγ₂ (σ' := fun _ ↦ 3) (fun t _ ↦ by
        simpa using ((hasDerivAt_id t).const_mul (3 : ℝ)).sub_const 2) continuousOn_const]
    norm_num
  rw [hl, hm, hr, zero_add]

/-- The line integral along a reversed `C¹` curve is the negative of the line integral. -/
private theorem pathIntegral_comp_one_sub [IsManifold I 1 M] {φ : RoughForm I M F 1}
    (hφ : IsSmoothForm I 0 φ) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    pathIntegral φ (γ ∘ fun t ↦ 1 - t) 0 1 = -pathIntegral φ γ 0 1 := by
  rw [pathIntegral_comp hφ hγ (σ' := fun _ ↦ -1) (fun t _ ↦ by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)) continuousOn_const]
  rw [sub_zero, sub_self]
  exact pathIntegral_symm φ γ 0 1

/-- If the integrals of `φ` along smooth loops at `x₀` vanish, then two smooth curves from `x₀` to
`y`, constant on `(-∞, 0]` and on `[1, ∞)`, have the same line integral: the first followed by the
reversed second is a smooth loop at `x₀`. -/
private theorem pathIntegral_eq_of_forall_pathIntegral_eq_zero [IsManifold I 1 M]
    {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 0 φ) {x₀ y : M}
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      pathIntegral φ γ 0 1 = 0)
    {γ γ' : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hγ₀ : ∀ t ≤ 0, γ t = x₀)
    (hγ₁ : ∀ t, 1 ≤ t → γ t = y) (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ')
    (hγ'₀ : ∀ t ≤ 0, γ' t = x₀) (hγ'₁ : ∀ t, 1 ≤ t → γ' t = y) :
    pathIntegral φ γ 0 1 = pathIntegral φ γ' 0 1 := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ fun t : ℝ ↦ 1 - t :=
    (by fun_prop : ContDiff ℝ ∞ fun t : ℝ ↦ 1 - t).contMDiff
  have h₂ : ∀ t ≤ 0, (γ' ∘ fun t ↦ 1 - t) t = y := fun t ht ↦ hγ'₁ _ (by linarith)
  have hloop := h _ (hγ.curveConcat (hγ'.comp hs) hγ₁ h₂)
    (by rw [curveConcat_of_le (by norm_num), hγ₀ _ (by norm_num)])
    (by rw [curveConcat_of_lt (by norm_num)]; exact hγ'₀ _ (by norm_num))
  rw [pathIntegral_curveConcat hφ (hγ.of_le (by simp)) ((hγ'.comp hs).of_le (by simp)) hγ₁ h₂,
    pathIntegral_comp_one_sub hφ (hγ'.of_le (by simp))] at hloop
  exact sub_eq_zero.mp ((sub_eq_add_neg _ _).trans hloop)

/-- A function which near `x` differs by a constant from a function `g` differentiable at `x` has
the same exterior derivative at `x` as `g`. -/
private theorem mextDeriv_ofFunction_eq_of_eventuallyEq_add_const {f g : M → F} {x : M} {c : F}
    (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) (hfg : ∀ᶠ y in 𝓝 x, f y = g y + c) :
    mextDeriv (RoughForm.ofFunction I f) x = mextDeriv (RoughForm.ofFunction I g) x := by
  rw [mextDeriv_ofFunction, mextDeriv_ofFunction,
    Filter.EventuallyEq.mvfderiv_eq (f₁ := f) (f := (fun z ↦ z + c) ∘ g) hfg]
  congr 1
  ext v
  rw [mvfderiv_comp_apply_of_differentiableAt (by fun_prop) hg, fderiv_add_const, fderiv_fun_id,
    ContinuousLinearMap.id_apply]

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
