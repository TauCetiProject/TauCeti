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

* `TauCeti.exists_local_primitive_pathIntegral_eq_add_sub`: near a point `x`, a closed form `φ`
  has a function `g`, `C^r` at `x` with `dg x = φ x`, such that extending a curve from the base
  point to `x` by short curves changes its line integral by the increment of `g`.
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
  obtain ⟨ℓ, hℓ, hℓ₀, hℓ₁, hℓφ⟩ :=
    exists_contMDiff_loop_pathIntegral_eq_sub hφ hγ hγ₀ hγ₁ hγ' hγ'₀ hγ'₁
  exact sub_eq_zero.mp (hℓφ ▸ h ℓ hℓ hℓ₀ hℓ₁)

variable [CompleteSpace F]

/-- **Local primitives extend line integrals.** Let `φ` be a `C^r` `1`-form (`1 ≤ r`) closed near
`x`, and `γ` a smooth curve from `x₀` to `x`, constant on `(-∞, 0]` and on `[1, ∞)`. Then there is
a function `g`, `C^r` at `x` with `dg x = φ x`, such that every `y` near `x` is reached from `x₀` by
a smooth curve `δ`, `γ` followed by a short curve from `x` to `y`, with
`∫_δ φ = ∫_γ φ + g y - g x`. -/
theorem exists_local_primitive_pathIntegral_eq_add_sub [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I ∞ M] {r : ℕ∞} (hr : 1 ≤ r) {φ : RoughForm I M F 1} (hφ : IsSmoothForm I r φ)
    {x₀ x : M} (hclosed : ∀ᶠ y in 𝓝 x, mextDeriv φ y = 0) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hγ₀ : ∀ t ≤ 0, γ t = x₀) (hγ₁ : ∀ t, 1 ≤ t → γ t = x) :
    ∃ g : M → F, ContMDiffAt I 𝓘(ℝ, F) r g x ∧ mextDeriv (RoughForm.ofFunction I g) x = φ x ∧
      ∀ᶠ y in 𝓝 x, ∃ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ δ ∧ (∀ t ≤ 0, δ t = x₀) ∧
        (∀ t, 1 ≤ t → δ t = y) ∧ pathIntegral φ δ 0 1 = pathIntegral φ γ 0 1 + (g y - g x) := by
  have hφ₀ : IsSmoothForm I 0 φ := hφ.of_le (by simp)
  obtain ⟨U, hU, ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_nhds hr hφ hclosed
  have hψ' := hψ
  rw [RoughForm.eq_ofFunction ψ, isSmoothForm_ofFunction_iff] at hψ'
  refine ⟨fun y ↦ ψ y 0, hψ' x, ?_, ?_⟩
  · rw [← RoughForm.eq_ofFunction]
    exact hdψ x (mem_of_mem_nhds hU)
  filter_upwards [eventually_exists_contMDiff_curve (I := I) (n := ⊤) hU] with y hy
  obtain ⟨c, hc, hc₀, hc₁, hcU⟩ := hy
  have hc' : ContMDiff 𝓘(ℝ, ℝ) I 1 c := hc.of_le (by simp)
  -- Follow `γ` to `x`, then the short curve `c` from `x` to `y`, along which `φ = dψ`.
  refine ⟨_, hγ.curveConcat hc hγ₁ hc₀,
    fun t ht ↦ by rw [curveConcat_of_le (by linarith), hγ₀ _ (by linarith)],
    fun t ht ↦ by rw [curveConcat_of_lt (by linarith), hc₁ _ (by linarith)], ?_⟩
  rw [pathIntegral_curveConcat hφ₀ (hγ.of_le (by simp)) hc' hγ₁ hc₀,
    pathIntegral_congr (ψ := mextDeriv ψ) fun t _ ↦ (hdψ _ (hcU t)).symm,
    pathIntegral_mextDeriv (hψ.of_le (by exact_mod_cast hr)) hc', hc₁ 1 le_rfl, hc₀ 0 le_rfl]

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
  refine exists_mextDeriv_eq_of_forall_eventuallyEq_add_const (f := f) fun x ↦ ?_
  obtain ⟨g, hg, hdg, hδ⟩ := exists_local_primitive_pathIntegral_eq_add_sub hr hφ
    (Eventually.of_forall fun y ↦ congrFun hclosed y) (hγ x) (hγ₀ x) (hγ₁ x)
  refine ⟨g, f x - g x, hg, ?_, hdg⟩
  filter_upwards [hδ] with y ⟨δ, hδ, hδ₀, hδ₁, hδφ⟩
  simp only [hf_def]
  rw [pathIntegral_eq_of_forall_pathIntegral_eq_zero hφ₀ h (hγ y) (hγ₀ y) (hγ₁ y) hδ hδ₀ hδ₁, hδφ]
  abel

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
  exact ⟨⟨ψ, hψ.mem_smoothBundleForms⟩, Subtype.ext ((mextDerivₗ_apply I 0 _).trans hdψ)⟩

/-- A de Rham class of degree one on a preconnected manifold vanishes exactly when the integrals
of a representative along all smooth loops at a base point `x₀` vanish. -/
theorem deRhamCohomology.mk_eq_zero_iff_forall_pathIntegral_eq_zero [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I ∞ M] [PreconnectedSpace M] (φ : closedForms I M 1) (x₀ : M) :
    deRhamCohomology.mk I 1 φ = 0 ↔ ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ →
      γ 1 = x₀ → pathIntegral ((φ : SmoothForm I M ℝ 1) : RoughForm I M ℝ 1) γ 0 1 = 0 := by
  rw [deRhamCohomology.mk_eq_zero_iff, mem_exactForms_one_iff_forall_pathIntegral_eq_zero φ.2]

end TauCeti
