/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# One-dimensional harmonic functions

On the real line `ℝ`, harmonic functions are precisely the locally affine functions: on every
connected open subset `V ⊆ ℝ`, a harmonic function agrees with `y ↦ a * y + b`
(`InnerProductSpace.exists_affine_eqOn_of_harmonicOnNhd_real`), and every affine function is
globally harmonic (`InnerProductSpace.harmonicOnNhd_affine_real`). When `K ⊆ Ω ⊆ ℝ` is filled in
`Ω`, `K` intersects each connected component of `Ω` in a preconnected set
(`TauCeti.IsFilledIn.isPreconnected_inter_connectedComponentIn`), so every function harmonic near
`K` extends to a function harmonic on all of `Ω` that agrees with it on a neighbourhood of `K`
(`InnerProductSpace.exists_harmonicOnNhd_real_of_isFilledIn`).

## Main declarations

* `InnerProductSpace.exists_affine_eqOn_of_harmonicOnNhd_real`: every harmonic function on a
  preconnected open subset of `ℝ` is affine.
* `InnerProductSpace.harmonicOnNhd_affine_real`: every affine function on `ℝ` is harmonic.
* `InnerProductSpace.exists_harmonicOnNhd_real_of_isFilledIn`: exact harmonic extension from a
  filled-in subset `K ⊆ Ω ⊆ ℝ` to all of `Ω`.
-/

public section

noncomputable section

open Filter Set TauCeti TopologicalSpace Topology

namespace InnerProductSpace

/-- On an open connected subset of `ℝ`, every real-valued harmonic function is affine. -/
theorem exists_affine_eqOn_of_harmonicOnNhd_real {V : Set ℝ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) {h : ℝ → ℝ} (hh : HarmonicOnNhd h V) :
    ∃ a b : ℝ, ∀ y ∈ V, h y = a * y + b := by
  have hc2 : ContDiffOn ℝ 2 h V := hh.contDiffOn
  have hderiv_diff : DifferentiableOn ℝ (deriv h) V :=
    (hc2.deriv_of_isOpen hVo (by norm_num)).differentiableOn one_ne_zero
  have hderiv2 : ∀ y ∈ V, deriv (deriv h) y = 0 := fun y hy ↦ by
    have hΔ := (hh y hy).2.self_of_nhds
    simpa [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one] using hΔ
  obtain ⟨a, ha⟩ := hVo.exists_is_const_of_deriv_eq_zero hVc hderiv_diff hderiv2
  have hg_diff : DifferentiableOn ℝ (fun y ↦ h y - a * y) V :=
    (hc2.differentiableOn (by norm_num)).sub (differentiableOn_const a |>.mul differentiableOn_id)
  have hg_deriv : ∀ y ∈ V, deriv (fun z ↦ h z - a * z) y = 0 := fun y hy ↦ by
    have hhd : DifferentiableAt ℝ h y :=
      ((hc2.differentiableOn (by norm_num)).differentiableAt (hVo.mem_nhds hy))
    have hlin : HasDerivAt (fun z : ℝ ↦ a * z) a y := by
      simpa using (hasDerivAt_id y).const_mul a
    rw [deriv_fun_sub hhd hlin.differentiableAt, hlin.deriv, ha y hy, sub_self]
  obtain ⟨b, hb⟩ := hVo.exists_is_const_of_deriv_eq_zero hVc hg_diff hg_deriv
  exact ⟨a, b, fun y hy ↦ by linarith [hb y hy]⟩

/-- Every affine function on `ℝ` is harmonic everywhere. -/
theorem harmonicOnNhd_affine_real (a b : ℝ) :
    HarmonicOnNhd (fun y : ℝ ↦ a * y + b) univ := fun _ _ ↦ by
  refine ⟨(contDiff_const.mul contDiff_id |>.add contDiff_const).contDiffAt,
    Eventually.of_forall fun y ↦ ?_⟩
  have hd : deriv (fun z : ℝ ↦ a * z + b) = fun _ ↦ a := by
    ext z
    simp
  simp [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, hd]

/-- In dimension `1`, every function harmonic near a filled-in set `K ⊆ Ω` extends to a
function harmonic on all of `Ω` that agrees with `h` on a neighbourhood of `K`. -/
theorem exists_harmonicOnNhd_real_of_isFilledIn {Ω K : Set ℝ} (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) {h : ℝ → ℝ} (hh : HarmonicOnNhd h K) :
    ∃ H : ℝ → ℝ, HarmonicOnNhd H Ω ∧ H =ᶠ[𝓝ˢ K] h := by
  classical
  let U : Set ℝ := {y | HarmonicAt h y}
  have hUo : IsOpen U := isOpen_setOfPred_harmonicAt (f := h)
  -- For each `x ∈ K`, pick an affine function agreeing with `h` on `connectedComponentIn U x`.
  have haff : ∀ x ∈ K, ∃ a b : ℝ, ∀ y ∈ connectedComponentIn U x, h y = a * y + b := fun x _ ↦
    exists_affine_eqOn_of_harmonicOnNhd_real (hUo.connectedComponentIn)
      isPreconnected_connectedComponentIn fun y hy ↦ connectedComponentIn_subset U x hy
  -- Define `H` on each connected component `C = connectedComponentIn Ω y` using a chosen point
  -- of `K ∩ C` (depending only on `C`) when `K ∩ C` is nonempty, and `0` otherwise.
  let H (y : ℝ) : ℝ :=
    if hne : (K ∩ connectedComponentIn Ω y).Nonempty then
      let x₀ := hne.choose
      have hx₀ : x₀ ∈ K := hne.choose_spec.1
      (haff x₀ hx₀).choose * y + (haff x₀ hx₀).choose_spec.choose
    else 0
  have hH_harm : HarmonicOnNhd H Ω := by
    intro y hy
    let C := connectedComponentIn Ω y
    have hCo : IsOpen C := hΩ.connectedComponentIn
    have hCeq : ∀ z ∈ C, connectedComponentIn Ω z = C := fun z hz ↦
      (connectedComponentIn_eq hz).symm
    by_cases hne : (K ∩ C).Nonempty
    · let x₀ := hne.choose
      have hx₀ : x₀ ∈ K := hne.choose_spec.1
      let a := (haff x₀ hx₀).choose
      let b := (haff x₀ hx₀).choose_spec.choose
      have hev : H =ᶠ[𝓝 y] fun z ↦ a * z + b := by
        filter_upwards [hCo.mem_nhds (mem_connectedComponentIn hy)] with z hz
        simp only [H, hCeq z hz, hne, ↓reduceDIte, x₀, a, b]
      exact (harmonicAt_congr_nhds hev).2 (harmonicOnNhd_affine_real a b y (mem_univ y))
    · have hev : H =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hCo.mem_nhds (mem_connectedComponentIn hy)] with z hz
        simp only [H, hCeq z hz, hne, ↓reduceDIte]
      exact (harmonicAt_congr_nhds hev).2 (harmonicOnNhd_const (0 : ℝ) y (mem_univ y))
  refine ⟨H, hH_harm, ?_⟩
  rw [EventuallyEq, eventually_nhdsSet_iff_forall]
  intro x hx
  let C := connectedComponentIn Ω x
  have hCo : IsOpen C := hΩ.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn (hKΩ hx)
  have hne : (K ∩ C).Nonempty := ⟨x, hx, hxC⟩
  let x₀ := hne.choose
  have hx₀K : x₀ ∈ K := hne.choose_spec.1
  have hx₀C : x₀ ∈ C := hne.choose_spec.2
  have hKC_sub : K ∩ C ⊆ connectedComponentIn U x₀ :=
    (hfill.isPreconnected_inter_connectedComponentIn x).subset_connectedComponentIn
      ⟨hx₀K, hx₀C⟩ (inter_subset_left.trans hh)
  have hxU₀ : x ∈ connectedComponentIn U x₀ := hKC_sub ⟨hx, hxC⟩
  have hVo : IsOpen (connectedComponentIn U x₀) := hUo.connectedComponentIn
  filter_upwards [(hCo.inter hVo).mem_nhds ⟨hxC, hxU₀⟩] with y ⟨hyC, hyV⟩
  have hCeq : connectedComponentIn Ω y = C := (connectedComponentIn_eq hyC).symm
  simp only [H, hCeq, hne, ↓reduceDIte]
  exact ((haff x₀ hx₀K).choose_spec.choose_spec y hyV).symm

end InnerProductSpace
