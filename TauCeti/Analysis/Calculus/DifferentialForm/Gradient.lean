/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare

/-!
# Gradient fields on star-convex sets

A map `h : (ι → ℝ) → (ι → ℝ)` is the gradient of a function `S : (ι → ℝ) → ℝ` on a set `D` when
`dS = ∑ⱼ hⱼ dcⱼ` on `D`, that is `S` has derivative `∑ⱼ hⱼ(c) projⱼ` at every `c ∈ D`. The one-form
`β = ∑ⱼ hⱼ dcⱼ` has exterior derivative

`dβ(v, w) = dh(v) ⬝ w - dh(w) ⬝ v`

(`TauCeti.extDeriv_sum_smul_proj_apply`), so the derivative of a differentiable gradient field is
symmetric, `∂ⱼ hᵢ = ∂ᵢ hⱼ` (`TauCeti.fderiv_dotProduct_comm_of_eventually_hasFDerivAt`), by the
symmetry of second derivatives. On an open star-convex set this condition is also sufficient: by
the Poincaré lemma, a `Cʳ` map with symmetric derivative, `r ≥ 1`, is the gradient of a `Cʳ⁺¹`
function (`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11 (closed and exact covector fields) and Chapter 17 (the Poincaré
  lemma).
-/

public section

open Set Filter Topology
open ContinuousLinearMap (proj)
open scoped ContDiff

variable {ι : Type*} [Fintype ι] {h : (ι → ℝ) → ι → ℝ} {c : ι → ℝ}

namespace TauCeti

/-- **The exterior derivative of a coordinate one-form.** The one-form `β = ∑ⱼ hⱼ dcⱼ` of a map
`h : (ι → ℝ) → (ι → ℝ)` differentiable at `c` has exterior derivative
`dβ(v, w) = dh(v) ⬝ w - dh(w) ⬝ v` at `c`. -/
theorem extDeriv_sum_smul_proj_apply (hh : DifferentiableAt ℝ h c) (v w : ι → ℝ) :
    extDeriv (fun c ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      (∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ))) c ![v, w] =
      fderiv ℝ h c v ⬝ᵥ w - fderiv ℝ h c w ⬝ᵥ v := by
  classical
  have hβ : DifferentiableAt ℝ (fun c ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      (∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ))) c :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ι → ℝ) (F := ℝ)
      (0 : Fin 1)).differentiableAt.comp c
      (DifferentiableAt.fun_sum fun j _ ↦ (differentiableAt_pi.1 hh j).smul_const _)
  -- The coefficients of the one-form are the components of `h`.
  have hcoef (i : ι) : (fun y ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      (∑ j, h y j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) fun _ ↦ Pi.single i 1) = fun y ↦ h y i := by
    funext y
    simp [Pi.single_apply]
  have hd (i : ι) (u : ι → ℝ) : fderiv ℝ (fun y ↦ h y i) c u = fderiv ℝ h c u i := by
    rw [(hasFDerivAt_pi'.1 hh.hasFDerivAt i).fderiv]
    rfl
  rw [extDeriv_apply_pair_eq_sum hβ]
  simp only [hcoef, hd, smul_eq_mul, Finset.sum_sub_distrib, dotProduct]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- **Gradient fields have symmetric derivatives.** If `dS = ∑ⱼ hⱼ dcⱼ` near `c` and `h` is
differentiable at `c`, then the derivative of `h` at `c` is symmetric: `dh(v) ⬝ w = dh(w) ⬝ v`,
that is `∂ⱼ hᵢ = ∂ᵢ hⱼ`. -/
theorem fderiv_dotProduct_comm_of_eventually_hasFDerivAt {S : (ι → ℝ) → ℝ}
    (hh : DifferentiableAt ℝ h c)
    (hS : ∀ᶠ c' in 𝓝 c, HasFDerivAt S (∑ j, h c' j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c')
    (v w : ι → ℝ) :
    fderiv ℝ h c v ⬝ᵥ w = fderiv ℝ h c w ⬝ᵥ v := by
  -- The derivative of `c' ↦ ∑ⱼ hⱼ(c') projⱼ` at `c` is `v ↦ ∑ⱼ dhⱼ(v) projⱼ`, the second
  -- derivative of `S`, which is symmetric.
  have hd : HasFDerivAt (fun c' ↦ ∑ j, h c' j • (proj j : (ι → ℝ) →L[ℝ] ℝ))
      (∑ j, (((proj j : (ι → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ h c)).smulRight
        (proj j : (ι → ℝ) →L[ℝ] ℝ))) c :=
    HasFDerivAt.fun_sum fun j _ ↦
      (hasFDerivAt_pi'.1 hh.hasFDerivAt j).smul_const (proj j : (ι → ℝ) →L[ℝ] ℝ)
  simpa [dotProduct, mul_comm] using second_derivative_symmetric_of_eventually_of_real hS hd v w

end TauCeti

namespace StarConvex

/-- **Closed coordinate one-forms on star-convex sets are exact.** Let `D` be an open set,
star-convex with respect to `c₀`, and let `h : (ι → ℝ) → (ι → ℝ)` be `Cʳ` on `D`, `r ≥ 1`, with
symmetric derivative: `dh(v) ⬝ w = dh(w) ⬝ v` on `D`. Then `h` is the gradient of a `Cʳ⁺¹`
function `S` on `D`: `dS = ∑ⱼ hⱼ dcⱼ`. -/
theorem exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm {D : Set (ι → ℝ)}
    {c₀ : ι → ℝ} (hD : StarConvex ℝ c₀ D) (hDo : IsOpen D) {r : ℕ∞} (hr : 1 ≤ r)
    (hh : ContDiffOn ℝ r h D)
    (hsym : ∀ c ∈ D, ∀ v w, fderiv ℝ h c v ⬝ᵥ w = fderiv ℝ h c w ⬝ᵥ v) :
    ∃ S : (ι → ℝ) → ℝ, ContDiffOn ℝ (r + 1) S D ∧
      ∀ c ∈ D, HasFDerivAt S (∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c := by
  have hr' : (r : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  set L : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ := fun c ↦ ∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)
  have hLs : ContDiffOn ℝ r L D :=
    ContDiffOn.sum fun j _ ↦ (contDiffOn_pi.1 hh j).smul_const _
  -- The one-form `β = ∑ⱼ hⱼ dcⱼ` is closed, since the derivative of `h` is symmetric.
  set β : (ι → ℝ) → (ι → ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun c ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (L c)
  have hβs : ContDiffOn ℝ r β D :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ι → ℝ) (F := ℝ)
      (0 : Fin 1)).contDiff.comp_contDiffOn hLs
  have hdβ : ∀ c ∈ D, extDeriv β c = 0 := by
    intro c hcD
    have hhd : DifferentiableAt ℝ h c :=
      (hh.differentiableOn hr' c hcD).differentiableAt (hDo.mem_nhds hcD)
    ext m
    have hm : m = ![m 0, m 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hm, TauCeti.extDeriv_sum_smul_proj_apply hhd, hsym c hcD, sub_self,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  -- By the Poincaré lemma `β = dS` for a function `S`.
  obtain ⟨α, hα, -, hdα⟩ := hD.exists_contDiffOn_forall_extDeriv_eq hDo hr hβs hdβ
  let e := ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (ι → ℝ) ℝ (Fin 0)
  set S : (ι → ℝ) → ℝ := fun y ↦ e.symm (α y)
  have hS : ContDiffOn ℝ r S D := e.symm.contDiff.comp_contDiffOn hα
  have hαS : α = fun y ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ (ι → ℝ) (Fin 0) (S y) := by
    funext y
    exact (e.apply_symm_apply (α y)).symm
  have hSL : ∀ c ∈ D, HasFDerivAt S (L c) c := by
    intro c hcD
    have heq := hdα c hcD
    rw [hαS, extDeriv_constOfIsEmpty] at heq
    have hder : fderiv ℝ S c = L c :=
      (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).injective heq
    rw [← hder]
    exact ((hS.differentiableOn hr' c hcD).differentiableAt (hDo.mem_nhds hcD)).hasFDerivAt
  -- `S` is one degree smoother than its derivative `L`.
  exact ⟨S, (contDiffOn_succ_iff_fderiv_of_isOpen hDo).2
    ⟨fun c hcD ↦ (hSL c hcD).differentiableAt.differentiableWithinAt, by simp,
      hLs.congr fun c hcD ↦ (hSL c hcD).fderiv⟩, hSL⟩

end StarConvex
