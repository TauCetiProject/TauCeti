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

A covector field `L : E → E →L[ℝ] F` is the gradient of a function `S : E → F` on a set `D` when
`dS = L` on `D`, that is `S` has derivative `L c` at every `c ∈ D`. The one-form
`β = ofSubsingletonLIE 0 ∘ L` has exterior derivative

`dβ(v, w) = dL(v)(w) - dL(w)(v)`

(`TauCeti.extDeriv_ofSubsingletonLIE_apply_pair`). On an open star-convex set, a closed `Cʳ`
covector field, `r ≥ 1`, is the gradient of a `Cʳ⁺¹` function
(`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_extDeriv_eq_zero`), by the Poincaré lemma
`StarConvex.exists_contDiffOn_forall_extDeriv_eq`. Equivalently, a `Cʳ` covector field with
symmetric derivative is a gradient
(`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_symmetric`). Mathlib's
`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric` gives a potential on convex sets for a
covector field that is only differentiable. The star-convex version here instead needs `L` to be
`Cʳ` with `r ≥ 1`, and it also shows that the potential is `Cʳ⁺¹`.

In coordinates on `ι → ℝ`, the gradient field of `h : (ι → ℝ) → (ι → ℝ)` is the one-form
`∑ⱼ hⱼ dcⱼ`, with value `v ↦ h ⬝ v` (`TauCeti.sum_smul_proj_apply`). Its derivative is
`(v, w) ↦ dh(v) ⬝ w` (`TauCeti.fderiv_sum_smul_proj_apply`).
So the derivative of a differentiable gradient field is symmetric, `∂ⱼ hᵢ = ∂ᵢ hⱼ`
(`TauCeti.fderiv_dotProduct_comm_of_eventually_hasFDerivAt`), by Mathlib's
`second_derivative_symmetric_of_eventually_of_real`, and conversely on an open star-convex set
(`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11 (closed and exact covector fields) and Chapter 17 (the Poincaré
  lemma).
-/

public section

open Set Filter Topology ContinuousAlternatingMap
open ContinuousLinearMap (proj)
open scoped ContDiff

namespace TauCeti

/-- **The exterior derivative of a covector field.** The one-form `β = ofSubsingletonLIE 0 ∘ L` of
a covector field `L : E → E →L[𝕜] F` differentiable at `x` has exterior derivative
`dβ(v, w) = dL(v)(w) - dL(w)(v)` at `x`. -/
theorem extDeriv_ofSubsingletonLIE_apply_pair {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {L : E → E →L[𝕜] F} {x : E} (hL : DifferentiableAt 𝕜 L x) (v w : E) :
    extDeriv (fun y ↦ ofSubsingletonLIE (0 : Fin 1) (L y)) x ![v, w] =
      fderiv 𝕜 L x v w - fderiv 𝕜 L x w v := by
  have hβ : DifferentiableAt 𝕜 (fun y ↦ ofSubsingletonLIE (0 : Fin 1) (L y)) x :=
    (ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := F) (0 : Fin 1)).differentiableAt.comp x hL
  rw [extDeriv_apply_pair_of_differentiableAt hβ]
  simp [(hL.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv,
    (hL.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]

variable {ι : Type*} [Fintype ι] {h : (ι → ℝ) → ι → ℝ} {c : ι → ℝ}

/-- **A coordinate covector.** The covector `∑ⱼ aⱼ dcⱼ` on `ι → ℝ` is `v ↦ a ⬝ v`. -/
theorem sum_smul_proj_apply (a v : ι → ℝ) :
    (∑ j, a j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) v = a ⬝ᵥ v := by
  simp [dotProduct]

/-- **The derivative of a coordinate one-form.** The covector field `∑ⱼ hⱼ dcⱼ` of a map
`h : (ι → ℝ) → (ι → ℝ)` differentiable at `c` has derivative `(v, w) ↦ dh(v) ⬝ w` at `c`. -/
theorem fderiv_sum_smul_proj_apply (hh : DifferentiableAt ℝ h c) (v w : ι → ℝ) :
    fderiv ℝ (fun c ↦ ∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c v w =
      fderiv ℝ h c v ⬝ᵥ w := by
  have hd : HasFDerivAt (fun c' ↦ ∑ j, h c' j • (proj j : (ι → ℝ) →L[ℝ] ℝ))
      (∑ j, (((proj j : (ι → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ h c)).smulRight
        (proj j : (ι → ℝ) →L[ℝ] ℝ))) c :=
    HasFDerivAt.fun_sum fun j _ ↦
      (hasFDerivAt_pi'.1 hh.hasFDerivAt j).smul_const (proj j : (ι → ℝ) →L[ℝ] ℝ)
  simp [hd.fderiv, dotProduct]

/-- **Gradient fields have symmetric derivatives.** If `dS = ∑ⱼ hⱼ dcⱼ` near `c` and `h` is
differentiable at `c`, then the derivative of `h` at `c` is symmetric: `dh(v) ⬝ w = dh(w) ⬝ v`,
that is `∂ⱼ hᵢ = ∂ᵢ hⱼ`. This is Mathlib's `second_derivative_symmetric_of_eventually_of_real`
in coordinates. -/
theorem fderiv_dotProduct_comm_of_eventually_hasFDerivAt {S : (ι → ℝ) → ℝ}
    (hh : DifferentiableAt ℝ h c)
    (hS : ∀ᶠ c' in 𝓝 c, HasFDerivAt S (∑ j, h c' j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c')
    (v w : ι → ℝ) :
    fderiv ℝ h c v ⬝ᵥ w = fderiv ℝ h c w ⬝ᵥ v := by
  have hL : DifferentiableAt ℝ (fun c ↦ ∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c :=
    DifferentiableAt.fun_sum fun j _ ↦ (differentiableAt_pi.1 hh j).smul_const _
  rw [← fderiv_sum_smul_proj_apply hh, ← fderiv_sum_smul_proj_apply hh]
  exact second_derivative_symmetric_of_eventually_of_real hS hL.hasFDerivAt v w

end TauCeti

namespace StarConvex

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {D : Set E} {c₀ : E} {L : E → E →L[ℝ] F} {r : ℕ∞}

/-- **Closed covector fields on star-convex sets are exact.** Let `D` be an open set, star-convex
with respect to `c₀`, and let `L : E → E →L[ℝ] F` be `Cʳ` on `D`, `r ≥ 1`, with closed one-form:
`d(ofSubsingletonLIE 0 ∘ L) = 0` on `D`. Then `L` is the gradient of a `Cʳ⁺¹` function `S` on
`D`: `dS = L`. -/
theorem exists_contDiffOn_forall_hasFDerivAt_of_extDeriv_eq_zero (hD : StarConvex ℝ c₀ D)
    (hDo : IsOpen D) (hr : 1 ≤ r) (hL : ContDiffOn ℝ r L D)
    (hdL : ∀ c ∈ D, extDeriv (fun y ↦ ofSubsingletonLIE (0 : Fin 1) (L y)) c = 0) :
    ∃ S : E → F, ContDiffOn ℝ (r + 1) S D ∧ ∀ c ∈ D, HasFDerivAt S (L c) c := by
  have hr' : (r : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  -- By the Poincaré lemma the one-form of `L` is `dα` for a `0`-form `α`.
  obtain ⟨α, hα, -, hdα⟩ := hD.exists_contDiffOn_forall_extDeriv_eq hDo hr
    ((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).contDiff.comp_contDiffOn hL) hdL
  -- The `0`-form `α` is a function `S`.
  let e := constOfIsEmptyLIE ℝ E F (Fin 0)
  set S : E → F := fun y ↦ e.symm (α y)
  have hS : ContDiffOn ℝ r S D := e.symm.contDiff.comp_contDiffOn hα
  have hαS : α = fun y ↦ constOfIsEmpty ℝ E (Fin 0) (S y) := by
    funext y
    exact (e.apply_symm_apply (α y)).symm
  have hSL : ∀ c ∈ D, HasFDerivAt S (L c) c := by
    intro c hcD
    have heq := hdα c hcD
    rw [hαS, extDeriv_constOfIsEmpty] at heq
    have hder : fderiv ℝ S c = L c :=
      (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).injective heq
    rw [← hder]
    exact ((hS.differentiableOn hr' c hcD).differentiableAt (hDo.mem_nhds hcD)).hasFDerivAt
  -- `S` is one degree smoother than its derivative `L`.
  exact ⟨S, (contDiffOn_succ_iff_fderiv_of_isOpen hDo).2
    ⟨fun c hcD ↦ (hSL c hcD).differentiableAt.differentiableWithinAt, by simp,
      hL.congr fun c hcD ↦ (hSL c hcD).fderiv⟩, hSL⟩

/-- **Covector fields with symmetric derivative on star-convex sets are gradients.** Let `D` be an
open set, star-convex with respect to `c₀`, and let `L : E → E →L[ℝ] F` be `Cʳ` on `D`, `r ≥ 1`,
with symmetric derivative: `dL(v)(w) = dL(w)(v)` on `D`. Then `L` is the gradient of a `Cʳ⁺¹`
function `S` on `D`: `dS = L`. For convex `D`, the existence of `S` is Mathlib's
`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`. -/
theorem exists_contDiffOn_forall_hasFDerivAt_of_fderiv_symmetric (hD : StarConvex ℝ c₀ D)
    (hDo : IsOpen D) (hr : 1 ≤ r) (hL : ContDiffOn ℝ r L D)
    (hsym : ∀ c ∈ D, ∀ v w, fderiv ℝ L c v w = fderiv ℝ L c w v) :
    ∃ S : E → F, ContDiffOn ℝ (r + 1) S D ∧ ∀ c ∈ D, HasFDerivAt S (L c) c := by
  have hr' : (r : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  -- The one-form of `L` is closed, since the derivative of `L` is symmetric.
  refine hD.exists_contDiffOn_forall_hasFDerivAt_of_extDeriv_eq_zero hDo hr hL fun c hcD ↦ ?_
  ext m
  have hm : m = ![m 0, m 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hm, TauCeti.extDeriv_ofSubsingletonLIE_apply_pair
      ((hL.differentiableOn hr' c hcD).differentiableAt (hDo.mem_nhds hcD))]
  simp [hsym c hcD]

end General

variable {ι : Type*} [Fintype ι] {h : (ι → ℝ) → ι → ℝ}

/-- **Closed coordinate one-forms on star-convex sets are exact.** Let `D` be an open set,
star-convex with respect to `c₀`, and let `h : (ι → ℝ) → (ι → ℝ)` be `Cʳ` on `D`, `r ≥ 1`, with
symmetric derivative: `dh(v) ⬝ w = dh(w) ⬝ v` on `D`. Then `h` is the gradient of a `Cʳ⁺¹`
function `S` on `D`: `dS = ∑ⱼ hⱼ dcⱼ`. This is
`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_symmetric` in coordinates. -/
theorem exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm {D : Set (ι → ℝ)}
    {c₀ : ι → ℝ} (hD : StarConvex ℝ c₀ D) (hDo : IsOpen D) {r : ℕ∞} (hr : 1 ≤ r)
    (hh : ContDiffOn ℝ r h D)
    (hsym : ∀ c ∈ D, ∀ v w, fderiv ℝ h c v ⬝ᵥ w = fderiv ℝ h c w ⬝ᵥ v) :
    ∃ S : (ι → ℝ) → ℝ, ContDiffOn ℝ (r + 1) S D ∧
      ∀ c ∈ D, HasFDerivAt S (∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c := by
  have hr' : (r : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  refine hD.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_symmetric
    (L := fun c ↦ ∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) hDo hr
    (ContDiffOn.sum fun j _ ↦ (contDiffOn_pi.1 hh j).smul_const _) fun c hcD v w ↦ ?_
  have hhd := (hh.differentiableOn hr' c hcD).differentiableAt (hDo.mem_nhds hcD)
  rw [TauCeti.fderiv_sum_smul_proj_apply hhd, TauCeti.fderiv_sum_smul_proj_apply hhd,
    hsym c hcD]

end StarConvex
