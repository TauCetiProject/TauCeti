/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.LogDeriv
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.Meromorphic.Continuation
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# The Laurent data of a Dirichlet L-function at the origin

Let `χ` be a primitive nonprincipal Dirichlet character of conductor `N`, let `a` be `2` for
even and `1` for odd `χ`, and write `Λ₀ = (dirichletData χ hχ).entireCompletion`. Shifting the
real gamma factor by `2` in the even case moves its pole at the origin into the term
`(a - 1) / s`, so that near the origin
`L'/L (s, χ) = Λ₀'/Λ₀ (s) - ½ log N - Γℝ'/Γℝ (s + a) + (a - 1) / s`,
with the first three terms analytic at `0`. Consequently `L(χ, ·)` has order `1` at the origin
for even and order `0` for odd `χ`, and the finite part of `L'/L` at the origin is
`Λ₀'/Λ₀ (0) - ½ log N - Γℝ'/Γℝ (a)`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex Filter TauCeti TauCeti.LFunctions Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

variable (hχ : χ.IsPrimitive)

open scoped Classical in
/-- Near the origin, `L'/L` is an analytic function plus `(a - 1) / z`. -/
private theorem logDeriv_LFunction_eventuallyEq_nhdsNE_zero (hne : χ ≠ 1) :
    let a : ℝ := if χ.Even then 2 else 1
    let g := fun z : ℂ ↦ logDeriv (dirichletData χ hχ).entireCompletion z -
      (Real.log N : ℂ) / 2 - logDeriv Gammaℝ (z + a)
    AnalyticAt ℂ g 0 ∧ logDeriv χ.LFunction =ᶠ[𝓝[≠] 0] fun z ↦ g z + ((a : ℂ) - 1) / z := by
  intro a g
  let F := (dirichletData χ hχ).entireCompletion
  have hF (z : ℂ) : AnalyticAt ℂ F z :=
    (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion z
  have hmF : Meromorphic F := fun z ↦ (hF z).meromorphicAt
  have hmG : Meromorphic (fun z : ℂ ↦ logDeriv Gammaℝ (z + a)) :=
    Meromorphic.meromorphic_fun_comp_add_const_iff_meromorphic.mpr meromorphic_Gammaℝ.logDeriv
  have hg' : Meromorphic g := (hmF.logDeriv.fun_sub (Meromorphic.const _)).fun_sub hmG
  have hg : AnalyticAt ℂ g 0 := by
    have ha : 0 < a := by dsimp [a]; split <;> norm_num
    have hF₀ : F 0 ≠ 0 := dirichletData_entireCompletion_ne_zero_of_re_nonpos χ hχ (by simp)
    have hGa := analyticAt_logDeriv_Gammaℝ (s := (0 : ℂ) + a)
      (Gammaℝ_ne_zero_of_re_pos (by simpa using ha))
    have hlog : AnalyticAt ℂ (logDeriv F) 0 := (hF 0).deriv.div (hF 0) hF₀
    have hshift : AnalyticAt ℂ (fun z : ℂ ↦ z + a) 0 := by fun_prop
    exact (hlog.fun_sub analyticAt_const).fun_sub (hGa.fun_comp (f := _) (x := 0) hshift)
  refine ⟨hg, eventuallyEq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    χ.meromorphic_LFunction.logDeriv (by fun_prop) (fun z hz ↦ ?_) 0⟩
  have hz' : 1 < z.re := hz
  have hlog := logDeriv_dirichletData_entireCompletion χ hχ hne (one_pos.trans hz')
    (χ.LFunction_ne_zero_of_one_le_re (.inl hne) hz'.le)
  rw [χ.logDeriv_gammaFactor_eq_logDeriv_Gammaℝ_add_sub_div
    (χ.gammaFactor_ne_zero_of_re_pos (one_pos.trans hz'))] at hlog
  dsimp only [g]
  push_cast only [ofReal_sub, ofReal_one] at hlog
  linear_combination -hlog

include hχ in
open scoped Classical in
/-- A primitive nonprincipal Dirichlet L-function vanishes to order `1` at the origin for even
characters and does not vanish there for odd characters. -/
theorem meromorphicOrderAt_LFunction_zero (hne : χ ≠ 1) :
    meromorphicOrderAt χ.LFunction 0 = if χ.Even then 1 else 0 := by
  obtain ⟨hg, heq⟩ := χ.logDeriv_LFunction_eventuallyEq_nhdsNE_zero hχ hne
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (χ.meromorphicOrderAt_LFunction_ne_top 0)
  have hres := Contour.residue_logDeriv_eq_meromorphicOrderAt (χ.meromorphic_LFunction 0) hn.symm
  rw [Contour.residue_congr_nhdsNE heq] at hres
  have hpole := Contour.residue_add_div_sub_mul_of_analyticAt
    (r := ((if χ.Even then 2 else 1 : ℝ) : ℂ) - 1) hg (analyticAt_const (v := (1 : ℂ)))
  simp only [sub_zero, mul_one] at hpole
  have h := hpole.symm.trans hres
  rw [← hn]
  split_ifs with he <;> simp only [he, ↓reduceIte] at h <;> norm_num at h <;>
    exact_mod_cast h.symm

include hχ in
open scoped Classical in
/-- The complex order coefficient at the origin is `a - 1`, where `a` is the first strictly
positive gamma-pole offset (`2` for even characters and `1` for odd characters). -/
theorem untop₀_meromorphicOrderAt_LFunction_zero (hne : χ ≠ 1) :
    ((meromorphicOrderAt χ.LFunction 0).untop₀ : ℂ) = ((if χ.Even then 2 else 1 : ℝ) : ℂ) - 1 := by
  rw [χ.meromorphicOrderAt_LFunction_zero hχ hne]
  split_ifs <;> norm_num

open scoped Classical in
/-- The finite part of `L'/L` at the origin for a primitive nonprincipal Dirichlet character. -/
theorem logDerivFinitePart_LFunction_zero (hne : χ ≠ 1) :
    logDerivFinitePart χ.LFunction 0 =
      logDeriv (dirichletData χ hχ).entireCompletion 0 - (Real.log N : ℂ) / 2 -
        logDeriv Gammaℝ (if χ.Even then 2 else 1 : ℝ) := by
  obtain ⟨hg, heq⟩ := χ.logDeriv_LFunction_eventuallyEq_nhdsNE_zero hχ hne
  have hpart := hg.logDerivFinitePart_eq (f := χ.LFunction) (by
    filter_upwards [heq] with z hz
    rw [hz, sub_zero, χ.untop₀_meromorphicOrderAt_LFunction_zero hχ hne, add_sub_cancel_right])
  simpa only [zero_add] using hpart

end DirichletCharacter
