/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Meromorphic.Order

/-!
# Regularity, meromorphy, and poles of continued Dirichlet `L`-functions

Mathlib's continued Dirichlet `L`-function `DirichletCharacter.LFunction χ` is entire for every
nonprincipal character `χ ≠ 1` and differentiable away from `s = 1` for the principal character
`LFunctionTrivChar N` (`DirichletCharacter.differentiableAt_LFunction`,
`DirichletCharacter.LFunctionTrivChar_residue_one`).

This file packages the basic regularity and meromorphic-order API for the uncompleted continued
function `χ.LFunction`, without going through completed `L`-functions or Gamma factors:

* `TauCeti.not_differentiableAt_LFunctionTrivChar_one` and
  `DirichletCharacter.differentiableAt_LFunction_iff`: `χ.LFunction` is differentiable at `s` if
  and only if `s ≠ 1` or `χ ≠ 1`.
* `DirichletCharacter.analyticAt_LFunction`, `DirichletCharacter.analyticAt_LFunction_iff`, and
  `DirichletCharacter.meromorphic_LFunction`: `χ.LFunction` is analytic at `s` if and only if
  `s ≠ 1` or `χ ≠ 1`, and is meromorphic on `ℂ` (with the forward analyticity and meromorphy
  lemmas registered as `@[fun_prop]` rules).
* `TauCeti.meromorphicOrderAt_LFunctionTrivChar_one` and
  `DirichletCharacter.meromorphicOrderAt_LFunction_pos_iff`: `LFunctionTrivChar N` has a simple
  pole (meromorphic order `-1`) at `s = 1`, so positive meromorphic order characterizes the zeros
  of `χ.LFunction` away from that pole.
* `DirichletCharacter.LFunctionTrivChar₁_apply_of_ne_one`,
  `DirichletCharacter.LFunctionTrivChar₁_one_apply_of_ne_one`,
  `DirichletCharacter.LFunctionTrivChar₁_one_ne_zero`,
  `DirichletCharacter.LFunctionTrivChar₁_one_apply_one`, and
  `DirichletCharacter.analyticOrderAt_LFunctionTrivChar₁_one`: the values of the pole-removed
  function `LFunctionTrivChar₁ N`, which is `(s - 1) L(s)` away from `s = 1` and, for `N = 1`,
  `(s - 1) ζ(s)` away from `1` and `1` at `1`; away from `1` it vanishes exactly where `ζ` does,
  and its analytic orders agree with `ζ`.
* `DirichletCharacter.re_lt_one_of_LFunction_eq_zero`: every zero of `χ.LFunction` away from the
  simple pole `(s = 1, χ = 1)` satisfies `s.re < 1`.

## References

* D. Loeffler, M. Stoll, `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
* M. Stoll, D. Loeffler, T. Tao, `Mathlib.NumberTheory.LSeries.Nonvanishing`.
* H. Davenport, *Multiplicative Number Theory*, Ch. 4.
-/

public section

open Complex Filter
open scoped Topology

namespace DirichletCharacter

/-- Away from `s = 1`, the pole-removed principal `L`-function is `(s - 1) L(s)`. -/
theorem LFunctionTrivChar₁_apply_of_ne_one (N : ℕ) [NeZero N] {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ N s = (s - 1) * LFunctionTrivChar N s :=
  Function.update_of_ne hs ..

/-- Away from `s = 1`, Mathlib's pole-removed zeta function is `(s - 1) ζ(s)`. -/
theorem LFunctionTrivChar₁_one_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  simp [LFunctionTrivChar₁_apply_of_ne_one 1 hs]

/-- Away from `s = 1`, the pole-removed zeta function `(s - 1) ζ(s)` is nonzero wherever `ζ` is. -/
theorem LFunctionTrivChar₁_one_ne_zero {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    LFunctionTrivChar₁ 1 s ≠ 0 := by
  rw [LFunctionTrivChar₁_one_apply_of_ne_one hs]
  exact mul_ne_zero (sub_ne_zero.mpr hs) hζ

/-- At `s = 1`, the pole-removed zeta function takes the value `1`, the residue of `ζ`. -/
theorem LFunctionTrivChar₁_one_apply_one : LFunctionTrivChar₁ 1 1 = 1 := by
  simp [LFunctionTrivChar₁]

/-- Away from `s = 1`, the analytic orders of `(s - 1) ζ(s)` and `ζ(s)` agree. -/
theorem analyticOrderAt_LFunctionTrivChar₁_one {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunctionTrivChar₁ 1) ρ = analyticOrderAt riemannZeta ρ := by
  have hev : LFunctionTrivChar₁ 1 =ᶠ[𝓝 ρ] (fun z ↦ z - 1) * riemannZeta :=
    Filter.mem_of_superset (isOpen_ne.mem_nhds hρ) fun z hz ↦
      LFunctionTrivChar₁_one_apply_of_ne_one hz
  have hlin : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) ρ := by fun_prop
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hlin (analyticOn_riemannZeta ρ hρ),
    hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ), zero_add]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- The continued Dirichlet L-function is analytic everywhere except possibly at `s = 1` for the
principal character. -/
@[fun_prop]
theorem analyticAt_LFunction {s : ℂ} (h1 : s ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.LFunction s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have he1 : ∀ᶠ z in 𝓝 s, z ≠ 1 ∨ χ ≠ 1 := by
    rcases h1 with h1 | h1
    · filter_upwards [eventually_ne_nhds h1] with z hz using Or.inl hz
    · exact Filter.Eventually.of_forall fun _ ↦ Or.inr h1
  filter_upwards [he1] with z hz1
  exact χ.differentiableAt_LFunction z hz1

/-- Every Dirichlet character has a meromorphic continued L-function on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_LFunction : Meromorphic χ.LFunction := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · by_cases hχ : χ = 1
    · subst hχ
      refine MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
        ⟨-1, LFunctionTrivChar₁ N, (differentiable_LFunctionTrivChar₁ N).analyticAt 1, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
      rw [LFunctionTrivChar₁_apply_of_ne_one N hs, smul_eq_mul, zpow_neg_one]
      field_simp [sub_ne_zero.mpr hs]
    · exact (χ.analyticAt_LFunction (.inr hχ)).meromorphicAt
  · exact (χ.analyticAt_LFunction (.inl hz)).meromorphicAt

end DirichletCharacter

namespace TauCeti

open DirichletCharacter

/-- The principal Dirichlet `L`-function modulo `N` has a simple pole (meromorphic order `-1`) at
`s = 1`. -/
@[simp]
theorem meromorphicOrderAt_LFunctionTrivChar_one {N : ℕ} [NeZero N] :
    meromorphicOrderAt (LFunctionTrivChar N) 1 = -1 := by
  simpa using ((1 : DirichletCharacter ℂ N).meromorphic_LFunction 1)
    |>.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul (LFunctionTrivChar₁_apply_one_ne_zero N)
    (by simpa using LFunctionTrivChar_residue_one (N := N))

/-- The principal Dirichlet `L`-function modulo `N` is not differentiable at its simple pole
`s = 1`. -/
theorem not_differentiableAt_LFunctionTrivChar_one {N : ℕ} [NeZero N] :
    ¬ DifferentiableAt ℂ (LFunctionTrivChar N) 1 := by
  intro hd
  have hnonneg : 0 ≤ meromorphicOrderAt (LFunctionTrivChar N) 1 :=
    Filter.BoundedAtFilter.meromorphicOrderAt_nonneg
      ((hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ)
  rw [meromorphicOrderAt_LFunctionTrivChar_one] at hnonneg
  exact not_lt_of_ge hnonneg (by simpa using WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0))

end TauCeti

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- The continued Dirichlet `L`-function `χ.LFunction` is differentiable at `s` if and only if
`s ≠ 1` or `χ ≠ 1`. -/
@[simp]
theorem differentiableAt_LFunction_iff (s : ℂ) :
    DifferentiableAt ℂ χ.LFunction s ↔ s ≠ 1 ∨ χ ≠ 1 := by
  refine ⟨fun hd ↦ by_contra fun h ↦ ?_, χ.differentiableAt_LFunction s⟩
  obtain ⟨hs1, hχ1⟩ := not_or.mp h
  rw [not_ne_iff.mp hs1, not_ne_iff.mp hχ1] at hd
  exact TauCeti.not_differentiableAt_LFunctionTrivChar_one hd

/-- The continued Dirichlet `L`-function `χ.LFunction` is analytic at `s` if and only if
`s ≠ 1` or `χ ≠ 1`. -/
@[simp]
theorem analyticAt_LFunction_iff (s : ℂ) :
    AnalyticAt ℂ χ.LFunction s ↔ s ≠ 1 ∨ χ ≠ 1 :=
  ⟨fun ha ↦ (χ.differentiableAt_LFunction_iff s).mp ha.differentiableAt, χ.analyticAt_LFunction⟩

/-- The continued Dirichlet `L`-function `χ.LFunction` has positive meromorphic order at `s` if and
only if `χ.LFunction s = 0` and `(s ≠ 1 ∨ χ ≠ 1)`. -/
@[simp]
theorem meromorphicOrderAt_LFunction_pos_iff {s : ℂ} :
    0 < meromorphicOrderAt χ.LFunction s ↔ χ.LFunction s = 0 ∧ (s ≠ 1 ∨ χ ≠ 1) := by
  by_cases hs : s = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := hs
    rw [← LFunctionTrivChar]
    simp
  · have hs' := not_and_or.mp hs
    simp [(χ.analyticAt_LFunction hs').meromorphicOrderAt_pos_iff_eq_zero, hs']

/-- Every zero of `χ.LFunction` away from the simple pole `(s = 1, χ = 1)` lies in `s.re < 1`. -/
theorem re_lt_one_of_LFunction_eq_zero {s : ℂ} (h1 : s ≠ 1 ∨ χ ≠ 1) (h : χ.LFunction s = 0) :
    s.re < 1 :=
  not_le.mp fun hs ↦ χ.LFunction_ne_zero_of_one_le_re h1.symm hs h

end DirichletCharacter
