/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Injectivity
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
  `(s - 1) ζ(s)` away from `1` and `1` at `1`; it is nonzero wherever `ζ` is, and away from `1`
  its analytic orders agree with `ζ`.
* `DirichletCharacter.entireLFunction`, with `DirichletCharacter.entireLFunction_one` and
  `DirichletCharacter.entireLFunction_of_ne_one`: the entire function `E_χ`, which is `χ.LFunction`
  for `χ ≠ 1` and `LFunctionTrivChar₁ N` for `χ = 1`.
* `DirichletCharacter.LFunctionTrivChar₁_eq_of_primeFactors_eq`: the pole-removed principal
  functions agree at levels with the same prime factors, including at `s = 1`.
* `DirichletCharacter.meromorphicOrderAt_LFunction_ne_top`,
  `DirichletCharacter.analyticOrderAt_LFunction_ne_top`,
  `DirichletCharacter.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt`,
  `DirichletCharacter.one_le_analyticOrderNatAt_LFunction_iff`, and
  `DirichletCharacter.meromorphicOrderAt_LFunction_eq_natCast_iff`: the orders of `χ.LFunction`
  are finite everywhere, away from the pole `(s = 1, χ = 1)` its meromorphic order is the cast of
  `analyticOrderNatAt`, the multiplicity in which zero sums over `χ.LFunction` are stated, and
  everywhere a positive meromorphic order `n` is the same as `analyticOrderNatAt` equal to `n`.
* `DirichletCharacter.re_lt_one_of_LFunction_eq_zero`: every zero of `χ.LFunction` away from the
  simple pole `(s = 1, χ = 1)` satisfies `s.re < 1`.
* `DirichletCharacter.eq_of_LFunction_eq`: a Dirichlet character is determined by its
  `L`-function on `Re s > 1`.

## References

* D. Loeffler, M. Stoll, `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
* M. Stoll, D. Loeffler, T. Tao, `Mathlib.NumberTheory.LSeries.Nonvanishing`.
* H. Davenport, *Multiplicative Number Theory*, Ch. 4.
* The function `E_χ` (`DirichletCharacter.entireLFunction`) follows the formal proof in the
  folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, where it enters `New.logDerivMean`.

The order lemmas are adapted, with the hypothesis `χ ≠ 1` weakened, from chrisflav's
file `LFunction/Order.lean` in
https://github.com/TauCetiProject/TauCeti/pull/45143
(feat: prove Layer 6 zero-free regions over Q).

The equal-prime-factor comparison for the pole-removed principal function is used in
`New.exists_regularL_eq_of_sq_eq_one` in `grh/src/Lib/Analytic/Primes.lean` of
https://github.com/lsernau/grh-lean (rev. `72fead1`).
-/

public section

open Complex Filter
open scoped Topology

namespace DirichletCharacter

/-- Away from `s = 1`, the pole-removed principal `L`-function is `(s - 1) L(s)`. -/
theorem LFunctionTrivChar₁_apply_of_ne_one (N : ℕ) [NeZero N] {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ N s = (s - 1) * LFunctionTrivChar N s :=
  Function.update_of_ne hs ..

/-- The entire pole-cleared L-functions of principal characters agree at levels with the same
prime factors, including their residue values at `1`. -/
theorem LFunctionTrivChar₁_eq_of_primeFactors_eq {M N : ℕ} [NeZero M] [NeZero N]
    (h : N.primeFactors = M.primeFactors) : LFunctionTrivChar₁ N = LFunctionTrivChar₁ M := by
  funext s
  rcases eq_or_ne s 1 with rfl | hs
  · simp only [LFunctionTrivChar₁, Function.update_self, h]
  · simp only [LFunctionTrivChar₁_apply_of_ne_one _ hs, LFunctionTrivChar_eq_mul_riemannZeta hs, h]

/-- Away from `s = 1`, Mathlib's pole-removed zeta function is `(s - 1) ζ(s)`. -/
theorem LFunctionTrivChar₁_one_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  simp [LFunctionTrivChar₁_apply_of_ne_one 1 hs]

/-- The pole-removed zeta function, `(s - 1) ζ(s)` away from `s = 1`, is nonzero wherever `ζ` is
nonzero. -/
theorem LFunctionTrivChar₁_one_ne_zero {s : ℂ} (hζ : riemannZeta s ≠ 0) :
    LFunctionTrivChar₁ 1 s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · exact LFunctionTrivChar₁_apply_one_ne_zero 1
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

/-- The **entire `L`-function** `E_χ` of a Dirichlet character `χ`: its `L`-function if `χ` is
not principal, and the entire continuation `DirichletCharacter.LFunctionTrivChar₁ N` of
`(s - 1) L(s, χ)` if it is. -/
noncomputable def entireLFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  open Classical in if χ = 1 then LFunctionTrivChar₁ N else χ.LFunction

/-- `E_χ` of the principal character is `DirichletCharacter.LFunctionTrivChar₁`. -/
@[simp]
theorem entireLFunction_one (N : ℕ) [NeZero N] :
    entireLFunction (1 : DirichletCharacter ℂ N) = LFunctionTrivChar₁ N := by
  simp [entireLFunction]

/-- `E_χ` of a non-principal character `χ` is its `L`-function. -/
theorem entireLFunction_of_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    entireLFunction χ = χ.LFunction := by
  simp [entireLFunction, hχ]

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

/-- The continued Dirichlet `L`-function `χ.LFunction` has finite meromorphic order at every
point: it is meromorphic on the connected set `ℂ` and nonzero at `s = 2`. -/
theorem meromorphicOrderAt_LFunction_ne_top (s : ℂ) : meromorphicOrderAt χ.LFunction s ≠ ⊤ := by
  have h2 : χ.LFunction 2 ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inr (by norm_num)) (by norm_num)
  have ha2 : AnalyticAt ℂ χ.LFunction 2 := χ.analyticAt_LFunction (.inl (by norm_num))
  refine (meromorphicOn_univ.mpr χ.meromorphic_LFunction)
    |>.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 2)
      (Set.mem_univ s) ?_
  rw [ha2.meromorphicOrderAt_eq, ha2.analyticOrderAt_eq_zero.mpr h2]
  simp

/-- The continued Dirichlet `L`-function `χ.LFunction` has finite analytic order at every point. At
the pole `(s = 1, χ = 1)` the analytic order is the junk value `0`. -/
theorem analyticOrderAt_LFunction_ne_top (s : ℂ) : analyticOrderAt χ.LFunction s ≠ ⊤ := by
  by_cases ha : AnalyticAt ℂ χ.LFunction s
  · simpa [ha.meromorphicOrderAt_eq] using χ.meromorphicOrderAt_LFunction_ne_top s
  · simp [ha]

/-- Away from the pole `(s = 1, χ = 1)`, the meromorphic order of `χ.LFunction` is the cast of its
natural analytic order. -/
theorem meromorphicOrderAt_LFunction_eq_analyticOrderNatAt {s : ℂ} (h1 : s ≠ 1 ∨ χ ≠ 1) :
    meromorphicOrderAt χ.LFunction s = (analyticOrderNatAt χ.LFunction s : ℤ) := by
  rw [(χ.analyticAt_LFunction h1).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (χ.analyticOrderAt_LFunction_ne_top s), ENat.map_natCast]

/-- The natural analytic order of `χ.LFunction` at `s` is at least `1` if and only if
`χ.LFunction s = 0` and `(s ≠ 1 ∨ χ ≠ 1)`. -/
theorem one_le_analyticOrderNatAt_LFunction_iff {s : ℂ} :
    1 ≤ analyticOrderNatAt χ.LFunction s ↔ χ.LFunction s = 0 ∧ (s ≠ 1 ∨ χ ≠ 1) := by
  rw [← meromorphicOrderAt_LFunction_pos_iff]
  by_cases h1 : s ≠ 1 ∨ χ ≠ 1
  · rw [χ.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt h1]
    norm_cast
  · obtain ⟨rfl, rfl⟩ := not_or.mp h1 |>.imp not_ne_iff.mp not_ne_iff.mp
    rw [← LFunctionTrivChar]
    simp

/-- For `n ≠ 0`, the meromorphic order of `χ.LFunction` at `s` is `n` if and only if its natural
analytic order at `s` is `n`. At the pole `(s = 1, χ = 1)` both sides are false, the orders being
`-1` and `0`. -/
theorem meromorphicOrderAt_LFunction_eq_natCast_iff {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    meromorphicOrderAt χ.LFunction s = n ↔ analyticOrderNatAt χ.LFunction s = n := by
  by_cases h1 : s ≠ 1 ∨ χ ≠ 1
  · rw [χ.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt h1]
    norm_cast
  · obtain ⟨rfl, rfl⟩ := not_or.mp h1 |>.imp not_ne_iff.mp not_ne_iff.mp
    rw [← LFunctionTrivChar, TauCeti.meromorphicOrderAt_LFunctionTrivChar_one]
    have h : ((-1 : ℤ) : WithTop ℤ) ≠ (n : ℤ) := WithTop.coe_injective.ne (by omega)
    simpa [hn.symm] using h

/-- Every zero of `χ.LFunction` away from the simple pole `(s = 1, χ = 1)` lies in `s.re < 1`. -/
theorem re_lt_one_of_LFunction_eq_zero {s : ℂ} (h1 : s ≠ 1 ∨ χ ≠ 1) (h : χ.LFunction s = 0) :
    s.re < 1 :=
  not_le.mp fun hs ↦ χ.LFunction_ne_zero_of_one_le_re h1.symm hs h

/-- The natural analytic order of a Dirichlet L-function vanishes throughout `1 ≤ re s`,
including at the principal character's pole, which is not counted as a zero. -/
@[simp] theorem analyticOrderNatAt_LFunction_eq_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    analyticOrderNatAt χ.LFunction s = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  obtain ⟨hz, hg⟩ := χ.one_le_analyticOrderNatAt_LFunction_iff.mp h
  exact (χ.re_lt_one_of_LFunction_eq_zero hg hz).not_ge hs

/-- **A Dirichlet character is determined by its `L`-function.** Two Dirichlet characters of the
same level whose `L`-functions agree on `Re s > 1` are equal, since a Dirichlet series determines
its coefficients. -/
theorem eq_of_LFunction_eq {ψ : DirichletCharacter ℂ N}
    (h : ∀ s : ℂ, 1 < s.re → χ.LFunction s = ψ.LFunction s) : χ = ψ := by
  have hcoef (n : ℕ) (hn : n ≠ 0) : χ n = ψ n := by
    refine LSeries.eq_of_LSeries_eventually_eq (f := fun n ↦ χ n) (g := fun n ↦ ψ n) ?_ ?_ ?_ hn
    · rw [abscissaOfAbsConv_eq_one (NeZero.ne N)]
      exact EReal.coe_lt_top 1
    · rw [abscissaOfAbsConv_eq_one (NeZero.ne N)]
      exact EReal.coe_lt_top 1
    · filter_upwards [eventually_gt_atTop 1] with x hx
      rw [← LFunction_eq_LSeries _ (by simpa using hx),
        ← LFunction_eq_LSeries _ (by simpa using hx), h _ (by simpa using hx)]
  refine MulChar.ext' fun a ↦ ?_
  have ha : ((a.val + N : ℕ) : ZMod N) = a := by simp
  rw [← ha]
  exact hcoef _ (by have := NeZero.pos N; omega)

end DirichletCharacter
