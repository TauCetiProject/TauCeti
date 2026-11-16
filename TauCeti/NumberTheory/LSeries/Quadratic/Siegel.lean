/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Data.Nat.GCD
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.ContourShift
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Sign

/-!
# Siegel's theorem for quadratic Dirichlet `L`-functions

For every `ε > 0` there exists a constant `c > 0` such that every primitive nonprincipal quadratic
Dirichlet character `χ` of conductor `q` satisfies

`c q ^ (-ε) ≤ Re L(1, χ)`.

Following Goldfeld's contour proof, we combine the four-factor residue lower bound
`DirichletCharacter.exists_pos_mul_rpow_le_LFunction_one_re_mul` with the logarithmic upper bound
`‖L(1, ρ)‖ ≤ 1 + log N` (`DirichletCharacter.norm_LFunction_one_le_one_add_log`), applied both to
an auxiliary character `χ₀` of conductor `M` and to the (generally imprimitive) product `χ₀.mul χ`
at level `lcm(M, q) ≤ M q`. Whenever `χ₀.mul χ ≠ 1` and the four-factor product
`ζ(β) L(β, χ₀) L(β, χ) L(β, χ₀.mul χ)` is nonpositive at some `β ∈ [3 / 4, 1)`, dividing out the
two factors other than `L(1, χ)` yields a lower bound for `L(1, χ)` in terms of `1 - β`, `M` and
`q`.

Given `ε > 0`, set `β₀ = max (3 / 4) (1 - ε / 16)`. Two cases exhaust all possibilities:
* **Zero-free alternative**: if no primitive nonprincipal quadratic character vanishes at a real
  point of `(β₀, 1)`, pairing `χ` with the Legendre character modulo `3` (and passing from
  `χ₀.mul χ` to its primitive character via `DirichletCharacter.LFunction_changeLevel_eq_zero_iff`
  when `χ₀.mul χ ≠ 1`) makes the four-factor product nonpositive at `β₀` by
  `DirichletCharacter.pair_nonpos_of_forall_ne_zero`.
* **Exceptional-zero comparison**: if some primitive nonprincipal quadratic character `χ₀` has a
  real zero `β ∈ (β₀, 1)`, the four-factor product vanishes at `β` for every `χ` with
  `χ₀.mul χ ≠ 1`, while the equal-character case `χ = χ₀`
  (`DirichletCharacter.IsPrimitive.mul_eq_one_iff`) is absorbed into the constant using
  `0 < L(1, χ₀)`.

Because the choice between these two cases is nonconstructive, the resulting constant `c` is
ineffective.

## Main results

* `DirichletCharacter.exists_pos_div_log_le_LFunction_one_re_of_pair_nonpos`: dividing the
  four-factor residue lower bound by the logarithmic upper bounds for `L(1, χ)` and
  `L(1, χ.mul ψ)` bounds `Re L(1, ψ)` from below when the four-factor product is nonpositive at `β`.
* `TauCeti.exists_pos_rpow_le_LFunction_one_re_of_forall_ne_zero`: the zero-free alternative on
  `(max (3 / 4) (1 - ε / 16), 1)` implies the uniform `q ^ (-ε)` lower bound.
* `TauCeti.exists_pos_rpow_le_LFunction_one_re_of_LFunction_eq_zero`: a real zero of a fixed
  primitive quadratic character in `[max (3 / 4) (1 - ε / 16), 1)` implies the uniform `q ^ (-ε)`
  lower bound for all primitive nonprincipal quadratic characters.
* `TauCeti.quadratic_LFunction_siegel`: Siegel's theorem `c q ^ (-ε) ≤ Re L(1, χ)` for primitive
  nonprincipal quadratic Dirichlet characters.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Complex
open scoped ComplexOrder

namespace DirichletCharacter

/-- **Two-character lower bound for `L(1, ψ)`.** There exists an absolute constant `c > 0` such
that if `χ` (level `M`) and `ψ` (level `N`) are nonprincipal quadratic characters with
`χ.mul ψ ≠ 1` and `ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ) ≤ 0` at `β ∈ [3 / 4, 1)`, then
`c (1 - β) (M N) ^ (-8 (1 - β)) / ((1 + log M) (1 + log (M N))) ≤ Re L(1, ψ)`. -/
theorem exists_pos_div_log_le_LFunction_one_re_of_pair_nonpos :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M N : ℕ} [NeZero M] [NeZero N]
        (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
        χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
        ∀ {β : ℝ}, β ∈ Set.Ico (3 / 4) 1 →
          riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β ≤ 0 →
          c * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) /
            ((1 + Real.log M) * (1 + Real.log ((M : ℝ) * N))) ≤ (ψ.LFunction 1).re := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_mul_rpow_le_LFunction_one_re_mul
  refine ⟨c, hc0, fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ hFβ ↦ ?_⟩
  have hres := hc χ ψ hχq hψq hχ hψ hχψ hβ hFβ
  have : NeZero (Nat.lcm M N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr NeZero.one_le
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hMN1 : (1 : ℝ) ≤ (M : ℝ) * N := by nlinarith
  have hlogM_pos : 0 < 1 + Real.log M := by linarith [Real.log_nonneg hM1]
  have hlogMN_pos : 0 < 1 + Real.log ((M : ℝ) * N) := by linarith [Real.log_nonneg hMN1]
  have hLψ_pos : 0 < (ψ.LFunction 1).re :=
    (Complex.pos_iff.mp (LFunction_apply_one_pos hψq hψ)).1
  have hLχ_le : (χ.LFunction 1).re ≤ 1 + Real.log M :=
    (Complex.re_le_norm _).trans (χ.norm_LFunction_one_le_one_add_log hχ)
  have hlcm_le : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_neZero M) (Nat.pos_of_neZero N))
      (Nat.lcm_dvd_mul M N)
  have hLχψ_le : ((χ.mul ψ).LFunction 1).re ≤ 1 + Real.log ((M : ℝ) * N) := by
    have h1 := (Complex.re_le_norm _).trans ((χ.mul ψ).norm_LFunction_one_le_one_add_log hχψ)
    have h2 := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_neZero (Nat.lcm M N))) hlcm_le
    linarith
  have hprod_le : (χ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re ≤
      (1 + Real.log M) * (1 + Real.log ((M : ℝ) * N)) :=
    mul_le_mul hLχ_le hLχψ_le
      (Complex.pos_iff.mp (LFunction_apply_one_pos (isQuadratic_mul hχq hψq) hχψ)).1.le
      hlogM_pos.le
  rw [div_le_iff₀ (mul_pos hlogM_pos hlogMN_pos)]
  calc c * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β))
      ≤ (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := hres
    _ = (ψ.LFunction 1).re * ((χ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re) := by ring
    _ ≤ (ψ.LFunction 1).re * ((1 + Real.log M) * (1 + Real.log ((M : ℝ) * N))) :=
        mul_le_mul_of_nonneg_left hprod_le hLψ_pos.le

end DirichletCharacter

namespace TauCeti

/-- Quantitative reduction for both branches of Siegel's theorem: if a fixed primitive nonprincipal
quadratic character `χ₀` of conductor `M` makes the four-factor product nonpositive at
`β ∈ [max (3 / 4) (1 - ε / 16), 1)` against every distinct primitive nonprincipal quadratic
character `χ`, then all primitive nonprincipal quadratic characters satisfy a uniform `q ^ (-ε)`
lower bound at `1` (including `χ₀` itself). -/
private theorem exists_pos_rpow_le_LFunction_one_re_of_forall_pair_nonpos
    {M : ℕ} [NeZero M] {χ₀ : DirichletCharacter ℂ M}
    (hχ₀p : χ₀.IsPrimitive) (hχ₀q : χ₀.IsQuadratic) (hχ₀1 : χ₀ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : β ∈ Set.Ico (max (3 / 4) (1 - ε / 16)) 1)
    (hpair : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 → χ₀.mul χ ≠ 1 →
      riemannZeta β * χ₀.LFunction β * χ.LFunction β * (χ₀.mul χ).LFunction β ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
      c * Real.rpow (q : ℝ) (-ε) ≤ (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨c₀, hc₀, hbound⟩ :=
    DirichletCharacter.exists_pos_div_log_le_LFunction_one_re_of_pair_nonpos
  have hβ_Ico : β ∈ Set.Ico (3 / 4) 1 := ⟨(le_max_left _ _).trans hβ.1, hβ.2⟩
  have h1β : 0 < 1 - β := sub_pos.mpr hβ.2
  have hexp : -ε / 2 ≤ -8 * (1 - β) := by
    linarith [(le_max_right (3 / 4) (1 - ε / 16)).trans hβ.1]
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr NeZero.one_le
  have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM1
  have hlogM : 0 < 1 + Real.log M := by linarith [Real.log_nonneg hM1]
  set K : ℝ := (1 + Real.log M) * ((1 + 1 / (ε / 2)) * (M : ℝ) ^ (ε / 2))
  have : 0 < K := by positivity
  set c₁ : ℝ := c₀ * (1 - β) * (M : ℝ) ^ (-8 * (1 - β)) / K
  have hLχ₀ : 0 < (χ₀.LFunction 1).re :=
    (Complex.pos_iff.mp (DirichletCharacter.LFunction_apply_one_pos hχ₀q hχ₀1)).1
  set c₂ : ℝ := (χ₀.LFunction 1).re * (M : ℝ) ^ ε
  refine ⟨min c₁ c₂, lt_min (by positivity) (by positivity), fun q _ χ hχp hχq hχ1 ↦ ?_⟩
  by_cases hmul : χ₀.mul χ = 1
  · obtain ⟨hMq, hχeq⟩ := (hχ₀p.mul_eq_one_iff hχp hχq).mp hmul
    subst hMq
    cases hχeq
    calc min c₁ c₂ * (M : ℝ) ^ (-ε)
        ≤ c₂ * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hM0.le _)
      _ = (χ₀.LFunction 1).re * ((M : ℝ) ^ ε * (M : ℝ) ^ (-ε)) := by simp only [c₂, mul_assoc]
      _ = (χ₀.LFunction 1).re := by
          rw [← Real.rpow_add hM0, add_neg_cancel, Real.rpow_zero, mul_one]
  · have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr NeZero.one_le
    have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
    have hnum : c₀ * (1 - β) * (M : ℝ) ^ (-8 * (1 - β)) * (q : ℝ) ^ (-ε / 2) ≤
        c₀ * (1 - β) * ((M : ℝ) * q) ^ (-8 * (1 - β)) := by
      rw [Real.mul_rpow hM0.le hq0.le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hexp) (by positivity)
    have hMq1 : (1 : ℝ) ≤ (M : ℝ) * q := by nlinarith
    have hden : (1 + Real.log M) * (1 + Real.log ((M : ℝ) * q)) ≤ K * (q : ℝ) ^ (ε / 2) := by
      have h1pow : 1 ≤ ((M : ℝ) * q) ^ (ε / 2) := Real.one_le_rpow hMq1 (half_pos hε).le
      have hlogpow : Real.log ((M : ℝ) * q) ≤ ((M : ℝ) * q) ^ (ε / 2) / (ε / 2) :=
        Real.log_le_rpow_div (zero_le_one.trans hMq1) (half_pos hε)
      have hsplit : (1 + 1 / (ε / 2)) * (((M : ℝ) * q) ^ (ε / 2)) =
          ((M : ℝ) * q) ^ (ε / 2) + ((M : ℝ) * q) ^ (ε / 2) / (ε / 2) := by ring
      have hlog : 1 + Real.log ((M : ℝ) * q) ≤
          (1 + 1 / (ε / 2)) * (((M : ℝ) * q) ^ (ε / 2)) := by linarith
      rw [Real.mul_rpow hM0.le hq0.le] at hlog
      have hring : K * (q : ℝ) ^ (ε / 2) =
          (1 + Real.log M) * ((1 + 1 / (ε / 2)) * ((M : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2))) := by
        simp only [K]; ring
      rw [hring]
      exact mul_le_mul_of_nonneg_left hlog hlogM.le
    have hden_pos : 0 < (1 + Real.log M) * (1 + Real.log ((M : ℝ) * q)) :=
      mul_pos hlogM (by linarith [Real.log_nonneg hMq1])
    calc min c₁ c₂ * (q : ℝ) ^ (-ε)
        ≤ c₁ * ((q : ℝ) ^ (-ε / 2) / (q : ℝ) ^ (ε / 2)) := by
          have hq_sub : (q : ℝ) ^ (-ε) = (q : ℝ) ^ (-ε / 2) / (q : ℝ) ^ (ε / 2) := by
            rw [← Real.rpow_sub hq0]; ring_nf
          rw [← hq_sub]
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hq0.le _)
      _ = c₀ * (1 - β) * (M : ℝ) ^ (-8 * (1 - β)) * (q : ℝ) ^ (-ε / 2) /
            (K * (q : ℝ) ^ (ε / 2)) := div_mul_div_comm _ _ _ _
      _ ≤ c₀ * (1 - β) * ((M : ℝ) * q) ^ (-8 * (1 - β)) /
            ((1 + Real.log M) * (1 + Real.log ((M : ℝ) * q))) :=
          div_le_div₀ (by positivity) hnum hden_pos hden
      _ ≤ (χ.LFunction 1).re :=
          hbound χ₀ χ hχ₀q hχq hχ₀1 hχ1 hmul hβ_Ico (hpair q χ hχp hχq hχ1 hmul)

/-- **Zero-free alternative in Siegel's theorem.** For `ε > 0`, if no primitive nonprincipal
quadratic character has a real zero in `(max (3 / 4) (1 - ε / 16), 1)`, then there exists `c > 0`
such that `c q ^ (-ε) ≤ Re L(1, χ)` for every primitive nonprincipal quadratic character `χ` of
conductor `q`. -/
theorem exists_pos_rpow_le_LFunction_one_re_of_forall_ne_zero {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ (r : ℕ) [NeZero r] (ρ : DirichletCharacter ℂ r),
      ρ.IsPrimitive → ρ.IsQuadratic → ρ ≠ 1 →
      ∀ σ ∈ Set.Ioo (max (3 / 4) (1 - ε / 16)) 1, ρ.LFunction σ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
      c * Real.rpow (q : ℝ) (-ε) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set χ₀ : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  have hχ₀q : χ₀.IsQuadratic := (quadraticChar_isQuadratic (ZMod 3)).comp (Int.castRingHom ℂ)
  have hχ₀1 : χ₀ ≠ 1 := DirichletCharacter.quadraticChar_ringHomComp_ne_one hR (by decide)
  have hχ₀p : χ₀.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    simpa only [DirichletCharacter.changeLevel_self] using
      DirichletCharacter.conductor_changeLevel_quadraticChar hR (by decide) (dvd_refl 3)
  set β : ℝ := max (3 / 4) (1 - ε / 16)
  have hβ1 : β < 1 := max_lt (by norm_num) (by linarith)
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (le_max_left _ _)
  refine exists_pos_rpow_le_LFunction_one_re_of_forall_pair_nonpos hχ₀p hχ₀q hχ₀1 hε
    ⟨le_rfl, hβ1⟩ fun q _ χ hχp hχq hχ1 hmul ↦ ?_
  refine DirichletCharacter.pair_nonpos_of_forall_ne_zero hχ₀q hχq hχ₀1 hχ1 hmul hβ0 hβ1
    fun σ hσ ↦ ⟨hzero 3 χ₀ hχ₀p hχ₀q hχ₀1 σ hσ, hzero q χ hχp hχq hχ1 σ hσ, ?_⟩
  have : NeZero (Nat.lcm 3 q) := ⟨Nat.lcm_ne_zero (by decide) (NeZero.ne q)⟩
  have : NeZero (χ₀.mul χ).conductor := ⟨DirichletCharacter.conductor_ne_zero (χ₀.mul χ)⟩
  set ρ := (χ₀.mul χ).primitiveCharacter
  have hρp : ρ.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive _
  have hρq : ρ.IsQuadratic := (DirichletCharacter.isQuadratic_mul hχ₀q hχq).primitiveCharacter
  have hρ1 : ρ ≠ 1 := fun h1 ↦ hmul <| DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
    ((hρp.eq_one_iff).mp h1)
  have hσ_re : 0 < (σ : ℂ).re := by simp only [ofReal_re]; exact hβ0.trans hσ.1
  have hσ_ne : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg re h
    simp only [ofReal_re, one_re] at this
    exact hσ.2.ne this
  rw [← (χ₀.mul χ).changeLevel_primitiveCharacter, ne_eq,
    DirichletCharacter.LFunction_changeLevel_eq_zero_iff ρ (χ₀.mul χ).conductor_dvd_level
      hσ_re (Or.inr hσ_ne)]
  exact hzero (χ₀.mul χ).conductor ρ hρp hρq hρ1 σ hσ

/-- **Exceptional-zero comparison in Siegel's theorem.** For `ε > 0`, if a primitive nonprincipal
quadratic character `χ₀` has a real zero `β ∈ [max (3 / 4) (1 - ε / 16), 1)`, then there exists
`c > 0` (depending on `χ₀`, `β` and `ε`) such that `c q ^ (-ε) ≤ Re L(1, χ)` for every primitive
nonprincipal quadratic character `χ` of conductor `q`. -/
theorem exists_pos_rpow_le_LFunction_one_re_of_LFunction_eq_zero
    {M : ℕ} [NeZero M] {χ₀ : DirichletCharacter ℂ M}
    (hχ₀p : χ₀.IsPrimitive) (hχ₀q : χ₀.IsQuadratic) (hχ₀1 : χ₀ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : β ∈ Set.Ico (max (3 / 4) (1 - ε / 16)) 1)
    (hLβ : χ₀.LFunction β = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
      c * Real.rpow (q : ℝ) (-ε) ≤ (DirichletCharacter.LFunction χ 1).re :=
  exists_pos_rpow_le_LFunction_one_re_of_forall_pair_nonpos hχ₀p hχ₀q hχ₀1 hε hβ
    fun _ _ _ _ _ _ _ ↦ by rw [hLβ, mul_zero, zero_mul, zero_mul]

/-- **Siegel's theorem for quadratic Dirichlet `L`-functions.** For every `ε > 0` there exists a
constant `c > 0` such that every primitive nonprincipal quadratic Dirichlet character `χ` of
conductor `q` satisfies `c q ^ (-ε) ≤ Re L(1, χ)`. -/
theorem quadratic_LFunction_siegel (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
      c * Real.rpow (q : ℝ) (-ε) ≤ (DirichletCharacter.LFunction χ 1).re := by
  by_cases h : ∃ (M : ℕ) (_ : NeZero M) (χ₀ : DirichletCharacter ℂ M),
      χ₀.IsPrimitive ∧ χ₀.IsQuadratic ∧ χ₀ ≠ 1 ∧
      ∃ β ∈ Set.Ioo (max (3 / 4) (1 - ε / 16)) 1, χ₀.LFunction β = 0
  · obtain ⟨M, hM, χ₀, hχ₀p, hχ₀q, hχ₀1, β, hβ, hLβ⟩ := h
    exact exists_pos_rpow_le_LFunction_one_re_of_LFunction_eq_zero hχ₀p hχ₀q hχ₀1 hε
      ⟨hβ.1.le, hβ.2⟩ hLβ
  · exact exists_pos_rpow_le_LFunction_one_re_of_forall_ne_zero hε
      fun r hr ρ hρp hρq hρ1 σ hσ h0 ↦ h ⟨r, hr, ρ, hρp, hρq, hρ1, σ, hσ, h0⟩

end TauCeti
