/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.LSeries.Quadratic.TailComparison

/-!
# Zero-density counting bridges for quadratic twists

Combines pointwise lower bounds on the joint Gaussian theta tail with mean-tail upper bounds
to bound the number of primes `d ≡ 7 (mod 8)` whose Legendre twists have large theta tails,
and reduces zero-density counts for all characters modulo `N` to their inducing primitive
characters.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically the counting
and primitive-reduction steps of `New.exists_card_zero_quadTwist_le` and
`New.zero_density_quadTwist` in `grh/src/Lib/Analytic/QuadraticTwist.lean`.
-/

public section

open Asymptotics Complex DirichletCharacter Filter Finset Real
open scoped Nat

namespace TauCeti

/-- Markov's inequality for Legendre-twist theta tails: if every prime `d ∈ S` (with `d ≤ X`
and `d ≡ 7 mod 8`) has joint theta tail at least `T ^ (2 * δ)`, while the sum of the
corresponding Jacobi-twisted tails over `[1, X]` is at most `C * T ^ (2 + δ)`, then
`#S ≤ C * T ^ (2 - δ)`. -/
theorem card_le_of_forall_le_thetaTailIntegral_legendreTwist {q X : ℕ}
    (χ : DirichletCharacter ℂ q) (j : Fin 2) {T δ C : ℝ} (hT : 0 < T) {S : Finset ℕ}
    (hle : ∀ d ∈ S, d ≤ X) (hprime : ∀ d ∈ S, d.Prime) (hmod : ∀ d ∈ S, d % 8 = 7)
    (hlow : ∀ d ∈ S, ∀ hd : d.Prime,
      have : Fact d.Prime := ⟨hd⟩
      T ^ (2 * δ) ≤ quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ.legendreTwist d n) T)
    (hsum : ∑ d ∈ Icc 1 X, quadraticTwistGaussianThetaTailIntegral j
      (fun n ↦ χ n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T ≤ C * T ^ (2 + δ)) :
    (S.card : ℝ) ≤ C * T ^ (2 - δ) := by
  refine le_of_mul_le_mul_right ?_ (rpow_pos_of_pos hT (2 * δ))
  have hcard : (S.card : ℝ) * T ^ (2 * δ) ≤
      ∑ d : S,
        have : Fact (d : ℕ).Prime := ⟨hprime d d.property⟩
        quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ.legendreTwist d n) T := by
    calc (S.card : ℝ) * T ^ (2 * δ)
        = ∑ _d : S, T ^ (2 * δ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun d _ ↦ hlow d d.property (hprime d d.property)
  calc (S.card : ℝ) * T ^ (2 * δ)
      ≤ ∑ d ∈ Icc 1 X, quadraticTwistGaussianThetaTailIntegral j
          (fun n ↦ χ n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T :=
        hcard.trans (χ.sum_quadraticTwistGaussianThetaTailIntegral_legendreTwist_le
          j T hle hprime hmod)
    _ ≤ C * T ^ (2 + δ) := hsum
    _ = C * T ^ (2 - δ) * T ^ (2 * δ) := by
        rw [mul_assoc, ← rpow_add hT]
        ring_nf

/-- Passing from an arbitrary character `χ` modulo `N` to its inducing primitive character `ψ`
preserves zeros of the Legendre twist `χ.legendreTwist d` off the imaginary axis `Re s = 0`
for every odd prime `d` coprime to `N`. -/
theorem primitiveCharacter_legendreTwist_LFunction_eq_zero {N d : ℕ} [NeZero N] [Fact d.Prime]
    [NeZero d] (χ : DirichletCharacter ℂ N) (hd : d ≠ 2) (hcop : N.Coprime d) {s : ℂ}
    (hs : s.re ≠ 0) (hzero : (χ.legendreTwist d).LFunction s = 0) :
    have : NeZero (χ.conductor * d) :=
      ⟨Nat.mul_ne_zero (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos N)).ne'
        (NeZero.ne d)⟩
    (χ.primitiveCharacter.legendreTwist d).LFunction s = 0 := by
  have hdvd : χ.conductor ∣ N := χ.conductor_dvd_level
  have hcop' : χ.conductor.Coprime d := hcop.of_dvd_left hdvd
  have hlevel : χ.legendreTwist d =
      changeLevel (Nat.mul_dvd_mul_right hdvd d) (χ.primitiveCharacter.legendreTwist d) := by
    conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
    exact legendreTwist_changeLevel hdvd χ.primitiveCharacter d
  rw [hlevel, LFunction_changeLevel _ _
    (.inl (χ.primitiveCharacter.legendreTwist_ne_one d hd hcop'))] at hzero
  exact (mul_eq_zero.mp hzero).resolve_right (prod_one_sub_mul_prime_cpow_ne_zero _ hs)

open scoped Classical in
/-- Reducing a bad-prime zero-density bound for all characters modulo `N` to the inducing
primitive characters: if each primitive character `ψ` inducing some `ξ` modulo `N` has
`O(T ^ (2 - δ))` bad primes `d ≡ 7 mod 8` with `M * d ≤ T²`, then at most `O(X ^ (1 - δ / 2))`
primes `d ≤ X` in the class `a` have a twist zero with `Re s ≥ β > 0` and `|Im s| ≤ H`. -/
theorem isBigO_card_legendreTwist_badPrimes_of_primitive {N : ℕ} [NeZero N] {β H δ : ℝ}
    (hβ : 0 < β) {a : ZMod N}
    (hclass : ∀ d : ℕ, d.Prime → (d : ZMod N) = a → d % 8 = 7 ∧ N.Coprime d)
    (hprim : ∀ ξ : DirichletCharacter ℂ N, ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
      (#((Finset.Ioc 0 ⌊T ^ 2⌋₊).filter fun d : ℕ ↦
          d % 8 = 7 ∧ ξ.conductor.Coprime d ∧ (ξ.conductor : ℝ) * d ≤ T ^ 2 ∧
          ∃ hd : d.Prime, have : Fact d.Prime := ⟨hd⟩
          have : NeZero (ξ.conductor * d) :=
            ⟨Nat.mul_ne_zero (Nat.pos_of_dvd_of_pos ξ.conductor_dvd_level (NeZero.pos N)).ne'
              hd.ne_zero⟩
          ∃ s : ℂ, β ≤ s.re ∧ |s.im| ≤ H ∧
            (ξ.primitiveCharacter.legendreTwist d).LFunction s = 0) : ℝ) ≤
        C * T ^ (2 - δ)) :
    (fun X : ℕ ↦ (#((Finset.Ioc 0 X).filter fun d : ℕ ↦
        (d : ZMod N) = a ∧ ∃ hd : d.Prime,
        have : Fact d.Prime := ⟨hd⟩; have : NeZero d := ⟨hd.ne_zero⟩
        ∃ (ξ : DirichletCharacter ℂ N) (s : ℂ),
          β ≤ s.re ∧ |s.im| ≤ H ∧ (ξ.legendreTwist d).LFunction s = 0) : ℝ)) =O[atTop]
      fun X : ℕ ↦ (X : ℝ) ^ (1 - δ / 2) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  choose C hC using hprim
  have hpos (ξ : DirichletCharacter ℂ N) : 0 < ξ.conductor :=
    Nat.pos_of_dvd_of_pos ξ.conductor_dvd_level (NeZero.pos N)
  let S (ξ : DirichletCharacter ℂ N) (T : ℝ) : Finset ℕ :=
    (Finset.Ioc 0 ⌊T ^ 2⌋₊).filter fun d : ℕ ↦
      d % 8 = 7 ∧ ξ.conductor.Coprime d ∧ (ξ.conductor : ℝ) * d ≤ T ^ 2 ∧
      ∃ hd : d.Prime, have : Fact d.Prime := ⟨hd⟩
      have : NeZero (ξ.conductor * d) := ⟨Nat.mul_ne_zero (hpos ξ).ne' hd.ne_zero⟩
      ∃ s : ℂ, β ≤ s.re ∧ |s.im| ≤ H ∧
        (ξ.primitiveCharacter.legendreTwist d).LFunction s = 0
  have htend : Tendsto (fun X : ℕ ↦ √((N : ℝ) * X)) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hN)
  refine .of_bound ((∑ ξ, C ξ) * (N : ℝ) ^ (1 - δ / 2)) ?_
  filter_upwards [htend.eventually (eventually_all.mpr hC)] with X hX
  set T : ℝ := √((N : ℝ) * X)
  have hT : T ^ 2 = (N : ℝ) * X := sq_sqrt (by positivity)
  have hpow : T ^ (2 - δ) = (N : ℝ) ^ (1 - δ / 2) * (X : ℝ) ^ (1 - δ / 2) := by
    rw [← mul_rpow hN.le X.cast_nonneg, ← hT, ← rpow_natCast_mul (sqrt_nonneg _),
      Nat.cast_ofNat, mul_one_sub, mul_div_cancel₀ δ two_ne_zero]
  have hsub : ((Finset.Ioc 0 X).filter fun d : ℕ ↦ (d : ZMod N) = a ∧ ∃ hd : d.Prime,
      have : Fact d.Prime := ⟨hd⟩; have : NeZero d := ⟨hd.ne_zero⟩
      ∃ (ξ : DirichletCharacter ℂ N) (s : ℂ),
        β ≤ s.re ∧ |s.im| ≤ H ∧ (ξ.legendreTwist d).LFunction s = 0) ⊆
      univ.biUnion (S · T) := by
    intro d hd
    obtain ⟨hmem, hda, hprime, ξ, s, hre, him, hzero⟩ := mem_filter.mp hd
    have : Fact d.Prime := ⟨hprime⟩; have : NeZero d := ⟨hprime.ne_zero⟩
    obtain ⟨h8, hcop⟩ := hclass d hprime hda
    have hcond : ξ.conductor * d ≤ N * X :=
      Nat.mul_le_mul (Nat.le_of_dvd (NeZero.pos N) ξ.conductor_dvd_level) (mem_Ioc.mp hmem).right
    have hd_floor : d ≤ ⌊T ^ 2⌋₊ := by
      rw [hT, ← Nat.cast_mul, Nat.floor_natCast]
      exact (Nat.le_mul_of_pos_left d (hpos ξ)).trans hcond
    exact mem_biUnion.mpr ⟨ξ, mem_univ ξ, mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hmem).left,
      hd_floor⟩, h8, hcop.of_dvd_left ξ.conductor_dvd_level,
      (by exact_mod_cast hcond : (ξ.conductor : ℝ) * d ≤ N * X).trans hT.ge, hprime, s, hre, him,
      primitiveCharacter_legendreTwist_LFunction_eq_zero ξ (by omega) hcop
        (hβ.trans_le hre).ne' hzero⟩⟩
  rw [Real.norm_natCast, norm_of_nonneg (by positivity), mul_assoc, ← hpow, sum_mul]
  exact ((by exact_mod_cast (card_le_card hsub).trans card_biUnion_le :
    (_ : ℝ) ≤ ∑ ξ, (#(S ξ T) : ℝ))).trans (sum_le_sum fun ξ _ ↦ hX ξ)

end TauCeti
