/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Conductor
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The signed prime remainder at modulus one

At modulus one the progression condition disappears. Multiplying the remainder by its cutoff
then gives the difference of the first Riesz remainders for zeta and the Legendre character.
The constant involves Euler's constant from the pole-removed zeta function and the logarithmic
derivative of the quadratic L-function at one. The comparison allows estimates and integral
transforms for the individual Riesz remainders to be applied to the signed prime sum.

The constant normalization follows `New.re_logDerivMean_one` in
`grh/src/New/Reduction/Zeros/PrimeError.lean` of lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open ArithmeticFunction DirichletCharacter

namespace TauCeti.OneSidedBound

variable (d : ℕ) [Fact d.Prime]

private theorem quadraticTwist_modOne :
    quadraticTwist d (1 : DirichletCharacter ℂ 1) =
      changeLevel (dvd_mul_left d 1) (jacobiChar ℂ d) := by
  rw [quadraticTwist_def, changeLevel_one, jacobiChar_eq_ringHomComp_quadraticChar]
  exact one_mul _

/-- In the progression of modulus one, the logarithmic derivative mean at `1` is
`L′(1, χ_d)/L(1, χ_d) - γ - 1`, where `χ_d` is the Legendre character of the odd prime `d`. -/
theorem logDerivMean_modOne_at_one (hd : d ≠ 2) :
    logDerivMean d 1 1 = logDeriv (jacobiChar ℂ d).LFunction 1 -
      (Real.eulerMascheroniConstant : ℂ) - 1 := by
  have : NeZero (1 * d) := ⟨by simp [(Fact.out : d.Prime).ne_zero]⟩
  have hχ : jacobiChar ℂ d ≠ 1 := by
    rw [jacobiChar_eq_ringHomComp_quadraticChar]
    exact quadraticChar_ringHomComp_ne_one (by simp [ringChar.eq_zero]) hd
  have hdiv : d ∣ 1 * d := dvd_mul_left d 1
  have hL : (changeLevel hdiv (jacobiChar ℂ d)).LFunction = (jacobiChar ℂ d).LFunction := by
    funext s
    rw [LFunction_changeLevel hdiv _ (.inl hχ), Finset.prod_eq_one, mul_one]
    intro p hp
    have hp' : p = d := by simpa [one_mul, (Fact.out : d.Prime).primeFactors] using hp
    rw [hp', ZMod.natCast_self, MulChar.map_zero, zero_mul, sub_zero]
  rw [logDerivMean_def, Fintype.sum_unique, Unique.default_eq (1 : DirichletCharacter ℂ 1),
    quadraticTwist_modOne, entireLFunction_of_ne_one (fun h ↦
      hχ ((changeLevel_eq_one_iff hdiv).mp h)), entireLFunction_one, hL,
    logDeriv_LFunctionTrivChar₁_one_one]
  simp

private theorem rieszSum_primeWeight_modOne (y : ℝ) :
    rieszSum (fun n ↦ (primeWeight d 1 n : ℂ)) y =
      rieszSum (fun n ↦ (Λ n : ℂ)) y -
        rieszSum (fun n ↦ (jacobiChar ℂ d) n * (Λ n : ℂ)) y := by
  simp only [rieszSum_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp only [primeWeight_def, hn, ite_true, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_intCast, jacobiChar_natCast,
    ← jacobiSym.legendreSym.to_jacobiSym]
  ring

/-- The signed remainder at modulus `1`, multiplied by the cutoff, is the untwisted first
Riesz remainder minus that of the Legendre character. This includes the endpoint `y = 1`. -/
theorem mul_primeRemainder_one_eq_rieszRemainder_sub (hd : d ≠ 2) (y : ℝ) :
    ((y * primeRemainder d 1 y : ℝ) : ℂ) =
      (1 : PrimitiveDirichletCharacter).rieszRemainder y -
        (PrimitiveDirichletCharacter.of (jacobiChar ℂ d)).rieszRemainder y := by
  have hp : d.Prime := Fact.out
  have hprim : (jacobiChar ℂ d).IsPrimitive :=
    isPrimitive_jacobiChar_of_odd_squarefree (by norm_num) (hp.odd_of_ne_two hd) hp.squarefree
  -- Bundle the primitive character at its original level, so its projections compute directly.
  let ψ : PrimitiveDirichletCharacter := ⟨⟨d, hp.pos⟩, jacobiChar ℂ d, hprim⟩
  have hof : PrimitiveDirichletCharacter.of (jacobiChar ℂ d) = ψ :=
    PrimitiveDirichletCharacter.of_character ψ
  have hψ : ψ ≠ 1 := by
    intro h
    exact hp.ne_one (by simpa [ψ] using congrArg (fun χ ↦ (χ.level : ℕ)) h)
  have hcoeff (n : ℕ) : ψ.character n = jacobiChar ℂ d n := rfl
  have hL : ψ.character.LFunction = (jacobiChar ℂ d).LFunction := rfl
  have hlog : ((logDeriv (jacobiChar ℂ d).LFunction 1).re : ℂ) =
      logDeriv (jacobiChar ℂ d).LFunction 1 := by
    have h := (jacobiChar ℂ d).logDeriv_LFunction_inv_conj 1
    rw [jacobiChar_isQuadratic.inv, map_one] at h
    exact Complex.conj_eq_iff_re.mp h.symm
  have hR : (y : ℂ) * (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      (primeWeight d 1 n : ℂ) * (1 / (n : ℂ) - 1 / (y : ℂ))) =
        rieszSum (fun n ↦ (primeWeight d 1 n : ℂ)) y := by
    rcases le_or_gt y 0 with hy | hy
    · simp [rieszSum_def, Nat.floor_of_nonpos hy]
    · rw [rieszSum_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
      field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
  rw [hof, PrimitiveDirichletCharacter.rieszRemainder_one,
    PrimitiveDirichletCharacter.rieszRemainder_of_ne_one hψ, hL,
    primeRemainder_def, logDerivMean_modOne_at_one d hd]
  simp only [hcoeff, Nat.totient_one, Nat.cast_one, div_one, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
    Complex.sub_re, Complex.ofReal_re, Complex.one_re, hlog]
  rw [mul_sub, mul_sub, hR, rieszSum_primeWeight_modOne]
  ring

/-- In logarithmic coordinates, the modulus-one prime remainder times its cutoff has the
difference of the untwisted and quadratic Riesz transforms on `Re s > 1`. -/
theorem hasLaplace_exp_mul_primeRemainder_one (hd : d ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun u ↦ ((Real.exp u * primeRemainder d 1 (Real.exp u) : ℝ) : ℂ)) s
      (rieszRemainderMellin riemannZeta s -
        rieszRemainderMellin (jacobiChar ℂ d).LFunction s) := by
  have h := ((1 : PrimitiveDirichletCharacter).hasLaplace_rieszRemainder_comp_exp hs).sub
    ((PrimitiveDirichletCharacter.of (jacobiChar ℂ d)).hasLaplace_rieszRemainder_comp_exp hs)
  have hzeta : (1 : PrimitiveDirichletCharacter).character.LFunction = riemannZeta := by
    rw [PrimitiveDirichletCharacter.character_one]
    exact LFunction_modOne_eq
  have hp : d.Prime := Fact.out
  have hprim : (jacobiChar ℂ d).IsPrimitive :=
    isPrimitive_jacobiChar_of_odd_squarefree (by norm_num) (hp.odd_of_ne_two hd) hp.squarefree
  let ψ : PrimitiveDirichletCharacter := ⟨⟨d, hp.pos⟩, jacobiChar ℂ d, hprim⟩
  have hof : PrimitiveDirichletCharacter.of (jacobiChar ℂ d) = ψ :=
    PrimitiveDirichletCharacter.of_character ψ
  have h := h.congr_ae (Filter.Eventually.of_forall fun u ↦
    (mul_primeRemainder_one_eq_rieszRemainder_sub d hd (Real.exp u)).symm)
  rwa [hzeta, hof] at h

end TauCeti.OneSidedBound
