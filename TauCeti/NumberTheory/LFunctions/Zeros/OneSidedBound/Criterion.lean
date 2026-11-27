/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Laplace
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.CompensatedRiesz
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.OneSided

/-!
# Zero exclusion from the signed prime remainder

Multiplying `R_q(exp u)` by `φ(q) exp u` gives a Laplace transform that is a signed sum of
Dirichlet Riesz transforms. If the quadratic twists have no zeros in a box, the one-sided
Landau argument turns an eventual upper bound on `R_q` into nonvanishing of the untwisted
L-functions in that box. The prime specifying the twist is fixed throughout.

This is the analytic step of `New.LFunction_ne_zero_of_primeRemainder_le` in
`grh/src/New/Reduction/Zeros/Criterion.lean` of lsernau/grh-lean (`72fead1`), based on Landau's
theorem for Laplace transforms of functions of one sign.
-/

public section

open ArithmeticFunction.vonMangoldt Complex DirichletCharacter Filter MeasureTheory Set

namespace TauCeti.OneSidedBound

variable {d q : ℕ} [Fact d.Prime] [NeZero q]

private theorem logDerivMean_eq_residueClassAux (hd : d ≠ 2) (hc : q.Coprime d) (s : ℂ) :
    logDerivMean d q s = LFunctionResidueClassAux (1 : ZMod q) s +
      (∑ ψ : DirichletCharacter ℂ q, logDeriv (ψ.legendreTwist d).LFunction s) /
        (q.totient : ℂ) - (q.totient : ℂ)⁻¹ := by
  classical
  let ψ₀ : DirichletCharacter ℂ q := 1
  have hsplit := Finset.sum_compl_add_sum ({ψ₀} : Finset (DirichletCharacter ℂ q))
    (fun ψ ↦ logDeriv ψ.entireLFunction s)
  simp only [Finset.sum_singleton] at hsplit
  rw [logDerivMean_def, Finset.sum_sub_distrib, ← hsplit]
  have hsum : (∑ ψ ∈ ({ψ₀}ᶜ : Finset (DirichletCharacter ℂ q)), logDeriv ψ.entireLFunction s) =
      ∑ ψ ∈ ({ψ₀}ᶜ : Finset (DirichletCharacter ℂ q)), logDeriv ψ.LFunction s := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    rw [entireLFunction_of_ne_one (by simpa [ψ₀] using hψ)]
  rw [hsum]
  simp only [quadraticTwist_eq_legendreTwist,
    entireLFunction_of_ne_one (legendreTwist_ne_one _ d hd hc), ψ₀, entireLFunction_one,
    LFunctionResidueClassAux, ZMod.inv_one, MulChar.map_one, one_mul, logDeriv_apply,
    div_eq_mul_inv]
  ring

/-- The Laplace transform of the prime remainder multiplied by `φ(q) exp u` is the sum of the
untwisted Riesz transforms minus the sum of their quadratic twists, on `Re s > 1`. -/
theorem hasLaplace_totient_mul_exp_mul_primeRemainder (hd : d ≠ 2) (hc : q.Coprime d) {s : ℂ}
    (hs : 1 < s.re) :
    HasLaplace (fun u ↦ ((q.totient * (Real.exp u * primeRemainder d q (Real.exp u)) : ℝ) : ℂ)) s
      ((∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin ψ.LFunction s) -
        ∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin (ψ.legendreTwist d).LFunction s) := by
  have ht := hasLaplace_primeRemainder hd hc hs
  have hshift := ht.cexp_mul_smul (w := 1)
  simp only [one_mul] at hshift
  have hsum := sum_sub_rieszRemainderMellin_eq_compensated_mean (fun ψ ↦ ψ.legendreTwist d)
    (fun ψ ↦ legendreTwist_ne_one ψ d hd hc) hs
  simp only [← logDerivMean_eq_residueClassAux hd hc, Finset.sum_sub_distrib] at hsum
  have hq : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [← hsum] at hshift
  have hscaled := hshift.const_smul (q.totient : ℂ)
  simp only [smul_eq_mul, mul_div_cancel₀ _ hq] at hscaled
  refine hscaled.congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, ofReal_exp, ofReal_mul, ofReal_natCast]

/-- An eventual upper bound `R_q(y) ≤ y^(β - 1)` excludes a zero at `ρ` with `β < Re ρ`, provided
all the quadratic twists are nonzero on the real interval `(β, 1)` and, if `Re ρ < 1`, at `ρ`.
A zero-free box through height `|Im ρ|` supplies both conditions. The value of a principal
L-function at its pole is not asserted to be nonzero. -/
theorem _root_.DirichletCharacter.LFunction_ne_zero_of_primeRemainder_le
    (χ : DirichletCharacter ℂ q) (hd : d ≠ 2) (hc : q.Coprime d) {β : ℝ} {ρ : ℂ}
    (hβ : 0 ≤ β) (hρ : β < ρ.re) (hreg : ρ ≠ 1 ∨ χ ≠ 1)
    (hR : ∀ᶠ y in atTop, primeRemainder d q y ≤ y ^ (β - 1))
    (hreal : ∀ b ∈ Ioo β 1,
      ∀ ψ : DirichletCharacter ℂ q, (ψ.legendreTwist d).LFunction (b : ℂ) ≠ 0)
    (htwist : ρ.re < 1 → ∀ ψ : DirichletCharacter ℂ q, (ψ.legendreTwist d).LFunction ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let g : ℝ → ℝ := fun u ↦ q.totient * (Real.exp u * primeRemainder d q (Real.exp u))
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (Real.tendsto_exp_atTop.eventually hR)
  have hg : ∀ᵐ u ∂volume.restrict (Ioi u₀), g u ≤ q.totient * Real.exp (β * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hbound := hu₀ u (mem_Ioi.mp hu).le
    dsimp only [g]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc
      Real.exp u * primeRemainder d q (Real.exp u) ≤ Real.exp u * (Real.exp u) ^ (β - 1) :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_pos u).le
      _ = Real.exp (β * u) := by rw [← Real.exp_mul, ← Real.exp_add]; congr 1; ring
  exact χ.LFunction_ne_zero_of_hasLaplace_sub_rieszRemainderMellin (fun ψ ↦ ψ.legendreTwist d)
    hβ hρ hreg hg (fun _ hz ↦ hasLaplace_totient_mul_exp_mul_primeRemainder hd hc hz)
    (fun b hb hb₁ ↦ hreal b ⟨hb.1, hb₁⟩) htwist

end TauCeti.OneSidedBound
