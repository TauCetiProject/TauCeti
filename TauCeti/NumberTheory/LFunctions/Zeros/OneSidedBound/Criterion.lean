/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Laplace
import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.CompensatedRiesz
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.OneSided

/-!
# One-sided zero exclusion for the signed prime remainder

The Laplace transform of the signed Legendre-weighted remainder is a difference of
ordinary Dirichlet Riesz transforms after shifting the Laplace parameter by one.
The one-sided Landau argument then rules out an untwisted zero by using twist
nonvanishing on a real interval and at the point being tested. A zero-free box
supplies both conditions.

The compensated mean and Laplace identification follow
`grh/src/New/Reduction/Zeros/PrimeError.lean`; the one-sided argument follows
`grh/src/New/Reduction/Zeros/Criterion.lean`, using Landau's theorem on Laplace transforms.
Both files are from [grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open Complex DirichletCharacter Filter MeasureTheory Set

namespace TauCeti.OneSidedBound

/-- After shifting the Laplace parameter by one and multiplying by `φ(q)`, the signed
prime remainder has transform equal to the difference of the untwisted and twisted
Dirichlet Riesz expressions. -/
theorem hasLaplace_totient_mul_exp_mul_primeRemainder (d q : ℕ) [Fact d.Prime] [NeZero q]
    (hd : d ≠ 2) (hc : q.Coprime d) {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun u : ℝ ↦ (((q.totient : ℝ) * Real.exp u *
      primeRemainder d q (Real.exp u) : ℝ) : ℂ)) s
      ((∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin ψ.LFunction s) -
        ∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin (ψ.legendreTwist d).LFunction s) := by
  classical
  let : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have h := ((hasLaplace_primeRemainder hd hc hs).cexp_mul_smul (w := 1)).fun_const_smul
    (q.totient : ℂ)
  simp only [one_mul, ofReal_mul, ofReal_natCast, ofReal_exp, smul_eq_mul, mul_assoc] at h ⊢
  convert h using 1
  have hq : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hnonprincipal (ψ : DirichletCharacter ℂ q) : ψ.legendreTwist d ≠ 1 :=
    legendreTwist_ne_one ψ d hd hc
  have H := sum_sub_rieszRemainderMellin_eq_compensated_mean (fun ψ ↦ ψ.legendreTwist d)
    hnonprincipal hs
  rw [mul_comm ((q.totient : ℂ)), ← div_eq_iff hq,
    logDerivMean_eq_residueClassAux_add hnonprincipal s,
    logDerivMean_eq_residueClassAux_add hnonprincipal 1]
  simpa only [Finset.sum_sub_distrib] using H

/-- An eventual upper bound `R_q(y) ≤ y^(β - 1)` excludes a zero at `ρ` with `β < Re ρ`, provided
all the Legendre twists are nonzero on the real interval `(β, 1)` and, if `Re ρ < 1`, at `ρ`.
The value of a principal L-function at its pole is not asserted to be nonzero. -/
theorem _root_.DirichletCharacter.LFunction_ne_zero_of_primeRemainder_le
    {q d : ℕ} [NeZero q] [Fact d.Prime]
    (χ : DirichletCharacter ℂ q) (hd : d ≠ 2) (hc : q.Coprime d) {β : ℝ} {ρ : ℂ}
    (hβ : 0 ≤ β) (hρ : β < ρ.re) (hreg : ρ ≠ 1 ∨ χ ≠ 1)
    (hR : ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (β - 1))
    (hreal : ∀ b ∈ Ioo β 1,
      ∀ ψ : DirichletCharacter ℂ q, (ψ.legendreTwist d).LFunction (b : ℂ) ≠ 0)
    (htwist : ρ.re < 1 → ∀ ψ : DirichletCharacter ℂ q, (ψ.legendreTwist d).LFunction ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  let g := fun u : ℝ ↦ (q.totient : ℝ) * Real.exp u * primeRemainder d q (Real.exp u)
  have hg : ∀ᶠ u : ℝ in atTop, g u ≤ (q.totient : ℝ) * Real.exp (β * u) := by
    filter_upwards [Real.tendsto_exp_atTop.eventually hR] with u hu
    calc
      _ ≤ (q.totient : ℝ) * Real.exp u * Real.exp u ^ (β - 1) := by
        dsimp only [g]
        gcongr
      _ = _ := by rw [← Real.exp_mul, mul_assoc, ← Real.exp_add]; congr 2; ring
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp hg
  exact χ.LFunction_ne_zero_of_hasLaplace_sub_rieszRemainderMellin
    (fun ψ ↦ ψ.legendreTwist d) (A := 1) (u₀ := u₀) hβ hρ hreg
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ hu₀ u hu.le)
    (fun _ hs ↦ hasLaplace_totient_mul_exp_mul_primeRemainder d q hd hc hs)
    (fun b hb hb₁ ↦ hreal b ⟨hb.1, hb₁⟩) htwist

/-- A one-sided bound for the signed remainder gives zero exclusion at `ρ`, provided the
Legendre twists by the chosen odd prime have no zero with `β < Re z < 1` and
`|Im z| ≤ |Im ρ|`. -/
theorem LFunction_ne_zero_of_primeRemainder_le {q d : ℕ} [NeZero q] [Fact d.Prime]
    (hd : d ≠ 2) (hc : q.Coprime d) (χ : DirichletCharacter ℂ q) {β : ℝ} {ρ : ℂ}
    (hβ : 0 ≤ β) (hρ : β < ρ.re) (hreg : ρ ≠ 1 ∨ χ ≠ 1)
    (hR : ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (β - 1))
    (htwist : ∀ ψ : DirichletCharacter ℂ q, ∀ z : ℂ, β < z.re → z.re < 1 →
      |z.im| ≤ |ρ.im| → (ψ.legendreTwist d).LFunction z ≠ 0) : χ.LFunction ρ ≠ 0 :=
  χ.LFunction_ne_zero_of_primeRemainder_le hd hc hβ hρ hreg hR
    (fun b hb ψ ↦ htwist ψ b (by simpa using hb.1) (by simpa using hb.2) (by simp))
    (fun hρ₁ ψ ↦ htwist ψ ρ hρ hρ₁ le_rfl)

end TauCeti.OneSidedBound
