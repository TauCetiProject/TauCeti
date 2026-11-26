/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
import TauCeti.Analysis.Contour.Residue.Noncancellation
import TauCeti.Analysis.LaplaceTransform.PoleComparison
import TauCeti.Analysis.Meromorphic.Order

/-!
# One-sided zero exclusion for a signed Dirichlet Riesz transform

A signed sum of Riesz transforms can lose poles by cancellation. When the subtracted
characters have no zeros on the real segment relevant to Landau's theorem, an eventual upper
bound on the real function giving the transform rules out poles of the signed sum. At a point
where the subtracted characters again have no zeros, the untwisted characters have no zeros
either. In the quadratic application one chooses the twist to avoid zeros on a box containing
both the real segment in the critical strip and the point to be tested.

This is the Landau step of `New.LFunction_ne_zero_of_primeRemainder_le` in lsernau/grh-lean
(`72fead1`, `grh/src/New/Reduction/Zeros/Criterion.lean`).
-/

public section

open Complex MeasureTheory Set TauCeti

namespace DirichletCharacter

private theorem re_trailingCoeff_sum_riesz_nonneg {q : ℕ} [NeZero q] {b : ℝ} (hb : 0 < b)
    (hp : meromorphicOrderAt
      (∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin ψ.LFunction) (b : ℂ) < 0) :
    0 ≤ (meromorphicTrailingCoeffAt
      (∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin ψ.LFunction) (b : ℂ)).re := by
  classical
  have hb₀ : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hb₁ : b < 1 := by
    by_contra! h
    exact hp.not_ge (Finset.analyticAt_sum _ fun ψ _ ↦
      ψ.analyticAt_rieszRemainderMellin_LFunction_of_one_le_re
        (by simpa using h)).meromorphicOrderAt_nonneg
  have hm (ψ : DirichletCharacter ℂ q) :
      MeromorphicAt (rieszRemainderMellin ψ.LFunction) (b : ℂ) :=
    (meromorphicNFOn_rieszRemainderMellin _).meromorphicOn _ (mem_univ _)
  have hlo := le_meromorphicOrderAt_sum (s := Finset.univ) (fun ψ _ ↦ hm ψ) (fun ψ _ ↦
    ψ.meromorphic_LFunction.neg_one_le_meromorphicOrderAt_rieszRemainderMellin hb₀)
  obtain ⟨n, hn⟩ := exists_meromorphicOrderAt_eq_neg_succ_of_lt_zero hp
  rw [hn] at hlo
  have hle : (-1 : ℤ) ≤ Int.negSucc n := WithTop.coe_le_coe.mp hlo
  have hn₀ : n = 0 := by omega
  have hsimp : meromorphicOrderAt
      (∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin ψ.LFunction) (b : ℂ) = -1 := by
    simpa [hn₀] using hn
  rw [← Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hsimp,
    Contour.residue_sum _ (fun ψ _ ↦ hm ψ), re_sum]
  refine Finset.sum_nonneg fun ψ _ ↦ ?_
  rw [ψ.residue_rieszRemainderMellin_LFunction hb₀, ← ofReal_natCast, ← ofReal_one,
    ← ofReal_sub, ← ofReal_mul, ← ofReal_div, ofReal_re]
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hb.le (sub_nonneg.mpr hb₁.le))

/-- Suppose the continued Laplace transform of `g` is the sum of the Riesz transforms at level
`q` minus the corresponding sum for the characters `ξ ψ`. If `g` is bounded above by
`C * exp (θ * u)` eventually, then `L(ρ, χ)` is nonzero for `Re ρ > θ`, away from the principal
pole. The subtracted characters need to be zero-free only at `ρ` and at the possible real Landau
poles with `θ < b ≤ A` and `b < 1`; the initial Laplace transform is given on `Re z > A`. -/
theorem LFunction_ne_zero_of_hasLaplace_sub_rieszRemainderMellin {q d : ℕ} [NeZero q] [NeZero d]
    (χ : DirichletCharacter ℂ q) (ξ : DirichletCharacter ℂ q → DirichletCharacter ℂ d)
    {g : ℝ → ℝ} {A θ C u₀ : ℝ} {ρ : ℂ} (hθ : 0 ≤ θ) (hρ : θ < ρ.re)
    (hreg : ρ ≠ 1 ∨ χ ≠ 1)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi u₀), g u ≤ C * Real.exp (θ * u))
    (hL : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z
      ((∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin ψ.LFunction z) -
        ∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin (ξ ψ).LFunction z))
    (hreal : ∀ b ∈ Ioc θ A, b < 1 → ∀ ψ, (ξ ψ).LFunction (b : ℂ) ≠ 0)
    (hξ : ρ.re < 1 → ∀ ψ, (ξ ψ).LFunction ρ ≠ 0) : χ.LFunction ρ ≠ 0 := by
  classical
  let F := ∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin ψ.LFunction
  let G := ∑ ψ : DirichletCharacter ℂ q, rieszRemainderMellin (ξ ψ).LFunction
  have hm {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) :
      Meromorphic (rieszRemainderMellin ψ.LFunction) :=
    meromorphicOn_univ.mp (meromorphicNFOn_rieszRemainderMellin _).meromorphicOn
  have hF : Meromorphic F := Meromorphic.sum fun ψ _ ↦ hm ψ
  have hG : Meromorphic G := Meromorphic.sum fun ψ _ ↦ hm (ξ ψ)
  have hGord {z : ℂ} (hz : θ < z.re)
      (h : z.re < 1 → ∀ ψ, (ξ ψ).LFunction z ≠ 0) : 0 ≤ meromorphicOrderAt G z := by
    apply le_meromorphicOrderAt_sum (fun ψ _ ↦ hm (ξ ψ) z)
    intro ψ _
    rcases lt_or_ge z.re 1 with hz₁ | hz₁
    · have h₀ : z ≠ 0 := fun he ↦ by simp [he, not_lt.mpr hθ] at hz
      rw [← not_lt, (ξ ψ).meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff h₀,
        (ξ ψ).meromorphicOrderAt_LFunction_pos_iff]
      exact fun he ↦ h hz₁ ψ he.1
    · exact ((ξ ψ).analyticAt_rieszRemainderMellin_LFunction_of_one_le_re
        hz₁).meromorphicOrderAt_nonneg
  have hLap : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z ((F - G) z) := by
    simpa only [F, G, Pi.sub_apply, Finset.sum_apply] using hL
  have hFo := meromorphicOrderAt_nonneg_of_hasLaplace_sub_of_ae_le_exp hg
    hF.meromorphicOn hG.meromorphicOn hLap
    (fun b hb ↦ re_trailingCoeff_sum_riesz_nonneg (hθ.trans_lt hb.1))
    (fun b hb ↦ hGord (by simpa using hb.1) (fun h ↦ hreal b hb (by simpa using h)))
    hρ (hGord hρ hξ)
  have h₀ : ρ ≠ 0 := fun he ↦ by simp [he, not_lt.mpr hθ] at hρ
  have hnc := Contour.meromorphicOrderAt_sum_lt_zero_iff_of_pairwise_sameRay
    (s := Finset.univ) (f := fun ψ : DirichletCharacter ℂ q ↦ rieszRemainderMellin ψ.LFunction)
    (fun ψ _ ↦ hm ψ ρ) (fun ψ _ ↦
      ψ.meromorphic_LFunction.neg_one_le_meromorphicOrderAt_rieszRemainderMellin h₀)
    (fun ψ _ η _ _ ↦ by
      simp only [Function.onFun, residue_rieszRemainderMellin_LFunction _ h₀,
        div_eq_mul_inv, ← ofReal_natCast, ← Complex.real_smul]
      exact ((SameRay.refl _).nonneg_smul_left (Nat.cast_nonneg _)).nonneg_smul_right
        (Nat.cast_nonneg _))
  intro hz
  have hz' := χ.meromorphicOrderAt_LFunction_pos_iff.mpr ⟨hz, hreg⟩
  exact hFo.not_gt (hnc.mpr ⟨χ, Finset.mem_univ _,
    (χ.meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff h₀).mpr hz'⟩)

end DirichletCharacter
