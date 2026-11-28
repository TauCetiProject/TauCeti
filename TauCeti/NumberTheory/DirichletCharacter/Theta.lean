/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.LSeries.GaussianTheta
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic

/-!
# Change of level for Dirichlet theta integrals

Raising the level by a prime deletes its multiples from the positive-index theta series.
These multiples form a dilated copy of the original series. The corresponding change in the
Mellin transform gives the deleted Euler factor and preserves absolute convergence. Iterating
this argument transports the absolutely convergent Mellin representation from the inducing
character to the induced character, without using a functional equation at the higher level.

The Mellin representation has the normalization of `New.hasMellin_thetaSeries_char` in
`grh/src/Lib/Analytic/DirichletTheta.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Complex Set TauCeti

namespace DirichletCharacter

/-- At positive arguments, raising the level from `M` to `M * p` subtracts the dilated theta
sum for the multiples of `p`. If `p` divides `M`, the scalar `χ p` is already zero. -/
theorem gaussianDirichletTheta_changeLevel_mul_prime {M p : ℕ} (χ : DirichletCharacter ℂ M)
    (hp : p.Prime) (j : ℕ) :
    EqOn (gaussianDirichletTheta j (fun n ↦ (χ.changeLevel (dvd_mul_right M p)) n))
      (fun t ↦ gaussianDirichletTheta j (fun n ↦ χ n) t -
        χ p * gaussianDirichletTheta j (fun n ↦ χ n) ((p : ℝ) * t)) (Ioi 0) := by
  classical
  intro t ht
  let a (n : ℕ) := χ (n + 1 : ℕ) *
    ((((n + 1 : ℕ) : ℝ) * t) ^ j * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) * t) ^ 2) : ℝ)
  let D : Set ℕ := {n | p ∣ n + 1}
  let f (k : ℕ) := p * (k + 1) - 1
  have hf (k : ℕ) : f k + 1 = p * (k + 1) := by
    dsimp [f]
    exact Nat.sub_add_cancel (Nat.mul_pos hp.pos (by omega : 0 < k + 1))
  have hinj : Function.Injective f := by
    intro k l h
    have he : p * (k + 1) = p * (l + 1) := by rw [← hf, ← hf, h]
    exact Nat.succ.inj (Nat.mul_left_cancel hp.pos he)
  have hrange : Set.range f = D := by
    ext n
    constructor
    · rintro ⟨k, rfl⟩
      simpa only [D, mem_ofPred_eq, hf] using dvd_mul_right p (k + 1)
    · rintro ⟨k, hk⟩
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hk : k ≠ 0)
      exact ⟨l, Nat.succ.inj ((hf l).trans hk.symm)⟩
  have ha : Summable a := (summable_norm_gaussianDirichletTheta j
    (a := fun n ↦ χ n) (M := 1) (fun n _ ↦ χ.norm_le_one n) ht).of_norm
  have hcut (n : ℕ) : (χ.changeLevel (dvd_mul_right M p)) (n + 1 : ℕ) *
      ((((n + 1 : ℕ) : ℝ) * t) ^ j * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) * t) ^ 2) : ℝ) =
      a n - D.indicator a n := by
    rw [changeLevel_mul_prime_natCast hp, Set.indicator_apply]
    by_cases hn : p ∣ n + 1 <;> simp [D, a, hn]
  have hsum : ∑' n, D.indicator a n = ∑' k, a (f k) := by
    rw [← hinj.tsum_eq (f := D.indicator a) (by simpa only [hrange] using
      (support_indicator_subset : Function.support (D.indicator a) ⊆ D))]
    exact tsum_congr fun k ↦ indicator_of_mem (hrange ▸ mem_range_self k) _
  simp_rw [gaussianDirichletTheta_def]
  rw [tsum_congr hcut, ha.tsum_sub (ha.indicator D), hsum, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k ↦ ?_
  dsimp only [a]
  rw [hf k, Nat.cast_mul, map_mul, Nat.cast_mul, mul_assoc]
  have harg : (p : ℝ) * (↑(k + 1) : ℝ) * t = (↑(k + 1) : ℝ) * (p * t) := by ring
  rw [harg]

/-- Raising the level by a prime preserves Mellin convergence and multiplies the transform
by the deleted Euler factor. This holds at any frequency with absolute convergence, not just
where the ordinary Dirichlet series converges absolutely. -/
theorem hasMellin_gaussianDirichletTheta_changeLevel_mul_prime {M p : ℕ}
    (χ : DirichletCharacter ℂ M) (hp : p.Prime) (j : ℕ) {s m : ℂ}
    (h : HasMellin (gaussianDirichletTheta j (fun n ↦ χ n)) s m) :
    HasMellin (gaussianDirichletTheta j (fun n ↦ (χ.changeLevel (dvd_mul_right M p)) n)) s
      (m * (1 - χ p * p ^ (-s))) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hd := (MellinConvergent.comp_mul_left hpR).mpr h.1
  have hc := hasMellin_const_smul hd (χ (p : ZMod M))
  have hsub := hasMellin_sub h.1 hc.1
  rw [hc.2, mellin_comp_mul_left _ _ hpR, h.2] at hsub
  simp only [smul_eq_mul, Complex.ofReal_natCast] at hsub
  rw [← (by ring : m - χ p * ((p : ℂ) ^ (-s) * m) = m * (1 - χ p * p ^ (-s)))]
  exact (hasMellin_congr (χ.gaussianDirichletTheta_changeLevel_mul_prime hp j)).mpr hsub

/-- Raising the level from `M` to `N` preserves absolute convergence of the Dirichlet theta
integral. Its Mellin value changes by the same finite Euler product as the L-function.
Primes already dividing `M` contribute `1` to the product. -/
theorem hasMellin_gaussianDirichletTheta_changeLevel {M N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) (j : ℕ) {s m : ℂ}
    (h : HasMellin (gaussianDirichletTheta j (fun n ↦ χ n)) s m) :
    HasMellin (gaussianDirichletTheta j (fun n ↦ (χ.changeLevel hMN) n)) s
      (m * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) := by
  classical
  have hzero {r p : ℕ} (ξ : DirichletCharacter ℂ r) (hp : p ∈ r.primeFactors) : ξ p = 0 :=
    ξ.map_nonunit <| fun hu ↦
      ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp
        ((ZMod.isUnit_iff_coprime p r).mp hu)) (Nat.dvd_of_mem_primeFactors hp)
  have ⟨k, hk⟩ := hMN
  suffices ∀ k N : ℕ, N = M * k → N ≠ 0 → ∀ hd : M ∣ N,
      HasMellin (gaussianDirichletTheta j (fun n ↦ (χ.changeLevel hd) n)) s
        (m * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) from this k N hk (NeZero.ne N) hMN
  intro k
  induction k using induction_on_primes with
  | zero => simp
  | one =>
    intro n hn _ hd
    have he : n = M := by simpa using hn
    clear hn
    subst n
    have hprod : ∏ p ∈ M.primeFactors, (1 - χ p * p ^ (-s)) = 1 :=
      Finset.prod_eq_one fun p hp ↦ by simp [hzero χ hp]
    have he : χ.changeLevel hd = χ := changeLevel_self χ
    simpa only [he, hprod, mul_one] using h
  | prime_mul p k hp ih =>
    intro n hn hn₀ hd
    have he : n = M * k * p := hn.trans (by ac_rfl)
    clear hn
    subst n
    have hk₀ : M * k ≠ 0 := left_ne_zero_of_mul hn₀
    let ψ := χ.changeLevel (dvd_mul_right M k)
    have hψ := ih (M * k) rfl hk₀ (dvd_mul_right M k)
    have hchar : χ.changeLevel hd = ψ.changeLevel (dvd_mul_right (M * k) p) :=
      changeLevel_trans χ (dvd_mul_right M k) (dvd_mul_right (M * k) p)
    rw [hchar]
    have ht := ψ.hasMellin_gaussianDirichletTheta_changeLevel_mul_prime hp j hψ
    have hf : (M * k * p).primeFactors = insert p (M * k).primeFactors := by
      rw [Nat.primeFactors_mul hk₀ hp.ne_zero, hp.primeFactors, Finset.union_comm]
      simp
    rw [hf]
    by_cases hpk : p ∈ (M * k).primeFactors
    · rw [Finset.insert_eq_of_mem hpk]
      simpa only [hzero ψ hpk, zero_mul, sub_zero, mul_one] using ht
    · have hcop : p.Coprime (M * k) := hp.coprime_iff_not_dvd.mpr
        (fun hp' ↦ hpk (hp.mem_primeFactors hp' hk₀))
      rw [Finset.prod_insert hpk, ← mul_left_comm]
      simpa only [ψ, changeLevel_natCast_of_coprime _ _ hcop, mul_comm] using ht

end DirichletCharacter
