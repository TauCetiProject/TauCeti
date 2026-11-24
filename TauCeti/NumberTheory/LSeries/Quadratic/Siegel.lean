/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.SmoothedShift
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Primitive
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Sign

/-!
# Siegel's theorem on `L(1, χ)` for quadratic characters

For every `ε > 0` there is a constant `c > 0` such that `L(1, χ) ≥ c N ^ (-ε)` for every
nonprincipal quadratic Dirichlet character `χ` of level `N`
(`TauCeti.Multiquadratic.quadratic_LFunction_siegel`). For a primitive character the level is the
conductor, so this is Siegel's lower bound in its usual form; the level form also covers imprimitive
characters. The constant is ineffective: the proof does not say how to compute it.

We follow Goldfeld's proof. Let `χ` and `ψ` be nonprincipal quadratic characters with nonprincipal
product `χ.mul ψ`, and write `F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)`. The smoothed contour shift
of `TauCeti.NumberTheory.LSeries.Quadratic.Pair.SmoothedShift` shows that whenever `F(β) ≤ 0` at a
real `β < 1` close to `1`, the residue `L(1, χ) L(1, ψ) L(1, χ.mul ψ)` of `F` at `1` is at least a
constant multiple of `(1 - β) (M N) ^ (-8 (1 - β))`
(`DirichletCharacter.le_re_LFunction_one_mul_of_re_pair_nonpos`). The upper bounds
`L(1, χ) ≤ 1 + log M` and `L(1, χ.mul ψ) ≤ (1 + t⁻¹) (M N) ^ t`
(`DirichletCharacter.norm_LFunction_one_le_mul_rpow`, `t = 8 (1 - β)`) turn this into a lower bound
for `L(1, ψ)` (`DirichletCharacter.exists_pos_mul_rpow_le_LFunction_one_re_of_re_pair_nonpos`). The
sign condition `F(β) ≤ 0` holds in two situations:

* `χ` has a real zero at `β` (`exists_pos_mul_rpow_le_LFunction_one_re_of_LFunction_eq_zero`);
* no nonprincipal quadratic character has a real zero in `(β, 1)`, and then every factor of `F` is
  nonnegative on `[β, 1)` while `ζ(β) < 0`
  (`exists_pos_mul_rpow_le_LFunction_one_re_of_forall_LFunction_ne_zero`).

Siegel's theorem follows by choosing `β` close to `1` in terms of `ε` and applying whichever
alternative holds. In the first alternative the constant depends on the possible exceptional
character `χ`, which is the source of ineffectivity. Characters `ψ` with `χ.mul ψ = 1` induce the
same primitive character as `χ`, and are bounded using `L(1, χ.primitiveCharacter)` and the Euler
factors removed by raising the level.

## Main results

* `DirichletCharacter.le_re_LFunction_one_mul_of_re_pair_nonpos`: Goldfeld's lower bound for the
  residue `L(1, χ) L(1, ψ) L(1, χ.mul ψ)` when `F(β) ≤ 0`.
* `DirichletCharacter.exists_pos_mul_rpow_le_LFunction_one_re_of_LFunction_eq_zero`,
  `TauCeti.Multiquadratic.exists_pos_mul_rpow_le_LFunction_one_re_of_forall_LFunction_ne_zero`: the
  two alternatives, each giving `L(1, ψ) ≥ c N ^ (-16 (1 - β))` for every nonprincipal quadratic
  `ψ`.
* `TauCeti.Multiquadratic.quadratic_LFunction_siegel`: Siegel's theorem.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9.
-/

public section

open Complex
open scoped ComplexOrder

namespace DirichletCharacter

variable {M N : ℕ} [NeZero M] [NeZero N]

/-- The real-variable step of Goldfeld's argument: if `1 / 3 ≤ λ Γ(1 - β) x ^ (β - 1)` with `x > 0`
and `0 ≤ β < 1`, then `λ ≥ (1 - β) x ^ (1 - β) / 3`, because `(1 - β) Γ(1 - β) = Γ(2 - β) ≤ 1`. -/
private lemma one_sub_mul_rpow_div_three_le {lam x β : ℝ} (hx₀ : 0 < x) (hβ₀ : 0 ≤ β)
    (hβ₁ : β < 1) (h : 1 / 3 ≤ lam * Real.Gamma (1 - β) * x ^ (β - 1)) :
    (1 - β) * x ^ (1 - β) / 3 ≤ lam := by
  have hγ : 0 < 1 - β := by linarith
  have hy : 0 < x ^ (1 - β) := Real.rpow_pos_of_pos hx₀ _
  have hxx : x ^ (β - 1) * x ^ (1 - β) = 1 := by
    rw [← Real.rpow_add hx₀]
    simp
  have hres : (1 - β) * x ^ (1 - β) / 3 ≤ lam * ((1 - β) * Real.Gamma (1 - β)) := by
    calc (1 - β) * x ^ (1 - β) / 3 = (1 - β) * x ^ (1 - β) * (1 / 3) := by ring
      _ ≤ (1 - β) * x ^ (1 - β) * (lam * Real.Gamma (1 - β) * x ^ (β - 1)) :=
          mul_le_mul_of_nonneg_left h (mul_pos hγ hy).le
      _ = lam * ((1 - β) * Real.Gamma (1 - β)) * (x ^ (β - 1) * x ^ (1 - β)) := by ring
      _ = lam * ((1 - β) * Real.Gamma (1 - β)) := by rw [hxx, mul_one]
  have hg₀ : 0 < (1 - β) * Real.Gamma (1 - β) := mul_pos hγ (Real.Gamma_pos_of_pos hγ)
  have hlam₀ : 0 < lam := pos_of_mul_pos_left ((by positivity : (0 : ℝ) < _).trans_le hres) hg₀.le
  -- `(1 - β) Γ(1 - β) = Γ(2 - β) ≤ 1`.
  have hg₁ : (1 - β) * Real.Gamma (1 - β) ≤ 1 := by
    rw [← Real.Gamma_add_one hγ.ne']
    exact Real.Gamma_le_one_of_mem_Icc ⟨by linarith, by linarith⟩
  exact hres.trans (mul_le_of_le_one_right hlam₀.le hg₁)

/-- For the smoothing parameter `x = (6 · 300000 P ^ 2) ^ (-4)` and `3 / 4 ≤ β`, the factor
`x ^ (1 - β) = (1800000 P ^ 2) ^ (-4 (1 - β))` is at least `P ^ (-8 (1 - β)) / 1800000`. -/
private lemma inv_mul_rpow_le_rpow_one_sub {P β : ℝ} (hP : 1 ≤ P) (hβ₀ : 3 / 4 ≤ β) :
    (1800000 : ℝ)⁻¹ * P ^ (-(8 * (1 - β))) ≤
      ((6 * (300000 * P ^ 2)) ^ (-4 : ℝ)) ^ (1 - β) := by
  rw [← Real.rpow_mul (by positivity), ← mul_assoc, Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hc : (1800000 : ℝ)⁻¹ ≤ (6 * 300000 : ℝ) ^ (-4 * (1 - β)) := by
    rw [show (6 * 300000 : ℝ) = 1800000 by norm_num, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hP' : P ^ (-(8 * (1 - β))) = P ^ (((2 : ℕ) : ℝ) * (-4 * (1 - β))) := by
    congr 1
    push_cast
    ring
  rw [hP']
  gcongr

/-- **Goldfeld's lower bound for the residue.** Let `χ`, `ψ` be nonprincipal quadratic characters
of nonzero levels `M`, `N` with nonprincipal product `χ.mul ψ`, and let `3 / 4 ≤ β < 1`. If
`ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)` has nonpositive real part, then the residue
`L(1, χ) L(1, ψ) L(1, χ.mul ψ)` of this product at `1` has real part at least
`(1 - β) / 5400000 · (M N) ^ (-8 (1 - β))`. -/
theorem le_re_LFunction_one_mul_of_re_pair_nonpos {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1)
    (hψ₁ : ψ ≠ 1) (hχψ₁ : χ.mul ψ ≠ 1) {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β < 1)
    (hF : (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0) :
    (1 - β) / 5400000 * ((M : ℝ) * N) ^ (-(8 * (1 - β))) ≤
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re := by
  set P : ℝ := (M : ℝ) * N
  set lam : ℝ := (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le (by exact_mod_cast NeZero.one_le)
    (by exact_mod_cast NeZero.one_le)
  set A : ℝ := 300000 * P ^ 2 with hA_def
  have hA : 1 ≤ A := by nlinarith
  -- The smoothing parameter `x = (6 A) ^ (-4)` makes the shifted integral at most `1 / 6`.
  set x : ℝ := (6 * A) ^ (-4 : ℝ) with hx_def
  have hx₀ : 0 < x := by positivity
  have hx₁ : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hx₄ : x ^ (1 / 4 : ℝ) = (6 * A)⁻¹ := by
    rw [hx_def, ← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg_one]
  have hx₆ : x ≤ 1 / 6 := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁ (by norm_num)
      _ ≤ 1 / 6 := by
        rw [hx₄, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hexp : 1 / 2 ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have herr : 37500 * P ^ 2 / ((β - 1 / 2) * (3 / 2 - β)) * x ^ (β - 1 / 2) ≤ 1 / 6 := by
    have hD : 1 / 8 ≤ (β - 1 / 2) * (3 / 2 - β) := by nlinarith
    calc 37500 * P ^ 2 / ((β - 1 / 2) * (3 / 2 - β)) * x ^ (β - 1 / 2)
        ≤ A * x ^ (1 / 4 : ℝ) := by
          refine mul_le_mul ?_ (Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁ (by linarith))
            (by positivity) (by positivity)
          rw [div_le_iff₀ (by linarith), hA_def]
          nlinarith [sq_nonneg P]
      _ = 1 / 6 := by rw [hx₄]; field_simp
  have hG := exp_neg_le_re_pair_add_of_mul_ne_one hχ hψ hχ₁ hψ₁ hχψ₁ (by linarith)
    (by linarith) hβ₁.ne hx₀
  -- The contour inequality leaves the residue term `≥ 1 / 2 - 1 / 6`.
  have hmain : 1 / 3 ≤ lam * Real.Gamma (1 - β) * x ^ (β - 1) := by linarith
  have hlam := one_sub_mul_rpow_div_three_le hx₀ (by linarith) hβ₁ hmain
  calc (1 - β) / 5400000 * P ^ (-(8 * (1 - β)))
      = (1 - β) * ((1800000 : ℝ)⁻¹ * P ^ (-(8 * (1 - β)))) / 3 := by ring
    _ ≤ (1 - β) * x ^ (1 - β) / 3 := by
        gcongr
        exact inv_mul_rpow_le_rpow_one_sub hP hβ₀
    _ ≤ lam := hlam

/-- The case `χ.mul ψ ≠ 1` of the two-character comparison: dividing Goldfeld's residue bound by
`L(1, χ) ≤ 1 + log M` and `L(1, χ.mul ψ) ≤ (1 + t⁻¹) (M N) ^ t`, where `t = 8 (1 - β)`, bounds
`L(1, ψ)` from below. -/
private lemma mul_rpow_le_LFunction_one_re_of_mul_ne_one {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1)
    (hψ₁ : ψ ≠ 1) (hχψ₁ : χ.mul ψ ≠ 1) {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β < 1)
    (hF : (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0) :
    (1 - β) / 5400000 * (M : ℝ) ^ (-(16 * (1 - β))) /
        ((1 + Real.log M) * (1 + (8 * (1 - β))⁻¹)) * (N : ℝ) ^ (-(16 * (1 - β))) ≤
      (ψ.LFunction 1).re := by
  have : NeZero (M.lcm N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  have ht : 0 < 8 * (1 - β) := by linarith
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  set P : ℝ := (M : ℝ) * N
  have hPt : 0 < P ^ (8 * (1 - β)) := by positivity
  -- The three values at `1` are positive real numbers.
  obtain ⟨-, ha'⟩ := Complex.pos_iff.mp (LFunction_apply_one_pos hχ hχ₁)
  obtain ⟨hb, hb'⟩ := Complex.pos_iff.mp (LFunction_apply_one_pos hψ hψ₁)
  obtain ⟨hd, hd'⟩ := Complex.pos_iff.mp (LFunction_apply_one_pos (isQuadratic_mul hχ hψ) hχψ₁)
  have hprod : (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re =
      (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := by
    simp [Complex.mul_re, Complex.mul_im, ← ha', ← hb', ← hd']
  have haM : (χ.LFunction 1).re ≤ 1 + Real.log M :=
    (Complex.re_le_norm _).trans (norm_LFunction_one_le_one_add_log χ hχ₁)
  have hdP : ((χ.mul ψ).LFunction 1).re ≤ (1 + (8 * (1 - β))⁻¹) * P ^ (8 * (1 - β)) := by
    refine (Complex.re_le_norm _).trans ((norm_LFunction_one_le_mul_rpow _ hχψ₁ ht).trans ?_)
    gcongr
    rw [show P = ((M * N : ℕ) : ℝ) by push_cast; rfl]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.lcm_dvd_mul M N)
  have hLT : 0 < (1 + Real.log M) * (1 + (8 * (1 - β))⁻¹) := by
    have := Real.log_nonneg hM
    positivity
  have hkey : (1 - β) / 5400000 * P ^ (-(8 * (1 - β))) ≤
      (ψ.LFunction 1).re * ((1 + Real.log M) * (1 + (8 * (1 - β))⁻¹)) * P ^ (8 * (1 - β)) := by
    calc (1 - β) / 5400000 * P ^ (-(8 * (1 - β)))
        ≤ (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re :=
          hprod ▸ le_re_LFunction_one_mul_of_re_pair_nonpos hχ hψ hχ₁ hψ₁ hχψ₁ hβ₀ hβ₁ hF
      _ ≤ (1 + Real.log M) * (ψ.LFunction 1).re *
          ((1 + (8 * (1 - β))⁻¹) * P ^ (8 * (1 - β))) := by gcongr
      _ = _ := by ring
  have heq : (M : ℝ) ^ (-(16 * (1 - β))) * (N : ℝ) ^ (-(16 * (1 - β))) =
      P ^ (-(8 * (1 - β))) / P ^ (8 * (1 - β)) := by
    simp only [P]
    rw [← Real.mul_rpow (by positivity) (by positivity), div_eq_mul_inv,
      ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
    ring_nf
  calc (1 - β) / 5400000 * (M : ℝ) ^ (-(16 * (1 - β))) /
        ((1 + Real.log M) * (1 + (8 * (1 - β))⁻¹)) * (N : ℝ) ^ (-(16 * (1 - β)))
      = (1 - β) / 5400000 * P ^ (-(8 * (1 - β))) / P ^ (8 * (1 - β)) /
          ((1 + Real.log M) * (1 + (8 * (1 - β))⁻¹)) := by
        rw [mul_div_assoc ((1 - β) / 5400000) (P ^ (-(8 * (1 - β)))), ← heq]
        ring
    _ ≤ (ψ.LFunction 1).re := by
        rw [div_le_iff₀ hLT, div_le_iff₀ hPt]
        linarith

/-- **The two-character comparison.** Fix a nonprincipal quadratic character `χ` of nonzero level
`M` and `3 / 4 ≤ β < 1` such that `ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)` has nonpositive real part
for every nonprincipal quadratic character `ψ` with nonprincipal product `χ.mul ψ`. Then there is
`c > 0`, depending on `χ` and `β`, such that `c N ^ (-16 (1 - β)) ≤ Re L(1, ψ)` for every
nonprincipal quadratic character `ψ` of every nonzero level `N`. -/
theorem exists_pos_mul_rpow_le_LFunction_one_re_of_re_pair_nonpos {χ : DirichletCharacter ℂ M}
    (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β < 1)
    (hF : ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ.IsQuadratic → ψ ≠ 1 →
      χ.mul ψ ≠ 1 →
        (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ.IsQuadratic → ψ ≠ 1 →
      c * (N : ℝ) ^ (-(16 * (1 - β))) ≤ (ψ.LFunction 1).re := by
  have hγ : 0 < 1 - β := by linarith
  obtain ⟨A, hA, hcmp⟩ :=
    exists_norm_LFunction_changeLevel_le_rpow (δ := 1) (ε := 16 * (1 - β)) one_pos (by linarith)
  have hL : 0 < ‖χ.primitiveCharacter.LFunction 1‖ := norm_pos_iff.mpr
    (LFunction_apply_one_ne_zero (mt χ.primitiveCharacter_eq_one_iff.mp hχ₁))
  set c₁ : ℝ := (1 - β) / 5400000 * (M : ℝ) ^ (-(16 * (1 - β))) /
    ((1 + Real.log M) * (1 + (8 * (1 - β))⁻¹))
  have hc₁ : 0 < c₁ := by
    have := Real.log_nonneg (by exact_mod_cast NeZero.one_le : (1 : ℝ) ≤ M)
    have : 0 < (8 * (1 - β))⁻¹ := inv_pos.mpr (by linarith)
    exact div_pos (mul_pos (div_pos hγ (by norm_num))
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos M)) _)) (by positivity)
  refine ⟨min c₁ (‖χ.primitiveCharacter.LFunction 1‖ / A), lt_min hc₁ (div_pos hL hA),
    fun N _ ψ hψ hψ₁ ↦ ?_⟩
  by_cases hχψ : χ.mul ψ = 1
  · -- `ψ` induces the same primitive character as `χ`, and raising the level from the conductor
    -- of `ψ` to `N` changes `L(1, ψ)` by at most a factor `A N ^ (16 (1 - β))`.
    have heq : ψ.primitiveCharacter.LFunction 1 = χ.primitiveCharacter.LFunction 1 := by
      rw [LFunction_primitiveCharacter_eq_of_mul_eq_one hχψ, hψ.inv]
    have h := (hcmp _ _ ψ.primitiveCharacter ψ.conductor_dvd_level 1 (by simp)
      (.inl (mt ψ.primitiveCharacter_eq_one_iff.mp hψ₁))).2
    rw [changeLevel_primitiveCharacter, heq] at h
    have hNε : 0 < (N : ℝ) ^ (16 * (1 - β)) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos N)) _
    rw [Complex.re_eq_norm.mpr (LFunction_apply_one_pos hψ hψ₁).le]
    calc min c₁ (‖χ.primitiveCharacter.LFunction 1‖ / A) * (N : ℝ) ^ (-(16 * (1 - β)))
        ≤ ‖χ.primitiveCharacter.LFunction 1‖ / A * (N : ℝ) ^ (-(16 * (1 - β))) := by
          gcongr
          exact min_le_right _ _
      _ = ‖χ.primitiveCharacter.LFunction 1‖ / (A * (N : ℝ) ^ (16 * (1 - β))) := by
          rw [Real.rpow_neg (by positivity)]
          field_simp
      _ ≤ ‖ψ.LFunction 1‖ := by
          rw [div_le_iff₀ (by positivity)]
          linarith
  · calc min c₁ (‖χ.primitiveCharacter.LFunction 1‖ / A) * (N : ℝ) ^ (-(16 * (1 - β)))
        ≤ c₁ * (N : ℝ) ^ (-(16 * (1 - β))) := by
          gcongr
          exact min_le_left _ _
      _ ≤ (ψ.LFunction 1).re := mul_rpow_le_LFunction_one_re_of_mul_ne_one hχ hψ hχ₁ hψ₁ hχψ
          hβ₀ hβ₁ (hF N ψ hψ hψ₁ hχψ)

/-- **Siegel's alternative with an exceptional zero.** If a nonprincipal quadratic character `χ` of
nonzero level has a real zero `β` with `3 / 4 ≤ β < 1`, then there is `c > 0`, depending on `χ`
and `β`, such that `c N ^ (-16 (1 - β)) ≤ Re L(1, ψ)` for every nonprincipal quadratic character
`ψ` of every nonzero level `N`. -/
theorem exists_pos_mul_rpow_le_LFunction_one_re_of_LFunction_eq_zero {χ : DirichletCharacter ℂ M}
    (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {β : ℝ} (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β < 1)
    (hβ : χ.LFunction β = 0) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ.IsQuadratic → ψ ≠ 1 →
      c * (N : ℝ) ^ (-(16 * (1 - β))) ≤ (ψ.LFunction 1).re :=
  exists_pos_mul_rpow_le_LFunction_one_re_of_re_pair_nonpos hχ hχ₁ hβ₀ hβ₁
    fun _ _ _ _ _ _ ↦ by simp [hβ]

end DirichletCharacter

namespace TauCeti.Multiquadratic

open DirichletCharacter

/-- **Siegel's zero-free alternative.** If no nonprincipal quadratic character of any nonzero level
has a real zero in `(β, 1)`, where `3 / 4 ≤ β < 1`, then there is `c > 0` such that
`c N ^ (-16 (1 - β)) ≤ Re L(1, ψ)` for every nonprincipal quadratic character `ψ` of every nonzero
level `N`. -/
theorem exists_pos_mul_rpow_le_LFunction_one_re_of_forall_LFunction_ne_zero {β : ℝ}
    (hβ₀ : 3 / 4 ≤ β) (hβ₁ : β < 1)
    (h : ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ.IsQuadratic → χ ≠ 1 →
      ∀ σ ∈ Set.Ioo β 1, χ.LFunction σ ≠ 0) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), ψ.IsQuadratic → ψ ≠ 1 →
      c * (N : ℝ) ^ (-(16 * (1 - β))) ≤ (ψ.LFunction 1).re := by
  by_cases hex : ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter ℂ M), χ.IsQuadratic ∧ χ ≠ 1
  · obtain ⟨M, _, χ, hχ, hχ₁⟩ := hex
    refine exists_pos_mul_rpow_le_LFunction_one_re_of_re_pair_nonpos hχ hχ₁ hβ₀ hβ₁
      fun N _ ψ hψ hψ₁ hχψ₁ ↦ ?_
    have : NeZero (M.lcm N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
    exact (Complex.le_def.mp (pair_nonpos_of_forall_ne_zero hχ hψ hχ₁ hψ₁ hχψ₁ (by linarith) hβ₁
      fun σ hσ ↦ ⟨h M χ hχ hχ₁ σ hσ, h N ψ hψ hψ₁ σ hσ,
        h _ _ (isQuadratic_mul hχ hψ) hχψ₁ σ hσ⟩)).1
  · exact ⟨1, one_pos, fun N _ ψ hψ hψ₁ ↦ (hex ⟨N, inferInstance, ψ, hψ, hψ₁⟩).elim⟩

/-- **Siegel's theorem.** For every `ε > 0` there is `c > 0` such that `c N ^ (-ε) ≤ Re L(1, χ)`
for every nonprincipal quadratic Dirichlet character `χ` of every nonzero level `N`. For a
primitive character the level is its conductor `q`, giving Siegel's bound `L(1, χ) ≥ c q ^ (-ε)`.
The constant `c` is ineffective. -/
theorem quadratic_LFunction_siegel {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      c * (N : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  set δ : ℝ := min (ε / 16) (1 / 4)
  have hδ₀ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : 16 * δ ≤ ε := by linarith [min_le_left (ε / 16) (1 / 4)]
  have hδ₁ : δ ≤ 1 / 4 := min_le_right _ _
  -- A bound with exponent `e ≤ ε` implies the bound with exponent `ε`, since `N ≥ 1`.
  have hmono {e : ℝ} (he : e ≤ ε) (hb : ∃ c > 0, ∀ (N : ℕ) [NeZero N]
      (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
        c * (N : ℝ) ^ (-e) ≤ (χ.LFunction 1).re) :
      ∃ c > 0, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
        c * (N : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
    obtain ⟨c, hc, hb⟩ := hb
    refine ⟨c, hc, fun N _ χ hχ hχ₁ ↦ le_trans ?_ (hb N χ hχ hχ₁)⟩
    gcongr
    exact_mod_cast NeZero.one_le
  by_cases hz : ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter ℂ M), χ.IsQuadratic ∧ χ ≠ 1 ∧
      ∃ σ ∈ Set.Ioo (1 - δ) 1, χ.LFunction σ = 0
  · obtain ⟨M, _, χ, hχ, hχ₁, σ, hσ, hσ₀⟩ := hz
    exact hmono (by linarith [hσ.1]) (exists_pos_mul_rpow_le_LFunction_one_re_of_LFunction_eq_zero
      hχ hχ₁ (by linarith [hσ.1]) hσ.2 hσ₀)
  · push Not at hz
    exact hmono (by linarith) (exists_pos_mul_rpow_le_LFunction_one_re_of_forall_LFunction_ne_zero
      (by linarith) (by linarith) fun M _ χ hχ hχ₁ σ hσ ↦ hz M inferInstance χ hχ hχ₁ σ hσ)

end TauCeti.Multiquadratic
