/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FrobeniusRiesz.PrimeSide
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.FrobeniusMainTerm
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate

/-!
# The character average of a Frobenius Riesz remainder

For a quadratic character of a finite abelian quotient of cyclotomic units, restrict the
prime-power ramps to the complement of its kernel. Translate this complement into the kernel to
read off the caps. The difference between twice this prime sum and its main term is the average
of the first Riesz remainders of the primitive Dirichlet pullbacks. Only the principal and
quadratic terms survive in the main term; the Frobenius averages include ramified prime powers.

The identity and normalization are those of Levent Alpöge's `Deduction.ch_balance` in
[`ChBalance.lean`][ch-balance].

[ch-balance]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean
-/

public section

open ArithmeticFunction Finset Function TauCeti
open scoped BigOperators ComplexConjugate

namespace MonoidHom

variable {N : ℕ} [NeZero N] {G : Type*} [Group G]

/-- The main term for the Frobenius Riesz sum off the kernel of `q`, normalized with twice
the prime-power ramp. Its dependence on the caps is through their mean logarithm on the kernel. -/
noncomputable def frobeniusRieszMainTerm [Fintype G] (f : (ZMod N)ˣ →* G) (q : G →* ℂˣ)
    (w : G → ℝ) (a : ℝ) : ℂ := by
  classical
  exact (a : ℂ) * ((Real.log a : ℂ) - (1 + (Real.eulerMascheroniConstant : ℂ)) +
    logDeriv (PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (q.comp f))).character.LFunction 1 -
      𝔼 h with q h = 1, (Real.log (w h) : ℂ))

open scoped Classical in
/-- Formula for the Frobenius main term in terms of the quadratic logarithmic derivative and
the mean of the logarithms of the caps. -/
theorem frobeniusRieszMainTerm_def [Fintype G] (f : (ZMod N)ˣ →* G) (q : G →* ℂˣ)
    (w : G → ℝ) (a : ℝ) :
    f.frobeniusRieszMainTerm q w a =
      (a : ℂ) * ((Real.log a : ℂ) - (1 + (Real.eulerMascheroniConstant : ℂ)) +
        logDeriv (PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (q.comp f))).character.LFunction
          1 - 𝔼 h with q h = 1, (Real.log (w h) : ℂ)) := (rfl)

/-- The main term is real for a quadratic character. -/
@[simp] theorem conj_frobeniusRieszMainTerm [Fintype G] (f : (ZMod N)ˣ →* G) (q : G →* ℂˣ)
    (hq : q * q = 1) (w : G → ℝ) (a : ℝ) :
    conj (f.frobeniusRieszMainTerm q w a) = f.frobeniusRieszMainTerm q w a := by
  let χ := MulChar.ofUnitHom (q.comp f)
  have hsq : χ * χ = 1 := by
    apply MulChar.mulEquivToUnitHom.injective
    have hχ : MulChar.mulEquivToUnitHom χ = q.comp f :=
      MulChar.mulEquivToUnitHom.apply_symm_apply _
    rw [map_mul, map_one, hχ]
    exact DFunLike.ext _ _ fun u ↦ DFunLike.congr_fun hq (f u)
  let ψ := PrimitiveDirichletCharacter.of χ
  have hp : ψ⁻¹ = ψ := by
    rw [← PrimitiveDirichletCharacter.of_inv, inv_eq_of_mul_eq_one_right hsq]
  have hd := ψ.character.logDeriv_LFunction_inv_conj 1
  rw [← PrimitiveDirichletCharacter.character_inv, map_one] at hd
  have hreal := hd.symm.trans
    (congrArg (fun ξ : PrimitiveDirichletCharacter ↦ logDeriv ξ.character.LFunction 1) hp)
  simp only [ψ, χ] at hreal
  simp only [frobeniusRieszMainTerm_def, map_mul, map_sub, map_add, Complex.conj_ofReal,
    map_one, expect_eq_sum_div_card, map_div₀, map_sum, map_natCast, hreal]

/-- The character average for the Frobenius Riesz sum off the kernel of `q`. The argument `c`
translates the complement into the kernel (when `q` is quadratic and `q c ≠ 1`). Each term
uses the primitive Dirichlet pullback at the scale `a / w (c * g)`. -/
noncomputable def frobeniusRieszCharAverage [Fintype G] (f : (ZMod N)ˣ →* G) (q : G →* ℂˣ)
    (c : G) (w : G → ℝ) (a : ℝ) : ℂ := by
  classical
  exact 𝔼 g with q g ≠ 1, ∑ χ : G →* ℂˣ,
    conj (χ g : ℂ) * ((w (c * g) : ℂ) *
      (PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))).rieszRemainder
        (a / w (c * g)))

open scoped Classical in
/-- Expand the character average as a mean of scaled, primitive first Riesz remainders. -/
theorem frobeniusRieszCharAverage_def [Fintype G] (f : (ZMod N)ˣ →* G) (q : G →* ℂˣ)
    (c : G) (w : G → ℝ) (a : ℝ) :
    f.frobeniusRieszCharAverage q c w a = 𝔼 g with q g ≠ 1, ∑ χ : G →* ℂˣ,
      conj (χ g : ℂ) * ((w (c * g) : ℂ) *
        (PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))).rieszRemainder
          (a / w (c * g))) := (rfl)

private noncomputable abbrev pullback (f : (ZMod N)ˣ →* G) (χ : G →* ℂˣ) :
    PrimitiveDirichletCharacter :=
  PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))

private theorem pullback_eq_one_iff (f : (ZMod N)ˣ →* G) (hf : Surjective f) (χ : G →* ℂˣ) :
    pullback f χ = 1 ↔ χ = 1 := by
  rw [PrimitiveDirichletCharacter.of_eq_iff]
  simp only [PrimitiveDirichletCharacter.level_one]
  constructor
  · rintro ⟨_, h⟩
    rw [PrimitiveDirichletCharacter.character_one, DirichletCharacter.changeLevel_one] at h
    ext g
    obtain ⟨u, rfl⟩ := hf g
    have he := DFunLike.congr_fun h (u : ZMod N)
    simpa using he.symm
  · rintro rfl
    exact ⟨one_dvd N, by simp [← MulChar.mulEquivToUnitHom_symm_apply]⟩

open scoped Classical in
private theorem mul_expect_rieszSum_sub_charAverage [Fintype G]
    (f : (ZMod N)ˣ →* G) (hf : Surjective f) (q : G →* ℂˣ) (c : G)
    (w : G → ℝ) (a : ℝ) :
    (𝔼 g with q g ≠ 1, (w (c * g) : ℂ) * ∑ χ : G →* ℂˣ,
      conj (χ g : ℂ) * rieszSum (fun n ↦ (Λ n : ℂ) * (pullback f χ).character n)
        (a / w (c * g))) - f.frobeniusRieszCharAverage q c w a =
    𝔼 g with q g ≠ 1, (w (c * g) : ℂ) * ((a / w (c * g) : ℝ) : ℂ) *
      ((Real.log (a / w (c * g)) : ℂ) - (1 + (Real.eulerMascheroniConstant : ℂ)) -
        ∑ χ ∈ (univ : Finset (G →* ℂˣ)).erase 1,
          conj (χ g : ℂ) * logDeriv (pullback f χ).character.LFunction 1) := by
  rw [frobeniusRieszCharAverage_def, ← expect_sub_distrib]
  refine expect_congr rfl fun g _ ↦ ?_
  rw [← add_sum_erase _ _ (mem_univ (1 : G →* ℂˣ)),
    ← add_sum_erase _ _ (mem_univ (1 : G →* ℂˣ))]
  have h₁ : pullback f (1 : G →* ℂˣ) = 1 := (pullback_eq_one_iff f hf _).2 rfl
  have hχ : ∀ χ ∈ (univ : Finset (G →* ℂˣ)).erase 1, pullback f χ ≠ 1 :=
    fun χ hχ ↦ (pullback_eq_one_iff f hf χ).not.mpr (mem_erase.mp hχ).1
  simp only [h₁, one_apply, Units.val_one, map_one, one_mul,
    PrimitiveDirichletCharacter.rieszRemainder_one]
  have hsum : (∑ χ ∈ (univ : Finset (G →* ℂˣ)).erase 1,
      conj (χ g : ℂ) * ((w (c * g) : ℂ) * (pullback f χ).rieszRemainder (a / w (c * g)))) =
      (w (c * g) : ℂ) * (∑ χ ∈ (univ : Finset (G →* ℂˣ)).erase 1,
        conj (χ g : ℂ) * rieszSum (fun n ↦ (Λ n : ℂ) * (pullback f χ).character n)
          (a / w (c * g))) +
      ((w (c * g) : ℂ) * ((a / w (c * g) : ℝ) : ℂ)) *
        ∑ χ ∈ (univ : Finset (G →* ℂˣ)).erase 1,
          conj (χ g : ℂ) * logDeriv (pullback f χ).character.LFunction 1 := by
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun χ hχ' ↦ ?_
    rw [PrimitiveDirichletCharacter.rieszRemainder_of_ne_one (hχ χ hχ')]
    simp_rw [mul_comm (Λ _ : ℂ)]
    ring
  rw [hsum]
  have hcoeff : (fun n : ℕ ↦ (Λ n : ℂ) * (pullback f (1 : G →* ℂˣ)).character n) =
      fun n : ℕ ↦ (Λ n : ℂ) := by
    funext n
    have h := congrArg (fun ψ : PrimitiveDirichletCharacter ↦ ψ.character (n : ZMod ψ.level)) h₁
    simp only [PrimitiveDirichletCharacter.character_one_apply] at h
    rw [h, mul_one]
  rw [hcoeff]
  ring

open scoped Classical IsMulCommutative in
/-- Twice the Frobenius Riesz sum on the nonidentity coset of a quadratic kernel, minus its
main term, is the character average. Caps are read on the kernel via `g ↦ c * g`. On a CM
host one may take `c` to be complex conjugation times the reference place. -/
theorem frobeniusRieszSum_sub_main [Fintype G]
    (f : (ZMod N)ˣ →* G) (hf : Surjective f) (q : G →* ℂˣ) (hq : q * q = 1)
    {c : G} (hc : q c ≠ 1) {w : G → ℝ} (hw : ∀ h ∈ q.ker, 0 < w h) (a : ℝ) :
    2 * (f.frobeniusRieszSum (univ.filter fun g ↦ q g ≠ 1) (fun g ↦ w (c * g)) a : ℂ) -
      f.frobeniusRieszMainTerm q w a = f.frobeniusRieszCharAverage q c w a := by
  have : IsMulCommutative G := hf.isMulCommutative
  let S := univ.filter fun g ↦ q g ≠ 1
  have hc' := (q.apply_ne_one_iff_of_mul_self_eq_one hq c).mp hc
  have hmem (g : G) : g ∈ S ↔ q (c * g) = 1 := by
    rcases q.apply_eq_one_or_eq_neg_one_of_mul_self_eq_one hq g with hg | hg
    · simp [S, hg, hc]
    · have hcn := Units.val_eq_neg_one.mp hc'
      simp only [S, mem_filter, mem_univ, true_and, hg, map_mul, hcn]
      simp
  have hcard := card_equiv (Equiv.mulLeft c) (t := univ.filter fun h ↦ q h = 1)
    (fun g ↦ by simpa using hmem g)
  have htotal := card_filter_add_card_filter_not (s := univ) (fun g ↦ q g = 1)
  rw [← hcard, card_univ] at htotal
  have hnorm : 2 * (Nat.card G : ℂ)⁻¹ = (S.card : ℂ)⁻¹ := by
    rw [Nat.card_eq_fintype_card, ← htotal, Nat.cast_add, ← two_mul, mul_inv_rev,
      mul_left_comm, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), mul_one]
  -- The factor of two changes the full-group normalization to a mean over the coset.
  rw [f.ofReal_frobeniusRieszSum_eq_sum_rieszSum S _ a (fun g hg ↦
    hw _ (MonoidHom.mem_ker.mpr ((hmem g).mp hg))), ← mul_assoc, hnorm, ← div_eq_inv_mul,
    ← expect_eq_sum_div_card]
  have hconj (χ : G →* ℂˣ) (g : G) : (↑(χ g)⁻¹ : ℂ) = conj (χ g : ℂ) :=
    (Units.val_inv_eq_inv_val _).trans (Complex.inv_eq_conj
      (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite g)).norm_eq_one)
  simp_rw [hconj]
  apply sub_eq_iff_eq_add.mpr
  -- In the main term only the trivial and quadratic characters survive the coset mean.
  rw [add_comm, ← sub_eq_iff_eq_add, mul_expect_rieszSum_sub_charAverage f hf q c w a,
    f.frobeniusRieszMainTerm_def]
  simpa only [mul_one] using q.expect_filter_apply_ne_one_mul_log_div_sub_sum_conj_mul_eq hq hc'
    (map_one q) univ (mem_univ q) (fun χ ↦ logDeriv (pullback f χ).character.LFunction 1)
    (1 + (Real.eulerMascheroniConstant : ℂ)) a w (fun h hh ↦ (hw h hh).ne')

end MonoidHom
