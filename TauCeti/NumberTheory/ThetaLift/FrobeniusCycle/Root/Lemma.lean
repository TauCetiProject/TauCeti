/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Root.Basic
public import TauCeti.RingTheory.MvPolynomial.GaussFiltration
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.LocalRing.ResidueField.RootCount
import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# The root lemma

Let `T` be a Frobenius cycle (`TauCeti.FrobeniusCycle`): ring maps `ι s : W →+* R` for the letters
`s : ZMod N`, alternately even and odd, with `ι (s + 1) ≡ ι s ^ P` modulo a prime `p`, where `W`
has `q = P ^ N` residue classes, and a square root `w` of `p` in `R`. The group `GL_k(W)` acts on
polynomials over `R` in the variables `x (b, s)`, `b : Fin k`, by the twisted action: `g` acts
through the block diagonal matrix of its letter matrices `T.letterMatrix s g`, by Tau Ceti's
substitution of standard vectors `TauCeti.polynomialAction`. This file shows which monomials can
carry the least `w`-adic order plus weight among all translates of a polynomial by `SL₂(W)`, placed
in two rows and columns `a`, `a'` (`TauCeti.rootSL`): their exponents have defect at most `0`, which
is one of Pieri's inequalities.

Write `u_s = x (T.posIndex a a' s, s)` and `ū_s = x (T.negIndex a a' s, s)` for the two variables
of the root `(a, a')` at the letter `s`.

## Main results

* `TauCeti.FrobeniusCycle.defect_nonpos_of_extreme_term` (the root lemma): for weights `c` with
  `c(u_s) - c(ū_s) ∈ [1 / 2, 1]`, if every translate of `f` by `SL₂^{a,a'}(W)` lies in Gauss level
  `l + c · α` and `w ^ (l + 1)` does not divide the coefficient of `x ^ α` in `f`, then the defect
  of `α` at any letter along `(a, a')` is at most `0`.
* `TauCeti.FrobeniusCycle.mem_gaussFiltration_sub_defect_div_three`: if the weights `δ` rise by `1`
  from `ū_s` to `u_s` and every translate of `f` lies in Gauss level `v₀` for `δ`, then `f` lies in
  Gauss level `v₀` for `δ` minus a third of the defect weights.
* `TauCeti.FrobeniusCycle.defect_nonpos_of_least`: over a field of characteristic `p`, a term of
  least `δ`-weight among all translates has defect at most `0`.

## Proof

Fix the root `(a, a')` and the letter `i` (`TauCeti.FrobeniusCycle.RootAt`). Write `X_s = ū_s` and
`Y_s = u_s`. A substitution of polynomials in one affine coordinate `t` for these variables turns
the coefficient of a term of `f` into a univariate polynomial `Φ` over `R ⧸ (w ^ (l + 1))`. Its
expansion at infinity bounds its degree by `q ν'`, and its expansions at the `q` finite points
`ι i r`, which come from the translates of `f` by the matrices `!![0, 1; -1, ±r]` together with the
Frobenius congruences, give zeros of order at least `ν` there, where `ν q - q ν'` is `q (q - 1)`
times the defect. Stepanov's count (`Polynomial.mul_natCard_residueField_le_natDegree`) compares the
two.

The statements and proofs are adapted from the file
`New/UpperBound/ElementaryDivisors/RootLemma.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC):
`New.FrobeniusCycle.RootAt` and its lemmas, `New.FrobeniusCycle.defect_nonpos_of_extreme_term`,
`New.FrobeniusCycle.totalDegree_polyAction_le`,
`New.FrobeniusCycle.mem_gaussFiltration_sub_defect_div_three` and
`New.FrobeniusCycle.weight_defectWeight_nonpos_of_least`.

## References

The comparison of zeros with degree is Stepanov's method; see
* E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*,
  Séminaire Bourbaki, exp. 430 (1973).

Weight inequalities for twisted actions on Frobenius twists of symmetric powers are in the spirit of
* E. Ghate, A. Jana, *Modular representations of `GL₂(F_q)` using calculus*, 2025;
* N. Imai, J.-S. Koskivirta, *Automorphic vector bundles on the stack of `G`-zips*, Forum Math.
  Sigma 9 (2021).
-/

public section

namespace TauCeti

open MvPolynomial Matrix Finsupp SetLike Nat Ideal.Quotient

namespace FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N k : ℕ}

/-- The Gauss filtration on polynomials over `R[t]` in which `w` weighs `1`, `t` weighs `ρ` and
each variable `z` weighs `c z - v z * ρ`. -/
private noncomputable abbrev iteratedGaussFiltration (T : FrobeniusCycle W R N)
    (c : Fin k × ZMod N → ℝ) (ρ : ℝ) (v : Fin k × ZMod N → ℕ) :
    ℝ → AddSubgroup (MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :=
  gaussFiltration (gaussFiltration (adicFiltration T.w) fun _ : Unit ↦ ρ)
    fun z ↦ c z - v z * ρ

private theorem antitone_iteratedGaussFiltration (T : FrobeniusCycle W R N) (c : Fin k × ZMod N → ℝ)
    (ρ : ℝ) (v : Fin k × ZMod N → ℕ) : Antitone (T.iteratedGaussFiltration c ρ v) :=
  antitone_gaussFiltration (antitone_gaussFiltration (antitone_adicFiltration _))

variable {T : FrobeniusCycle W R N} {c : Fin k × ZMod N → ℝ} {ρ b : ℝ} {v : Fin k × ZMod N → ℕ}

private theorem algebraMap_mem_iteratedGaussFiltration {r : R} (hr : r ∈ adicFiltration T.w b) :
    algebraMap R (MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) r ∈
      T.iteratedGaussFiltration c ρ v b :=
  C_mem_gaussFiltration (C_mem_gaussFiltration hr)

/-- The term `r t ^ n` times the variable `X z` lies in `T.iteratedGaussFiltration c ρ v b` if
`r = 0` or `b ≤ c z - v z * ρ + n * ρ`, the weight of `t ^ n X z`. -/
private theorem C_monomial_mul_X_mem_iteratedGaussFiltration {z : Fin k × ZMod N} {n : ℕ} {r : R}
    (hb : r ≠ 0 → b ≤ c z - v z * ρ + n * ρ) :
    C (monomial (single () n) r) * X z ∈ T.iteratedGaussFiltration c ρ v b := by
  rw [C_mul_X_eq_monomial]
  refine monomial_mem_gaussFiltration (monomial_mem_gaussFiltration ?_)
  exact mem_adicFiltration_of_nonpos (by simpa [weight_single, add_comm] using hb)

namespace RootAt

variable {D : T.RootAt k}

/-- **Expansion at infinity.** Let the weights `c` rise from `X_s` to `Y_s` by amounts in
`[1 / 2, 1]`, let each term of `f` have `w`-adic order plus `c`-weight at least `b`, and put
`ρ = D.slope c`. In the filtration on polynomials over `R[t]` in which `w` weighs `1`, `t` weighs
`-ρ` and `X_s` weighs `c X_s + q P_s ρ`, the substitution `D.mainSubst - D.crossSubst` sends `f` to
level `b`, and the cross terms change the image of `f` only in level `b + 1 / 20`. -/
private theorem HasBoundedIncrements.aeval_mem_and_sub_mem_iteratedGaussFiltration
    (hc : D.HasBoundedIncrements c) {f : MvPolynomial (Fin k × ZMod N) R}
    (hf : f ∈ gaussFiltration (adicFiltration T.w) c b) :
    aeval (D.mainSubst - D.crossSubst) f ∈
        T.iteratedGaussFiltration c (-D.slope c) D.poleOrder b ∧
      aeval (D.mainSubst - D.crossSubst) f - aeval D.mainSubst f ∈
        T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (b + 20⁻¹) := by
  have := T.neZero
  have h_main (z : Fin k × ZMod N) :
      D.mainSubst z ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (c z) := by
    rw [mainSubst_apply]
    refine C_monomial_mul_X_mem_iteratedGaussFiltration fun _ ↦ ?_
    by_cases hz : z = D.varY D.letter
    · simp [hz, q_mul_slope]
    · simp [merge_def, hz]
  have h_cross (z : Fin k × ZMod N) :
      D.crossSubst z ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (c z + 20⁻¹) := by
    rw [crossSubst_apply]
    refine C_monomial_mul_X_mem_iteratedGaussFiltration fun h_sign ↦ ?_
    rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
    · simp at h_sign
    · simp at h_sign
    · -- `X_s` weighs `c X_s + q P_s * D.slope c ≥ c X_s + 2 ≥ c Y_s + 1`
      suffices c (D.varY s) + 20⁻¹ ≤ c (D.varX s) + T.q * D.frobPower s * D.slope c by simpa
      linarith [(hc.sub_mem_Icc s).2, hc.two_le_q_mul_frobPower_mul_slope hs]
    · -- `t ^ P_s Y_s` weighs `c Y_s - P_s * D.slope c ≥ c X_s + 1 / 2 - 1 / 5`
      suffices c (D.varX s) + 20⁻¹ ≤ c (D.varY s) + -(D.frobPower s * D.slope c) by simpa [hs]
      linarith [(hc.sub_mem_Icc s).1, hc.frobPower_mul_slope_le s]
    · exact absurd hz.crossSign_eq_zero h_sign
  exact algHom_sub_mem_of_mem_gaussFiltration (aeval D.mainSubst) _
    (antitone_iteratedGaussFiltration ..) hf (by simpa using h_main) _ (by norm_num)
    (by simpa using h_cross) algebraMap_mem_iteratedGaussFiltration

end RootAt

/-- The error in the rule `(t + ι_i(r)) ^ P ^ n = t ^ P ^ n + ι_{i + n}(r)`. -/
private noncomputable def frobeniusError (T : FrobeniusCycle W R N) (i : ZMod N) (r : W) (n : ℕ) :
    MvPolynomial Unit R :=
  (X () + C (T.ι i r)) ^ T.P ^ n - X () ^ T.P ^ n - C (T.ι (i + n) r)

/-- The Frobenius error is divisible by `p = w ^ 2`, so for `ρ ≥ 0` its product with a variable `z`
has level `2` more than the weight of `z`. -/
private theorem frobeniusError_mul_X_mem (hρ : 0 ≤ ρ) (v : Fin k × ZMod N → ℕ) (z : Fin k × ZMod N)
    (i : ZMod N) (r : W) (n : ℕ) :
    C (T.frobeniusError i r n) * X z ∈ T.iteratedGaussFiltration c ρ v (c z - v z * ρ + 2) := by
  have h_add : (T.p : MvPolynomial Unit R) ∣
      (X () + C (T.ι i r)) ^ T.P ^ n - X () ^ T.P ^ n - C (T.ι i r) ^ T.P ^ n := by
    simp [T.P_def, ← pow_mul, add_pow_prime_pow_eq' T.prime, add_assoc]
  have h_shift : (T.p : MvPolynomial Unit R) ∣
      C (T.ι (i + n) r) - C (T.ι i r) ^ T.P ^ n := by
    simpa using map_dvd C (T.dvd_ι_add_natCast_sub_pow i r n)
  have h_dvd : C (T.w ^ 2) ∣ T.frobeniusError i r n := by
    simpa [frobeniusError, w_sq] using dvd_sub h_add h_shift
  rw [C_mul_X_eq_monomial]
  refine monomial_mem_gaussFiltration (mem_gaussFiltration_iff.2 fun β ↦ ?_)
  refine mem_adicFiltration_iff.2 ((pow_dvd_pow T.w ?_).trans
    ((C_dvd_iff_dvd_coeff _ _).1 h_dvd β))
  -- The order asked for is `2` minus the weight `β () * ρ ≥ 0` of the monomial `β` in `t`.
  simpa [weight_single, β.weight_eq_sum _] using mul_nonneg (β ()).cast_nonneg hρ

namespace RootAt

variable {D : T.RootAt k}

/-- The shift of `t` undoes the transvection in `D.swapTransvection r` up to Frobenius errors. Act
on the variable `z` by `D.swapTransvection r`, substitute `D.mainSubst - D.crossSubst` and replace
`t` by `t + ι_i(r)` in the coefficients (the Taylor shift `MvPolynomial.taylor`). Up to the sign
`D.moveSign z` the result is the polynomial substituted for `D.swapVar z`, plus errors
`T.frobeniusError i r n` that occur only for `z = Y_s`: with `d = (s - i) mod N`, the error for
`n = N + d` multiplies `X_s`, and `-ε_s` times the error for `n = d` multiplies `Y_s`. -/
private theorem mapAlgHom_taylor_aeval_swapTransvection_X [NeZero N] (r : W)
    (z : Fin k × ZMod N) :
    mapAlgHom (MvPolynomial.taylor fun _ : Unit ↦ T.ι D.letter r)
        (aeval (D.mainSubst - D.crossSubst)
          (polynomialAction (blockDiagonal (T.letterMatrix · (D.swapTransvection r))) (X z))) -
      D.moveSign z • (D.mainSubst - D.crossSubst) (D.swapVar z) =
    D.moveSign z •
      (C (T.frobeniusError D.letter (|D.sign z| * r) (N + (z.2 - D.letter).val)) *
          X (D.swapVar z) -
        D.sign z • (C (T.frobeniusError D.letter r (z.2 - D.letter).val) * X z)) := by
  have := T.neZero
  rw [D.polynomialAction_swapTransvection_X, map_zsmul, map_zsmul, ← smul_sub]
  simp only [frobeniusError]
  congr 1
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · -- `z = Y_i`
    simp [monomial_eq, mainSubst_apply, crossSubst_apply, T.q_def]
    ring
  · -- `z = X_i`
    simp [monomial_eq, mainSubst_apply, crossSubst_apply]
  · -- `z = Y_s` with `s ≠ i`, the same computation for both signs
    rcases D.sign_varY_eq_one_or_neg_one s with h_sign | h_sign
    all_goals
      simp [monomial_eq, mainSubst_apply, crossSubst_apply, T.q_def, frobPower_def, pow_add, hs,
        h_sign]
      ring
  · -- `z = X_s` with `s ≠ i`
    simp [monomial_eq, mainSubst_apply, crossSubst_apply, hs]
  · -- `z` lies off the root
    simp [monomial_eq, mainSubst_apply, crossSubst_apply, hz.swapVar_eq, hz.sign_eq_zero,
      hz.poleOrder_eq_zero, hz.crossSign_eq_zero]

/-- With `ρ = D.slope c`, filter polynomials over `R[t]` so that `w` weighs `1`, `t` weighs `ρ` and
a variable `y` weighs `c y - D.zeroOrder y * ρ`. If `c` rises from `X_s` to `Y_s` by amounts in
`[1 / 2, 1]`, the substitution `D.mainSubst - D.crossSubst` sends `D.swapVar z` to level `c z`. -/
private theorem HasBoundedIncrements.subst_swapVar_mem_iteratedGaussFiltration
    (hc : D.HasBoundedIncrements c) (z : Fin k × ZMod N) :
    (D.mainSubst - D.crossSubst) (D.swapVar z) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z) := by
  have := T.neZero
  rw [Pi.sub_apply, mainSubst_apply, crossSubst_apply]
  refine sub_mem (C_monomial_mul_X_mem_iteratedGaussFiltration fun _ ↦ ?_)
    (C_monomial_mul_X_mem_iteratedGaussFiltration (by simp))
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · simp [q_mul_slope]
  · simp
  · suffices c (D.varY s) ≤ c (D.varX s) + T.q * D.frobPower s * D.slope c by simpa
    linarith [(hc.sub_mem_Icc s).2, hc.two_le_q_mul_frobPower_mul_slope hs]
  · suffices c (D.varX s) + D.frobPower s * D.slope c ≤ c (D.varY s) by
      simpa [hs, le_sub_iff_add_le]
    linarith [(hc.sub_mem_Icc s).1, hc.frobPower_mul_slope_le s]
  · simp [hz.swapVar_eq, hz.merge_eq, hz.poleOrder_eq_zero, hz.zeroOrder_eq_zero]

/-- At a finite point a variable `y` weighs `c y - D.zeroOrder y * D.slope c`. If `c` rises from
`X_s` to `Y_s` by amounts in `[1 / 2, 1]`, then `c z + 1 / 20` is at most `2` plus the weight of
`y`, both for `y = z` and for `y = D.swapVar z`. -/
private theorem HasBoundedIncrements.add_le_sub_zeroOrder_mul_slope_add_two
    (hc : D.HasBoundedIncrements c) (z : Fin k × ZMod N) :
    c z + 20⁻¹ ≤ c (D.swapVar z) - D.zeroOrder (D.swapVar z) * D.slope c + 2 ∧
      c z + 20⁻¹ ≤ c z - D.zeroOrder z * D.slope c + 2 := by
  have := T.neZero
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · suffices c (D.varY D.letter) + 20⁻¹ ≤ c (D.varX D.letter) + 2 by simpa [q_mul_slope]
    linarith [(hc.sub_mem_Icc D.letter).2]
  · norm_num [q_mul_slope]
  · suffices c (D.varY s) + 20⁻¹ ≤ c (D.varX s) + 2 ∧
        c (D.varY s) + 20⁻¹ ≤ c (D.varY s) - D.frobPower s * D.slope c + 2 by simpa [hs]
    constructor <;> linarith [(hc.sub_mem_Icc s).2, hc.frobPower_mul_slope_le s]
  · suffices c (D.varX s) + 20⁻¹ ≤ c (D.varY s) - D.frobPower s * D.slope c + 2 ∧
        (20⁻¹ : ℝ) ≤ 2 by simpa [hs]
    constructor <;> linarith [(hc.sub_mem_Icc s).1, hc.frobPower_mul_slope_le s]
  · norm_num [hz.swapVar_eq, hz.zeroOrder_eq_zero]

/-- **Expansion at the finite point `ι_i(r)`.** Let the weights `c` rise from `X_s` to `Y_s` by
amounts in `[1 / 2, 1]`, and let each term of the translate of `f` by `(D.swapTransvection r)⁻¹`
have `w`-adic order plus `c`-weight at least `b`. Substitute `D.mainSubst - D.crossSubst` in `f`,
then replace `t` by `t + ι_i(r)` in the coefficients. The result has level `b` when `w` weighs `1`,
`t` weighs `ρ = D.slope c` and a variable `z` weighs `c z - D.zeroOrder z * ρ`. -/
private theorem HasBoundedIncrements.mapAlgHom_taylor_aeval_mem [NeZero N]
    (hc : D.HasBoundedIncrements c) (r : W) {f : MvPolynomial (Fin k × ZMod N) R}
    (hf : polynomialAction (blockDiagonal (T.letterMatrix · (D.swapTransvection r)⁻¹)) f ∈
      gaussFiltration (adicFiltration T.w) c b) :
    mapAlgHom (MvPolynomial.taylor fun _ : Unit ↦ T.ι D.letter r)
        (aeval (D.mainSubst - D.crossSubst) f) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder b := by
  have := T.neZero
  -- `ψ` (act, substitute, shift) is `θ` (signed swap, substitute) up to terms of more weight.
  let E := MvPolynomial (Fin k × ZMod N) R →ₐ[R]
    MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)
  let ψ : E := (mapAlgHom (MvPolynomial.taylor fun _ : Unit ↦ T.ι D.letter r)).comp
    (.comp (aeval (D.mainSubst - D.crossSubst))
      (polynomialAction (blockDiagonal (T.letterMatrix · (D.swapTransvection r)))))
  let θ : E := aeval fun z ↦ D.moveSign z • (D.mainSubst - D.crossSubst) (D.swapVar z)
  have h_main (z : Fin k × ZMod N) :
      θ (X z) ∈ T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z) := by
    rw [aeval_X]
    exact zsmul_mem (hc.subst_swapVar_mem_iteratedGaussFiltration z) _
  have h_error (z : Fin k × ZMod N) : ψ (X z) - θ (X z) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z + 20⁻¹) := by
    obtain ⟨h_exchange, h_self⟩ := hc.add_le_sub_zeroOrder_mul_slope_add_two z
    rw [aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, mapAlgHom_taylor_aeval_swapTransvection_X]
    refine zsmul_mem (sub_mem (antitone_iteratedGaussFiltration _ _ _ _ h_exchange ?_)
      (zsmul_mem (antitone_iteratedGaussFiltration _ _ _ _ h_self ?_) _)) _
    all_goals apply frobeniusError_mul_X_mem hc.slope_pos.le
  have h_level :
      ψ (polynomialAction (blockDiagonal (T.letterMatrix · (D.swapTransvection r)⁻¹)) f) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder b :=
    (algHom_sub_mem_of_mem_gaussFiltration θ _ (antitone_iteratedGaussFiltration ..) hf h_main ψ
      (by norm_num) h_error algebraMap_mem_iteratedGaussFiltration).left
  have h_cancel : polynomialAction (blockDiagonal (T.letterMatrix · (D.swapTransvection r)))
      (polynomialAction (blockDiagonal (T.letterMatrix · (D.swapTransvection r)⁻¹)) f) = f := by
    rw [← polynomialAction_letterMatrix_mul, mul_inv_cancel, polynomialAction_letterMatrix_one]
  rwa [AlgHom.comp_apply, AlgHom.comp_apply, h_cancel] at h_level

variable (D) in
/-- The coefficient, a polynomial in `t`, of the monomial obtained from `x ^ α` by writing `X_i`
for `Y_i`. -/
private noncomputable def mergedCoeff (α : Fin k × ZMod N →₀ ℕ)
    (p : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) : Polynomial R :=
  uniqueAlgEquiv R Unit (p.coeff (mapDomain D.merge α))

private theorem mergedCoeff_add (α : Fin k × ZMod N →₀ ℕ)
    (p p' : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :
    D.mergedCoeff α (p + p') = D.mergedCoeff α p + D.mergedCoeff α p' := by
  simp [mergedCoeff]

private theorem mergedCoeff_sub (α : Fin k × ZMod N →₀ ℕ)
    (p p' : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :
    D.mergedCoeff α (p - p') = D.mergedCoeff α p - D.mergedCoeff α p' := by
  simp [mergedCoeff]

/-- Shifting `t` by `x` in the coefficients of `p` shifts the polynomial `D.mergedCoeff α p` by
`x`. -/
private theorem mergedCoeff_mapAlgHom_taylor (α : Fin k × ZMod N →₀ ℕ) (x : R)
    (p : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)) :
    D.mergedCoeff α (mapAlgHom (MvPolynomial.taylor fun _ : Unit ↦ x) p) =
      (D.mergedCoeff α p).taylor x := by
  have h_taylor : (uniqueAlgEquiv R Unit).toAlgHom.comp (MvPolynomial.taylor fun _ : Unit ↦ x) =
      (Polynomial.taylorAlgHom x).comp (uniqueAlgEquiv R Unit).toAlgHom := by
    refine MvPolynomial.algHom_ext fun _ ↦ ?_
    simp [Polynomial.taylor_X]
  simpa [mergedCoeff, coeff_map] using AlgHom.congr_fun h_taylor (p.coeff (mapDomain D.merge α))

/-- Let `p` have level `b` in `T.iteratedGaussFiltration c ρ v`, and let `X_i` and `Y_i` have the
same weight there. The coefficient of `t ^ j` in `D.mergedCoeff α p` is divisible by `w ^ (l + 1)`
once `b` less the weight of `t ^ j x ^ α` exceeds `l`. -/
private theorem pow_dvd_coeff_mergedCoeff {α : Fin k × ZMod N →₀ ℕ}
    {p : MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R)} {l : ℕ} (j : ℕ)
    (hp : p ∈ T.iteratedGaussFiltration c ρ v b)
    (h_merge_weight : c (D.varX D.letter) - v (D.varX D.letter) * ρ =
      c (D.varY D.letter) - v (D.varY D.letter) * ρ)
    (hj : l < b - (weight c α - weight v α * ρ) - j * ρ) :
    T.w ^ (l + 1) ∣ (D.mergedCoeff α p).coeff j := by
  have h_var (z : Fin k × ZMod N) : c (D.merge z) - v (D.merge z) * ρ = c z - v z * ρ := by
    grind [merge_def]
  have h_weight : weight (fun z ↦ c z - v z * ρ) (mapDomain D.merge α) =
      weight c α - weight v α * ρ := by
    rw [weight_apply, sum_mapDomain_index (by simp) (by simp [add_mul])]
    simp [h_var, weight_apply, mul_sub, Finsupp.sum_mul, mul_assoc]
  have h_coeff : T.w ^ ⌈b - (weight c α - weight v α * ρ) - j * ρ⌉₊ ∣
      (D.mergedCoeff α p).coeff j := by
    rw [mergedCoeff, coeff_uniqueAlgEquiv]
    simpa [h_weight, weight_single] using
      mem_gaussFiltration_iff.1 (mem_gaussFiltration_iff.1 hp (mapDomain D.merge α)) (single () j)
  exact (pow_dvd_pow T.w (lt_ceil.2 hj)).trans h_coeff

/-- An exponent is determined by its image under `D.merge` and its weight for `D.poleOrder`: the
first forgets only how the degree splits between `X_i` and `Y_i`, and the second recovers it. -/
private theorem eq_of_mapDomain_merge_eq {α β : Fin k × ZMod N →₀ ℕ}
    (h_merge : mapDomain D.merge β = mapDomain D.merge α)
    (h_weight : weight D.poleOrder β = weight D.poleOrder α) : β = α := by
  have h_merge_add (γ : Fin k × ZMod N →₀ ℕ) :
      mapDomain D.merge γ + single (D.varY D.letter) (γ (D.varY D.letter)) =
        γ + single (D.varX D.letter) (γ (D.varY D.letter)) := by
    induction γ using induction_linear with
    | zero => simp
    | add γ γ' hγ hγ' => grind [mapDomain_add, Finsupp.add_apply, Finsupp.single_add]
    | single z n => by_cases hz : z = D.varY D.letter <;> simp [merge_def, hz, Ne.symm, add_comm]
  have h_pole_merge (γ : Fin k × ZMod N →₀ ℕ) : weight D.poleOrder (mapDomain D.merge γ) =
      weight D.poleOrder γ + γ (D.varY D.letter) * T.q := by
    simpa [weight_single] using congrArg (weight D.poleOrder) (h_merge_add γ)
  have h_sum : weight D.poleOrder α + β (D.varY D.letter) * T.q =
      weight D.poleOrder α + α (D.varY D.letter) * T.q := by
    rw [← h_pole_merge, ← h_merge, h_pole_merge, h_weight]
  have h_exponent : β (D.varY D.letter) = α (D.varY D.letter) := by
    have h_q : T.q ≠ 0 := by have := T.five_le_q; omega
    simpa [h_q] using h_sum
  refine add_right_cancel (b := Finsupp.single (D.varX D.letter) (α (D.varY D.letter))) ?_
  rw [← h_merge_add α, ← h_merge, ← h_exponent, h_merge_add β]

/-- In `f` substitute `D.mainSubst`. The coefficient of `t ^ d` in `D.mergedCoeff α` of the result,
with `d` the weight of `α` for `D.poleOrder`, is the coefficient of `x ^ α` in `f`: no other
monomial of `f` contributes to it. -/
private theorem coeff_mergedCoeff_aeval_mainSubst (α : Fin k × ZMod N →₀ ℕ)
    (f : MvPolynomial (Fin k × ZMod N) R) :
    (D.mergedCoeff α (aeval D.mainSubst f)).coeff (weight D.poleOrder α) = f.coeff α := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial β r =>
    have h_image : aeval D.mainSubst (monomial β r) =
        monomial (mapDomain D.merge β) (monomial (single () (weight D.poleOrder β)) r) := by
      simp [mainSubst_apply, aeval_monomial, X, C_mul_monomial, monomial_pow, Finsupp.prod,
        ← monomial_sum_prod, mapDomain, weight_apply, Finsupp.sum, single_finsetSum]
    have h_iff : mapDomain D.merge β = mapDomain D.merge α ∧
        weight D.poleOrder β = weight D.poleOrder α ↔ β = α :=
      ⟨fun h ↦ eq_of_mapDomain_merge_eq h.left h.right, fun h ↦ by simp [h]⟩
    rw [h_image, mergedCoeff, coeff_uniqueAlgEquiv, coeff_monomial, coeff_monomial]
    split_ifs <;> simp_all [coeff_monomial]
  | add p p' hp hp' => simp [mergedCoeff_add, ← hp, ← hp']

/-- **Zeros against degree.** Let the weights `c` rise from `X_s` to `Y_s` by amounts in
`[1 / 2, 1]`. Suppose that in all translates of `f` by `SL₂(W)` placed in the rows and columns
`a`, `a'` each term has `w`-adic order plus `c`-weight at least `l + c · α`, and that `w ^ (l + 1)`
does not divide the coefficient of `x ^ α` in `f`. Let `ν` be the weight of `α` for
`D.zeroOrder` and `q ν'` its weight for `D.poleOrder`. Then `ν q ≤ q ν'`. -/
private theorem HasBoundedIncrements.weight_zeroOrder_mul_q_le [NeZero N]
    (hc : D.HasBoundedIncrements c) {f : MvPolynomial (Fin k × ZMod N) R}
    {α : Fin k × ZMod N →₀ ℕ} {l : ℕ}
    (h_least : ∀ g ∈ rootSL W D.fst D.snd,
      polynomialAction (blockDiagonal (T.letterMatrix · g)) f ∈
        gaussFiltration (adicFiltration T.w) c (l + weight c α))
    (h_not_dvd : ¬T.w ^ (l + 1) ∣ f.coeff α) :
    weight D.zeroOrder α * T.q ≤ weight D.poleOrder α := by
  have := T.neZero
  -- `Φ` is the auxiliary binary form in the affine coordinate `t`, modulo `w ^ (l + 1)`. Its degree
  -- is at most `q ν'`, and it vanishes to order at least `ν` at the `q` finite rational points.
  let p := aeval (D.mainSubst - D.crossSubst) f
  let Φ : Polynomial (R ⧸ Ideal.span {T.w ^ (l + 1)}) :=
    (D.mergedCoeff α p).map (Ideal.Quotient.mk _)
  obtain ⟨h_infinity, h_cross⟩ := hc.aeval_mem_and_sub_mem_iteratedGaussFiltration
    (by simpa using h_least 1 (one_mem _))
  have h_merge_weight : c (D.varX D.letter) - D.poleOrder (D.varX D.letter) * -D.slope c =
      c (D.varY D.letter) - D.poleOrder (D.varY D.letter) * -D.slope c := by
    simp [q_mul_slope]
  -- Modulo `w ^ (l + 1)` the coefficient of `t ^ (q ν')` is the coefficient of `x ^ α` in `f`.
  have h_top : T.w ^ (l + 1) ∣
      (D.mergedCoeff α p).coeff (weight D.poleOrder α) - f.coeff α := by
    rw [← coeff_mergedCoeff_aeval_mainSubst (D := D), ← Polynomial.coeff_sub, ← mergedCoeff_sub]
    exact pow_dvd_coeff_mergedCoeff _ h_cross h_merge_weight (by linarith)
  have Φ_ne : Φ ≠ 0 := by
    refine fun hΦ ↦ h_not_dvd ((dvd_sub_right ?_).1 h_top)
    simpa [Φ, eq_zero_iff_dvd] using
      congrArg (fun P : Polynomial _ ↦ P.coeff (weight D.poleOrder α)) hΦ
  have Φ_deg : Φ.natDegree ≤ weight D.poleOrder α := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun j hj ↦ ?_
    have h_gap : weight D.poleOrder α * D.slope c < j * D.slope c := by
      gcongr
      exact hc.slope_pos
    rw [Polynomial.coeff_map, eq_zero_iff_dvd]
    exact pow_dvd_coeff_mergedCoeff j h_infinity h_merge_weight (by linarith)
  have Φ_zero (r : W) : Polynomial.X ^ weight D.zeroOrder α ∣
      Φ.comp (Polynomial.X +
        Polynomial.C (((Ideal.Quotient.mk _).comp (T.ι D.letter)) r)) := by
    rw [← Polynomial.taylor_apply]
    refine Polynomial.X_pow_dvd_iff.2 fun j hj ↦ ?_
    have h_gap : j * D.slope c < weight D.zeroOrder α * D.slope c := by
      gcongr
      exact hc.slope_pos
    have h_shift : mapAlgHom (MvPolynomial.taylor fun _ : Unit ↦ T.ι D.letter r) p ∈
        T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (l + weight c α) :=
      hc.mapAlgHom_taylor_aeval_mem r (h_least _ (inv_mem (D.swapTransvection_mem_rootSL r)))
    rw [RingHom.comp_apply, ← Polynomial.map_taylor, ← mergedCoeff_mapAlgHom_taylor,
      Polynomial.coeff_map, eq_zero_iff_dvd]
    exact pow_dvd_coeff_mergedCoeff j h_shift (by simp [q_mul_slope]) (by linarith)
  calc weight D.zeroOrder α * T.q
      = weight D.zeroOrder α * Nat.card (IsLocalRing.ResidueField W) := by
        rw [T.card_residueField_eq_q]
    _ ≤ Φ.natDegree := Polynomial.mul_natCard_residueField_le_natDegree Φ_ne Φ_zero
    _ ≤ weight D.poleOrder α := Φ_deg

end RootAt

/-- **The root lemma.** Let the weights `c` of the variables
rise from `ū_s = x (T.negIndex a a' s, s)` to `u_s = x (T.posIndex a a' s, s)` by amounts in
`[1 / 2, 1]` (so that `a ≠ a'`). Suppose that every translate `g • f`, `g ∈ SL₂^{a,a'}(W)`, lies in
Gauss level `l + c · α` for the `w`-adic filtration, and that `w ^ (l + 1)` does not divide the
coefficient of `x ^ α` in `f`. Then the defect of `α` at any letter `i` along `(a, a')` is at most
`0`. These bounds along the roots are Pieri's inequalities for the exponent of a term that is least
among all translates. -/
theorem defect_nonpos_of_extreme_term [NeZero N] (T : FrobeniusCycle W R N) {a a' : Fin k}
    (i : ZMod N) {c : Fin k × ZMod N → ℝ}
    (hc : ∀ s, c (T.posIndex a a' s, s) - c (T.negIndex a a' s, s) ∈ Set.Icc 2⁻¹ 1)
    {f : MvPolynomial (Fin k × ZMod N) R} {α : Fin k × ZMod N →₀ ℕ} {l : ℕ}
    (h_least : ∀ g ∈ rootSL W a a', polynomialAction (blockDiagonal (T.letterMatrix · g)) f ∈
      gaussFiltration (adicFiltration T.w) c (l + weight c α))
    (h_not_dvd : ¬T.w ^ (l + 1) ∣ f.coeff α) :
    T.defect a a' i α ≤ 0 := by
  -- For `a = a'` the weights would not rise from `ū_s = u_s` to `u_s`.
  have ha : a ≠ a' := by
    rintro rfl
    have h_idx : T.negIndex a a i = T.posIndex a a i := by simp [negIndex_eq_ite, posIndex_eq_ite]
    have := (hc i).1
    rw [h_idx, sub_self] at this
    norm_num at this
  let D : T.RootAt k := ⟨i, a, a', ha⟩
  -- Stepanov's count gives `ν q ≤ q ν'`, and the defect is `(ν - ν') / (q - 1)`.
  have hD : D.HasBoundedIncrements c := D.hasBoundedIncrements_iff.2 fun s ↦ by
    simpa [RootAt.varX_def, RootAt.varY_def, D] using hc s
  have h_count : weight D.zeroOrder α * T.q ≤ weight D.poleOrder α :=
    RootAt.HasBoundedIncrements.weight_zeroOrder_mul_q_le (D := D) hD h_least h_not_dvd
  have h_card : (1 : ℝ) < T.q := mod_cast T.one_lt_q
  have h_defect : T.defect D.fst D.snd D.letter α =
      (weight D.zeroOrder α - weight D.poleOrder α / T.q) / (T.q - 1) := by
    simp [coe_defect, weight_eq_sum, D.defectWeight_eq, mul_sub, mul_div, ← Finset.sum_div]
  refine h_defect.trans_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ?_) (by linarith))
  exact (le_div_iff₀ (by linarith)).2 (mod_cast h_count)

/-- The weight of `α` for `δ - (defect weights) / 3` is its weight for `δ` minus a third of its
defect. -/
theorem weight_sub_defectWeight_div_three (T : FrobeniusCycle W R N) (a a' : Fin k) (i : ZMod N)
    (δ : Fin k × ZMod N → ℝ) (α : Fin k × ZMod N →₀ ℕ) :
    weight (fun x ↦ δ x - T.defectWeight a a' i x / 3) α = weight δ α - T.defect a a' i α / 3 := by
  rw [coe_defect]
  simp [weight_apply, Finsupp.sum, mul_sub, Finset.sum_sub_distrib, mul_div_assoc',
    Finset.sum_div]

/-- The weights `δ - (defect weights) / 3` rise by an amount in `[1 / 2, 1]` from `ū_s` to `u_s`
when the weights `δ` rise by `1`. -/
theorem sub_defectWeight_div_three_mem_Icc (T : FrobeniusCycle W R N) {a a' : Fin k} (i : ZMod N)
    {δ : Fin k × ZMod N → ℝ}
    (h_step : ∀ s, δ (T.posIndex a a' s, s) - δ (T.negIndex a a' s, s) = 1) (s : ZMod N) :
    (δ (T.posIndex a a' s, s) - T.defectWeight a a' i (T.posIndex a a' s, s) / 3) -
      (δ (T.negIndex a a' s, s) - T.defectWeight a a' i (T.negIndex a a' s, s) / 3) ∈
        Set.Icc (2⁻¹ : ℝ) 1 := by
  have h_rise := T.defectWeight_sub_mem_Icc a a' i s
  constructor <;> linarith [h_step s, h_rise.1, h_rise.2]

/-- Let `t ≤ v₀`, and suppose that whenever some translate of `f` by `SL₂^{a,a'}(W)` has a
coefficient at `x ^ α` not divisible by `w ^ (l + 1)` and `l + ω · α < v₀`, then
`t ≤ l + ω · α`. Then every such translate lies in Gauss level `t` for the weights `ω`. -/
private theorem polynomialAction_mem_of_forall_low [NeZero N] (T : FrobeniusCycle W R N)
    {a a' : Fin k} {ω : Fin k × ZMod N → ℝ} {f : MvPolynomial (Fin k × ZMod N) R} {v₀ t : ℝ}
    (ht : t ≤ v₀)
    (h_low : ∀ (α : Fin k × ZMod N →₀ ℕ) (l : ℕ), l + weight ω α < v₀ →
      (∃ g ∈ rootSL W a a',
        ¬T.w ^ (l + 1) ∣ (polynomialAction (blockDiagonal (T.letterMatrix · g)) f).coeff α) →
        t ≤ l + weight ω α)
    {g : GL (Fin k) W} (hg : g ∈ rootSL W a a') :
    polynomialAction (blockDiagonal (T.letterMatrix · g)) f ∈
      gaussFiltration (adicFiltration T.w) ω t := by
  refine mem_gaussFiltration_iff.2 fun α ↦ ?_
  by_contra h_not
  obtain ⟨l, hl⟩ : ∃ l : ℕ, ⌈t - weight ω α⌉₊ = l + 1 :=
    exists_eq_succ_of_ne_zero fun h_zero ↦ h_not (by simp [h_zero])
  have h_lt : l < t - weight ω α := lt_ceil.1 (by lia)
  linarith [h_low α l (by linarith) ⟨g, hg, by simpa [hl] using h_not⟩]

/-- **A large defect forces a divisible coefficient.** Let
the weights `δ` rise by `1` from `ū_s` to `u_s` in each letter (so that `a ≠ a'`). If every
translate of `f` by `SL₂^{a,a'}(W)` lies in Gauss level `v₀` for `δ`, then `f` lies in Gauss level
`v₀` for the weights `δ - (defect weights at i along (a, a')) / 3`: each term has order plus
`δ`-weight at least `v₀` plus a third of its defect. -/
theorem mem_gaussFiltration_sub_defect_div_three [NeZero N] (T : FrobeniusCycle W R N)
    {a a' : Fin k} (i : ZMod N) {δ : Fin k × ZMod N → ℝ}
    (h_step : ∀ s, δ (T.posIndex a a' s, s) - δ (T.negIndex a a' s, s) = 1)
    {v₀ : ℝ} {f : MvPolynomial (Fin k × ZMod N) R}
    (hf : ∀ g ∈ rootSL W a a', polynomialAction (blockDiagonal (T.letterMatrix · g)) f ∈
      gaussFiltration (adicFiltration T.w) δ v₀) :
    f ∈ gaussFiltration (adicFiltration T.w) (fun x ↦ δ x - T.defectWeight a a' i x / 3) v₀ := by
  -- Let `ω` be `δ` minus a third of the defect weight. Suppose that some translate has a term
  -- whose order plus `ω`-weight is below `v₀`, and take a least such term. By
  -- `defect_nonpos_of_extreme_term` its defect is at most `0`, so its order plus `δ`-weight is
  -- below `v₀` as well, against the hypothesis.
  set ω : Fin k × ZMod N → ℝ := fun x ↦ δ x - T.defectWeight a a' i x / 3
  -- `(α, l) ∈ low`: in some translate the term at `α` has order at most `l`, and `l + ω · α < v₀`.
  let low : Set ((Fin k × ZMod N →₀ ℕ) × ℕ) := {x | x.2 + weight ω x.1 < v₀ ∧
    ∃ g ∈ rootSL W a a',
      ¬T.w ^ (x.2 + 1) ∣ (polynomialAction (blockDiagonal (T.letterMatrix · g)) f).coeff x.1}
  suffices h_empty : ¬low.Nonempty by
    simpa using T.polynomialAction_mem_of_forall_low le_rfl
      (fun α l h_lt h_g ↦ absurd ⟨(α, l), h_lt, h_g⟩ h_empty) (one_mem _)
  intro h_ne
  -- The degree of `f` bounds `α`, and `v₀` bounds `l`.
  have h_finite : low.Finite := by
    refine ((finite_of_degree_le f.totalDegree).biUnion fun α _ ↦
      (Set.finite_singleton α).prod (Set.finite_Iio ⌈v₀ - weight ω α⌉₊)).subset ?_
    rintro ⟨α, l⟩ ⟨h_lt, g, -, h_not⟩
    have h_degree : α.degree ≤ f.totalDegree :=
      (le_totalDegree (MvPolynomial.mem_support_iff.2 fun h_zero ↦ h_not (by simp [h_zero]))).trans
        (totalDegree_polynomialAction_le (blockDiagonal (T.letterMatrix · g)) f)
    exact Set.mem_biUnion h_degree ⟨rfl, lt_ceil.2 (by linarith)⟩
  obtain ⟨⟨α, l⟩, ⟨h_lt, g₀, hg₀, h_not⟩, h_min⟩ :
      ∃ x ∈ low, ∀ y ∈ low, x.2 + weight ω x.1 ≤ y.2 + weight ω y.1 :=
    Set.exists_min_image low _ h_finite h_ne
  have h_defect : T.defect a a' i α ≤ 0 :=
    T.defect_nonpos_of_extreme_term i (T.sub_defectWeight_div_three_mem_Icc i h_step)
      (fun g hg ↦ by
        have h_mul := T.polynomialAction_letterMatrix_mul g g₀ f
        simpa [← h_mul] using T.polynomialAction_mem_of_forall_low h_lt.le
          (fun β m h_lt' h_g ↦ h_min (β, m) ⟨h_lt', h_g⟩) (mul_mem hg hg₀)) h_not
  have h_weight : weight ω α = weight δ α - T.defect a a' i α / 3 :=
    T.weight_sub_defectWeight_div_three a a' i δ α
  have h_depth : l < v₀ - weight δ α := by linarith
  exact h_not ((pow_dvd_pow _ (lt_ceil.2 h_depth)).trans
    (mem_adicFiltration_iff.1 (mem_gaussFiltration_iff.1 (hf g₀ hg₀) α)))

/-- **The root lemma over a field of characteristic `p`.** Let `R = K` be a field of characteristic
`p`, so that `w = 0`, and let the weights `δ` rise by `1` from `ū_s` to `u_s` in each letter (so
that `a ≠ a'`). If `x ^ α` occurs in `f` and every term of every translate of `f` by
`SL₂^{a,a'}(W)` has `δ`-weight at least `δ · α`, then the defect of `α` at any letter `i` along
`(a, a')` is at most `0`. -/
theorem defect_nonpos_of_least [NeZero N] {K : Type*} [Field K] (T : FrobeniusCycle W K N)
    [CharP K T.p] {a a' : Fin k} (i : ZMod N) {δ : Fin k × ZMod N → ℝ}
    (h_step : ∀ s, δ (T.posIndex a a' s, s) - δ (T.negIndex a a' s, s) = 1)
    {f : MvPolynomial (Fin k × ZMod N) K} {α : Fin k × ZMod N →₀ ℕ}
    (h_least : ∀ g ∈ rootSL W a a', ∀ β,
      (polynomialAction (blockDiagonal (T.letterMatrix · g)) f).coeff β ≠ 0 →
        weight δ α ≤ weight δ β)
    (hα : f.coeff α ≠ 0) : T.defect a a' i α ≤ 0 := by
  have w_zero : T.w = 0 := (pow_eq_zero_iff two_ne_zero).1 (T.w_sq.trans (CharP.cast_eq_zero K _))
  refine T.defect_nonpos_of_extreme_term i (c := δ) (l := 0) (fun s ↦ by norm_num [h_step])
    (fun g hg ↦ mem_gaussFiltration_iff.2 fun β ↦ mem_adicFiltration_of_nonpos fun hβ ↦ ?_)
    (by simpa [w_zero] using hα)
  simpa using h_least g hg β hβ

end FrobeniusCycle

end TauCeti
