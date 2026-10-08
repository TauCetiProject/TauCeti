/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Evaluation

/-!
# Lazard valuations at points over a base point

Let `f` be a polynomial in the variables `X₀, …, Xₙ` over a commutative ring `R`, and single out
the last variable `Xₙ`, which is the least significant one for the lexicographic order. Moving it
into the coefficients (`MvPolynomial.optionEquivRight` after renaming along `finSuccEquivLast`)
turns `f` into a polynomial `g` in the base variables `X₀, …, Xₙ₋₁` with coefficients in `R[Xₙ]`.
For a base point `α ∈ Rⁿ`, Lazard evaluation of `g` at the constant polynomials `C αᵢ` divides out
the base variables and leaves a univariate polynomial `q = g.lazardEval (C ∘ α)`, the Lazard
evaluation of `f` over `α`, which is nonzero when `f ≠ 0`; it records the removed base exponents
`u = g.lazardExponent (C ∘ α)`.

This file describes the Lazard invariants of `f` at a point `(α, β)` above `α`. The vector of
exponents removed by Lazard evaluation of `f`, and for `f ≠ 0` its Lazard valuation, is `u` with
the root multiplicity of `β` in `q` appended as last entry (`MvPolynomial.lazardExponent_snoc`,
`MvPolynomial.lazardValuation_snoc`). The Lazard evaluation of `f` at `(α, β)` is obtained from
`q` by one more step of division: it is the trailing coefficient of the Taylor expansion of `q` at
`β` (`MvPolynomial.lazardEval_snoc`); for `f ≠ 0` this is its lowest nonzero coefficient, and for
`f = 0` both sides are `0`.

So, for `f ≠ 0`, at the points of a root section `β = θ(α)` of the Lazard evaluations `q`, the
Lazard valuation of `f` is the removed base exponent vector followed by the multiplicity of the
root, and in a sector between root sections it is the removed base exponent vector followed by
`0`. Constancy of the removed base exponents and of the root multiplicities over a base set thus
makes the Lazard valuation of a nonzero `f` constant on each section and sector above it. This is
how Lazard's lifting theorem passes valuation-invariance from the base to the cylinder.

## Main results

* `MvPolynomial.lazardExponent_snoc`, `MvPolynomial.lazardValuation_snoc`: at `(α, β)` the
  removed exponents of `f`, and for `f ≠ 0` its Lazard valuation, are the removed exponents of `g`
  at `α`, followed by the root multiplicity of `β` in the Lazard evaluation of `g` at `α`.
* `MvPolynomial.lazardEval_snoc`: the Lazard evaluation of `f` at `(α, β)` is the trailing
  coefficient of the Taylor expansion at `β` of the Lazard evaluation of `g` at `α`.
* `MvPolynomial.coeff_lazardEval_optionEquivRight_rename_finSuccEquivLast`: the coefficients of
  the Lazard evaluation of `g` at `α` are Taylor coefficients of `f` at `(α, 0)`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 2.
-/

public section

open Finsupp

namespace MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ} {f : MvPolynomial (Fin (n + 1)) R}

/-- The exponent obtained by appending the root multiplicity at `β` of the Lazard evaluation over
`α` to the base exponents removed there characterizes the Lazard invariants of `f` at
`Fin.snoc α β`: the Taylor coefficient of `f` at that exponent is nonzero, and those at
lexicographically smaller exponents vanish. -/
private theorem coeff_taylor_snoc_lazardExponent_ne_zero_and (hf : f ≠ 0) (α : Fin n → R)
    (β : R) :
    (taylor (Fin.snoc α β) f).coeff
        (snoc ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardExponent
          (Polynomial.C ∘ α))
        (((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardEval
          (Polynomial.C ∘ α)).rootMultiplicity β)) ≠ 0 ∧
      ∀ d, toLex d < toLex (snoc ((optionEquivRight R (Fin n)
          (rename finSuccEquivLast f)).lazardExponent (Polynomial.C ∘ α))
        (((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardEval
          (Polynomial.C ∘ α)).rootMultiplicity β)) →
        (taylor (Fin.snoc α β) f).coeff d = 0 := by
  set g := optionEquivRight R (Fin n) (rename finSuccEquivLast f)
  have hg : g ≠ 0 := (map_ne_zero_iff _ (optionEquivRight R (Fin n)).injective).2
    ((map_ne_zero_iff _ (rename_injective _ finSuccEquivLast.injective)).2 hf)
  refine ⟨?_, fun d hd ↦ ?_⟩
  · rw [coeff_taylor_snoc, coeff_taylor_lazardExponent, Polynomial.coeff_taylor_rootMultiplicity]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero β (lazardEval_ne_zero hg _)
  · rw [← snoc_init_self d, coeff_taylor_snoc]
    rw [← snoc_init_self d, toLex_snoc_lt_toLex_snoc_iff] at hd
    obtain hd | ⟨hd, hk⟩ := hd
    · -- the base exponent is below the removed one, so the whole coefficient in `Xₙ` vanishes
      rw [coeff_taylor_eq_zero_of_lt_lazardExponent hd, map_zero, Polynomial.coeff_zero]
    · -- the base exponent is the removed one, and `Xₙ ^ k` is below the root multiplicity
      rw [hd, coeff_taylor_lazardExponent]
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
        (by rwa [Polynomial.natTrailingDegree_taylor])

/-- **Lazard evaluation at a point over a base point.** The exponents removed by Lazard
evaluation of `f` at `Fin.snoc α β` are those removed over the base point `α`, after moving the
last variable into the coefficients, followed by the multiplicity of `β` as a root of the
resulting Lazard evaluation over `α`. -/
theorem lazardExponent_snoc (f : MvPolynomial (Fin (n + 1)) R) (α : Fin n → R) (β : R) :
    f.lazardExponent (Fin.snoc α β) =
      snoc ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardExponent
          (Polynomial.C ∘ α))
        (((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardEval
          (Polynomial.C ∘ α)).rootMultiplicity β) := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  exact (lazardExponent_eq_iff hf).2 (coeff_taylor_snoc_lazardExponent_ne_zero_and hf α β)

/-- **The Lazard valuation at a point over a base point.** For `f ≠ 0`, the Lazard valuation of
`f` at `Fin.snoc α β` is the vector of base exponents removed by Lazard evaluation over `α`, after
moving the last variable into the coefficients, with the multiplicity of `β` as a root of the
resulting Lazard evaluation over `α` appended. In particular it is the removed base exponents
followed by `0` when `β` is not a root. -/
theorem lazardValuation_snoc (hf : f ≠ 0) (α : Fin n → R) (β : R) :
    f.lazardValuation (Fin.snoc α β) =
      toLex (snoc ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardExponent
          (Polynomial.C ∘ α))
        (((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardEval
          (Polynomial.C ∘ α)).rootMultiplicity β)) :=
  lazardValuation_eq_coe_iff.2 (coeff_taylor_snoc_lazardExponent_ne_zero_and hf α β)

/-- The Lazard evaluation of `f` at `Fin.snoc α β` is the trailing coefficient of the Taylor
expansion at `β` of the Lazard evaluation over the base point `α`, after moving the last variable
into the coefficients. By `Polynomial.trailingCoeff_taylor`, this is one more step of Lazard's
successive division: divide by the largest power of `Xₙ - β` and evaluate at `β`. -/
theorem lazardEval_snoc (f : MvPolynomial (Fin (n + 1)) R) (α : Fin n → R) (β : R) :
    f.lazardEval (Fin.snoc α β) =
      (Polynomial.taylor β ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardEval
        (Polynomial.C ∘ α))).trailingCoeff := by
  rw [Polynomial.trailingCoeff_taylor, ← Polynomial.coeff_taylor_rootMultiplicity,
    ← coeff_taylor_lazardExponent, lazardExponent_snoc, coeff_taylor_snoc,
    coeff_taylor_lazardExponent]

/-- The coefficient of `Xₙ ^ k` in the Lazard evaluation of `f` over the base point `α`, after
moving the last variable into the coefficients, is the Taylor coefficient of `f` at
`Fin.snoc α 0` whose exponent is the vector of base exponents removed over `α` followed by `k`.
So over a set of base points where the removed exponents are constant, the coefficients of the
Lazard evaluations are polynomial functions of the base point. -/
theorem coeff_lazardEval_optionEquivRight_rename_finSuccEquivLast
    (f : MvPolynomial (Fin (n + 1)) R) (α : Fin n → R) (k : ℕ) :
    ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardEval
        (Polynomial.C ∘ α)).coeff k =
      (taylor (Fin.snoc α 0) f).coeff
        (snoc ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardExponent
          (Polynomial.C ∘ α)) k) := by
  rw [coeff_taylor_snoc, Polynomial.taylor_zero, coeff_taylor_lazardExponent]

/-- On a stratum with fixed removed base exponents, Lazard evaluation in the last variable
is specialization of a single polynomial family. Its coefficients are polynomial in the base
point, including where the ordinary fiber is nullified. The coefficient ring need not be a
domain. -/
theorem exists_polynomial_map_eq_lazardEval (f : MvPolynomial (Fin (n + 1)) R)
    (e : Fin n →₀ ℕ) :
    ∃ P : Polynomial (MvPolynomial (Fin n) R), ∀ α : Fin n → R,
      (optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardExponent
        (Polynomial.C ∘ α) = e →
      P.map (eval α) =
        (optionEquivRight R (Fin n) (rename finSuccEquivLast f)).lazardEval
          (Polynomial.C ∘ α) := by
  classical
  let T := taylor (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (map C f)
  let c (j : ℕ) : MvPolynomial (Fin n) R :=
    eval₂ C (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin n) R) X 0) (T.coeff (snoc e j))
  have hc (α : Fin n → R) (j : ℕ) :
      eval α (c j) = (taylor (Fin.snoc α 0) f).coeff (snoc e j) := by
    have hcoords :
        (fun i ↦ eval α (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin n) R) X 0 i)) =
          Fin.snoc α 0 := by
      ext i
      cases i using Fin.lastCases <;> simp
    have hC : (eval α).comp (C : R →+* MvPolynomial (Fin n) R) = RingHom.id R := by
      ext r
      simp
    simp only [c, eval_eval₂, hC, hcoords, eval₂_id, T,
      eval_coeff_taylor_map_C]
  refine ⟨∑ j ∈ Finset.range (f.degreeOf (Fin.last n) + 1), Polynomial.monomial j (c j),
    fun α hα ↦ Polynomial.ext fun j ↦ ?_⟩
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  rw [coeff_lazardEval_optionEquivRight_rename_finSuccEquivLast, hα]
  split_ifs with hj
  · exact hc α j
  · symm
    apply notMem_support_iff.1
    apply notMem_support_of_degreeOf_lt (Fin.last n)
    rw [degreeOf_taylor, snoc_last]
    omega

end MvPolynomial
