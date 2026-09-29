/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Splitting

/-!
# The norm coefficient of `ℚ(i)` at `5`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² + 1`, the ideals
of absolute norm `5` are `(2 + θ)` and `(2 − θ)`
(`TauCeti.NumberField.GaussianRationals.absNorm_eq_five_iff`). So the Dedekind zeta function of
`ℚ(i)` has coefficient `2` at `5`, where the Riemann zeta function has `1`, and regrouping the
trivial ideal weight by norm gives the coefficient `2` there.

This is the smallest witness that regrouping by norm has no pointwise-product formula: the
pointwise product `1 * 1` of the trivial function with itself is `1`, whose coefficient at `5` is
`2`, not `2 · 2`.

## Main results

* `TauCeti.NumberField.GaussianRationals.dedekindZetaCoeff_five`: `ℚ(i)` has two integral
  ideals of absolute norm `5`.
* `TauCeti.NumberField.GaussianRationals.normCoeff_one_apply_five`: the trivial ideal
  arithmetic function regroups to the coefficient `2` at `5`.
* `TauCeti.NumberField.GaussianRationals.not_forall_normCoeff_mul_eq_pmul`: over `ℚ(i)`, the norm
  coefficients of a pointwise product are not the pointwise products of the norm coefficients.
-/

public section

open Polynomial NumberField Ideal
open scoped NumberField

namespace TauCeti.NumberField.GaussianRationals

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **`ℚ(i)` has two integral ideals of absolute norm `5`**, namely `(2 + θ)` and `(2 − θ)`. -/
theorem dedekindZetaCoeff_five (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : dedekindZetaCoeff K 5 = 2 := by
  have hfiber : (normFiber K 5).map (Function.Embedding.subtype _) =
      {span {2 + θ}, span {2 - θ}} := by
    ext J
    simp only [Finset.mem_map, mem_normFiber, Function.Embedding.subtype_apply,
      Finset.mem_insert, Finset.mem_singleton, ← absNorm_eq_five_iff hmin hgen]
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact hI
    · intro hJ
      exact ⟨⟨J, by rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors, hJ]; norm_num⟩, hJ, rfl⟩
  rw [← card_normFiber_eq_dedekindZetaCoeff K (by norm_num),
    ← Finset.card_map (Function.Embedding.subtype _), hfiber,
    Finset.card_pair (span_two_add_ne_span_two_sub hmin hgen)]

/-- The trivial ideal arithmetic function of `ℚ(i)` regroups to the coefficient `2` at `5`. -/
theorem normCoeff_one_apply_five (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    normCoeff K (1 : IdealArithmeticFunction K) 5 = 2 := by
  simp [dedekindZetaCoeff_five hmin hgen]

/-- **Over `ℚ(i)`, regrouping by norm has no pointwise-product formula.** The two ideals of
norm `5` give `normCoeff (1 * 1) 5 = 2`, while `(normCoeff 1).pmul (normCoeff 1)` is `4`
there. -/
theorem not_forall_normCoeff_mul_eq_pmul (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ¬ ∀ f g : IdealArithmeticFunction K,
      normCoeff K (f * g) = (normCoeff K f).pmul (normCoeff K g) :=
  TauCeti.not_forall_normCoeff_mul_eq_pmul K (n := 5) (by simp [dedekindZetaCoeff_five hmin hgen])

end TauCeti.NumberField.GaussianRationals
