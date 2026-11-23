/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The trivial ideal weight and Dedekind zeta coefficients

This file identifies the norm coefficients of the trivial ideal weight with the coefficients of
the Dedekind zeta function.  There is one necessary exception: Mathlib's coefficient counts all
integral ideals and therefore has value `1` at index zero, contributed by the zero ideal, whereas
an `ArithmeticFunction` has value zero there.  Since `LSeries` ignores its zero coefficient, the
two coefficient systems define the same series.

Since `1 * 1 = 1` pointwise, the same identification shows that regrouping has no
pointwise-product formula as soon as some norm is attained by two ideals
(`TauCeti.not_forall_normCoeff_mul_eq_pmul`): the coefficient of the product is the ideal count,
not its square. `ℚ(i)`, with its two ideals of norm `5`, is such a field.

For the rational field the ring of integers is isomorphic to `ℤ`.  Mapping an ideal through this
isomorphism and using `Int.ideal_span_absNorm_eq_self` shows that there is exactly one ideal of
each positive norm.  Thus the trivial ideal weight over `ℚ` regroups to the constant coefficient
`1` at every positive index, so `dedekindZeta ℚ` is `LSeries 1` (`TauCeti.dedekindZeta_rat`) and
its residue at `s = 1` is `1` (`TauCeti.dedekindZeta_residue_rat`).

The exact abscissa of convergence of the trivial weight is not asserted here; it is
`TauCeti.abscissaOfAbsConv_normCoeff_one` in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The coefficient used in Mathlib's definition of the Dedekind zeta function: the number of
integral ideals of absolute norm `n`.

Unlike an `ArithmeticFunction`, this function has value `1` at zero, contributed by the zero
ideal. -/
noncomputable def dedekindZetaCoeff (n : ℕ) : ℕ :=
  Nat.card {I : _root_.Ideal (𝓞 K) // _root_.Ideal.absNorm I = n}

/-- The zero ideal is the unique integral ideal of absolute norm zero. -/
@[simp]
theorem dedekindZetaCoeff_zero : dedekindZetaCoeff K 0 = 1 := by
  simp [dedekindZetaCoeff, Ideal.absNorm_eq_zero_iff]

/-- The Dedekind zeta function is the `LSeries` of `dedekindZetaCoeff`. -/
theorem dedekindZeta_eq_LSeries_dedekindZetaCoeff (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s := by
  simp [NumberField.dedekindZeta, dedekindZetaCoeff]

private def normFiberSubtypeEquiv {n : ℕ} (hn : n ≠ 0) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n} where
  toFun I := ⟨I.val, I.property⟩
  invFun I :=
    ⟨⟨I.val, by
      rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
      exact fun hzero ↦ hn (I.property.symm.trans hzero)⟩, I.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Away from zero, the cardinality of the finite nonzero-ideal norm fibre is the corresponding
Dedekind zeta coefficient. -/
theorem card_normFiber_eq_dedekindZetaCoeff {n : ℕ} (hn : n ≠ 0) :
    (normFiber K n).card = dedekindZetaCoeff K n := by
  rw [← Nat.card_eq_finsetCard, dedekindZetaCoeff]
  exact Nat.card_congr <|
    (Equiv.subtypeEquivRight fun I ↦ mem_normFiber (K := K)).trans
      (normFiberSubtypeEquiv K hn)

/-- The trivial ideal arithmetic function regroups to the Dedekind zeta coefficients away from
zero.  At zero its norm coefficient is forced to vanish by the `ArithmeticFunction` carrier. -/
@[simp]
theorem normCoeff_one_apply (n : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) n =
      if n = 0 then 0 else dedekindZetaCoeff K n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, normCoeff_eq_sum_normFiber]
    simp [card_normFiber_eq_dedekindZetaCoeff K hn]

/-- The trivial unitary ideal weight has the Dedekind zeta coefficients away from zero. -/
theorem normCoeff_toIdealArithmeticFunction_one_apply (n : ℕ) :
    normCoeff K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction n =
      if n = 0 then 0 else dedekindZetaCoeff K n := by
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_one]
  exact normCoeff_one_apply K n

/-- Regrouping the trivial ideal weight gives Mathlib's Dedekind zeta function. -/
theorem dedekindZeta_eq_LSeries_normCoeff_one (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (normCoeff K (1 : IdealArithmeticFunction K)) s := by
  rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  apply LSeries_congr
  intro n hn
  rw [normCoeff_one_apply, ite_eq_right hn]

/-- **Regrouping does not turn pointwise products into pointwise products.** If two or more
integral ideals share the absolute norm `n`, then no formula
`normCoeff (f * g) = (normCoeff f).pmul (normCoeff g)` holds: already for `f = g = 1` the
`n`-th coefficient of `1 * 1 = 1` is the ideal count `dedekindZetaCoeff K n`, not its square. -/
theorem not_forall_normCoeff_mul_eq_pmul {n : ℕ} (hn : 1 < dedekindZetaCoeff K n) :
    ¬ ∀ f g : IdealArithmeticFunction K,
      normCoeff K (f * g) = (normCoeff K f).pmul (normCoeff K g) := by
  intro h
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have h1 := congrArg (· n) (h 1 1)
  simp only [mul_one, ArithmeticFunction.pmul_apply, normCoeff_one_apply, hn0, ite_false] at h1
  have h2 : dedekindZetaCoeff K n = dedekindZetaCoeff K n * dedekindZetaCoeff K n := by
    exact_mod_cast h1
  nlinarith

private theorem rat_normFiber_subsingleton (n : ℕ) :
    Subsingleton {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := by
  constructor
  intro I J
  apply Subtype.ext
  have hmap : I.val.map Rat.ringOfIntegersEquiv = J.val.map Rat.ringOfIntegersEquiv := by
    rw [← Int.ideal_span_absNorm_eq_self (I.val.map Rat.ringOfIntegersEquiv),
      ← Int.ideal_span_absNorm_eq_self (J.val.map Rat.ringOfIntegersEquiv),
      Ideal.absNorm_map_of_ringEquiv Rat.ringOfIntegersEquiv I.val,
      Ideal.absNorm_map_of_ringEquiv Rat.ringOfIntegersEquiv J.val, I.property, J.property]
  calc
    I.val = Ideal.comap Rat.ringOfIntegersEquiv (I.val.map Rat.ringOfIntegersEquiv) :=
      (Ideal.comap_map_of_bijective _ Rat.ringOfIntegersEquiv.bijective).symm
    _ = Ideal.comap Rat.ringOfIntegersEquiv (J.val.map Rat.ringOfIntegersEquiv) :=
      congrArg (Ideal.comap Rat.ringOfIntegersEquiv) hmap
    _ = J.val := Ideal.comap_map_of_bijective _ Rat.ringOfIntegersEquiv.bijective

private theorem rat_normFiber_nonempty (n : ℕ) :
    Nonempty {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := by
  refine ⟨⟨(Ideal.span {(n : ℤ)}).map Rat.ringOfIntegersEquiv.symm, ?_⟩⟩
  rw [Ideal.absNorm_map_of_ringEquiv, Ideal.absNorm_span_singleton]
  simp

/-- There is exactly one integral ideal of `ℚ` of each absolute norm. -/
@[simp]
theorem dedekindZetaCoeff_rat (n : ℕ) :
    dedekindZetaCoeff ℚ n = 1 := by
  let _ : Subsingleton {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} :=
    rat_normFiber_subsingleton n
  let _ : Nonempty {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := rat_normFiber_nonempty n
  exact Nat.card_unique

/-- Over `ℚ`, a nonzero integral ideal is the only one of its absolute norm. -/
@[simp]
theorem normFiber_rat_absNorm (I : (Ideal (𝓞 ℚ))⁰) :
    normFiber ℚ (Ideal.absNorm (I : Ideal (𝓞 ℚ))) = {I} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_normFiber ℚ).mpr rfl, fun J hJ ↦ ?_⟩
  have := rat_normFiber_subsingleton (Ideal.absNorm (I : Ideal (𝓞 ℚ)))
  have hJI := Subsingleton.elim
    (α := {I' : Ideal (𝓞 ℚ) // Ideal.absNorm I' = Ideal.absNorm (I : Ideal (𝓞 ℚ))})
    ⟨J, (mem_normFiber ℚ).mp hJ⟩ ⟨I, rfl⟩
  exact Subtype.ext (Subtype.mk.inj hJI)

/-- Over `ℚ`, the trivial ideal weight has coefficient `1` at every positive integer. -/
theorem normCoeff_one_rat_apply {n : ℕ} (hn : 0 < n) :
    normCoeff ℚ (1 : IdealArithmeticFunction ℚ) n = 1 := by
  rw [normCoeff_one_apply, ite_eq_right hn.ne', dedekindZetaCoeff_rat]
  norm_num

/-- Over `ℚ`, the trivial unitary ideal weight has coefficient `1` at every positive integer. -/
theorem normCoeff_toIdealArithmeticFunction_one_rat_apply {n : ℕ} (hn : 0 < n) :
    normCoeff ℚ (1 : UnitaryIdealWeight ℚ).toIdealArithmeticFunction n = 1 := by
  rw [normCoeff_toIdealArithmeticFunction_one_apply, ite_eq_right hn.ne', dedekindZetaCoeff_rat]
  norm_num

/-- Over `ℚ`, the Dedekind zeta function is `LSeries 1`, the Dirichlet series with constant
coefficient `1`. -/
@[simp]
theorem dedekindZeta_rat (s : ℂ) : NumberField.dedekindZeta ℚ s = LSeries 1 s := by
  rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  exact congrArg (LSeries · s) (funext fun n ↦ by simp)

/-- The Dedekind zeta function of `ℚ` has residue `1` at `s = 1`. -/
@[simp]
theorem dedekindZeta_residue_rat : NumberField.dedekindZeta_residue ℚ = 1 := by
  have hsum : Filter.Tendsto (fun n : ℕ ↦ (∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) / (n : ℝ))
      Filter.atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
    simp [hn0]
  have hL := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg (fun _ ↦ (1 : ℝ)) hsum
    fun _ ↦ zero_le_one
  have hζ : Filter.Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * NumberField.dedekindZeta ℚ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((1 : ℝ) : ℂ)) := by
    refine hL.congr fun s ↦ ?_
    rw [dedekindZeta_rat]
    exact congrArg (((s : ℂ) - 1) * LSeries · s) (funext fun _ ↦ by simp)
  exact Complex.ofReal_injective
    (tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT ℚ) hζ)

end TauCeti
