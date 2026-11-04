/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Basic
public import TauCeti.RingTheory.Valuation.Continuous.Basic

import Mathlib.Data.Finsupp.Lex
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.RingTheory.Huber.Continuous.ValuativeCriterion
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenIdeal
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded
import TauCeti.RingTheory.Valuation.LtAddSubgroup

/-!
# The unit-radius Gauss valuation on restricted multivariate power series

Let `v : Valuation A Γ₀` be a continuous valuation on a commutative nonarchimedean ring `A` taking
values in a linearly ordered commutative group with zero `Γ₀`. For a restricted power series
`f = ∑_ν a_ν X^ν` in the trivial-weight subring `A⟨X₁, …, Xₖ⟩`, only finitely many coefficients
can exceed any nonzero value attained by `v`, because `{a : A | v a < v b}` is an open additive
subgroup of `A` whenever `v b ≠ 0`. Consequently the set of coefficient values `{v(a_ν) | ν}` has a
greatest element in `Γ₀`, attained at some multi-index whenever `f` is not in the kernel of all
coefficient valuations, without any completeness hypothesis on `Γ₀`.

Taking this maximum defines the *unit-radius Gauss valuation* `W` on `A⟨X₁, …, Xₖ⟩`.
Multiplicativity follows by choosing the lexicographically least multi-indices at which `f` and `g`
attain their maximal coefficient valuations (`Lex (Fin k →₀ ℕ)`): at their sum `ν₀ + μ₀`, every
other summand in the Cauchy product has strictly smaller valuation, so the ultrametric equality
`W(f g) = W(f) W(g)` holds. Because `W(g)` is itself an attained value of `v`, the strict sublevel
set `{f | W f < W g}` for `W g ≠ 0` coincides with the open subgroup neighbourhood
`{a | v a < W g}⟨X⟩`, making `W` continuous.

As an application via Wedhorn's valuative criterion for integrality by continuous valuations
(`TauCeti.Huber.isIntegral_of_forall_continuous_valuation_le_one`), for any open integrally closed
subring `R` of a Huber ring `A`, the coefficientwise subring `R⟨X₁, …, Xₖ⟩` is already integrally
closed in `A⟨X₁, …, Xₖ⟩`: any element integral over `R⟨X⟩` has Gauss valuation at most `1` for
every continuous valuation bounded by `1` on `R`, so each of its coefficients is integral over `R`
and therefore lies in `R`. In particular, for any Huber pair `S = (A, A⁺)`, the plus ring of
`S.weighted isWeightFamily_one_weight` is `A⁺⟨X₁, …, Xₖ⟩` on the nose, with no integral closure
needed.

## Main definitions

* `TauCeti.Huber.weightedGaussValuation`: the unit-radius Gauss valuation on
  `weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight` extending
  a continuous valuation `v : Valuation A Γ₀`.

## Main results

* `TauCeti.Huber.weightedGaussValuation_le_iff`,
  `TauCeti.Huber.weightedGaussValuation_eq_zero_iff`, and
  `TauCeti.Huber.exists_coeff_eq_weightedGaussValuation`:
  the Gauss valuation is the attained maximum of the coefficient valuations.
* `TauCeti.Huber.isContinuous_weightedGaussValuation`: the Gauss valuation of a continuous
  valuation is continuous.
* `TauCeti.Huber.isIntegrallyClosedIn_weightedSubring_one_weight`: if `R` is an open integrally
  closed subring of a Huber ring `A`, then `R⟨X₁, …, Xₖ⟩` is integrally closed in `A⟨X₁, …, Xₖ⟩`.
* `TauCeti.Huber.isRingOfIntegralElements_weightedSubring_one_weight` and
  `TauCeti.Huber.Pair.weighted_plus_one_weight`: `A⁺⟨X₁, …, Xₖ⟩` is a ring of integral elements of
  `A⟨X₁, …, Xₖ⟩`, equal to `(S.weighted isWeightFamily_one_weight).plus`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48, Proposition 7.18(1), and
  Example 7.57.
* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477, Lemma 3.3.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Annals of Mathematics
  Studies 207 (2020), Lecture 4.
-/

public section

namespace TauCeti.Huber

open MvPowerSeries

section GaussValuation

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation A Γ₀}

/-- For a continuous valuation `v` and an element `b` with `v b ≠ 0`, only finitely many
coefficients of a unit-weight restricted series have valuation at least `v b`. -/
private theorem finite_coeff_ge_of_ne_zero (hv : v.IsContinuous)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
    {b : A} (hb : v b ≠ 0) :
    {ν : Fin k →₀ ℕ | v b ≤ v (coeff ν (f : MvPowerSeries (Fin k) A))}.Finite := by
  have hopen : IsOpen ((v.ltAddSubgroupOfNeZero hb : AddSubgroup A) : Set A) := by
    rw [v.coe_ltAddSubgroupOfNeZero hb]
    exact v.isContinuous_def.mp hv b
  let U : OpenAddSubgroup A := ⟨v.ltAddSubgroupOfNeZero hb, hopen⟩
  refine ((mem_weightedRestrictedSubring.mp f.2).finite_coeff_notMem U).subset fun ν hν ↦ ?_
  rw [Set.mem_ofPred_eq, weightMul_one_weight]
  intro hlt
  exact not_lt_of_ge hν ((v.mem_ltAddSubgroupOfNeZero hb).mp hlt)

/-- Every unit-weight restricted series has a greatest coefficient valuation in `Γ₀`, attained at
some multi-index whenever that greatest value is nonzero. -/
private theorem exists_greatest_coeff_val (hv : v.IsContinuous)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ∃ γ : Γ₀, (∀ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) ≤ γ) ∧
      (γ ≠ 0 → ∃ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) = γ) := by
  classical
  by_cases h : ∃ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) ≠ 0
  · obtain ⟨ν₀, hν₀⟩ := h
    have hfin := finite_coeff_ge_of_ne_zero hv f hν₀
    have hne : hfin.toFinset.Nonempty := ⟨ν₀, hfin.mem_toFinset.mpr le_rfl⟩
    obtain ⟨νₘ, _, hmax⟩ :=
      Finset.exists_max_image hfin.toFinset
        (fun ν ↦ v (coeff ν (f : MvPowerSeries (Fin k) A))) hne
    refine ⟨v (coeff νₘ (f : MvPowerSeries (Fin k) A)), fun ν ↦ ?_, fun _ ↦ ⟨νₘ, rfl⟩⟩
    by_cases hle : v (coeff ν₀ (f : MvPowerSeries (Fin k) A)) ≤
        v (coeff ν (f : MvPowerSeries (Fin k) A))
    · exact hmax ν (hfin.mem_toFinset.mpr hle)
    · exact (lt_of_not_ge hle).le.trans (hmax ν₀ (hfin.mem_toFinset.mpr le_rfl))
  · push Not at h
    exact ⟨0, fun ν ↦ by simp [h ν], fun h0 ↦ absurd rfl h0⟩

/-- Auxiliary function extracting the greatest coefficient valuation of a restricted series. -/
private noncomputable def weightedGaussValAux (hv : v.IsContinuous)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    Γ₀ :=
  (exists_greatest_coeff_val hv f).choose

private theorem coeff_le_weightedGaussValAux (hv : v.IsContinuous)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
    (ν : Fin k →₀ ℕ) :
    v (coeff ν (f : MvPowerSeries (Fin k) A)) ≤ weightedGaussValAux hv f :=
  (exists_greatest_coeff_val hv f).choose_spec.1 ν

private theorem exists_coeff_eq_weightedGaussValAux (hv : v.IsContinuous)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
    (hf : weightedGaussValAux hv f ≠ 0) :
    ∃ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) = weightedGaussValAux hv f :=
  (exists_greatest_coeff_val hv f).choose_spec.2 hf

private theorem weightedGaussValAux_le_iff (hv : v.IsContinuous)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    {γ : Γ₀} :
    weightedGaussValAux hv f ≤ γ ↔
      ∀ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) ≤ γ := by
  refine ⟨fun h ν ↦ (coeff_le_weightedGaussValAux hv f ν).trans h, fun h ↦ ?_⟩
  rcases eq_or_ne (weightedGaussValAux hv f) 0 with h0 | h0
  · simp [h0]
  · obtain ⟨ν, hν⟩ := exists_coeff_eq_weightedGaussValAux hv f h0
    exact hν ▸ h ν

/-- Whenever the auxiliary Gauss value of `f` is nonzero, there is a lexicographically least
multi-index at which `f` attains it. -/
private theorem exists_lex_min_coeff_eq_weightedGaussValAux (hv : v.IsContinuous)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hf : weightedGaussValAux hv f ≠ 0) :
    ∃ ν₀ : Fin k →₀ ℕ,
      v (coeff ν₀ (f : MvPowerSeries (Fin k) A)) = weightedGaussValAux hv f ∧
      ∀ ν, toLex ν < toLex ν₀ →
        v (coeff ν (f : MvPowerSeries (Fin k) A)) < weightedGaussValAux hv f := by
  classical
  obtain ⟨ν₁, hν₁⟩ := exists_coeff_eq_weightedGaussValAux hv f hf
  have hν₁_ne : v (coeff ν₁ (f : MvPowerSeries (Fin k) A)) ≠ 0 := by rwa [hν₁]
  have hfin : {ν : Fin k →₀ ℕ |
      v (coeff ν (f : MvPowerSeries (Fin k) A)) = weightedGaussValAux hv f}.Finite :=
    (finite_coeff_ge_of_ne_zero hv f hν₁_ne).subset fun ν hν ↦ by
      simp only [Set.mem_ofPred_eq] at hν ⊢
      rw [hν₁, hν]
  have hne : hfin.toFinset.Nonempty := ⟨ν₁, hfin.mem_toFinset.mpr hν₁⟩
  obtain ⟨ν₀, hν₀S, hmin⟩ := Finset.exists_min_image hfin.toFinset toLex hne
  refine ⟨ν₀, hfin.mem_toFinset.mp hν₀S, fun ν hlt ↦ ?_⟩
  refine lt_of_le_of_ne (coeff_le_weightedGaussValAux hv f ν) fun heq ↦ ?_
  exact not_le_of_gt hlt (hmin ν (hfin.mem_toFinset.mpr heq))

private theorem weightedGaussValAux_mul (hv : v.IsContinuous)
    (f g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    weightedGaussValAux hv (f * g) = weightedGaussValAux hv f * weightedGaussValAux hv g := by
  refine le_antisymm ((weightedGaussValAux_le_iff hv).mpr fun ν ↦ ?_) ?_
  · rw [Subring.coe_mul, coeff_mul]
    refine v.map_sum_le fun p _ ↦ ?_
    rw [map_mul]
    exact mul_le_mul' (coeff_le_weightedGaussValAux hv f p.1)
      (coeff_le_weightedGaussValAux hv g p.2)
  · rcases eq_or_ne (weightedGaussValAux hv f) 0 with hf0 | hf0
    · simp [hf0]
    rcases eq_or_ne (weightedGaussValAux hv g) 0 with hg0 | hg0
    · simp [hg0]
    obtain ⟨ν₀, hν₀, hν₀_min⟩ := exists_lex_min_coeff_eq_weightedGaussValAux hv hf0
    obtain ⟨μ₀, hμ₀, hμ₀_min⟩ := exists_lex_min_coeff_eq_weightedGaussValAux hv hg0
    have hprod_eq :
        v (coeff (ν₀ + μ₀) ((f * g :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          MvPowerSeries (Fin k) A)) =
          weightedGaussValAux hv f * weightedGaussValAux hv g := by
      have hmem : (ν₀, μ₀) ∈ Finset.antidiagonal (ν₀ + μ₀) := Finset.mem_antidiagonal.mpr rfl
      rw [Subring.coe_mul, coeff_mul, ← Finset.add_sum_erase _ _ hmem]
      have hlead :
          v (coeff ν₀ (f : MvPowerSeries (Fin k) A) *
              coeff μ₀ (g : MvPowerSeries (Fin k) A)) =
            weightedGaussValAux hv f * weightedGaussValAux hv g := by
        rw [v.map_mul, hν₀, hμ₀]
      rw [v.map_add_eq_of_lt_left, hlead]
      rw [hlead]
      refine v.map_sum_lt (mul_ne_zero hf0 hg0) fun p hp ↦ ?_
      obtain ⟨hpne, hsum⟩ := Finset.mem_erase.mp hp
      rw [Finset.mem_antidiagonal] at hsum
      rw [v.map_mul]
      have hlt : toLex p.1 < toLex ν₀ ∨ toLex p.2 < toLex μ₀ := by
        by_contra! hge
        refine hpne (Prod.ext (toLex.injective (hge.1.antisymm' ?_))
          (toLex.injective (hge.2.antisymm' ?_)))
        · exact le_of_add_le_add_right (a := toLex μ₀)
            ((add_le_add_right hge.2 _).trans_eq (by rw [← toLex_add, hsum, toLex_add]))
        · exact le_of_add_le_add_left (a := toLex ν₀)
            ((add_le_add_left hge.1 _).trans_eq (by rw [← toLex_add, hsum, toLex_add]))
      rcases hlt with hlt1 | hlt2
      · exact (mul_le_mul_right (coeff_le_weightedGaussValAux hv g p.2) _).trans_lt
          (mul_lt_mul_of_pos_right (hν₀_min p.1 hlt1) (zero_lt_iff.mpr hg0))
      · exact (mul_le_mul_left (coeff_le_weightedGaussValAux hv f p.1) _).trans_lt
          (mul_lt_mul_of_pos_left (hμ₀_min p.2 hlt2) (zero_lt_iff.mpr hf0))
    exact hprod_eq ▸ coeff_le_weightedGaussValAux hv (f * g) (ν₀ + μ₀)

/-- **The unit-radius Gauss valuation on `A⟨X₁, …, Xₖ⟩`** extending a continuous valuation `v` on
`A`, sending each restricted power series `f = ∑_ν a_ν X^ν` to `max_ν v(a_ν)`. -/
noncomputable def weightedGaussValuation (k : ℕ) (hv : v.IsContinuous) :
    Valuation
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) Γ₀ where
  toFun := weightedGaussValAux hv
  map_zero' := le_antisymm ((weightedGaussValAux_le_iff hv).mpr fun _ ↦ by simp) zero_le
  map_one' := by
    refine le_antisymm ((weightedGaussValAux_le_iff hv).mpr fun ν ↦ ?_) ?_
    · rw [Subring.coe_one, coeff_one]
      split_ifs <;> simp
    · simpa only [Subring.coe_one, coeff_zero_one, map_one] using
        coeff_le_weightedGaussValAux hv 1 0
  map_mul' := weightedGaussValAux_mul hv
  map_add_le_max' f g := (weightedGaussValAux_le_iff hv).mpr fun ν ↦ by
    rw [Subring.coe_add, map_add]
    exact (v.map_add _ _).trans
      (max_le_max (coeff_le_weightedGaussValAux hv f ν) (coeff_le_weightedGaussValAux hv g ν))

/-- Every coefficient of `f` has `v`-valuation at most `weightedGaussValuation k hv f`. -/
theorem coeff_le_weightedGaussValuation (hv : v.IsContinuous)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
    (ν : Fin k →₀ ℕ) :
    v (coeff ν (f : MvPowerSeries (Fin k) A)) ≤ weightedGaussValuation k hv f :=
  coeff_le_weightedGaussValAux hv f ν

/-- When `weightedGaussValuation k hv f ≠ 0`, the Gauss valuation is attained at some
multi-index. -/
theorem exists_coeff_eq_weightedGaussValuation (hv : v.IsContinuous)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hf : weightedGaussValuation k hv f ≠ 0) :
    ∃ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) = weightedGaussValuation k hv f :=
  exists_coeff_eq_weightedGaussValAux hv f hf

/-- `weightedGaussValuation k hv f ≤ γ` holds if and only if every coefficient of `f` has
valuation at most `γ`. -/
theorem weightedGaussValuation_le_iff (hv : v.IsContinuous)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    {γ : Γ₀} :
    weightedGaussValuation k hv f ≤ γ ↔
      ∀ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) ≤ γ :=
  weightedGaussValAux_le_iff hv

/-- The unit-radius Gauss valuation of `f` vanishes if and only if every coefficient of `f` lies in
the support of `v`. -/
@[simp]
theorem weightedGaussValuation_eq_zero_iff (hv : v.IsContinuous)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight} :
    weightedGaussValuation k hv f = 0 ↔
      ∀ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) = 0 := by
  simp only [← le_zero_iff, weightedGaussValuation_le_iff hv]

/-- Because the Gauss valuation is attained whenever it is nonzero, for `γ ≠ 0` the strict bound
`weightedGaussValuation k hv f < γ` is equivalent to the strict bound on every coefficient. -/
theorem weightedGaussValuation_lt_iff (hv : v.IsContinuous)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    {γ : Γ₀} (hγ : γ ≠ 0) :
    weightedGaussValuation k hv f < γ ↔
      ∀ ν, v (coeff ν (f : MvPowerSeries (Fin k) A)) < γ := by
  refine ⟨fun h ν ↦ (coeff_le_weightedGaussValuation hv f ν).trans_lt h, fun h ↦ ?_⟩
  rcases eq_or_ne (weightedGaussValuation k hv f) 0 with h0 | h0
  · exact h0.symm ▸ zero_lt_iff.mpr hγ
  · obtain ⟨ν, hν⟩ := exists_coeff_eq_weightedGaussValuation hv h0
    exact hν ▸ h ν

/-- On constants, the unit-radius Gauss valuation restricts to `v`. -/
@[simp]
theorem weightedGaussValuation_weightedC (hv : v.IsContinuous) (a : A) :
    weightedGaussValuation k hv (weightedC (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight a) = v a := by
  refine le_antisymm ((weightedGaussValuation_le_iff hv).mpr fun ν ↦ ?_) ?_
  · rw [coe_weightedC, coeff_C]
    split_ifs <;> simp
  · simpa only [coe_weightedC, coeff_zero_C] using
      coeff_le_weightedGaussValuation hv (weightedC _ isWeightFamily_one_weight a) 0

/-- Every coordinate variable `Xᵢ` has unit-radius Gauss valuation `1`. -/
@[simp]
theorem weightedGaussValuation_weightedX (hv : v.IsContinuous) (i : Fin k) :
    weightedGaussValuation k hv (weightedX (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight i) = 1 := by
  refine le_antisymm ((weightedGaussValuation_le_iff hv).mpr fun ν ↦ ?_) ?_
  · rw [coe_weightedX, coeff_X]
    split_ifs <;> simp
  · simpa [coe_weightedX, coeff_X] using
      coeff_le_weightedGaussValuation hv (weightedX _ isWeightFamily_one_weight i)
        (Finsupp.single i 1)

/-- Each monomial `a X^ν` has unit-radius Gauss valuation `v a`. -/
@[simp]
theorem weightedGaussValuation_monomial (hv : v.IsContinuous) (ν : Fin k →₀ ℕ) (a : A) :
    weightedGaussValuation k hv
      (weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
        (MvPolynomial.monomial ν a)) = v a := by
  refine le_antisymm ((weightedGaussValuation_le_iff hv).mpr fun μ ↦ ?_) ?_
  · rw [coe_weightedPolynomialHom, MvPolynomial.coeff_coe, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  · simpa [coe_weightedPolynomialHom, MvPolynomial.coeff_coe, MvPolynomial.coeff_monomial] using
      coeff_le_weightedGaussValuation hv
        (weightedPolynomialHom _ isWeightFamily_one_weight (MvPolynomial.monomial ν a)) ν

/-- **The unit-radius Gauss valuation of a continuous valuation is continuous.** For any series `g`
with nonzero Gauss valuation, that value equals `v b` for some coefficient `b` of `g`, so the
sublevel set `{f | W f < W g}` coincides with the open neighbourhood `{a | v a < v b}⟨X⟩`. -/
theorem isContinuous_weightedGaussValuation (hv : v.IsContinuous) :
    (weightedGaussValuation k hv).IsContinuous := by
  rw [Valuation.isContinuous_iff_forall_ne_zero]
  intro g hg
  obtain ⟨ν₀, hν₀⟩ := exists_coeff_eq_weightedGaussValuation hv hg
  have hb : v (coeff ν₀ (g : MvPowerSeries (Fin k) A)) ≠ 0 := by rwa [hν₀]
  have heq : {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight |
        weightedGaussValuation k hv f < weightedGaussValuation k hv g} =
      (weightedNhd (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
        (v.ltAddSubgroupOfNeZero hb) : Set _) := by
    ext f
    simp only [Set.mem_ofPred_eq, weightedGaussValuation_lt_iff hv hg, SetLike.mem_coe,
      mem_weightedNhd, weightMul_one_weight, Valuation.mem_ltAddSubgroupOfNeZero, hν₀]
  rw [heq]
  exact isOpen_weightedNhd isWeightFamily_one_weight
    (by simpa only [v.coe_ltAddSubgroupOfNeZero hb] using v.isContinuous_def.mp hv _)

end GaussValuation

/-! ### Integral closedness of `R⟨X₁, …, Xₖ⟩` in `A⟨X₁, …, Xₖ⟩` -/

section IntegrallyClosed

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- **If `R` is an open integrally closed subring of a Huber ring `A`, then `R⟨X₁, …, Xₖ⟩` is
integrally closed in `A⟨X₁, …, Xₖ⟩`.**

Given `f` integral over `R⟨X₁, …, Xₖ⟩` and a continuous valuation `v` on `A` bounded by `1` on `R`,
the Gauss valuation `W` extending `v` is bounded by `1` on `R⟨X₁, …, Xₖ⟩`. Since `W.integer` is
integrally closed (`Valuation.Integers.mem_of_integral`), `W f ≤ 1`, so every coefficient of `f`
has `v`-valuation at most `1`. By Wedhorn's Proposition 7.18(1)
(`TauCeti.Huber.isIntegral_of_forall_continuous_valuation_le_one`), every coefficient of `f` is
integral over `R`, hence lies in `R`. -/
theorem isIntegrallyClosedIn_weightedSubring_one_weight {R : Subring A}
    (hR : IsOpen (R : Set A)) [IsIntegrallyClosedIn R A] :
    IsIntegrallyClosedIn
      (weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R)
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro f hf
  rw [mem_weightedSubring, mem_weightedNhd]
  intro ν
  rw [weightMul_one_weight, Subring.mem_toAddSubgroup]
  refine Subring.isIntegrallyClosedIn_iff.mp ‹_› ?_
  refine isIntegral_of_forall_continuous_valuation_le_one hR fun w hw hwR ↦ ?_
  let W := weightedGaussValuation k (TauCeti.ValuationSpectrum.isContinuous_def w |>.mp hw)
  have hle : weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R ≤
      W.integer := by
    intro g hg
    rw [Valuation.mem_integer_iff, weightedGaussValuation_le_iff]
    intro μ
    have hgμ : coeff μ (g : MvPowerSeries (Fin k) A) ∈ R := by
      simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
        mem_weightedNhd.mp (mem_weightedSubring.mp hg) μ
    simpa only [map_one] using (TauCeti.ValuationSpectrum.valuation_le_iff w _ 1).mpr (hwR _ hgμ)
  let : Algebra (weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R)
      W.integer := (Subring.inclusion hle).toAlgebra
  have : IsScalarTower
      (weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R) W.integer
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hfW : f ∈ W.integer :=
    (Valuation.integer.integers W).mem_of_integral (IsIntegral.tower_top hf)
  have hcW : w.valuation (coeff ν (f : MvPowerSeries (Fin k) A)) ≤ 1 :=
    (coeff_le_weightedGaussValuation _ f ν).trans ((Valuation.mem_integer_iff W f).mp hfW)
  exact (TauCeti.ValuationSpectrum.valuation_le_iff w _ 1).mp (by simpa only [map_one] using hcW)

/-- **If `R` is a ring of integral elements of a Huber ring `A`, then `R⟨X₁, …, Xₖ⟩` is a ring of
integral elements of `A⟨X₁, …, Xₖ⟩`**, with no integral closure needed. -/
theorem isRingOfIntegralElements_weightedSubring_one_weight {R : Subring A}
    (hR : IsRingOfIntegralElements R) :
    IsRingOfIntegralElements
      (weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R) := by
  have := hR.isIntegrallyClosedIn
  exact
    { isOpen := isOpen_weightedSubring isWeightFamily_one_weight hR.isOpen
      le_powerBoundedSubring := weightedSubring_le_powerBoundedSubring isWeightFamily_one_weight
        hR.le_powerBoundedSubring
      isIntegrallyClosedIn := isIntegrallyClosedIn_weightedSubring_one_weight hR.isOpen }

/-- **For the trivial weight `{1}`, the plus ring of `S.weighted isWeightFamily_one_weight` is
`S.plus⟨X₁, …, Xₖ⟩` on the nose.** -/
theorem Pair.weighted_plus_one_weight (S : Pair A) :
    (S.weighted (k := k) isWeightFamily_one_weight).plus =
      weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight S.plus := by
  have := S.isRingOfIntegralElements.isIntegrallyClosedIn
  have := isIntegrallyClosedIn_weightedSubring_one_weight (k := k) S.isRingOfIntegralElements.isOpen
  refine le_antisymm ?_ (S.weightedSubring_le_weighted_plus isWeightFamily_one_weight)
  rw [Pair.weighted_plus, Subring.integralClosure_subring_le_iff]
  exact fun _ h ↦ h

end IntegrallyClosed

end TauCeti.Huber
