/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.DiscApproximation
public import TauCeti.RingTheory.PowerSeries.Weierstrass.ZeroCount

/-!
# Factorisation of entire series by their zeros

Let `K` be a complete ultrametric normed field and `f` an entire power series over `K`. In every
complete normed field extension of `K`, the zeros of a nonzero `f` in each closed disc form a
finite multiset `PowerSeries.zeroMultiset`, so the zeros of `f` form a countable set.

Suppose now that `K` is algebraically closed and `f(0) = 1`. The polynomial factor `P_r` of the
normalised preparation of `f` on the closed disc of radius `r` is then the product of the factors
`1 - α⁻¹ X` over the zeros `α` of `f` with `‖α‖ ≤ r`, counted with multiplicity, and these
polynomials converge to `f` in every Gauss norm as `r → ∞`. This is the product expansion

```text
f = ∏ (1 - X / α)
```

over the zeros of `f`, defined as the limit of its finite subproducts over closed discs. In
particular two entire series with constant coefficient `1` and the same zeros, counted with
multiplicity, are equal, and an entire series with only finitely many zeros is a polynomial.

These statements concern the whole affine line. On a disc of finite radius the zeros may
accumulate towards the boundary, and the corresponding products need not converge.

## Main results

* `PowerSeries.IsEntire.countable_setOf_evalAt_eq_zero`: a nonzero entire series has countably
  many zeros in every complete normed field extension.
* `PowerSeries.IsEntire.tendsto_gaussNorm_sub_prod_zeroMultiset` and
  `PowerSeries.IsEntire.tendsto_polynomialHom_prod_zeroMultiset`: the product expansion, in each
  Gauss norm and in the topology of entire series.
* `PowerSeries.IsEntire.eq_of_order_taylor_eq`: an entire series with constant coefficient `1` is
  determined by the multiplicities of its zeros.
* `PowerSeries.IsEntire.eq_prod_zeroMultiset_of_forall_norm_le` and
  `PowerSeries.IsEntire.exists_polynomial_eq_of_finite`: an entire series with finitely many zeros
  is a polynomial, namely the product over its zeros when `f(0) = 1`.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §4, in particular (4.13).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §4.
-/

public section

open Filter
open scoped Topology

namespace PowerSeries.IsEntire

open TauCeti.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {f g : PowerSeries K}

/-- **Countably many zeros.** A nonzero entire series over a complete ultrametric normed field `K`
has only countably many zeros in any complete normed field extension `L` of `K`: those in each
closed disc form the finite zero multiset of `f` on that disc. -/
theorem countable_setOf_evalAt_eq_zero {L : Type*} [NormedField L] [NormedAlgebra K L]
    [CompleteSpace L] (hf : f.IsEntire) (hf0 : f ≠ 0) :
    {x : L | (_root_.PowerSeries.map (algebraMap K L) f).evalAt x = 0}.Countable := by
  have hset : {x : L | (_root_.PowerSeries.map (algebraMap K L) f).evalAt x = 0} ⊆
      ⋃ n : ℕ, {x | x ∈ f.zeroMultiset (n + 1) L} := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact Set.mem_iUnion.mpr ⟨n, ((hf.isRestricted _).mem_zeroMultiset_iff (by positivity) hf0).mpr
      ⟨hn.trans (by linarith), hx⟩⟩
  exact (Set.countable_iUnion fun n : ℕ ↦
    (Multiset.finite_toSet (f.zeroMultiset (n + 1) L)).countable).mono hset

variable [IsAlgClosed K]

/-- The products over the zeros in closed discs are the polynomial factors of a family of
normalised disc preparations at every positive radius. -/
private theorem exists_isDiscPreparation_prod_zeroMultiset (hf : f.IsEntire)
    (h0 : constantCoeff f = 1) :
    ∃ (D : ℝ → ℕ) (U : ℝ → PowerSeries K), ∀ᶠ r in atTop,
      IsDiscPreparation r (D r) f ((f.zeroMultiset r K).map fun α ↦ 1 - Polynomial.C α⁻¹ *
        Polynomial.X).prod (U r) := by
  have hex (r : ℝ) : ∃ (D : ℕ) (U : PowerSeries K), 0 < r → IsDiscPreparation r D f
      ((f.zeroMultiset r K).map fun α ↦ 1 - Polynomial.C α⁻¹ * Polynomial.X).prod U := by
    by_cases hr : 0 < r
    · obtain ⟨D, U, h⟩ := (hf.isRestricted r).exists_isDiscPreparation_prod_zeroMultiset hr h0
      exact ⟨D, U, fun _ ↦ h⟩
    · exact ⟨0, 0, fun h ↦ absurd h hr⟩
  choose D U hDU using hex
  exact ⟨D, U, (eventually_gt_atTop 0).mono hDU⟩

/-- **Product expansion over the zeros, in each Gauss norm.** Let `f` be an entire series with
constant coefficient `1` over an algebraically closed complete ultrametric normed field `K`. As
`r → ∞`, the products of the factors `1 - α⁻¹ X` over the zeros `α` of `f` with `‖α‖ ≤ r`,
counted with multiplicity, converge to `f` in the Gauss norm of every positive radius `s`. -/
theorem tendsto_gaussNorm_sub_prod_zeroMultiset (hf : f.IsEntire) (h0 : constantCoeff f = 1)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r ↦ (f - (((f.zeroMultiset r K).map fun α ↦
      1 - Polynomial.C α⁻¹ * Polynomial.X).prod : Polynomial K)).gaussNorm norm s) atTop
      (𝓝 0) := by
  obtain ⟨D, U, h⟩ := exists_isDiscPreparation_prod_zeroMultiset hf h0
  exact tendsto_gaussNorm_sub_of_isDiscPreparation tendsto_id h hs

/-- **Product expansion over the zeros.** Let `f` be an entire series with constant coefficient `1`
over an algebraically closed complete ultrametric normed field `K`. As `r → ∞`, the products of the
factors `1 - α⁻¹ X` over the zeros `α` of `f` with `‖α‖ ≤ r`, counted with multiplicity, converge
to `f` in the topology of entire series:

```text
f = ∏ (1 - X / α).
```
-/
theorem tendsto_polynomialHom_prod_zeroMultiset (hf : f.IsEntire) (h0 : constantCoeff f = 1) :
    Tendsto (fun r ↦ IsEntire.polynomialHom ((f.zeroMultiset r K).map fun α ↦
      1 - Polynomial.C α⁻¹ * Polynomial.X).prod) atTop
      (𝓝 (⟨f, IsEntire.mem_subring.mpr hf⟩ : IsEntire.subring K)) := by
  obtain ⟨D, U, h⟩ := exists_isDiscPreparation_prod_zeroMultiset hf h0
  exact tendsto_polynomialHom_of_isDiscPreparation hf tendsto_id h

/-- **Entire series are determined by their zeros.** Over an algebraically closed complete
ultrametric normed field, two entire series with constant coefficient `1` whose zeros have the same
multiplicities, the orders of their Taylor translates, are equal. -/
theorem eq_of_order_taylor_eq (hf : f.IsEntire) (hg : g.IsEntire) (hf0 : constantCoeff f = 1)
    (hg0 : constantCoeff g = 1)
    (h : ∀ x : K, (_root_.PowerSeries.taylor x f).order = (_root_.PowerSeries.taylor x g).order) :
    f = g := by
  have hg0' : g ≠ 0 := by
    rintro rfl
    simp at hg0
  -- The zero multisets of `f` and `g` agree on every disc, so their product expansions agree.
  have hz : ∀ᶠ r in atTop, f.zeroMultiset r K = g.zeroMultiset r K := by
    filter_upwards [eventually_gt_atTop 0] with r hr
    classical
    refine _root_.PowerSeries.zeroMultiset_eq_of_order_taylor_eq
      (fun z hz ↦ _root_.PowerSeries.norm_le_of_mem_zeroMultiset hz) fun x hx ↦ ?_
    rw [← (hg.isRestricted r).order_taylor_eq_count_zeroMultiset hr hg0' hx]
    simpa using h x
  exact congrArg Subtype.val (tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto_polynomialHom_prod_zeroMultiset hf0)
    (hg.tendsto_polynomialHom_prod_zeroMultiset hg0)
    (hz.mono fun r hr ↦ by simp only [hr]))

/-- **Finitely many zeros, normalised form.** Let `f` be an entire series with constant coefficient
`1` over an algebraically closed complete ultrametric normed field. If all zeros of `f` lie in the
closed disc of radius `R`, then `f` is the product of the factors `1 - α⁻¹ X` over its zeros `α`,
counted with multiplicity. -/
theorem eq_prod_zeroMultiset_of_forall_norm_le (hf : f.IsEntire) (h0 : constantCoeff f = 1)
    {R : ℝ} (hR : ∀ x : K, f.evalAt x = 0 → ‖x‖ ≤ R) :
    f = (((f.zeroMultiset R K).map fun α ↦ 1 - Polynomial.C α⁻¹ * Polynomial.X).prod :
      Polynomial K) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  -- Beyond `R` the zero multisets, hence the product expansions, are constant.
  have hz : ∀ᶠ r in atTop, f.zeroMultiset r K = f.zeroMultiset R K := by
    filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop R] with r hr hRr
    rw [← (hf.isRestricted r).filter_zeroMultiset_eq hr hf0 hRr, eq_comm, Multiset.filter_eq_self]
    intro x hx
    have hx' := ((hf.isRestricted r).mem_zeroMultiset_iff hr hf0).mp hx
    exact hR x (by simpa using hx'.2)
  have := congrArg Subtype.val (tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto_polynomialHom_prod_zeroMultiset h0) (tendsto_const_nhds (x := IsEntire.polynomialHom
      ((f.zeroMultiset R K).map fun α ↦ 1 - Polynomial.C α⁻¹ * Polynomial.X).prod))
    (hz.mono fun r hr ↦ by simp only [hr]))
  rwa [coe_polynomialHom] at this

/-- **Entire series with finitely many zeros are polynomials.** Over an algebraically closed
complete ultrametric normed field, an entire series with only finitely many zeros is a
polynomial. -/
theorem exists_polynomial_eq_of_finite (hf : f.IsEntire) (hfin : {x : K | f.evalAt x = 0}.Finite) :
    ∃ p : Polynomial K, f = p := by
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  -- Write `f = Xⁿ g` with `g(0) ≠ 0`, normalise `g`, and apply the normalised form.
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (order_eq_top.not.mpr hf0)
  obtain ⟨hcoeff, hlt⟩ := order_eq_nat.mp hn.symm
  obtain ⟨g, hg, hfg⟩ := hf.exists_eq_X_sub_C_pow_mul (a := 0) (h := n) fun j hj ↦ by
    simpa [evalAt_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_hasseDeriv] using hlt j hj
  rw [map_zero, sub_zero] at hfg
  have hg0 : constantCoeff g ≠ 0 := by
    simpa [hfg, coeff_X_pow_mul'] using hcoeff
  set c := constantCoeff g
  have hgc : (C c⁻¹ * g).IsEntire := (isEntire_C _).mul hg
  obtain ⟨R, hR⟩ := (hfin.image (‖·‖)).bddAbove
  have hzero : ∀ x : K, (C c⁻¹ * g).evalAt x = 0 → ‖x‖ ≤ R := fun x hx ↦ by
    rw [(isEntire_C _).evalAt_mul hg, evalAt_C, Algebra.algebraMap_self_apply, mul_eq_zero,
      or_iff_right (inv_ne_zero hg0)] at hx
    refine hR ⟨x, ?_, rfl⟩
    rw [Set.mem_ofPred_eq, hfg, (isEntire_X.pow n).evalAt_mul hg, hx, mul_zero]
  have hp := hgc.eq_prod_zeroMultiset_of_forall_norm_le (by simp [c, hg0]) hzero
  refine ⟨Polynomial.X ^ n * Polynomial.C c * ((((C c⁻¹ * g).zeroMultiset R K).map fun α ↦
    1 - Polynomial.C α⁻¹ * Polynomial.X).prod), ?_⟩
  rw [Polynomial.coe_mul, ← hp, hfg]
  push_cast
  have hc : C c * C c⁻¹ = 1 := by
    rw [← map_mul]
    simp [hg0]
  linear_combination (-(X ^ n * g)) * hc

end PowerSeries.IsEntire
