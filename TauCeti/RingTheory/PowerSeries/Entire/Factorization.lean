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
finite multiset `PowerSeries.zeroMultiset`, so the zeros of `f` form a countable set and any family
listing zeros with at most their multiplicities satisfies `‖α i‖ → ∞` cofinitely.

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
* `PowerSeries.IsEntire.finite_setOf_norm_le_of_encard_le_order_taylor`,
  `PowerSeries.IsEntire.tendsto_norm_cofinite_atTop_of_encard_le_order_taylor` and
  `PowerSeries.IsEntire.tendsto_norm_cofinite_atTop_of_injective_of_evalAt_eq_zero`: in any
  complete normed field extension, a family listing zeros of a nonzero entire series with at most
  their multiplicities has only finitely many terms in each bounded ball, so `‖α i‖ → ∞`
  cofinitely.
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

omit [CompleteSpace K] in
/-- **Finitely many zeros in each bounded ball, with multiplicity.** Let `f` be a nonzero entire
series over an ultrametric normed field `K` and `L` a complete normed field extension of `K`. If a
family `α : ι → L` repeats each value `α i` at most as often as its multiplicity as a zero of `f`
(the order of the Taylor translate at `α i`), then only finitely many indices satisfy `‖α i‖ ≤ r`.
Completeness of `K` is not needed, since the mapped series over `L` is itself entire and nonzero. -/
theorem finite_setOf_norm_le_of_encard_le_order_taylor {ι L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsEntire) (hf0 : f ≠ 0) {α : ι → L}
    (hα : ∀ i : ι, {j : ι | α j = α i}.encard ≤
      (_root_.PowerSeries.taylor (α i) (_root_.PowerSeries.map (algebraMap K L) f)).order)
    (r : ℝ) : {i : ι | ‖α i‖ ≤ r}.Finite := by
  classical
  have : IsUltrametricDist L := .of_normedAlgebra K
  set F : PowerSeries L := _root_.PowerSeries.map (algebraMap K L) f
  have hF : F.IsEntire := hf.map (algebraMap K L) (C := 1) fun a ↦ by rw [norm_algebraMap', one_mul]
  have hF0 : F ≠ 0 := fun h ↦ hf0 <| _root_.PowerSeries.ext fun n ↦
    (map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).mp
      (by simpa [F] using congrArg (_root_.PowerSeries.coeff n) h)
  have hFid : _root_.PowerSeries.map (algebraMap L L) F = F := by ext n; simp
  set R : ℝ := max r 1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hcount : ∀ i, ‖α i‖ ≤ R → {j : ι | α j = α i}.encard ≤ (F.zeroMultiset R L).count (α i) := by
    intro i hi
    have ho := (hF.isRestricted R).order_taylor_eq_count_zeroMultiset (L := L) hR0 hF0 hi
    rw [hFid] at ho
    exact (hα i).trans_eq ho
  refine ((F.zeroMultiset R L).toFinset.finite_toSet.biUnion (t := fun x ↦ {j : ι | α j = x})
      fun x hx ↦ ?_).subset fun i hi ↦ ?_
  · rcases Set.eq_empty_or_nonempty {j : ι | α j = x} with he | ⟨i, rfl⟩
    · simp [he]
    · have hiR : ‖α i‖ ≤ R :=
        _root_.PowerSeries.norm_le_of_mem_zeroMultiset (Multiset.mem_toFinset.mp hx)
      exact Set.encard_lt_top_iff.mp ((hcount i hiR).trans_lt (ENat.natCast_lt_top _))
  · have hiR : ‖α i‖ ≤ R := hi.trans (le_max_left r 1)
    have h1 : (1 : ℕ∞) ≤ {j : ι | α j = α i}.encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨i, rfl⟩
    have hc : 0 < (F.zeroMultiset R L).count (α i) := by
      exact_mod_cast h1.trans (hcount i hiR)
    exact Set.mem_biUnion (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hc)) rfl

omit [CompleteSpace K] in
/-- **Zero-norm growth, with multiplicity.** Let `f` be a nonzero entire series over an ultrametric
normed field `K` and `L` a complete normed field extension of `K`. For any family `α : ι → L`
repeating each point at most as often as its multiplicity as a zero of `f`, `‖α i‖ → ∞` along the
cofinite filter (and in particular as `n → ∞` when `ι = ℕ`, via `Nat.cofinite_eq_atTop`). -/
theorem tendsto_norm_cofinite_atTop_of_encard_le_order_taylor {ι L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsEntire) (hf0 : f ≠ 0) {α : ι → L}
    (hα : ∀ i : ι, {j : ι | α j = α i}.encard ≤
      (_root_.PowerSeries.taylor (α i) (_root_.PowerSeries.map (algebraMap K L) f)).order) :
    Tendsto (fun i ↦ ‖α i‖) cofinite atTop :=
  tendsto_atTop.mpr fun r ↦ eventually_cofinite.mpr <|
    (hf.finite_setOf_norm_le_of_encard_le_order_taylor hf0 hα r).subset fun _ hi ↦ le_of_not_ge hi

omit [CompleteSpace K] in
/-- **Zero-norm growth for distinct zeros.** In any complete normed field extension `L` of an
ultrametric normed field `K`, an injective family `α : ι → L` of zeros of a nonzero entire series
satisfies `‖α i‖ → ∞` along the cofinite filter. -/
theorem tendsto_norm_cofinite_atTop_of_injective_of_evalAt_eq_zero {ι L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsEntire) (hf0 : f ≠ 0) {α : ι → L}
    (hinj : Function.Injective α)
    (hα : ∀ i : ι, (_root_.PowerSeries.map (algebraMap K L) f).evalAt (α i) = 0) :
    Tendsto (fun i ↦ ‖α i‖) cofinite atTop := by
  refine hf.tendsto_norm_cofinite_atTop_of_encard_le_order_taylor hf0 fun i ↦ ?_
  have hset : {j : ι | α j = α i} = {i} :=
    Set.ext fun j ↦ ⟨fun h ↦ hinj h, fun h ↦ congrArg α (Set.mem_singleton_iff.mp h)⟩
  rw [hset, Set.encard_singleton, Order.one_le_iff_ne_zero,
    _root_.PowerSeries.order_ne_zero_iff_constCoeff_eq_zero,
    _root_.PowerSeries.constantCoeff_taylor]
  exact hα i

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
