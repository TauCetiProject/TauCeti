/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.RingTheory.NovikovSeries.Basic

/-!
# Generating series of weighted counts

Let `N : H →+ ℝ` be a period homomorphism and let `ι` index a family of objects, each with a class
`e i : H` and a weight `w i : R`. Suppose that only finitely many objects of nonzero weight have
period `N (e i)` below each cutoff. Then the weighted count `∑ᶠ i ∈ e ⁻¹' {h}, w i` in each class
`h` is a finite sum, and these counts are the coefficients of a Novikov series, the *generating
series* `∑ᵢ w i e^(e i)` of the family (`TauCeti.NovikovSeries.countSeries`). The pushforward
`TauCeti.NovikovSeries.map` of a Novikov series is the generating series of its monomials, with
classes and weights mapped.

The cutoff finiteness hypothesis is stable under the operations on families: sums of weightings,
negation, reindexing, disjoint and finite unions, and mapping the classes by a period-rescaling
homomorphism (the `TauCeti.NovikovSeries.finite_setOf_*_ne_zero_and_lt` lemmas). It implies that
only finitely many objects of nonzero weight lie in each class
(`TauCeti.NovikovSeries.finite_setOf_ne_zero_and_eq`).

* **Coefficients and support.** A coefficient of `countSeries e w` is a finite sum over any finite
  set containing the fibre (`TauCeti.NovikovSeries.coeff_countSeries_eq_sum`), and its support
  consists of classes of objects of nonzero weight
  (`TauCeti.NovikovSeries.support_countSeries_subset`). Over finitely many objects the generating
  series is the finite sum of its monomials (`TauCeti.NovikovSeries.countSeries_eq_sum`).
* **Cancellation.** If an involution pairs the objects, preserving the class and with weights
  adding to zero in each pair, and has no fixed point of nonzero weight, the generating series
  vanishes (`TauCeti.NovikovSeries.countSeries_eq_zero_of_involutive`). This is the count of the
  ends of a compact oriented one-manifold, paired along its components.

The topological algebra of generating series (sums of monomials, unions, pushforward and
products) is in `TauCeti/RingTheory/NovikovSeries/Count.lean`.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open Function Set

namespace TauCeti.NovikovSeries

variable {R S H H' ι κ : Type*}

section Finite

/-! ### Cutoff finiteness of combined families -/

variable [AddZeroClass H] {N : H →+ ℝ} {e : ι → H}

/-- If only finitely many objects of nonzero weight lie below each cutoff, then only finitely many
lie in each class. -/
theorem finite_setOf_ne_zero_and_eq [Zero R] {w : ι → R}
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite) (h : H) :
    {i | w i ≠ 0 ∧ e i = h}.Finite :=
  (hfin (N h + 1)).subset fun i ⟨hw, hi⟩ => ⟨hw, by rw [hi]; exact lt_add_one _⟩

/-- If two weightings have finitely many objects of nonzero weight below each cutoff, so does
their sum. -/
theorem finite_setOf_add_ne_zero_and_lt [AddZeroClass R] {w w' : ι → R}
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite)
    (hfin' : ∀ C : ℝ, {i | w' i ≠ 0 ∧ N (e i) < C}.Finite) (C : ℝ) :
    {i | w i + w' i ≠ 0 ∧ N (e i) < C}.Finite :=
  ((hfin C).union (hfin' C)).subset fun _ ⟨hw, hC⟩ =>
    (not_and_or.1 fun h => hw (by rw [h.1, h.2, add_zero])).imp (⟨·, hC⟩) (⟨·, hC⟩)

/-- Negating the weights does not change which objects have nonzero weight. -/
theorem finite_setOf_neg_ne_zero_and_lt [SubtractionMonoid R] {w : ι → R}
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite) (C : ℝ) :
    {i | -w i ≠ 0 ∧ N (e i) < C}.Finite := by
  simpa only [neg_ne_zero] using hfin C

/-- Reindexing along an injective map preserves finiteness of the objects of nonzero weight below
each cutoff. -/
theorem finite_setOf_comp_ne_zero_and_lt [Zero R] {w : ι → R} {σ : κ → ι} (hσ : Injective σ)
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite) (C : ℝ) :
    {k | w (σ k) ≠ 0 ∧ N (e (σ k)) < C}.Finite :=
  (hfin C).preimage hσ.injOn

/-- The disjoint union of two families with finitely many objects of nonzero weight below each
cutoff has the same property. -/
theorem finite_setOf_sumElim_ne_zero_and_lt [Zero R] {w : ι → R} {e' : κ → H} {w' : κ → R}
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite)
    (hfin' : ∀ C : ℝ, {k | w' k ≠ 0 ∧ N (e' k) < C}.Finite) (C : ℝ) :
    {x | Sum.elim w w' x ≠ 0 ∧ N (Sum.elim e e' x) < C}.Finite :=
  (((hfin C).image Sum.inl).union ((hfin' C).image Sum.inr)).subset fun
    | .inl i, hi => Or.inl ⟨i, hi, rfl⟩
    | .inr k, hk => Or.inr ⟨k, hk, rfl⟩

/-- The union of finitely many families with finitely many objects of nonzero weight below each
cutoff has the same property. -/
theorem finite_setOf_sigma_ne_zero_and_lt [Zero R] {β : Type*} [Finite β] {γ : β → Type*}
    {e : ∀ b, γ b → H} {w : ∀ b, γ b → R}
    (hfin : ∀ b C, {i | w b i ≠ 0 ∧ N (e b i) < C}.Finite) (C : ℝ) :
    {x : Σ b, γ b | w x.1 x.2 ≠ 0 ∧ N (e x.1 x.2) < C}.Finite :=
  (finite_univ.sigma fun b _ => hfin b C).subset fun _ hx => ⟨mem_univ _, hx⟩

/-- Mapping the weights by `ρ` and the classes by a period-rescaling homomorphism `φ` preserves
finiteness of the objects of nonzero weight below each cutoff. -/
theorem finite_setOf_map_ne_zero_and_lt [AddZeroClass H'] {N' : H' →+ ℝ} [AddZeroClass R]
    [AddZeroClass S] {w : ι → R} (ρ : R →+ S) (φ : H →+ H')
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite) (C : ℝ) :
    {i | ρ (w i) ≠ 0 ∧ N' (φ (e i)) < C}.Finite := by
  obtain ⟨c, hc, hcφ⟩ := hφ
  exact (hfin (C / c)).subset fun i ⟨hw, hC⟩ =>
    ⟨fun h0 => hw (by rw [h0, map_zero]), (lt_div_iff₀' hc).2 (hcφ (e i) ▸ hC)⟩

end Finite

section AddCommMonoid

variable [AddZeroClass H] {N : H →+ ℝ} [AddCommMonoid R]

/-- **The generating series of a weighted family** `∑ᵢ w i e^(e i)`: its coefficient at `h` is the
weighted count `∑ᶠ i ∈ e ⁻¹' {h}, w i` of the objects of class `h`. It is defined when only
finitely many objects of nonzero weight have period below each cutoff. -/
def countSeries (e : ι → H) (w : ι → R) (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite) :
    NovikovSeries R H N where
  coeff h := ∑ᶠ i ∈ e ⁻¹' {h}, w i
  finite_lt C := ((hfin C).image e).subset fun h ⟨hh, hC⟩ => by
    obtain ⟨i, rfl : e i = h, hw⟩ := exists_ne_zero_of_finsum_mem_ne_zero hh
    exact ⟨i, ⟨hw, hC⟩, rfl⟩

variable {e : ι → H} {w : ι → R} {hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite}

@[simp]
theorem coeff_countSeries (h : H) :
    (countSeries e w hfin).coeff h = ∑ᶠ i ∈ e ⁻¹' {h}, w i :=
  (rfl)

/-- A coefficient of a generating series is the weighted count over any finite set of objects
containing those of nonzero weight in its class. -/
theorem coeff_countSeries_eq_sum [DecidableEq H] {h : H} (s : Finset ι)
    (hs : ∀ i, e i = h → w i ≠ 0 → i ∈ s) :
    (countSeries e w hfin).coeff h = ∑ i ∈ s with e i = h, w i := by
  rw [coeff_countSeries]
  refine finsum_mem_eq_sum_of_inter_support_eq _ (Set.ext fun i => ?_)
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, Finset.coe_filter, mem_ofPred_eq]
  exact ⟨fun ⟨hi, hw⟩ => ⟨⟨hs i hi hw, hi⟩, hw⟩, fun ⟨⟨_, hi⟩, hw⟩ => ⟨hi, hw⟩⟩

/-- Over finitely many objects the generating series is the finite sum of the monomials. -/
theorem countSeries_eq_sum [Fintype ι] : countSeries e w hfin = ∑ i, single (e i) (w i) := by
  classical
  ext h
  rw [coeff_countSeries_eq_sum Finset.univ fun i _ _ => Finset.mem_univ i, coeff_sum_single]

/-- Every class in the support of a generating series is the class of an object of nonzero
weight. -/
theorem support_countSeries_subset : (countSeries e w hfin).support ⊆ e '' {i | w i ≠ 0} :=
  fun _ hh => by
    obtain ⟨i, hi, hw⟩ := exists_ne_zero_of_finsum_mem_ne_zero (mem_support.1 hh)
    exact ⟨i, hw, hi⟩

/-- **Cancellation in pairs.** If an involution `τ` of the objects preserves classes, the weights
of `i` and `τ i` add up to zero, and no object of nonzero weight is fixed, then the generating
series vanishes. For the ends of a compact oriented one-dimensional moduli space, `τ` exchanges
the two ends of each component. -/
theorem countSeries_eq_zero_of_involutive {τ : ι → ι} (hτ : Involutive τ)
    (he : ∀ i, e (τ i) = e i) (hw : ∀ i, w i + w (τ i) = 0) (hfix : ∀ i, w i ≠ 0 → τ i ≠ i) :
    countSeries e w hfin = 0 := by
  classical
  ext h
  set s := (finite_setOf_ne_zero_and_eq hfin h).toFinset
  have hmem {i : ι} : i ∈ s ↔ w i ≠ 0 ∧ e i = h := Set.Finite.mem_toFinset _
  rw [coeff_countSeries_eq_sum s fun i hi hw => hmem.2 ⟨hw, hi⟩, coeff_zero]
  refine Finset.sum_involution (fun i _ => τ i) (fun i _ => hw i) (fun i _ hi => hfix i hi)
    (fun i hi => ?_) fun i _ => hτ i
  obtain ⟨hs, hi⟩ := Finset.mem_filter.1 hi
  have hτs : e (τ i) = h := (he i).trans hi
  refine Finset.mem_filter.2 ⟨hmem.2 ⟨fun h0 => (hmem.1 hs).1 ?_, hτs⟩, hτs⟩
  simpa [h0] using hw i

end AddCommMonoid

end TauCeti.NovikovSeries
