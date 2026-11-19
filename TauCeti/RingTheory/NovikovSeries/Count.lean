/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Generating series of weighted counts

Let `N : H →+ ℝ` be a period homomorphism and let `ι` index a family of objects, each with a class
`e i : H` and a weight `w i : R`. Suppose that only finitely many objects of nonzero weight have
period `N (e i)` below each cutoff. Then the weighted count `∑ᶠ i ∈ e ⁻¹' {h}, w i` in each class
`h` is a finite sum, and these counts are the coefficients of a Novikov series, the *generating
series* `∑ᵢ w i e^(e i)` of the family (`TauCeti.NovikovSeries.countSeries`).

In Floer theory the objects are the rigid solutions of a Floer-type equation between fixed
asymptotic data, `e i` is the class of a solution, `w i` its orientation sign, and the finiteness
hypothesis is Gromov–Floer compactness below an energy level: by the energy identity, the energy
of a solution is its period up to a bounded error. The generating series are the entries of the
matrices of Floer differentials, continuation maps and products in reference bases. The
identities between these matrices come from identities between moduli spaces: the boundary of a
one-dimensional moduli space is a set of broken configurations, and its signed count vanishes.
This file provides the algebra turning such identities into identities of generating series.

* **Coefficients and support.** A coefficient of `countSeries e w` is a finite sum over any finite
  set containing the fibre (`TauCeti.NovikovSeries.coeff_countSeries_eq_sum`), and its support
  consists of classes of objects of nonzero weight
  (`TauCeti.NovikovSeries.support_countSeries_subset`). So a lower bound on the periods of the
  objects puts the series in the period filtration
  (`TauCeti.NovikovSeries.countSeries_mem_periodFiltration`).
* **Cancellation.** If an involution pairs the objects, preserving the class and with weights
  adding to zero in each pair, and has no fixed point of nonzero weight, the generating series
  vanishes (`TauCeti.NovikovSeries.countSeries_eq_zero_of_involutive`). This is the count of the
  ends of a compact oriented one-manifold, paired along its components.
* **Sums of monomials.** The generating series is the sum, in the period topology, of the
  monomials `w i e^(e i)` (`TauCeti.NovikovSeries.hasSum_countSeries`). Consequently it is
  additive in the weights, invariant under reindexing, additive over disjoint unions
  (`TauCeti.NovikovSeries.countSeries_sumElim`) and over finite unions
  (`TauCeti.NovikovSeries.sum_countSeries`), and compatible with the pushforward along
  period-rescaling homomorphisms (`TauCeti.NovikovSeries.map_countSeries`).
* **Products.** The product of two generating series is the generating series of the pairs, with
  added classes and multiplied weights (`TauCeti.NovikovSeries.countSeries_mul_countSeries`). For
  matrices of generating series, an entry of the product is thus the count of the broken
  configurations formed by two consecutive pieces.

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

/-- Only finitely many objects of nonzero weight lie in each class. -/
private theorem finite_setOf_eq_and_ne_zero
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite) (h : H) :
    {i | e i = h ∧ w i ≠ 0}.Finite :=
  (hfin (N h + 1)).subset fun i ⟨hi, hw⟩ => ⟨hw, by rw [hi]; exact lt_add_one _⟩

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
  rw [coeff_countSeries_eq_sum Finset.univ fun i _ _ => Finset.mem_univ i, coeff_sum,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeff_single, Pi.single_apply]
    exact if_congr eq_comm rfl rfl

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
  set s := (finite_setOf_eq_and_ne_zero hfin h).toFinset
  have hmem {i : ι} : i ∈ s ↔ e i = h ∧ w i ≠ 0 := Set.Finite.mem_toFinset _
  rw [coeff_countSeries_eq_sum s fun i hi hw => hmem.2 ⟨hi, hw⟩, coeff_zero]
  refine Finset.sum_involution (fun i _ => τ i) (fun i _ => hw i) (fun i _ hi => hfix i hi)
    (fun i hi => ?_) fun i _ => hτ i
  obtain ⟨hs, hi⟩ := Finset.mem_filter.1 hi
  have hτs : e (τ i) = h := (he i).trans hi
  refine Finset.mem_filter.2 ⟨hmem.2 ⟨hτs, fun h0 => (hmem.1 hs).2 ?_⟩, hτs⟩
  simpa [h0] using hw i

end AddCommMonoid

section AddCommGroup

variable [AddZeroClass H] {N : H →+ ℝ} [AddCommGroup R] {e : ι → H} {w : ι → R}
  {hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite}

/-- **Lower support bound.** If every object of nonzero weight has period at least `C`, the
generating series lies in the period filtration at `C`. -/
theorem countSeries_mem_periodFiltration {C : ℝ} (hC : ∀ i, w i ≠ 0 → C ≤ N (e i)) :
    countSeries e w hfin ∈ periodFiltration R N C := mem_periodFiltration.2 fun _ hh => by
  by_contra hne
  obtain ⟨i, hw, rfl⟩ := support_countSeries_subset (mem_support.2 hne)
  exact (hC i hw).not_gt hh

/-- **The generating series is the sum of its monomials** `w i e^(e i)` in the period topology. -/
theorem hasSum_countSeries :
    HasSum (fun i => single (e i) (w i) : ι → NovikovSeries R H N) (countSeries e w hfin) := by
  classical
  refine tendsto_nhds_iff.2 fun C => ?_
  filter_upwards [Filter.eventually_ge_atTop (hfin C).toFinset] with s hs h hh
  rw [coeff_sum, coeff_countSeries_eq_sum s fun i hi hw => hs ((hfin C).mem_toFinset.2
    ⟨hw, by rw [hi]; exact hh⟩), Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeff_single, Pi.single_apply]
    exact if_congr eq_comm rfl rfl

/-- The generating series is the infinite sum of its monomials. -/
theorem countSeries_eq_tsum : countSeries e w hfin = ∑' i, single (e i) (w i) :=
  hasSum_countSeries.tsum_eq.symm

/-- The generating series is additive in the weights. -/
theorem countSeries_add {w' : ι → R} (hfin' : ∀ C : ℝ, {i | w' i ≠ 0 ∧ N (e i) < C}.Finite)
    (hfin'' : ∀ C : ℝ, {i | w i + w' i ≠ 0 ∧ N (e i) < C}.Finite) :
    countSeries e (fun i => w i + w' i) hfin'' = countSeries e w hfin + countSeries e w' hfin' :=
  hasSum_countSeries.unique (by
    simpa only [single_add] using (hasSum_countSeries (hfin := hfin)).add hasSum_countSeries)

/-- Reversing all weights, for instance all orientations, negates the generating series. -/
theorem countSeries_neg (hfin' : ∀ C : ℝ, {i | -w i ≠ 0 ∧ N (e i) < C}.Finite) :
    countSeries e (fun i => -w i) hfin' = -countSeries e w hfin :=
  hasSum_countSeries.unique (by
    simpa only [single_neg] using (hasSum_countSeries (hfin := hfin)).neg)

/-- The generating series does not depend on how the objects are indexed. -/
theorem countSeries_comp_equiv (σ : κ ≃ ι)
    (hfin' : ∀ C : ℝ, {k | w (σ k) ≠ 0 ∧ N (e (σ k)) < C}.Finite) :
    countSeries (e ∘ σ) (w ∘ σ) hfin' = countSeries e w hfin :=
  hasSum_countSeries.unique ((σ.hasSum_iff (f := fun i => single (e i) (w i))).2
    hasSum_countSeries)

/-- The generating series of a disjoint union is the sum of the generating series. -/
theorem countSeries_sumElim {e' : κ → H} {w' : κ → R}
    (hfin' : ∀ C : ℝ, {k | w' k ≠ 0 ∧ N (e' k) < C}.Finite)
    (hfin'' : ∀ C : ℝ, {x | Sum.elim w w' x ≠ 0 ∧ N (Sum.elim e e' x) < C}.Finite) :
    countSeries (Sum.elim e e') (Sum.elim w w') hfin'' =
      countSeries e w hfin + countSeries e' w' hfin' :=
  hasSum_countSeries.unique (HasSum.sum (f := fun x => single (Sum.elim e e' x) (Sum.elim w w' x))
    (hasSum_countSeries (hfin := hfin)) (hasSum_countSeries (hfin := hfin')))

/-- The generating series of a finite union is the sum of the generating series of its parts. -/
theorem sum_countSeries {β : Type*} [Fintype β] {γ : β → Type*} {e : ∀ b, γ b → H}
    {w : ∀ b, γ b → R} (hfin : ∀ b C, {i | w b i ≠ 0 ∧ N (e b i) < C}.Finite)
    (hfin' : ∀ C : ℝ, {x : Σ b, γ b | w x.1 x.2 ≠ 0 ∧ N (e x.1 x.2) < C}.Finite) :
    ∑ b, countSeries (e b) (w b) (hfin b) =
      countSeries (fun x : Σ b, γ b => e x.1 x.2) (fun x => w x.1 x.2) hfin' :=
  (((hasSum_countSeries (hfin := hfin')).sigma fun _ => hasSum_countSeries).unique
    (hasSum_fintype _)).symm

/-- **Pushforward of a generating series.** Pushing a generating series forward along a
coefficient map `ρ` and a period-rescaling homomorphism `φ` gives the generating series of the
same objects, with classes mapped by `φ` and weights by `ρ`. -/
theorem map_countSeries [AddZeroClass H'] {N' : H' →+ ℝ} [AddCommGroup S] (ρ : R →+ S)
    (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    (hfin' : ∀ C : ℝ, {i | ρ (w i) ≠ 0 ∧ N' (φ (e i)) < C}.Finite) :
    map ρ φ hφ (countSeries e w hfin) = countSeries (fun i => φ (e i)) (fun i => ρ (w i)) hfin' :=
  ((hasSum_countSeries (hfin := hfin)).map (map ρ φ hφ) (continuous_map ρ φ hφ)).unique (by
    simpa only [comp_def, map_single] using hasSum_countSeries (hfin := hfin'))

end AddCommGroup

section Product

section Finite

variable [AddZeroClass H] {N : H →+ ℝ} [MulZeroClass R] {e : ι → H} {w : ι → R}
  {e' : κ → H} {w' : κ → R}

/-- The periods of the objects of nonzero weight are bounded below. -/
private theorem exists_le_period
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite) :
    ∃ m : ℝ, ∀ i, w i ≠ 0 → m ≤ N (e i) := by
  obtain ⟨m, hm⟩ := ((hfin 0).image fun i => N (e i)).bddBelow
  refine ⟨min m 0, fun i hi => ?_⟩
  rcases lt_or_ge (N (e i)) 0 with h0 | h0
  · exact (min_le_left _ _).trans (hm ⟨i, ⟨hi, h0⟩, rfl⟩)
  · exact (min_le_right _ _).trans h0

/-- Only finitely many pairs of objects of nonzero weight product have total period below each
cutoff: this is the finiteness hypothesis for the generating series of the pairs. -/
theorem finite_setOf_mul_ne_zero_and_add_lt
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite)
    (hfin' : ∀ C : ℝ, {k | w' k ≠ 0 ∧ N (e' k) < C}.Finite) (C : ℝ) :
    {p : ι × κ | w p.1 * w' p.2 ≠ 0 ∧ N (e p.1 + e' p.2) < C}.Finite := by
  obtain ⟨m, hm⟩ := exists_le_period hfin
  obtain ⟨m', hm'⟩ := exists_le_period hfin'
  refine ((hfin (C - m')).prod (hfin' (C - m))).subset fun p ⟨hw, hC⟩ => ?_
  have h₁ := left_ne_zero_of_mul hw
  have h₂ := right_ne_zero_of_mul hw
  rw [map_add] at hC
  exact ⟨⟨h₁, by linarith [hm' p.2 h₂]⟩, ⟨h₂, by linarith [hm p.1 h₁]⟩⟩

end Finite

variable [AddMonoid H] {N : H →+ ℝ} [Ring R] {e : ι → H} {w : ι → R}
  {hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite} {e' : κ → H} {w' : κ → R}
  {hfin' : ∀ C : ℝ, {k | w' k ≠ 0 ∧ N (e' k) < C}.Finite}

/-- **The product of generating series** is the generating series of the pairs of objects, with
classes added and weights multiplied. For matrices of generating series, this identifies an entry
of the matrix product with the count of the configurations broken into two pieces. -/
theorem countSeries_mul_countSeries :
    countSeries e w hfin * countSeries e' w' hfin' =
      countSeries (fun p : ι × κ => e p.1 + e' p.2) (fun p => w p.1 * w' p.2)
        (finite_setOf_mul_ne_zero_and_add_lt hfin hfin') :=
  ((hasSum_countSeries (hfin := hfin)).mul_of_nonarchimedean
    (hasSum_countSeries (hfin := hfin'))).unique (by
      simpa only [single_mul_single] using
        hasSum_countSeries (hfin := finite_setOf_mul_ne_zero_and_add_lt hfin hfin'))

end Product

end TauCeti.NovikovSeries
