/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Count.Basic
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# The algebra of generating series of weighted counts

The generating series `TauCeti.NovikovSeries.countSeries e w` of a family of objects with classes
`e i : H` and weights `w i : R`, finitely many of nonzero weight below each period cutoff, is the
Novikov series `∑ᵢ w i e^(e i)` (see `TauCeti/RingTheory/NovikovSeries/Count/Basic.lean`). This
file relates it to the period topology and the ring structure.

In Floer theory the objects are the rigid solutions of a Floer-type equation between fixed
asymptotic data, `e i` is the class of a solution, `w i` its orientation sign, and the finiteness
hypothesis is Gromov–Floer compactness below an energy level: by the energy identity, the energy
of a solution is its period up to a bounded error. The generating series are the entries of the
matrices of Floer differentials, continuation maps and products in reference bases. The
identities between these matrices come from identities between moduli spaces: the boundary of a
one-dimensional moduli space is a set of broken configurations, and its signed count vanishes.
This file provides the algebra turning such identities into identities of generating series.

* **Lower support bound.** A lower bound on the periods of the objects of nonzero weight puts the
  series in the period filtration (`TauCeti.NovikovSeries.countSeries_mem_periodFiltration`).
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
  rw [coeff_sum_single, coeff_countSeries_eq_sum s fun i hi hw => hs ((hfin C).mem_toFinset.2
    ⟨hw, by rw [hi]; exact hh⟩)]

/-- The generating series is the infinite sum of its monomials. -/
theorem countSeries_eq_tsum : countSeries e w hfin = ∑' i, single (e i) (w i) :=
  hasSum_countSeries.tsum_eq.symm

/-- The generating series is additive in the weights. -/
theorem countSeries_add {w' : ι → R} (hfin' : ∀ C : ℝ, {i | w' i ≠ 0 ∧ N (e i) < C}.Finite) :
    countSeries e (fun i => w i + w' i) (finite_setOf_add_ne_zero_and_lt hfin hfin') =
      countSeries e w hfin + countSeries e w' hfin' :=
  hasSum_countSeries.unique (by
    simpa only [single_add] using (hasSum_countSeries (hfin := hfin)).add hasSum_countSeries)

/-- Reversing all weights, for instance all orientations, negates the generating series. -/
theorem countSeries_neg :
    countSeries e (fun i => -w i) (finite_setOf_neg_ne_zero_and_lt hfin) = -countSeries e w hfin :=
  hasSum_countSeries.unique (by
    simpa only [single_neg] using (hasSum_countSeries (hfin := hfin)).neg)

/-- The generating series does not depend on how the objects are indexed. -/
theorem countSeries_comp_equiv (σ : κ ≃ ι) :
    countSeries (e ∘ σ) (w ∘ σ) (finite_setOf_comp_ne_zero_and_lt (σ := σ) σ.injective hfin) =
      countSeries e w hfin :=
  hasSum_countSeries.unique ((σ.hasSum_iff (f := fun i => single (e i) (w i))).2
    hasSum_countSeries)

/-- The generating series of a disjoint union is the sum of the generating series. -/
theorem countSeries_sumElim {e' : κ → H} {w' : κ → R}
    (hfin' : ∀ C : ℝ, {k | w' k ≠ 0 ∧ N (e' k) < C}.Finite) :
    countSeries (Sum.elim e e') (Sum.elim w w') (finite_setOf_sumElim_ne_zero_and_lt hfin hfin') =
      countSeries e w hfin + countSeries e' w' hfin' :=
  hasSum_countSeries.unique (HasSum.sum (f := fun x => single (Sum.elim e e' x) (Sum.elim w w' x))
    (hasSum_countSeries (hfin := hfin)) (hasSum_countSeries (hfin := hfin')))

/-- The generating series of a finite union is the sum of the generating series of its parts. -/
theorem sum_countSeries {β : Type*} [Fintype β] {γ : β → Type*} {e : ∀ b, γ b → H}
    {w : ∀ b, γ b → R} (hfin : ∀ b C, {i | w b i ≠ 0 ∧ N (e b i) < C}.Finite) :
    ∑ b, countSeries (e b) (w b) (hfin b) =
      countSeries (fun x : Σ b, γ b => e x.1 x.2) (fun x => w x.1 x.2)
        (finite_setOf_sigma_ne_zero_and_lt hfin) :=
  (((hasSum_countSeries (hfin := finite_setOf_sigma_ne_zero_and_lt hfin)).sigma
    fun _ => hasSum_countSeries).unique (hasSum_fintype _)).symm

/-- **Pushforward of a generating series.** Pushing a generating series forward along a
coefficient map `ρ` and a period-rescaling homomorphism `φ` gives the generating series of the
same objects, with classes mapped by `φ` and weights by `ρ`. -/
theorem map_countSeries [AddZeroClass H'] {N' : H' →+ ℝ} [AddCommGroup S] (ρ : R →+ S)
    (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) :
    map ρ φ hφ (countSeries e w hfin) = countSeries (fun i => φ (e i)) (fun i => ρ (w i))
      (finite_setOf_map_ne_zero_and_lt ρ φ hφ hfin) :=
  ((hasSum_countSeries (hfin := hfin)).map (map ρ φ hφ) (continuous_map ρ φ hφ)).unique (by
    simpa only [comp_def, map_single] using
      hasSum_countSeries (hfin := finite_setOf_map_ne_zero_and_lt ρ φ hφ hfin))

end AddCommGroup

section Product

section Finite

variable [AddZeroClass H] {N : H →+ ℝ} [MulZeroClass R] {e : ι → H} {w : ι → R}
  {e' : κ → H} {w' : κ → R}

/-- Only finitely many pairs of objects of nonzero weight product have total period below each
cutoff: this is the finiteness hypothesis for the generating series of the pairs. -/
theorem finite_setOf_mul_ne_zero_and_add_lt
    (hfin : ∀ C : ℝ, {i | w i ≠ 0 ∧ N (e i) < C}.Finite)
    (hfin' : ∀ C : ℝ, {k | w' k ≠ 0 ∧ N (e' k) < C}.Finite) (C : ℝ) :
    {p : ι × κ | w p.1 * w' p.2 ≠ 0 ∧ N (e p.1 + e' p.2) < C}.Finite :=
  (Set.Finite.setOf_and_add_lt hfin hfin' C).subset fun _ ⟨hw, hC⟩ =>
    ⟨⟨left_ne_zero_of_mul hw, right_ne_zero_of_mul hw⟩, by rwa [map_add] at hC⟩

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
