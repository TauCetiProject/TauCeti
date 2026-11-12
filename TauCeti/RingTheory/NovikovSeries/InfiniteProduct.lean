/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Northcott
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Filtered infinite products of Novikov series

A family of Novikov series has a convergent unordered product if,
below each period cutoff, only finitely many factors differ from one. The product
agrees below that cutoff with any finite product containing those exceptional
factors, provided all factors have nonnegative support. This makes infinite Euler
products computable by finite period windows, without discreteness or injectivity of the period map.

The factors need not be units. Only finitely many can have negative support; these
are separated off for the convergence theorem. Nonnegative support prevents
multiplication from lowering the period of an error in the cutoff formulas. The result
applies to principal units used in dynamical zeta products.

The main example is the *Euler product* `∏ᵢ (1 - r i e^(γ i)) ^ m i` over any commutative ring `R`,
for a family `γ : ι → H` of exponents of positive period, coefficients `r : ι → R` and integer
exponents `m : ι → ℤ`. It converges in the period topology when only finitely many periods
`N (γ i)` lie below each cutoff, since its factors are units of the nonnegative subring congruent
to `1` above the period `N (γ i)`. It is a unit with inverse the Euler product with exponents
`-m`, and it is natural in the coefficient ring and in exponent maps rescaling periods.

## Main definitions

* `TauCeti.NovikovSeries.eulerProduct`: the Euler product `∏ᵢ (1 - r i e^(γ i)) ^ m i`.

## Main results

* `TauCeti.NovikovSeries.multipliable_of_nonneg_finite_cutoffs`,
  `TauCeti.NovikovSeries.multipliable_of_finite_cutoffs`: convergence of products with finitely
  many factors differing from one below each cutoff.
* `TauCeti.NovikovSeries.tprod_sub_prod_mem_periodFiltration`,
  `TauCeti.NovikovSeries.coeff_tprod_eq_coeff_prod`: computing such products by finite cutoffs.
* `TauCeti.NovikovSeries.hasProd_eulerProduct`, `TauCeti.NovikovSeries.isUnit_eulerProduct`,
  `TauCeti.NovikovSeries.eulerProduct_sub_one_mem_periodFiltration`: convergence of the Euler
  product, which is a unit congruent to `1` above every lower bound of the periods.
* `TauCeti.NovikovSeries.mapRingHom_eulerProduct`: naturality of the Euler product.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.NovikovSeries

variable {R H ι : Type*} [CommRing R] [AddCommMonoid H] {N : H →+ ℝ}
  {f : ι → nonnegSubring R N} {C : ℝ}

/-- A finite product of nonnegative series congruent to one modulo `U_C` is
itself congruent to one modulo `U_C`. -/
theorem prod_sub_one_mem_periodFiltration (s : Finset ι)
    (hf : ∀ i ∈ s, (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C) :
    (∏ i ∈ s, (f i : NovikovSeries R H N)) - 1 ∈ periodFiltration R N C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have heq : (f i : NovikovSeries R H N) * (∏ j ∈ s, (f j : NovikovSeries R H N)) - 1 =
        (f i : NovikovSeries R H N) * ((∏ j ∈ s, (f j : NovikovSeries R H N)) - 1) +
          ((f i : NovikovSeries R H N) - 1) := by ring
    rw [heq]
    have hi0 := mem_periodFiltration.2 (mem_nonnegSubring.1 (f i).2)
    have hmul := mul_mem_periodFiltration hi0
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact add_mem (by simpa only [zero_add] using hmul) (hf i (Finset.mem_insert_self _ _))

/-- Adding factors congruent to one modulo `U_C` does not change a finite product
modulo `U_C`. -/
theorem prod_sub_prod_mem_periodFiltration {s t : Finset ι} (hst : s ⊆ t)
    (hf : ∀ i ∈ t, i ∉ s → (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C) :
    (∏ i ∈ t, (f i : NovikovSeries R H N)) - (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈
      periodFiltration R N C := by
  classical
  have hs : (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈ periodFiltration R N 0 :=
    mem_periodFiltration.2 (mem_nonnegSubring.1
      ((nonnegSubring R N).prod_mem fun i _ => (f i).2))
  have h := mul_mem_periodFiltration (prod_sub_one_mem_periodFiltration (t \ s)
    fun i hi => hf i (Finset.mem_sdiff.1 hi).1 (Finset.mem_sdiff.1 hi).2) hs
  simpa only [add_zero, sub_mul, one_mul, Finset.prod_sdiff hst] using h

/-- Nonnegative factors whose deviations from one escape each cutoff form a
multipliable family. The index type may be uncountable. -/
theorem multipliable_of_nonneg_finite_cutoffs
    (hf : ∀ C : ℝ, {i | (f i : NovikovSeries R H N) - 1 ∉ periodFiltration R N C}.Finite) :
    Multipliable (fun i => (f i : NovikovSeries R H N)) := by
  classical
  apply multipliable_iff_cauchySeq_finset.2
  refine hasBasis_uniformity.cauchySeq_iff.2 fun C _ => ?_
  let s := (hf C).toFinset
  have hs (t : Finset ι) (hst : s ⊆ t) :
      (∏ i ∈ t, (f i : NovikovSeries R H N)) - (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈
        periodFiltration R N C := by
    apply prod_sub_prod_mem_periodFiltration hst
    intro i _ hi
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
  refine ⟨s, fun t ht u hu => ?_⟩
  have h := sub_mem (hs u hu) (hs t ht)
  simpa using h

/-- An infinite filtered product agrees modulo `U_C` with any finite product
containing all factors that differ from one below `C`. -/
theorem tprod_sub_prod_mem_periodFiltration
    (hf : ∀ D : ℝ, {i | (f i : NovikovSeries R H N) - 1 ∉ periodFiltration R N D}.Finite)
    (s : Finset ι)
    (hs : ∀ i, i ∉ s → (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C) :
    (∏' i, (f i : NovikovSeries R H N)) - (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈
      periodFiltration R N C := by
  classical
  apply (isClosed_periodFiltration C).mem_of_tendsto
    ((multipliable_of_nonneg_finite_cutoffs hf).hasProd.sub_const _)
  filter_upwards [eventually_ge_atTop s] with t ht
  exact prod_sub_prod_mem_periodFiltration ht fun i _ hi => hs i hi

/-- Each coefficient of a filtered product can be computed from any finite cutoff
containing all factors that can affect that coefficient. -/
theorem coeff_tprod_eq_coeff_prod
    (hf : ∀ D : ℝ, {i | (f i : NovikovSeries R H N) - 1 ∉ periodFiltration R N D}.Finite)
    (s : Finset ι)
    (hs : ∀ i, i ∉ s → (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C)
    {h : H} (hh : N h < C) :
    (∏' i, (f i : NovikovSeries R H N)).coeff h =
      (∏ i ∈ s, (f i : NovikovSeries R H N)).coeff h := by
  have heq := mem_periodFiltration.1 (tprod_sub_prod_mem_periodFiltration hf s hs) h hh
  simpa only [coeff_sub, sub_eq_zero] using heq

/-- A family of arbitrary Novikov series has an unordered product if only finitely
many factors differ from one below each cutoff. No uniform lower bound on the
supports of all finite partial products is assumed. -/
theorem multipliable_of_finite_cutoffs {g : ι → NovikovSeries R H N}
    (hg : ∀ C : ℝ, {i | g i - 1 ∉ periodFiltration R N C}.Finite) : Multipliable g := by
  classical
  -- Separate the finitely many factors that can have negative support.
  let s := (hg 0).toFinset
  have hnonneg (i : ι) (hi : i ∉ s) : g i ∈ nonnegSubring R N := by
    have hdiff : g i - 1 ∈ periodFiltration R N 0 := by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
    have hsum := add_mem hdiff (one_mem_periodFiltration_zero (R := R) (N := N))
    exact mem_nonnegSubring.2 (mem_periodFiltration.1 (by simpa using hsum))
  let a : ι → nonnegSubring R N := fun i =>
    if hi : i ∉ s then ⟨g i, hnonneg i hi⟩ else 1
  let b : ι → NovikovSeries R H N := fun i => if i ∈ s then g i else 1
  have ha : Multipliable (fun i => (a i : NovikovSeries R H N)) := by
    apply multipliable_of_nonneg_finite_cutoffs
    intro C
    apply (hg C).subset
    intro i hi
    by_cases his : i ∈ s
    · simp [a, his] at hi
    · simpa [a, his] using hi
  have hb : Multipliable b := by
    apply multipliable_of_hasFiniteMulSupport
    exact s.finite_toSet.subset fun i hi => by
      by_contra his
      have his' : i ∉ s := his
      exact hi (by simp [b, his'])
  exact (ha.mul hb).congr fun i => by
    by_cases hi : i ∈ s <;> simp [a, b, hi]

section EulerProduct

variable {S : Type*} [CommRing S] {γ : ι → H}

variable (γ) in
/-- The **Euler product** `∏ᵢ (1 - r i e^(γ i)) ^ m i` of a family of exponents `γ i` of positive
period, with coefficients `r i` and integer exponents `m i`. It converges when only finitely many
periods `N (γ i)` lie below each cutoff (`TauCeti.NovikovSeries.hasProd_eulerProduct`). -/
def eulerProduct (hγ : ∀ i, 0 < N (γ i)) (r : ι → R) (m : ι → ℤ) : NovikovSeries R H N :=
  ∏' i, ((↑(unitsOneSubSingle (hγ i) (r i) ^ m i) : nonnegSubring R N) : NovikovSeries R H N)

variable {hγ : ∀ i, 0 < N (γ i)}

/-- Below each cutoff, only finitely many factors of the Euler product differ from `1`. -/
private theorem finite_cutoffs_eulerProduct (hfin : Tendsto (fun i => N (γ i)) cofinite atTop)
    (r : ι → R) (m : ι → ℤ) (D : ℝ) :
    {i | ((↑(unitsOneSubSingle (hγ i) (r i) ^ m i) : nonnegSubring R N) : NovikovSeries R H N) -
      1 ∉ periodFiltration R N D}.Finite :=
  (((northcott_iff_tendsto _).2 hfin).finite_le D).subset fun i hi => le_of_not_ge fun hD => hi <|
    antitone_periodFiltration hD <|
      coe_zpow_unitsOneSubSingle_sub_one_mem_periodFiltration (hγ i) (r i) (m i)

/-- The Euler product converges in the period topology when only finitely many periods lie below
each cutoff. -/
theorem hasProd_eulerProduct (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (r : ι → R)
    (m : ι → ℤ) :
    HasProd (fun i => ((↑(unitsOneSubSingle (hγ i) (r i) ^ m i) : nonnegSubring R N) :
      NovikovSeries R H N)) (eulerProduct γ hγ r m) :=
  (multipliable_of_nonneg_finite_cutoffs (finite_cutoffs_eulerProduct hfin r m)).hasProd

/-- The Euler product lies in the nonnegative subring. -/
theorem eulerProduct_mem_nonnegSubring (r : ι → R) (m : ι → ℤ) :
    eulerProduct γ hγ r m ∈ nonnegSubring R N :=
  tprod_mem isClosed_nonnegSubring fun i => (↑(unitsOneSubSingle (hγ i) (r i) ^ m i) :
    nonnegSubring R N).2

/-- The Euler product is congruent to `1` above every lower bound `c` of the periods. In
particular, when `c > 0`, its coefficients of period `< c`, so all those of nonpositive period,
are those of `1`. -/
theorem eulerProduct_sub_one_mem_periodFiltration
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) {c : ℝ} (hc : ∀ i, c ≤ N (γ i))
    (r : ι → R) (m : ι → ℤ) :
    eulerProduct γ hγ r m - 1 ∈ periodFiltration R N c := by
  have h := tprod_sub_prod_mem_periodFiltration (finite_cutoffs_eulerProduct hfin r m) ∅
    fun i _ => antitone_periodFiltration (hc i) <|
      coe_zpow_unitsOneSubSingle_sub_one_mem_periodFiltration (hγ i) (r i) (m i)
  simpa only [Finset.prod_empty, eulerProduct] using h

/-- The Euler product with all exponents `0` is `1`. -/
@[simp]
theorem eulerProduct_zero (r : ι → R) : eulerProduct γ hγ r 0 = 1 := by
  simp [eulerProduct]

/-- Euler products of the same factors multiply by adding exponents. -/
theorem eulerProduct_mul_eulerProduct (hfin : Tendsto (fun i => N (γ i)) cofinite atTop)
    (r : ι → R) (m m' : ι → ℤ) :
    eulerProduct γ hγ r m * eulerProduct γ hγ r m' = eulerProduct γ hγ r (m + m') := by
  rw [eulerProduct, eulerProduct, ← (hasProd_eulerProduct hfin r m).multipliable.tprod_mul
    (hasProd_eulerProduct hfin r m').multipliable, eulerProduct]
  simp [zpow_add]

/-- The Euler product is a unit. Its inverse is the Euler product with the opposite exponents, by
`TauCeti.NovikovSeries.eulerProduct_mul_eulerProduct`. -/
theorem isUnit_eulerProduct (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (r : ι → R)
    (m : ι → ℤ) : IsUnit (eulerProduct γ hγ r m) :=
  IsUnit.of_mul_eq_one _ <| by rw [eulerProduct_mul_eulerProduct hfin, add_neg_cancel,
    eulerProduct_zero]

/-- **Naturality of the Euler product.** The pushforward along a coefficient homomorphism `ρ` and
an exponent homomorphism `φ` rescaling periods by a positive constant sends the Euler product of
the factors `1 - r i e^(γ i)` to that of the factors `1 - ρ (r i) e^(φ (γ i))`, with the same
exponents. -/
theorem mapRingHom_eulerProduct {H' : Type*} [AddCommMonoid H'] {N' : H' →+ ℝ} (ρ : R →+* S)
    (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (hγ' : ∀ i, 0 < N' (φ (γ i)))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (r : ι → R) (m : ι → ℤ) :
    mapRingHom ρ φ hφ (eulerProduct γ hγ r m) =
      eulerProduct (fun i => φ (γ i)) hγ' (fun i => ρ (r i)) m := by
  rw [eulerProduct, (hasProd_eulerProduct hfin r m).multipliable.map_tprod _
    (continuous_mapRingHom ρ φ hφ), eulerProduct]
  refine tprod_congr fun i => ?_
  simp [← map_unitsOneSubSingle ρ φ hφ (hγ i) (hγ' i), ← map_zpow]

end EulerProduct

end TauCeti.NovikovSeries
