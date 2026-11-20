/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import TauCeti.LowDimTopology.Heegaard.HatDifferential
public import TauCeti.LowDimTopology.Heegaard.StrongAdmissibility

/-!
# The combinatorial minus, infinity and plus differentials of a Heegaard diagram

The hat differential of a pointed Heegaard diagram (`TauCeti.HeegaardRegionSystem.hatDifferential`)
counts the nonnegative domains of Maslov index one that avoid the basepoint. The other flavors of
Heegaard Floer homology count all of them, and record the multiplicity `n_z(D)` of a domain at the
basepoint as the power of a formal variable `U`. This file sets up these counts for the abstract
region incidence data `TauCeti.HeegaardRegionSystem` with region Euler characteristics `χ`.

* The counted domains from `x` to `y`, `H.minusDomains χ x y`, are the nonnegative domains from
  `x` to `y` of Maslov index one, with any multiplicities at the basepoints. In a singly pointed
  diagram of a closed surface that is strongly admissible at `y` there are finitely many
  (`StronglyAdmissible.finite_minusDomains`).
* The coefficient `H.minusCoefficient χ x y : (ZMod 2)[X]` is the sum of `U ^ n_z(D)` over these
  domains, where `U = X` and `n_z(D)` is the total multiplicity of `D` at the basepoints. Its
  coefficient of `U ^ k` is the number of counted domains with `n_z(D) = k`, modulo two
  (`coeff_minusCoefficient`).
* The **minus differential** `H.minusDifferential χ` is the `(ZMod 2)[X]`-linear endomorphism of
  the free `(ZMod 2)[X]`-module `CF⁻` on the generators with these coefficients. Being
  `(ZMod 2)[X]`-linear, it commutes with the action of `U`.
* The **infinity differential** `H.infinityDifferential χ` is the same matrix acting on the free
  module `CF^∞` over the Laurent polynomials `(ZMod 2)[T;T⁻¹]`, in which `U` becomes invertible.
  The chains with polynomial coefficients form a `(ZMod 2)[X]`-submodule `H.minusLattice`, a copy
  of `CF⁻` on which the infinity differential restricts to the minus differential
  (`infinityDifferential_mapRange_toLaurent`). So the infinity differential preserves `CF⁻`, and
  descends to the quotient `CF⁺ = CF^∞ / CF⁻` as the **plus differential**
  `H.plusDifferential χ`.

The flavors are related to the hat differential and to the relative grading as follows.

* Setting `U = 0` turns the minus differential into the hat differential
  (`mapRange_constantCoeff_minusDifferential`): the domains with `n_z(D) = 0` are exactly those
  counted by the hat differential (`coeff_zero_minusCoefficient`). So reduction modulo `U`
  carries `CF⁻` onto `CF̂` and intertwines the two differentials.
* Grade `U ^ k y` by `gr(y) - 2 k`, so that `U` lowers the grading by two. A term `U ^ k y` of the
  minus differential of `x` comes from a domain `D` from `x` to `y` with `μ(D) = 1` and
  `n_z(D) = k`, so `gr(x, y) = μ(D) - 2 n_z(D) = 1 - 2 k`
  (`relativeGrading_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero`): the minus
  differential lowers this grading by one.

With several basepoints the multiplicities at all of them are recorded by the single variable `U`,
which is the version of the multipointed complex in which all the variables `U_i` are identified.

As for the hat differential, these are counts of domains rather than of holomorphic disks. They
agree with the holomorphic counts only for diagrams in which each counted domain carries exactly
one holomorphic disk modulo translation, and neither that condition nor the agreement is
formalized here; nor is `∂ ∘ ∂ = 0`. In an infinite set of counted domains the coefficient is `0`
by the convention of `finsum`, and the results below carry the finiteness hypotheses under which
the count has the properties listed.

Our `CF⁻` is spanned by the chains `U ^ k x` with `k ≥ 0`, so that `CF⁺` is spanned by the classes
of `U ^ k x` with `k < 0`. In the notation `[x, i] = U ^ (-i) x` of Ozsváth and Szabó, whose `CF⁻`
is spanned by the `[x, i]` with `i < 0`, the two versions of `CF⁻` differ by multiplication by
`U`, an isomorphism of complexes.

## Main definitions

* `TauCeti.HeegaardRegionSystem.minusDomains`: the nonnegative domains of Maslov index one from
  `x` to `y`.
* `TauCeti.HeegaardRegionSystem.minusCoefficient`: the sum of `U ^ n_z(D)` over them.
* `TauCeti.HeegaardRegionSystem.minusDifferential`: the differential of `CF⁻`.
* `TauCeti.HeegaardRegionSystem.infinityDifferential`: the differential of `CF^∞`.
* `TauCeti.HeegaardRegionSystem.minusLattice`: the copy of `CF⁻` in `CF^∞`.
* `TauCeti.HeegaardRegionSystem.plusDifferential`: the differential of `CF⁺ = CF^∞ / CF⁻`.

## Main results

* `TauCeti.HeegaardRegionSystem.StronglyAdmissible.finite_minusDomains`: strong admissibility
  makes the counts finite in a singly pointed diagram.
* `TauCeti.HeegaardRegionSystem.coeff_minusCoefficient` and
  `TauCeti.HeegaardRegionSystem.coeff_zero_minusCoefficient`: the coefficients of `U ^ k`, and
  the constant coefficient is the hat coefficient.
* `TauCeti.HeegaardRegionSystem.mapRange_constantCoeff_minusDifferential`: setting `U = 0` gives
  the hat differential.
* `HeegaardRegionSystem.relativeGrading_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero`
  and its version modulo the periodic Maslov indices: the minus differential lowers the grading
  by one.
* `TauCeti.HeegaardRegionSystem.infinityDifferential_mapRange_toLaurent`: the infinity
  differential restricts to the minus differential on `CF⁻`.
* `TauCeti.HeegaardRegionSystem.plusDifferential_mk`: the plus differential is induced by the
  infinity differential.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.1 (the complexes `CF^∞`, `CF⁻`,
  `CF⁺` and `CF̂`, and the action of `U`) and §4.2 (strong admissibility and the finiteness of the
  counts, Lemma 4.14).
-/

public section

open Polynomial LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section Lattice

variable (H) in
/-- The copy of `CF⁻` in `CF^∞`: the chains whose coefficients are polynomials in `U`, a
`(ZMod 2)[X]`-submodule of the free module on generators over `(ZMod 2)[T;T⁻¹]`. -/
noncomputable def minusLattice : Submodule (ZMod 2)[X] (H.Generator →₀ (ZMod 2)[T;T⁻¹]) :=
  LinearMap.range (Finsupp.mapRange.linearMap (Algebra.linearMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹]))

/-- A chain of `CF^∞` lies in `CF⁻` exactly when it is the image of a chain with polynomial
coefficients. -/
theorem mem_minusLattice_iff_exists {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]} :
    c ∈ H.minusLattice ↔ ∃ d : H.Generator →₀ (ZMod 2)[X],
      Finsupp.mapRange toLaurent (map_zero _) d = c := by
  have h : algebraMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹] = toLaurent := RingHom.ext algebraMap_eq_toLaurent
  simp only [minusLattice, LinearMap.mem_range, Finsupp.mapRange.linearMap_apply,
    Algebra.coe_linearMap, h]

/-- A chain of `CF^∞` lies in `CF⁻` exactly when each of its coefficients is a polynomial in
`U`. -/
theorem mem_minusLattice_iff {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]} :
    c ∈ H.minusLattice ↔ ∀ x, c x ∈ Set.range (toLaurent : (ZMod 2)[X] → (ZMod 2)[T;T⁻¹]) := by
  rw [mem_minusLattice_iff_exists, ← Set.mem_range, Finsupp.range_mapRange, Set.mem_ofPred_eq]

/-- The image of a chain with polynomial coefficients lies in `CF⁻`. -/
@[simp]
theorem mapRange_toLaurent_mem_minusLattice (d : H.Generator →₀ (ZMod 2)[X]) :
    Finsupp.mapRange toLaurent (map_zero _) d ∈ H.minusLattice :=
  mem_minusLattice_iff_exists.mpr ⟨d, rfl⟩

end Lattice

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

section Domains

variable (H) in
/-- The domains counted by the minus differential from the generator `x` to the generator `y`:
the nonnegative domains from `x` to `y` of Maslov index one, for the region Euler characteristics
`χ`, with any multiplicities at the basepoints. -/
def minusDomains (χ : Region → ℤ) (x y : H.Generator) : Set (Region → ℤ) :=
  {D | H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = 1}

variable {χ : Region → ℤ} {x y : H.Generator} {D : Region → ℤ}

@[simp]
theorem mem_minusDomains_iff : D ∈ H.minusDomains χ x y ↔
    H.IsDomainBetween x y D ∧ 0 ≤ D ∧ H.maslovIndex χ x y D = 1 :=
  Iff.rfl

/-- The domains counted by the hat differential are those counted by the minus differential
with multiplicity zero at every basepoint. -/
theorem hatDomains_eq_setOf_mem_minusDomains :
    H.hatDomains χ x y = {D ∈ H.minusDomains χ x y | ∀ z, D (H.basepoint z) = 0} := by
  ext D
  simp only [mem_hatDomains_iff, Set.mem_ofPred_eq, mem_minusDomains_iff]
  tauto

/-- Every domain counted by the hat differential is counted by the minus differential. -/
theorem hatDomains_subset_minusDomains : H.hatDomains χ x y ⊆ H.minusDomains χ x y := by
  rw [hatDomains_eq_setOf_mem_minusDomains]
  exact Set.sep_subset _ _

/-- In a singly pointed diagram of a closed surface of genus `n` that is strongly admissible at
`y`, only finitely many domains are counted by the minus differential from any generator to `y`,
whatever their multiplicity at the basepoint. -/
theorem StronglyAdmissible.finite_minusDomains [Subsingleton Basepoint]
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) (hH : H.StronglyAdmissible χ y)
    (x : H.Generator) : (H.minusDomains χ x y).Finite :=
  hH.finite_setOf_isDomainBetween_nonneg_index hχ x 1

end Domains

variable [Fintype Basepoint]

section Coefficient

variable (H) in
/-- The coefficient of the generator `y` in the minus differential of the generator `x`: the sum
of `U ^ n_z(D)`, with `U = X`, over the nonnegative domains `D` of Maslov index one from `x` to
`y`, where `n_z(D)` is the total multiplicity of `D` at the basepoints. This is meaningful when
the set `H.minusDomains χ x y` of these domains is finite, for instance in a singly pointed
diagram strongly admissible at `y` (`StronglyAdmissible.finite_minusDomains`); for an infinite set
the coefficient is `0`. -/
noncomputable def minusCoefficient (χ : Region → ℤ) (x y : H.Generator) : (ZMod 2)[X] :=
  ∑ᶠ D ∈ H.minusDomains χ x y, X ^ (∑ z, D (H.basepoint z)).toNat

variable {χ : Region → ℤ} {x y : H.Generator} {D : Region → ℤ}

theorem minusCoefficient_def : H.minusCoefficient χ x y =
    ∑ᶠ D ∈ H.minusDomains χ x y, X ^ (∑ z, D (H.basepoint z)).toNat :=
  (rfl)

/-- A counted domain has nonnegative total multiplicity at the basepoints. -/
theorem sum_basepoint_nonneg_of_mem_minusDomains (hD : D ∈ H.minusDomains χ x y) :
    0 ≤ ∑ z, D (H.basepoint z) :=
  Finset.sum_nonneg fun _ _ => (mem_minusDomains_iff.mp hD).2.1 _

/-- When finitely many domains are counted, the minus coefficient is a finite sum. -/
theorem minusCoefficient_eq_sum (hfin : (H.minusDomains χ x y).Finite) :
    H.minusCoefficient χ x y = ∑ D ∈ hfin.toFinset, X ^ (∑ z, D (H.basepoint z)).toNat :=
  finsum_mem_eq_finite_toFinset_sum _ hfin

/-- The coefficient of `U ^ k` in the minus coefficient from `x` to `y` is the number, modulo
two, of counted domains from `x` to `y` with total multiplicity `k` at the basepoints. -/
theorem coeff_minusCoefficient (hfin : (H.minusDomains χ x y).Finite) (k : ℕ) :
    (H.minusCoefficient χ x y).coeff k =
      {D ∈ H.minusDomains χ x y | ∑ z, D (H.basepoint z) = k}.ncard := by
  rw [minusCoefficient_eq_sum hfin, finsetSum_coeff]
  simp only [coeff_X_pow, Finset.sum_boole]
  rw [← Set.ncard_coe_finset]
  congr 2
  ext D
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine and_congr_right fun hD => ?_
  have h := sum_basepoint_nonneg_of_mem_minusDomains hD
  omega

/-- The constant coefficient of the minus coefficient is the hat coefficient: the counted domains
with multiplicity zero at the basepoints are those counted by the hat differential. -/
theorem coeff_zero_minusCoefficient (hfin : (H.minusDomains χ x y).Finite) :
    (H.minusCoefficient χ x y).coeff 0 = H.hatCoefficient χ x y := by
  rw [coeff_minusCoefficient hfin, hatCoefficient_def, hatDomains_eq_setOf_mem_minusDomains]
  congr 3
  ext D
  refine and_congr_right fun hD => ?_
  rw [Nat.cast_zero, Finset.sum_eq_zero_iff_of_nonneg (f := fun z => D (H.basepoint z))
    fun _ _ => (mem_minusDomains_iff.mp hD).2.1 _]
  simp

/-- When infinitely many domains are counted, the minus coefficient is `0`. -/
theorem minusCoefficient_eq_zero_of_infinite (h : (H.minusDomains χ x y).Infinite) :
    H.minusCoefficient χ x y = 0 :=
  finsum_mem_eq_zero_of_infinite <| by
    rwa [Set.inter_eq_left.mpr fun _ _ => Function.mem_support.mpr (monic_X_pow _).ne_zero]

/-- The minus coefficient vanishes when no domain is counted. -/
theorem minusCoefficient_eq_zero_of_minusDomains_eq_empty (h : H.minusDomains χ x y = ∅) :
    H.minusCoefficient χ x y = 0 := by
  simp [minusCoefficient_def, h]

/-- A nonzero coefficient of `U ^ k` in the minus coefficient from `x` to `y` comes from a counted
domain from `x` to `y` with total multiplicity `k` at the basepoints. -/
theorem exists_mem_minusDomains_of_coeff_minusCoefficient_ne_zero {k : ℕ}
    (h : (H.minusCoefficient χ x y).coeff k ≠ 0) :
    ∃ D ∈ H.minusDomains χ x y, ∑ z, D (H.basepoint z) = k := by
  by_cases hfin : (H.minusDomains χ x y).Finite
  · rw [coeff_minusCoefficient hfin] at h
    exact Set.nonempty_of_ncard_ne_zero
      (s := {D ∈ H.minusDomains χ x y | ∑ z, D (H.basepoint z) = k})
      fun h0 => h (by rw [h0, Nat.cast_zero])
  · simp [minusCoefficient_eq_zero_of_infinite hfin] at h

/-- When the relative Maslov grading is normalized, as in a singly pointed diagram of a closed
surface of genus `n`
(`maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton`),
and the periodic domains have Maslov index zero at `x`, a term `U ^ k y` of the minus
differential of `x` has `gr(x, y) = 1 - 2 k`. Grading `U ^ k y` by `gr(y) - 2 k`, the minus
differential lowers the grading by one. -/
theorem relativeGrading_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) {k : ℕ}
    (hc : (H.minusCoefficient χ x y).coeff k ≠ 0) : H.relativeGrading χ x y = 1 - 2 * k := by
  obtain ⟨D, ⟨hD, -, hμ⟩, hk⟩ := exists_mem_minusDomains_of_coeff_minusCoefficient_ne_zero hc
  rw [hD.relativeGrading_eq hself hP, hμ, ← Int.cast_sum, hk, Int.cast_natCast]

/-- When the relative Maslov grading is normalized, as in a singly pointed diagram of a closed
surface of genus `n`, a term `U ^ k y` of the minus differential of `x` has `gr(x, y) = 1 - 2 k`
modulo the periodic Maslov indices at `x`. -/
theorem coe_relativeGrading_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)
    {k : ℕ} (hc : (H.minusCoefficient χ x y).coeff k ≠ 0) :
    (H.relativeGrading χ x y : ℚ ⧸ H.periodicMaslovIndices χ x) = ((1 - 2 * k : ℚ) : _) := by
  obtain ⟨D, ⟨hD, -, hμ⟩, hk⟩ := exists_mem_minusDomains_of_coeff_minusCoefficient_ne_zero hc
  rw [hD.coe_relativeGrading_eq hself, hμ, ← Int.cast_sum, hk, Int.cast_natCast]

end Coefficient

section Minus

variable (H) in
/-- The minus differential of a Heegaard diagram with region Euler characteristics `χ`: the
`(ZMod 2)[X]`-linear endomorphism of the free `(ZMod 2)[X]`-module on generators whose coefficient
from `x` to `y` is the sum of `U ^ n_z(D)`, with `U = X`, over the nonnegative domains `D` of
Maslov index one from `x` to `y` (`TauCeti.HeegaardRegionSystem.minusCoefficient`). -/
noncomputable def minusDifferential (χ : Region → ℤ) :
    (H.Generator →₀ (ZMod 2)[X]) →ₗ[(ZMod 2)[X]] H.Generator →₀ (ZMod 2)[X] :=
  Finsupp.linearCombination (ZMod 2)[X] fun x =>
    Finsupp.equivFunOnFinite.symm (H.minusCoefficient χ x)

variable {χ : Region → ℤ}

/-- The matrix coefficients of the minus differential are the polynomials
`TauCeti.HeegaardRegionSystem.minusCoefficient`. -/
@[simp]
theorem minusDifferential_single_apply (x y : H.Generator) (a : (ZMod 2)[X]) :
    H.minusDifferential χ (Finsupp.single x a) y = a * H.minusCoefficient χ x y :=
  Finsupp.linearCombination_equivFunOnFinite_symm_single_apply _ x y a

/-- The coefficient of `y` in the minus differential of a chain `c`. -/
theorem minusDifferential_apply (c : H.Generator →₀ (ZMod 2)[X]) (y : H.Generator) :
    H.minusDifferential χ c y = c.sum fun x a => a * H.minusCoefficient χ x y :=
  Finsupp.linearCombination_equivFunOnFinite_symm_apply _ c y

/-- The minus differential vanishes exactly when all of its coefficients vanish. -/
theorem minusDifferential_eq_zero_iff :
    H.minusDifferential χ = 0 ↔ ∀ x y, H.minusCoefficient χ x y = 0 :=
  Finsupp.linearCombination_equivFunOnFinite_symm_eq_zero_iff

/-- **Setting `U = 0` gives the hat differential.** When the counts are finite, reducing the
coefficients of a chain of `CF⁻` modulo `U` (taking constant coefficients) intertwines the minus
differential with the hat differential. -/
theorem mapRange_constantCoeff_minusDifferential
    (hfin : ∀ x y, (H.minusDomains χ x y).Finite) (c : H.Generator →₀ (ZMod 2)[X]) :
    Finsupp.mapRange constantCoeff (map_zero _) (H.minusDifferential χ c) =
      H.hatDifferential χ (Finsupp.mapRange constantCoeff (map_zero _) c) := by
  ext y
  rw [Finsupp.mapRange_apply, minusDifferential_apply, hatDifferential_apply,
    Finsupp.sum_mapRange_index fun _ => zero_mul _, map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [map_mul, constantCoeff_apply (p := H.minusCoefficient χ x y),
    coeff_zero_minusCoefficient (hfin x y)]

end Minus

section Infinity

variable (H) in
/-- The infinity differential of a Heegaard diagram with region Euler characteristics `χ`: the
`(ZMod 2)[T;T⁻¹]`-linear endomorphism of the free module on generators over the Laurent
polynomials in `U = T 1` with the same coefficients as the minus differential
(`TauCeti.HeegaardRegionSystem.minusCoefficient`). -/
noncomputable def infinityDifferential (χ : Region → ℤ) :
    (H.Generator →₀ (ZMod 2)[T;T⁻¹]) →ₗ[(ZMod 2)[T;T⁻¹]] H.Generator →₀ (ZMod 2)[T;T⁻¹] :=
  Finsupp.linearCombination (ZMod 2)[T;T⁻¹] fun x =>
    Finsupp.equivFunOnFinite.symm fun y => toLaurent (H.minusCoefficient χ x y)

variable {χ : Region → ℤ}

/-- The matrix coefficients of the infinity differential are the minus coefficients, viewed as
Laurent polynomials. -/
@[simp]
theorem infinityDifferential_single_apply (x y : H.Generator) (a : (ZMod 2)[T;T⁻¹]) :
    H.infinityDifferential χ (Finsupp.single x a) y =
      a * toLaurent (H.minusCoefficient χ x y) :=
  Finsupp.linearCombination_equivFunOnFinite_symm_single_apply _ x y a

/-- The coefficient of `y` in the infinity differential of a chain `c`. -/
theorem infinityDifferential_apply (c : H.Generator →₀ (ZMod 2)[T;T⁻¹]) (y : H.Generator) :
    H.infinityDifferential χ c y = c.sum fun x a => a * toLaurent (H.minusCoefficient χ x y) :=
  Finsupp.linearCombination_equivFunOnFinite_symm_apply _ c y

/-- The infinity differential vanishes exactly when all of the minus coefficients vanish, that is
exactly when the minus differential vanishes (`minusDifferential_eq_zero_iff`). -/
theorem infinityDifferential_eq_zero_iff :
    H.infinityDifferential χ = 0 ↔ ∀ x y, H.minusCoefficient χ x y = 0 :=
  Finsupp.linearCombination_equivFunOnFinite_symm_eq_zero_iff.trans (by simp)

/-- On chains with polynomial coefficients the infinity differential is the minus differential:
including `CF⁻` into `CF^∞` intertwines the two differentials. -/
theorem infinityDifferential_mapRange_toLaurent (c : H.Generator →₀ (ZMod 2)[X]) :
    H.infinityDifferential χ (Finsupp.mapRange toLaurent (map_zero _) c) =
      Finsupp.mapRange toLaurent (map_zero _) (H.minusDifferential χ c) := by
  ext y
  rw [infinityDifferential_apply, Finsupp.mapRange_apply, minusDifferential_apply,
    Finsupp.sum_mapRange_index fun _ => zero_mul _, map_finsuppSum]
  simp only [map_mul]

/-- The infinity differential preserves `CF⁻`, the chains with polynomial coefficients. -/
theorem minusLattice_le_comap_infinityDifferential :
    H.minusLattice ≤
      H.minusLattice.comap ((H.infinityDifferential χ).restrictScalars (ZMod 2)[X]) :=
  fun c hc => by
    obtain ⟨d, rfl⟩ := mem_minusLattice_iff_exists.mp hc
    simp [infinityDifferential_mapRange_toLaurent]

variable (H) in
/-- The plus differential of a Heegaard diagram with region Euler characteristics `χ`: the
`(ZMod 2)[X]`-linear endomorphism of `CF⁺ = CF^∞ / CF⁻` induced by the infinity differential,
which preserves `CF⁻` (`minusLattice_le_comap_infinityDifferential`). -/
noncomputable def plusDifferential (χ : Region → ℤ) :
    ((H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice) →ₗ[(ZMod 2)[X]]
      (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice :=
  H.minusLattice.mapQ H.minusLattice ((H.infinityDifferential χ).restrictScalars (ZMod 2)[X])
    minusLattice_le_comap_infinityDifferential

/-- The plus differential of the class of a chain is the class of its infinity differential. -/
@[simp]
theorem plusDifferential_mk (c : H.Generator →₀ (ZMod 2)[T;T⁻¹]) :
    H.plusDifferential χ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (H.infinityDifferential χ c) :=
  Submodule.mapQ_apply _ _ _ c

end Infinity

end HeegaardRegionSystem

end TauCeti
