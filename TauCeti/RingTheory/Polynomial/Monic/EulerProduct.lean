/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.RingTheory.Polynomial.Monic.Squarefree
public import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.FieldTheory.Finite.Irreducible.Count
import TauCeti.RingTheory.Polynomial.Factors
import TauCeti.RingTheory.Polynomial.DegreeLT
import TauCeti.RingTheory.Polynomial.Monic.Factorization
import TauCeti.RingTheory.PowerSeries.Binomial
import TauCeti.RingTheory.PowerSeries.EulerTransform
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# The weighted Euler product for monic squarefree polynomials

Over a finite field, weighting a monic squarefree polynomial with `k` irreducible factors
by `c ^ k` gives the generating series `∏_P (1 + c X ^ deg P)`, indexed by the monic
irreducibles. Each coefficient only uses prime polynomials up to that degree. This is the
first Euler product in the proof of Lemma 7.4 of T. Browning and W. Sawin, *A geometric
version of the circle method*, Ann. of Math. 191 (2020). Gauss’s formula for the number
of irreducibles in each degree and the integral cyclotomic identity give the ordinary
Euler product and all its integer powers.
-/

public section

open Finset PowerSeries UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius PowerSeries.WithPiTopology

namespace TauCeti

private abbrev MonicIrreducible (F : Type*) [Field F] :=
  {p : Polynomial F // p.Monic ∧ Irreducible p}

/-- There are finitely many monic irreducibles of bounded degree over a finite field. -/
theorem finite_monicIrreducible_natDegree_le (F : Type*) [Field F] [Finite F] (m : ℕ) :
    {p : {p : Polynomial F // p.Monic ∧ Irreducible p} |
      (p : Polynomial F).natDegree ≤ m}.Finite := by
  apply (Set.finite_Iic m).preimage'
  intro d _
  exact ((Polynomial.finite_setOf_monic_natDegree_eq F d).preimage
    Subtype.val_injective.injOn).subset fun p hp ↦ ⟨p.property.1, hp⟩

/-- The coefficient of degree `m` sums `c ^ k` over the monic squarefree polynomials of degree
`m`, with `k` the number of monic irreducible factors. -/
noncomputable def weightedSquarefreeSeries (F : Type*) [Field F] [DecidableEq F] [Finite F]
    {R : Type*} [CommRing R] (c : R) : R⟦X⟧ :=
  PowerSeries.mk fun m ↦
    ∑ f ∈ (Polynomial.finite_monicSquarefreePolysOfDegree F m).toFinset,
      c ^ (normalizedFactors f).card

/-- The degree-`m` coefficient is the finite weighted sum over monic squarefree polynomials. -/
@[simp]
theorem coeff_weightedSquarefreeSeries (F : Type*) [Field F] [DecidableEq F] [Finite F]
    {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    coeff m (weightedSquarefreeSeries F c) =
      ∑ f ∈ (Polynomial.finite_monicSquarefreePolysOfDegree F m).toFinset,
        c ^ (normalizedFactors f).card := by
  rw [weightedSquarefreeSeries, coeff_mk]

variable {F : Type*} [Field F]

section Weighted

variable [DecidableEq F]

private theorem weightedSum_eq_sum_powerset [Finite F] {R : Type*} [CommRing R]
    (c : R) (m : ℕ) :
    (∑ s ∈ ((finite_monicIrreducible_natDegree_le F m).toFinset.powerset.filter
      fun s : Finset (MonicIrreducible F) ↦ ∑ p ∈ s, (p : Polynomial F).natDegree = m),
      c ^ s.card) =
    ∑ f ∈ (Polynomial.finite_monicSquarefreePolysOfDegree F m).toFinset,
      c ^ (normalizedFactors f).card := by
  classical
  have hfac (s : Finset (MonicIrreducible F)) :
      (∏ p ∈ s, (p : Polynomial F)).Monic ∧ Squarefree (∏ p ∈ s, (p : Polynomial F)) ∧
        normalizedFactors (∏ p ∈ s, (p : Polynomial F)) = s.val.map Subtype.val := by
    simp only [Finset.prod_eq_multiset_prod]
    exact Polynomial.monic_squarefree_normalizedFactors_prod
      (fun _ hp ↦ by obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hp; exact p.property.1)
      (fun _ hp ↦ by obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hp; exact p.property.2)
      (s.nodup.map Subtype.val_injective)
  refine sum_bij (fun s _ ↦ ∏ p ∈ s, (p : Polynomial F)) ?_ ?_ ?_ ?_
  · intro s hs
    refine (Set.Finite.mem_toFinset _).mpr (Polynomial.mem_monicSquarefreePolysOfDegree_iff.mpr
      ⟨(hfac s).1, (hfac s).2.1, ?_⟩)
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun p _ ↦ p.property.1), (mem_filter.mp hs).2]
  · intro a _ b _ hab
    have he := congrArg normalizedFactors hab
    rw [(hfac a).2.2, (hfac b).2.2] at he
    exact Finset.val_injective (Multiset.map_injective Subtype.val_injective he)
  · intro f hf
    obtain ⟨hm, hsf, hd⟩ := Polynomial.mem_monicSquarefreePolysOfDegree_iff.mp
      ((Set.Finite.mem_toFinset _).mp hf)
    let s := (finite_monicIrreducible_natDegree_le F m).toFinset.filter
      fun p : MonicIrreducible F ↦ (p : Polynomial F) ∈ normalizedFactors f
    have hmap : s.map (Function.Embedding.subtype _) = (normalizedFactors f).toFinset := by
      ext p
      simp only [s, mem_map, mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
        Function.Embedding.subtype_apply, Multiset.mem_toFinset]
      refine ⟨fun ⟨q, hq, he⟩ ↦ he ▸ hq.2, fun hp ↦ ?_⟩
      refine ⟨⟨p, hm.monic_of_mem_normalizedFactors hp,
        irreducible_of_normalized_factor p hp⟩, ⟨?_, hp⟩, rfl⟩
      exact hd ▸ Polynomial.natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hp) hm.ne_zero
    refine ⟨s, mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), ?_⟩, ?_⟩
    · simpa only [sum_map, Function.Embedding.subtype_apply] using
        (congrArg (fun t : Finset (Polynomial F) ↦ ∑ p ∈ t, p.natDegree) hmap).trans
          ((Polynomial.sum_natDegree_toFinset_normalizedFactors hsf).trans hd)
    · simpa only [prod_map, Function.Embedding.subtype_apply] using
        (congrArg (fun t : Finset (Polynomial F) ↦ ∏ p ∈ t, p) hmap).trans
          (hm.prod_toFinset_normalizedFactors_of_squarefree hsf)
  · intro s _
    rw [(hfac s).2.2, Multiset.card_map, Finset.card_def]

/-- The weighted generating series is the coefficientwise product of
`1 + c X ^ p.natDegree` over all monic irreducible polynomials `p`. -/
theorem hasProd_weightedSquarefreeSeries (F : Type*) [Field F] [DecidableEq F] [Finite F]
    {R : Type*} [CommRing R] [TopologicalSpace R] (c : R) :
    HasProd (fun p : {p : Polynomial F // p.Monic ∧ Irreducible p} ↦
      1 + C c * X ^ (p : Polynomial F).natDegree) (weightedSquarefreeSeries F c) := by
  classical
  let degree : MonicIrreducible F → ℕ+ := fun p ↦ ⟨_, p.property.2.natDegree_pos⟩
  have h := hasProd_expand (m := degree) (finite_monicIrreducible_natDegree_le F)
    (f := fun _ ↦ 1 + C c * X) (fun _ ↦ by simp)
  have hexpand (p : MonicIrreducible F) :
      expand (degree p) (degree p).ne_zero (1 + C c * X) =
        1 + C c * X ^ (p : Polynomial F).natDegree := by
    simp [expand_C, expand_X, degree]
  simp only [hexpand] at h
  convert h using 1
  ext m
  rw [coeff_weightedSquarefreeSeries, coeff_mk, prod_one_add, map_sum,
    ← weightedSum_eq_sum_powerset]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, ← map_pow, Finset.prod_pow_eq_pow_sum,
    coeff_C_mul_X_pow, Finset.sum_filter, eq_comm (a := m)]
  rfl

end Weighted

private def monicIrreducibleDegree (p : MonicIrreducible F) : ℕ+ :=
  ⟨_, p.property.2.natDegree_pos⟩

private theorem neg_moebius_div_eq_neg_ncard [Finite F] (r : ℕ+) :
    -(∑ d ∈ (r : ℕ).divisors, μ d * (Nat.card F : ℤ) ^ ((r : ℕ) / d)) / (r : ℤ) =
      -((Polynomial.monicIrreduciblesOfDegree F r).ncard : ℤ) := by
  have h := Polynomial.natCast_mul_ncard_monicIrreduciblesOfDegree (K := F) (r : ℕ)
  rw [← Nat.sum_divisorsAntidiagonal' (fun a b ↦ μ a * (Nat.card F : ℤ) ^ b),
    Nat.sum_divisorsAntidiagonal (fun a b ↦ μ a * (Nat.card F : ℤ) ^ b)] at h
  rw [← h, ← mul_neg, Int.mul_ediv_cancel_left _ (by exact_mod_cast r.ne_zero)]

private theorem hasProd_monicIrreducible_degree_fiber [Finite F] (r : ℕ+) :
    HasProd (fun p : monicIrreducibleDegree (F := F) ⁻¹' {r} ↦
      (1 - X ^ (p.val.val : Polynomial F).natDegree : ℤ⟦X⟧))
        (expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^
          (-((Polynomial.monicIrreduciblesOfDegree F r).ncard : ℤ)))) := by
  classical
  let d : MonicIrreducible F → ℕ+ := monicIrreducibleDegree
  let e : (d ⁻¹' {r}) ≃ Polynomial.monicIrreduciblesOfDegree F r :=
    { toFun := fun p ↦ ⟨p.val.val, Polynomial.mem_monicIrreduciblesOfDegree_iff.mpr
        ⟨p.val.property.1, p.val.property.2,
          congrArg PNat.val (Set.mem_singleton_iff.mp p.property)⟩⟩
      invFun := fun p ↦
        let hp := Polynomial.mem_monicIrreduciblesOfDegree_iff.mp p.property
        ⟨⟨p.val, hp.1, hp.2.1⟩, Set.mem_singleton_iff.mpr (Subtype.ext hp.2.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have : Finite (d ⁻¹' {r}) :=
    have := (Polynomial.finite_monicIrreduciblesOfDegree F r).to_subtype
    Finite.of_equiv _ e.symm
  let _ := Fintype.ofFinite (d ⁻¹' {r})
  have hcard : Fintype.card (d ⁻¹' {r}) = (Polynomial.monicIrreduciblesOfDegree F r).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_coe_set_eq]
  have hdeg (p : d ⁻¹' {r}) : (p.val.val : Polynomial F).natDegree = r :=
    congrArg PNat.val (Set.mem_singleton_iff.mp p.property)
  rw [expand_invOneSubPow_zpow_neg_natCast]
  have h := hasProd_fintype (fun p : d ⁻¹' {r} ↦
    (1 - X ^ (p.val.val : Polynomial F).natDegree : ℤ⟦X⟧))
  simpa only [hdeg, prod_const, card_univ, hcard] using h

private theorem multipliable_monicIrreducible_one_sub_X_pow [Finite F] :
    Multipliable (fun p : MonicIrreducible F ↦
      (1 - X ^ (p : Polynomial F).natDegree : ℤ⟦X⟧)) := by
  let d : MonicIrreducible F → ℕ+ := monicIrreducibleDegree
  have hexpand (p : MonicIrreducible F) :
      expand (d p) (d p).ne_zero (1 - X : ℤ⟦X⟧) = 1 - X ^ (p : Polynomial F).natDegree := by
    rw [map_sub, map_one, expand_X]
    rfl
  have h := multipliable_expand (m := d) (finite_monicIrreducible_natDegree_le F)
    (f := fun _ ↦ (1 - X : ℤ⟦X⟧)) (fun _ ↦ by simp)
  simp only [hexpand] at h
  exact h

private theorem hasProd_monicIrreducible_one_sub_X_pow [Finite F] :
    HasProd (fun p : MonicIrreducible F ↦ 1 - X ^ (p : Polynomial F).natDegree)
      (1 - C (Nat.card F : ℤ) * X) := by
  let g : MonicIrreducible F → ℤ⟦X⟧ := fun p ↦ 1 - X ^ (p : Polynomial F).natDegree
  have hp : Multipliable g := multipliable_monicIrreducible_one_sub_X_pow
  have h := (Equiv.sigmaFiberEquiv (monicIrreducibleDegree (F := F))).hasProd_iff.mpr hp.hasProd
  have h' : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero
      (↑(invOneSubPow ℤ 1 ^
        (-((Polynomial.monicIrreduciblesOfDegree F r).ncard : ℤ))) : ℤ⟦X⟧))
      (1 - C (Nat.card F : ℤ) * X) := by
    exact (hasProd_expand_invOneSubPow_zpow_one_sub_C_mul_X (Nat.card F : ℤ)).congr_fun
      fun r ↦ by rw [neg_moebius_div_eq_neg_ncard (F := F) r]
  have hf : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero
      (↑(invOneSubPow ℤ 1 ^
        (-((Polynomial.monicIrreduciblesOfDegree F r).ncard : ℤ))) : ℤ⟦X⟧)) (∏' p, g p) :=
    h.sigma (hasProd_monicIrreducible_degree_fiber (F := F))
  have he : (∏' p, g p) = 1 - C (Nat.card F : ℤ) * X := hf.unique h'
  exact he ▸ hp.hasProd

/-- The ordinary Euler product over the monic irreducibles of a finite field, raised to any
integer power. Every factor is expanded at its degree, and the product is the corresponding
power of the geometric series in `q X`, with `q` the cardinality of the field. -/
theorem hasProd_expand_invOneSubPow_monicIrreducible [Finite F] (k : ℤ) :
    HasProd (fun p : {p : Polynomial F // p.Monic ∧ Irreducible p} ↦
      expand (p : Polynomial F).natDegree p.property.2.natDegree_pos.ne'
        (↑(invOneSubPow ℤ 1 ^ k) : ℤ⟦X⟧))
      (rescale (Nat.card F : ℤ) ↑(invOneSubPow ℤ 1 ^ k)) := by
  let d : MonicIrreducible F → ℕ+ := monicIrreducibleDegree
  let u := Units.map (rescale (Nat.card F : ℤ)).toMonoidHom (invOneSubPow ℤ 1)
  have hu :
      (↑(u ^ k) : ℤ⟦X⟧) = rescale (Nat.card F : ℤ) ↑(invOneSubPow ℤ 1 ^ k) := by
    simp only [u, ← map_zpow, Units.coe_map]
    rfl
  rw [← hu]
  have huinv : (↑u⁻¹ : ℤ⟦X⟧) = 1 - C (Nat.card F : ℤ) * X := by
    simp [u, rescale_X]
  have hneg : HasProd (fun p ↦ expand (d p) (d p).ne_zero (↑(invOneSubPow ℤ 1)⁻¹ : ℤ⟦X⟧))
      (↑u⁻¹ : ℤ⟦X⟧) := by
    simpa [d, monicIrreducibleDegree, invOneSubPow_inv_eq_one_sub_pow, expand_X, huinv] using
      hasProd_monicIrreducible_one_sub_X_pow (F := F)
  -- The inverse factors also converge, and their product inverts the ordinary Euler product.
  have hm := multipliable_expand (m := d) (finite_monicIrreducible_natDegree_le F)
    (f := fun _ ↦ (↑(invOneSubPow ℤ 1) : ℤ⟦X⟧))
    (fun _ ↦ by simpa using constantCoeff_invOneSubPow_zpow (R := ℤ) 1)
  have hmul := hm.hasProd.mul hneg
  have hone :
      (∏' p, expand (d p) (d p).ne_zero ↑(invOneSubPow ℤ 1)) * (↑u⁻¹ : ℤ⟦X⟧) = 1 := by
    exact hmul.unique (hasProd_one.congr_fun fun p ↦ by
      rw [← map_mul, Units.mul_inv, map_one])
  have hpos : HasProd (fun p ↦ expand (d p) (d p).ne_zero (↑(invOneSubPow ℤ 1) : ℤ⟦X⟧))
      (↑u : ℤ⟦X⟧) := by
    have h := congrArg (fun x : ℤ⟦X⟧ ↦ x * u) hone
    have h' : (∏' p, expand (d p) (d p).ne_zero ↑(invOneSubPow ℤ 1)) = (↑u : ℤ⟦X⟧) :=
      by simpa [mul_assoc] using h
    exact h' ▸ hm.hasProd
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    exact (hpos.pow n).congr_fun fun _ ↦ rfl
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    exact (hneg.pow (n + 1)).congr_fun fun _ ↦ rfl

end TauCeti
