/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.RootEnumeration

/-!
# Discriminants under integral normalization

Integral normalization replaces a degree `n` polynomial with leading coefficient `a` by a
monic polynomial whose roots are the original roots multiplied by `a`. Its discriminant is
`a ^ ((n - 1) * (n - 2))` times the original discriminant. This identity lets one reduce
nonmonic polynomial families to monic families while retaining control of the discriminant,
even when the leading coefficient vanishes on an exceptional parameter set.

We first establish the root-scaling law over any commutative ring. Both formulas use
Mathlib's convention that constant polynomials, including zero, have discriminant `1`.

Mathlib's `scaleRoots` and `integralNormalization` satisfy
`f.scaleRoots f.leadingCoeff = f.integralNormalization * C f.leadingCoeff`.
The root-scaling identity controls the discriminant before monic normalization; for nonzero
`f`, the integral-normalization identity gives the discriminant of the resulting monic polynomial.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

private theorem discr_prod_scaled_roots {n : ℕ} (r : Fin n → R) (a : R) :
    (∏ i, (X - C (r i * a))).discr =
      a ^ (n * (n - 1)) * (∏ i, (X - C (r i))).discr := by
  simp only [discr_prod_X_sub_C, ← sub_mul, mul_pow, prod_mul_distrib,
    prod_const, prod_pow_eq_pow_sum]
  have hcard : ∑ i : Fin n, #(Ioi i) = n * (n - 1) / 2 := by
    simp only [Fin.card_Ioi, Fin.sum_univ_eq_sum_range fun i ↦ n - 1 - i]
    rw [sum_range_reflect (fun i ↦ i) n, sum_range_id]
  rw [hcard, ← pow_mul, mul_comm 2, Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd]
  ring

private theorem discr_scaleRoots_of_splits {K : Type*} [Field K] {f : K[X]}
    (hs : f.Splits) (a : K) :
    (f.scaleRoots a).discr = a ^ (f.natDegree * (f.natDegree - 1)) * f.discr := by
  classical
  obtain rfl | hf := eq_or_ne f 0
  · simp only [zero_scaleRoots, natDegree_zero, Nat.zero_mul, pow_zero, one_mul]
  obtain ⟨r, hr⟩ := (exists_isRootEnumeration_iff_splits
    (R := K) (f := f) (L := K) (ι := Fin f.natDegree) (by simp)).2 (by simpa using hs)
  have hfac : f = C f.leadingCoeff * ∏ i, (X - C (r i)) := by
    have hroots : f.roots = univ.val.map r := by
      simpa [isRootEnumeration_iff] using hr
    conv_lhs => rw [hs.eq_prod_roots, hroots, Multiset.map_map, ← prod_eq_multiset_prod]
    rfl
  have hscale : (∏ i, (X - C (r i))).scaleRoots a =
      ∏ i, (X - C (r i * a)) := by
    induction (univ : Finset (Fin f.natDegree)) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [prod_insert hi, mul_scaleRoots_of_noZeroDivisors, X_sub_C_scaleRoots, ih]
  have hlc := leadingCoeff_ne_zero.2 hf
  conv_lhs => rw [hfac, mul_scaleRoots_of_noZeroDivisors, scaleRoots_C, hscale]
  rw [discr_C_mul _ hlc, discr_prod_scaled_roots]
  conv_rhs => rw [hfac, discr_C_mul _ hlc]
  simp only [natDegree_C_mul hlc, natDegree_finsetProd_X_sub_C_eq_card, card_univ, Fintype.card_fin]
  ring

/-- Scaling every root by `a` multiplies the discriminant of a degree `n` polynomial by
`a ^ (n * (n - 1))`. The formula holds over every commutative ring, including at `a = 0`. -/
theorem discr_scaleRoots {f : R[X]} (a : R) :
    (f.scaleRoots a).discr = a ^ (f.natDegree * (f.natDegree - 1)) * f.discr := by
  -- Establish the universal identity by degree-preserving base change from split fields.
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits K f hs => exact discr_scaleRoots_of_splits hs a
  | injective R S φ hφ f ih =>
    obtain rfl | hf := eq_or_ne f 0
    · simp only [zero_scaleRoots, natDegree_zero, Nat.zero_mul, pow_zero, one_mul]
    apply hφ
    have hlc : φ f.leadingCoeff ≠ 0 :=
      (map_eq_zero_iff φ hφ).not.2 (leadingCoeff_ne_zero.2 hf)
    rw [map_mul, map_pow,
      ← discr_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ _),
      ← discr_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ _),
      map_scaleRoots _ _ _ hlc, ih]
    simp [natDegree_map_eq_of_injective hφ]
  | surjective R S φ hφ f ih =>
    obtain rfl | hf := eq_or_ne f 0
    · simp only [zero_scaleRoots, natDegree_zero, Nat.zero_mul, pow_zero, one_mul]
    obtain ⟨g, hg, hdeg⟩ := exists_degree_eq_of_mem_lifts (map_surjective φ hφ f)
    obtain ⟨a', rfl⟩ := hφ a
    have hnat : g.natDegree = f.natDegree := natDegree_eq_natDegree hdeg
    have hlc : φ g.leadingCoeff = f.leadingCoeff := by
      rw [← coeff_natDegree, hnat, ← coeff_map, hg, coeff_natDegree]
    have hmap : (g.map φ).natDegree = g.natDegree := by rw [hg, hnat]
    have hscale : ((g.scaleRoots a').map φ).natDegree = (g.scaleRoots a').natDegree := by
      rw [map_scaleRoots _ _ _ (hlc ▸ leadingCoeff_ne_zero.2 hf), hg,
        natDegree_scaleRoots, natDegree_scaleRoots, hnat]
    have key := congrArg φ (ih g a')
    rw [← discr_map_of_natDegree_eq φ hscale,
      map_scaleRoots _ _ _ (hlc ▸ leadingCoeff_ne_zero.2 hf), hg,
      map_mul, map_pow, ← discr_map_of_natDegree_eq φ hmap, hg, hnat] at key
    exact key

/-- Integral normalization multiplies the discriminant of a degree `n` polynomial by the
`(n - 1) * (n - 2)` power of its leading coefficient. In particular, normalization preserves the
form “a power of a parameter times a unit” when both the leading coefficient and the
discriminant have that form. Constants and zero are included. -/
theorem discr_integralNormalization {f : R[X]} :
    f.integralNormalization.discr =
      f.leadingCoeff ^ ((f.natDegree - 1) * (f.natDegree - 2)) * f.discr := by
  obtain rfl | hf := eq_or_ne f 0
  · simp only [integralNormalization_zero, natDegree_zero, Nat.zero_sub, Nat.zero_mul,
      pow_zero, one_mul]
  -- Lift to a polynomial ring over ℤ, where cancellation is legitimate, then specialize.
  wlog hR : IsDomain R generalizing R
  · let A := MvPolynomial R ℤ
    let φ : A →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) id
    have hφ : Function.Surjective φ :=
      fun x ↦ ⟨MvPolynomial.X x, by simp [φ, MvPolynomial.eval₂Hom]⟩
    obtain ⟨g, hg, hdeg⟩ := exists_degree_eq_of_mem_lifts (map_surjective φ hφ f)
    have hnat : g.natDegree = f.natDegree := natDegree_eq_natDegree hdeg
    have hlc : φ g.leadingCoeff = f.leadingCoeff := by
      rw [← coeff_natDegree, hnat, ← coeff_map, hg, coeff_natDegree]
    have hne : φ g.leadingCoeff ≠ 0 := hlc ▸ leadingCoeff_ne_zero.2 hf
    have hmap : (g.map φ).natDegree = g.natDegree := by rw [hg, hnat]
    have hnorm : (g.integralNormalization.map φ).natDegree = g.integralNormalization.natDegree :=
      by rw [← integralNormalization_map φ g hne, natDegree_integralNormalization,
        natDegree_integralNormalization, hmap]
    have key := congrArg φ (this (f := g) (by aesop) inferInstance)
    rw [← discr_map_of_natDegree_eq φ hnorm, ← integralNormalization_map φ g hne, hg,
      map_mul, map_pow, hlc, ← discr_map_of_natDegree_eq φ hmap, hg, hnat] at key
    exact key
  rcases Nat.eq_zero_or_pos f.natDegree with hd | hd
  · rw [eq_C_of_natDegree_eq_zero hd] at hf ⊢
    have hc := (C_ne_zero.1 hf)
    simp only [integralNormalization_C hc, natDegree_C, Nat.zero_sub, Nat.zero_mul,
      pow_zero, discr_C, mul_one]
    simpa only [C_1] using discr_C (R := R) 1
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf
  have key := discr_scaleRoots (f := f) f.leadingCoeff
  rw [← integralNormalization_mul_C_leadingCoeff, mul_comm f.integralNormalization,
    discr_C_mul _ hlc, natDegree_integralNormalization] at key
  -- Cancel only in the domain case; the resulting identity then descends to all rings.
  apply mul_left_cancel₀ (a := f.leadingCoeff ^ (2 * f.natDegree - 2)) (pow_ne_zero _ hlc)
  rw [key, ← mul_assoc, ← pow_add]
  have hexp : 2 * f.natDegree - 2 + (f.natDegree - 1) * (f.natDegree - 2) =
      f.natDegree * (f.natDegree - 1) := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd) with h | h
    · simp [← h]
    · have h1 : f.natDegree = f.natDegree - 1 + 1 := by omega
      have h2 : f.natDegree - 1 = f.natDegree - 2 + 1 := by omega
      have h3 : 2 * f.natDegree - 2 = 2 * (f.natDegree - 1) := by omega
      nlinarith
  rw [hexp]

end TauCeti
