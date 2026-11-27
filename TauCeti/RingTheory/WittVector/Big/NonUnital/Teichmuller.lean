/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Big.NonUnital.Frobenius
public import TauCeti.RingTheory.WittVector.Big.NonUnital.Verschiebung
public import TauCeti.RingTheory.WittVector.Big.Teichmuller

/-!
# Teichmüller representatives over nonunital rings

For a nonunital commutative ring, the Teichmüller representative of an element is the
Teichmüller representative of its image in the integral unitization. This lies in the
augmentation kernel. Its coordinates, ghost components, and Verschiebung expansions
inherit the corresponding formulas for unital rings.

## References

* F. Wagner, *q-Witt vectors and q-Hodge complexes*, §2.6,
  <https://arxiv.org/abs/2410.23078v5>.
-/

public section

noncomputable section

namespace TauCeti.NonUnitalBigWittVector

open BigWitt Function

variable {S T : TruncationSet} {R A : Type*} [NonUnitalCommRing R] [NonUnitalCommRing A]

variable (S) in
/-- The multiplicative Teichmüller map into the nonunital big Witt ring. Its coordinate at
index one is the input whenever the truncation set is nonempty. All other coordinates vanish. -/
def teichmuller : R →ₙ* NonUnitalBigWittVector S R :=
  MulHom.codRestrict
    ((BigWittVector.teichmuller (R := Unitization ℤ R) S).toMulHom.comp
      (Unitization.inrNonUnitalAlgHom ℤ R).toMulHom)
    (NonUnitalSubring.comap (S := BigWittVector S ℤ)
      (BigWittVector.map (R := Unitization ℤ R)
        (Unitization.fstHom ℤ R).toRingHom).toNonUnitalRingHom ⊥) fun r ↦ by
      rw [NonUnitalSubring.mem_comap, NonUnitalSubring.mem_bot]
      -- Unfold the bundled composite and the augmentation to apply coefficient naturality.
      change BigWittVector.map (R := Unitization ℤ R) (Unitization.fstHom ℤ R).toRingHom
        (BigWittVector.teichmuller (R := Unitization ℤ R) S (Unitization.inr r)) = 0
      simp

/-- The kernel inclusion carries a Teichmüller representative to the representative of the
coefficient in the unitization. -/
@[simp]
theorem toBigWitt_teichmuller (r : R) :
    toBigWitt (teichmuller S r) =
      BigWittVector.teichmuller S (Unitization.inr r : Unitization ℤ R) := by
  rw [toBigWitt_apply]
  rfl

/-- The coordinates of the Teichmüller representative over a nonunital ring. -/
theorem coeff_teichmuller (r : R) (n : S) :
    coeff (teichmuller S r) n = if (n : ℕ) = 1 then r else 0 := by
  apply Unitization.inr_injective (R := ℤ)
  rw [← coeff_toBigWitt, toBigWitt_teichmuller, BigWittVector.coeff_teichmuller]
  by_cases h : (n : ℕ) = 1
  · have hS : 1 ∈ S := h ▸ n.property
    simp [h, hS]
  · simp [h]

/-- The first coordinate recovers the input of the nonunital Teichmüller map. -/
@[simp]
theorem coeff_one_teichmuller (h : 1 ∈ S) (r : R) : coeff (teichmuller S r) ⟨1, h⟩ = r := by
  simp [coeff_teichmuller]

/-- The higher coordinates of a nonunital Teichmüller representative vanish. -/
@[simp]
theorem coeff_teichmuller_of_ne_one {n : S} (hn : (n : ℕ) ≠ 1) (r : R) :
    coeff (teichmuller S r) n = 0 := by
  simp [coeff_teichmuller, hn]

/-- The nonunital Teichmüller map preserves zero. -/
@[simp]
theorem teichmuller_zero : teichmuller S (0 : R) = 0 := by
  apply toBigWitt_injective
  simp

/-- The ghost at index `n` is the positive power of the coefficient, computed by repeated
multiplication in the nonunital ring. -/
@[simp]
theorem ghostComponent_teichmuller (r : R) (n : S) :
    ghostComponent n (teichmuller S r) = (· * r)^[(n : ℕ) - 1] r := by
  rw [ghostComponent_apply, ← ghostPolynomial_single_one_eq_iterate
    (S.ne_zero_of_mem n.property) r]
  refine ghostPolynomial_congr fun d hd ↦ ?_
  have hdS := S.mem_of_dvd n.property hd
  rw [coordinates_apply, dite_eq_left hdS, coeff_teichmuller]
  rcases eq_or_ne d 1 with rfl | h
  · simp
  · simp [h, Pi.single_eq_of_ne]

/-- Teichmüller representatives commute with nonunital homomorphisms of coefficient rings. -/
@[simp]
theorem map_teichmuller (f : R →ₙ+* A) (r : R) :
    map f (teichmuller S r) = teichmuller S (f r) := by
  apply ext
  intro n
  by_cases h : (n : ℕ) = 1 <;> simp [coeff_teichmuller, h]

/-- Restriction preserves nonunital Teichmüller representatives. -/
@[simp]
theorem restrict_teichmuller (h : T ≤ S) (r : R) :
    restrict h (teichmuller S r) = teichmuller T r := by
  apply toBigWitt_injective
  simp

/-- On unital coefficients the comparison with the unital Witt ring preserves Teichmüller
representatives. -/
@[simp]
theorem unitalEquiv_teichmuller {C : Type*} [CommRing C] (r : C) :
    unitalEquiv (teichmuller S r) = BigWittVector.teichmuller S r := by
  rw [unitalEquiv_apply, toBigWitt_teichmuller, BigWittVector.map_teichmuller]
  simp

/-- A positive-index Frobenius raises a nonunital Teichmüller representative to the
corresponding positive power in the coefficient ring and shifts the truncation set. -/
@[simp]
theorem frobenius_teichmuller (n : ℕ) (r : R) :
    frobenius (n + 1) (teichmuller S r) = teichmuller (S / (n + 1)) ((· * r)^[n] r) := by
  apply toBigWitt_injective
  rw [toBigWitt_frobenius, toBigWitt_teichmuller, BigWittVector.frobenius_teichmuller,
    toBigWitt_teichmuller]
  congr 1
  have h : Semiconj (Unitization.inr : R → Unitization ℤ R) (· * r)
      (· * (Unitization.inr r : Unitization ℤ R)) := fun a ↦ Unitization.inr_mul ℤ a r
  exact (mul_right_iterate_apply_self (Unitization.inr r : Unitization ℤ R) n).symm.trans
    (h.iterate_right n r).symm

/-- The Teichmüller expansion on a finite restriction, over a nonunital coefficient ring. -/
theorem sum_verschiebung_teichmuller_eq_restrict (h : T ≤ S) (s : Finset ℕ)
    (hs : ∀ n ∈ T, n ∈ s) (x : NonUnitalBigWittVector S R) :
    (∑ d ∈ s, verschiebung d (teichmuller (T / d) (coordinates x d))) = restrict h x := by
  apply toBigWitt_injective
  simp only [map_sum, toBigWitt_verschiebung, toBigWitt_teichmuller, toBigWitt_restrict]
  simpa only [coordinates_toBigWitt, Function.comp_apply, Unitization.inrNonUnitalAlgHom_toFun]
    using BigWittVector.sum_verschiebung_teichmuller_eq_restrict (R := Unitization ℤ R)
      h s hs (toBigWitt x)

/-- The partial Teichmüller sum over a nonunital ring agrees with the original vector
upon restriction to any truncation set whose indices already occur in the sum. -/
theorem restrict_sum_verschiebung_teichmuller (h : T ≤ S) (s : Finset ℕ)
    (hs : ∀ n ∈ T, n ∈ s) (x : NonUnitalBigWittVector S R) :
    restrict h (∑ d ∈ s, verschiebung d (teichmuller (S / d) (coordinates x d))) =
      restrict h x := by
  simpa only [map_sum, restrict_verschiebung, restrict_teichmuller] using
    sum_verschiebung_teichmuller_eq_restrict h s hs x

end TauCeti.NonUnitalBigWittVector
