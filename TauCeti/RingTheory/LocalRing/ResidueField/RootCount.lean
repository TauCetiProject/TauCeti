/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.SetTheory.Cardinal.Finite
-- Non-public: `Polynomial.sum_rootMultiplicity_le_natDegree_of_pairwise_isUnit_sub` is used only
-- inside the proofs.
import TauCeti.Algebra.Polynomial.Roots

/-!
# Zeros of polynomials at representatives of residue classes

Let `W` be a local ring and `ι : W →+* R` a ring homomorphism to a commutative ring. Elements of
`W` in distinct residue classes differ by units, and so do their images in `R`. Over any
commutative ring, the root multiplicities of a polynomial at points with unit differences add up
to at most its degree (`Polynomial.sum_rootMultiplicity_le_natDegree_of_pairwise_isUnit_sub`), so
a nonzero polynomial `Φ ∈ R[X]` that vanishes to order at least `E` at the images of `q`
representatives of distinct residue classes has degree at least `E * q`.

## Main results

* `Polynomial.mul_card_le_natDegree_of_injOn_residue`: if `s` is a finite set of elements of `W`
  in distinct residue classes, `Φ ≠ 0` and `X ^ E ∣ Φ.comp (X + C (ι y))` for every `y ∈ s`, then
  `E * #s ≤ Φ.natDegree`.
* `Polynomial.mul_natCard_residueField_le_natDegree` (Stepanov's count): if `Φ ≠ 0` and
  `X ^ E ∣ Φ.comp (X + C (ι y))` for every `y : W`, then
  `E * Nat.card (ResidueField W) ≤ Φ.natDegree`. When the residue field is infinite, its
  `Nat.card` is `0` and the statement is trivial.

## References

* E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*,
  Séminaire Bourbaki, exposé 430 (1973): a polynomial with zeros of multiplicity at least `E`
  at `q` points has degree at least `E * q`.
* The statement of `Polynomial.mul_natCard_residueField_le_natDegree` is that of
  `New.stepanov_count` (file `New/UpperBound/ElementaryDivisors/RootLemma.lean`) in the folder
  `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

namespace Polynomial

variable {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {ι : W →+* R} {E : ℕ}
  {Φ : R[X]}

/-- Let `ι : W →+* R` be a ring homomorphism from a local ring and `s` a finite set of elements
of `W` in pairwise distinct residue classes. If `Φ ≠ 0` and `X ^ E ∣ Φ.comp (X + C (ι y))` for
every `y ∈ s`, then `E * #s ≤ Φ.natDegree`. -/
theorem mul_card_le_natDegree_of_injOn_residue (hΦ0 : Φ ≠ 0) {s : Finset W}
    (hs : Set.InjOn (IsLocalRing.residue W) s) (hΦ : ∀ y ∈ s, X ^ E ∣ Φ.comp (X + C (ι y))) :
    E * s.card ≤ Φ.natDegree := by
  have ha : (s : Set W).Pairwise fun y z ↦ IsUnit (ι y - ι z) := by
    intro y hy z hz hyz
    have hres : IsLocalRing.residue W (y - z) ≠ 0 := by
      rwa [map_sub, sub_ne_zero, Ne, hs.eq_iff hy hz]
    simpa only [map_sub] using ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres).map ι
  calc E * s.card = ∑ _y ∈ s, E := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ y ∈ s, Φ.rootMultiplicity (ι y) := Finset.sum_le_sum fun y hy ↦
        (le_rootMultiplicity_iff hΦ0).mpr (X_sub_C_pow_dvd_iff.mpr (hΦ y hy))
    _ ≤ Φ.natDegree := sum_rootMultiplicity_le_natDegree_of_pairwise_isUnit_sub ha Φ

/-- **Stepanov's count.** Let `ι : W →+* R` be a ring homomorphism from a local ring to a
commutative ring. If `Φ ≠ 0` and `X ^ E ∣ Φ.comp (X + C (ι y))` for every `y : W`, then
`E * q ≤ Φ.natDegree`, where `q = Nat.card (ResidueField W)` (which is `0` when the residue field
is infinite). -/
theorem mul_natCard_residueField_le_natDegree (hΦ0 : Φ ≠ 0)
    (hΦ : ∀ y, X ^ E ∣ Φ.comp (X + C (ι y))) :
    E * Nat.card (IsLocalRing.ResidueField W) ≤ Φ.natDegree := by
  classical
  rcases finite_or_infinite (IsLocalRing.ResidueField W) with hfin | hinf
  · have := Fintype.ofFinite (IsLocalRing.ResidueField W)
    obtain ⟨σ, hσ⟩ := (IsLocalRing.residue_surjective (R := W)).hasRightInverse
    have hs : Set.InjOn (IsLocalRing.residue W) (Finset.univ.image σ : Finset W) := by
      rintro _ hy _ hz h
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hz
      rw [hσ k, hσ l] at h
      rw [h]
    have h := mul_card_le_natDegree_of_injOn_residue hΦ0 hs fun y _ ↦ hΦ y
    rwa [Finset.card_image_of_injective _ hσ.injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card] at h
  · simp [Nat.card_eq_zero_of_infinite]

end Polynomial
