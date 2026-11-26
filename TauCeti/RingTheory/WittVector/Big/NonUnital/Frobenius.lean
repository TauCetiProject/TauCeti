/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Big.Frobenius
public import TauCeti.RingTheory.WittVector.Big.NonUnital

/-!
# Frobenius on nonunital big Witt vectors

The big Witt Frobenius preserves the augmentation kernel of the integral unitization.
Restricting it to this kernel defines Frobenius over a nonunital commutative ring without
choosing new coordinate polynomials. Its ghost components, coefficient maps, and restrictions
are inherited from the unital construction.

## References

* F. Wagner, *q-Witt vectors and q-Hodge complexes*, §2.6,
  <https://arxiv.org/abs/2410.23078v5>.
-/

public section

namespace TauCeti.NonUnitalBigWittVector

open BigWitt

variable {S T : TruncationSet} {R A : Type*} [NonUnitalCommRing R] [NonUnitalCommRing A]

/-- The big Witt Frobenius restricted to the augmentation kernel of the integral unitization. -/
noncomputable def frobenius (n : ℕ) :
    NonUnitalBigWittVector S R →ₙ+* NonUnitalBigWittVector (S / n) R :=
  codRestrict
    ((BigWittVector.frobenius (R := Unitization ℤ R) n).toNonUnitalRingHom.comp toBigWitt)
    fun x ↦ by
      rw [NonUnitalRingHom.comp_apply]
      -- Reduce `RingHom.toNonUnitalRingHom` so Frobenius naturality can rewrite the application.
      change BigWittVector.map _
        (BigWittVector.frobenius (R := Unitization ℤ R) n (toBigWitt x)) = 0
      rw [← BigWittVector.frobenius_map, map_fst_toBigWitt, map_zero]

/-- The kernel inclusion intertwines nonunital Frobenius with the unital Frobenius. -/
@[simp]
theorem toBigWitt_frobenius (n : ℕ) (x : NonUnitalBigWittVector S R) :
    toBigWitt (frobenius n x) =
      BigWittVector.frobenius (R := Unitization ℤ R) n (toBigWitt x) :=
  toBigWitt_codRestrict _ _ x

/-- Frobenius shifts nonunital ghost components by multiplication of their indices. -/
@[simp]
theorem ghostComponent_frobenius (n : ℕ) (x : NonUnitalBigWittVector S R) (k : S / n) :
    ghostComponent k (frobenius n x) =
      ghostComponent ⟨n * k, TruncationSet.mem_div.mp k.property⟩ x := by
  apply Unitization.inr_injective (R := ℤ)
  rw [← ghostMap_toBigWitt, toBigWitt_frobenius, BigWittVector.ghostMap_frobenius,
    ghostMap_toBigWitt]

/-- Frobenius commutes with homomorphisms of nonunital coefficient rings. -/
@[simp]
theorem frobenius_map (n : ℕ) (f : R →ₙ+* A) (x : NonUnitalBigWittVector S R) :
    frobenius n (map f x) = map f (frobenius n x) := by
  apply toBigWitt_injective
  simp only [toBigWitt_frobenius, toBigWitt_map, BigWittVector.frobenius_map]

/-- Frobenius commutes with restriction of truncation sets. -/
theorem frobenius_restrict (n : ℕ) (h : T ≤ S) (x : NonUnitalBigWittVector S R) :
    frobenius n (restrict h x) =
      restrict (TruncationSet.div_le_div h n) (frobenius n x) := by
  apply toBigWitt_injective
  simp only [toBigWitt_frobenius, toBigWitt_restrict, BigWittVector.frobenius_restrict]

/-- Frobenius at index one is the identity, with its target presented as `S / 1`. -/
@[simp]
theorem frobenius_one (x : NonUnitalBigWittVector S R) :
    frobenius 1 x = restrict (le_of_eq (TruncationSet.div_one S)) x := by
  apply toBigWitt_injective
  simp only [toBigWitt_frobenius, toBigWitt_restrict, BigWittVector.frobenius_one]

/-- Successive Frobenius maps multiply their indices. -/
theorem frobenius_frobenius (n k : ℕ) (x : NonUnitalBigWittVector S R) :
    frobenius k (frobenius n x) =
      restrict (le_of_eq (TruncationSet.div_div S n k)) (frobenius (n * k) x) := by
  apply toBigWitt_injective
  simp only [toBigWitt_frobenius, toBigWitt_restrict, BigWittVector.frobenius_frobenius]

/-- Frobenius at index zero is zero because its target truncation set is empty. -/
@[simp]
theorem frobenius_zero (x : NonUnitalBigWittVector S R) : frobenius 0 x = 0 := by
  apply toBigWitt_injective
  rw [toBigWitt_frobenius, BigWittVector.frobenius_zero, map_zero]

/-- The first coordinate of Frobenius is the corresponding original ghost component. -/
@[simp]
theorem coeff_one_frobenius (n : ℕ) (hn : n ∈ S) (x : NonUnitalBigWittVector S R) :
    coeff (frobenius n x) ⟨1, TruncationSet.one_mem_div_iff.mpr hn⟩ =
      ghostComponent ⟨n, hn⟩ x := by
  have h := ghostComponent_frobenius n x ⟨1, TruncationSet.one_mem_div_iff.mpr hn⟩
  rw [ghostComponent_apply, ghostPolynomial_one,
    coordinates_coe (frobenius n x) ⟨1, TruncationSet.one_mem_div_iff.mpr hn⟩] at h
  simpa only [mul_one] using h

section Unital

variable {C : Type*} [CommRing C]

/-- On unital coefficient rings, the comparison with usual Witt vectors preserves Frobenius. -/
@[simp]
theorem unitalEquiv_frobenius (n : ℕ) (x : NonUnitalBigWittVector S C) :
    unitalEquiv (frobenius n x) = BigWittVector.frobenius n (unitalEquiv x) := by
  rw [unitalEquiv_apply, toBigWitt_frobenius, ← BigWittVector.frobenius_map,
    ← unitalEquiv_apply]

end Unital

end TauCeti.NonUnitalBigWittVector
