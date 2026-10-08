/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Projection
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.FixedPointCount
public import TauCeti.RepresentationTheory.Induction.Artin.PermutationIdentity

/-!
# Artin's identity in the exact Grothendieck ring

For a finite group `G`, let `a_C = C.artinCoeff * |C|`.  The two actual `G`-sets
`TauCeti.ArtinPositiveSet G` and `TauCeti.ArtinNegativeSet G` split the positive and negative
parts of the coefficients `a_C`. Their fixed-point counts agree, so the permutation-class
comparison identifies their classes in `G₀(k[G])` over every field, including when the
characteristic divides `|G|`.
Expanding the two disjoint unions and recombining the positive and negative parts gives

`|G| [k] = ∑ᶠ C, a_C [k[G/C]]`.

Rewriting the coset classes as induced units gives Artin's identity in the Grothendieck ring.
The projection formula then gives the identity for every virtual class by multiplication.

## Main results

* `TauCeti.permK0_artinPositiveSet` and `TauCeti.permK0_artinNegativeSet`: expansion of the two
  Artin permutation classes.
* `TauCeti.permK0_artinPositiveSet_eq_artinNegativeSet`: their classes agree over every field.
* `TauCeti.natCard_nsmul_permK0_quotient_top_eq_sum_artinCoeff`: the signed permutation-class
  identity.
* `TauCeti.natCard_nsmul_one_eq_sum_artinCoeff_indK0`: Artin's identity written with
  induction from subgroups.
* `TauCeti.natCard_nsmul_eq_sum_artinCoeff_indK0_resK0`: the identity for every virtual class.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part II, §9.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  VII.3, (7.3.3)–(7.3.4).
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u

section Expansion

variable (k G : Type u) [CommRing k] [Group G] [Finite G]

/-- The class of the positive Artin set is the sum of the positive parts of the Artin
coefficients times the corresponding coset classes. -/
theorem permK0_artinPositiveSet : permK0 k G (ArtinPositiveSet G) =
    ∑ᶠ C : Subgroup G,
      (C.artinCoeff * (Nat.card C : ℤ)).toNat • permK0 k G (G ⧸ C) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  rw [permK0_congr k (artinPositiveSetEquiv G) (artinPositiveSetEquiv_smul G), permK0_sigma]
  simp only [permK0_sigma_fin, finsum_eq_sum_of_fintype]

/-- The class of the negative Artin set is the sum of `|G|` fixed points and the negative parts
of the Artin coefficients times the corresponding coset classes. -/
theorem permK0_artinNegativeSet :
    permK0 k G (ArtinNegativeSet G) =
      Nat.card G • permK0 k G (G ⧸ (⊤ : Subgroup G)) +
        ∑ᶠ C : Subgroup G,
          (-(C.artinCoeff * (Nat.card C : ℤ))).toNat • permK0 k G (G ⧸ C) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  rw [permK0_congr k (artinNegativeSetEquiv G) (artinNegativeSetEquiv_smul G),
    permK0_sum, permK0_sigma_fin, permK0_sigma]
  simp only [permK0_sigma_fin, finsum_eq_sum_of_fintype]

end Expansion

section Field

variable (k G : Type u) [Field k] [Group G] [Finite G]

/-- The positive and negative Artin sets have equal permutation classes over every field. -/
theorem permK0_artinPositiveSet_eq_artinNegativeSet :
    permK0 k G (ArtinPositiveSet G) = permK0 k G (ArtinNegativeSet G) :=
  permK0_eq_of_forall_natCard_fixedBy_eq k
    card_fixedBy_artinPositiveSet_eq_card_fixedBy_artinNegativeSet

/-- **Artin's signed permutation identity in the exact Grothendieck group over every field.** -/
theorem natCard_nsmul_permK0_quotient_top_eq_sum_artinCoeff :
    Nat.card G • permK0 k G (G ⧸ (⊤ : Subgroup G)) =
      ∑ᶠ C : Subgroup G,
        (C.artinCoeff * (Nat.card C : ℤ)) • permK0 k G (G ⧸ C) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  have h := permK0_artinPositiveSet_eq_artinNegativeSet k G
  rw [permK0_artinPositiveSet, permK0_artinNegativeSet] at h
  simp only [finsum_eq_sum_of_fintype] at h ⊢
  calc
    Nat.card G • permK0 k G (G ⧸ (⊤ : Subgroup G)) =
        (∑ C : Subgroup G,
            (C.artinCoeff * (Nat.card C : ℤ)).toNat • permK0 k G (G ⧸ C)) -
          ∑ C : Subgroup G,
            (-(C.artinCoeff * (Nat.card C : ℤ))).toNat • permK0 k G (G ⧸ C) := by
              rw [h]
              abel
    _ = ∑ C : Subgroup G,
          ((C.artinCoeff * (Nat.card C : ℤ)).toNat • permK0 k G (G ⧸ C) -
            (-(C.artinCoeff * (Nat.card C : ℤ))).toNat • permK0 k G (G ⧸ C)) := by
              rw [Finset.sum_sub_distrib]
    _ = ∑ C : Subgroup G,
          (C.artinCoeff * (Nat.card C : ℤ)) • permK0 k G (G ⧸ C) := by
      apply Finset.sum_congr rfl
      intro C _
      rw [← natCast_zsmul, ← natCast_zsmul, sub_eq_add_neg, ← sub_zsmul,
        Int.toNat_sub_toNat_neg]

/-- **Artin's identity in `G₀(k[G])` over every field**, written as induction of the unit
from subgroups. No division by the group order is required. -/
theorem natCard_nsmul_one_eq_sum_artinCoeff_indK0 :
    Nat.card G • (1 : ExactK0 (finiteModulesExactStructure k[G])) =
      ∑ᶠ C : Subgroup G, (C.artinCoeff * (Nat.card C : ℤ)) • indK0 k C 1 := by
  let : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  simpa only [permK0_of_subsingleton, ← exactK0_one_eq_of_trivial, indK0_one] using
    natCard_nsmul_permK0_quotient_top_eq_sum_artinCoeff k G

/-- **Artin's induction identity for every virtual class over every field.** Multiplying by
`|G|` expresses a class as the Artin-coefficient sum of its induced restrictions. -/
theorem natCard_nsmul_eq_sum_artinCoeff_indK0_resK0
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    Nat.card G • x = ∑ᶠ C : Subgroup G,
      (C.artinCoeff * (Nat.card C : ℤ)) • indK0 k C (resK0 k C.subtype x) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  have h := congrArg (· * x) (natCard_nsmul_one_eq_sum_artinCoeff_indK0 k G)
  simpa only [finsum_eq_sum_of_fintype, Finset.sum_mul, smul_mul_assoc, one_mul,
    ← indK0_mul_resK0] using h

end Field

end TauCeti
