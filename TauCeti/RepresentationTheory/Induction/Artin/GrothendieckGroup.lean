/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Induction
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.FixedPointCount
public import TauCeti.RepresentationTheory.Induction.Artin.PermutationIdentity

/-!
# Artin's identity in the Grothendieck group of a group algebra

Let `G` be a finite group and put `a_C = C.artinCoeff * |C|` for each subgroup `C`; these vanish
unless `C` is cyclic. Artin's identity for fixed points (`TauCeti.sum_artinCoeff_mul_card_fixedBy`)
says that the virtual `G`-set `∑ C, a_C • G/C` has `|G|` fixed points under every element. This
file transfers it to the exact Grothendieck group `G₀(k[G])` of finitely generated
`k[G]`-modules, where it reads

```text
|G| • [k] = ∑ᶠ C, a_C • Ind_C^G [k].
```

The transfer goes through the two finite `G`-sets `ArtinPositiveSet G` and `ArtinNegativeSet G`
into which the signed identity splits. Their permutation classes are computed by additivity
(`TauCeti.permK0_artinPositiveSet`, `TauCeti.permK0_artinNegativeSet`), and the difference between
the two sides of Artin's identity in `G₀(k[G])` is exactly the difference of these two permutation
classes (`TauCeti.natCard_nsmul_of_trivial_sub_finsum_artinCoeff`). This holds over every
commutative ring `k`.

So Artin's identity in `G₀(k[G])` is equivalent to the equality of the permutation classes of two
finite `G`-sets with the same fixed-point counts. Over a field of characteristic zero such
`G`-sets have equivalent permutation representations, which gives the equality
(`TauCeti.permK0_eq_of_natCard_fixedBy_eq`) and hence Artin's identity
(`TauCeti.natCard_nsmul_of_trivial_eq_finsum_artinCoeff`). In characteristic `ℓ` dividing `|G|`
the two permutation modules need not be isomorphic, and this file does not prove the equality of
their classes there. The rationalizations of the integral permutation lattices are isomorphic
(`TauCeti.nonempty_equiv_rationalized_artinPermutationLattices`), but deducing the equality of the
classes in characteristic `ℓ` from that isomorphism needs a separate reduction theorem for
lattices, which is not available yet.

Multiplying the identity by a class and applying the projection formula is the route to Artin's
induction theorem in `G₀(k[G])` and to its modular form.

## Main results

* `TauCeti.permK0_artinPositiveSet`, `TauCeti.permK0_artinNegativeSet`: the permutation classes of
  the two Artin sets, as sums of classes induced from trivial lines.
* `TauCeti.natCard_nsmul_of_trivial_sub_finsum_artinCoeff`: over any commutative ring, the
  difference of the two sides of Artin's identity is the difference of the two Artin permutation
  classes.
* `TauCeti.natCard_nsmul_of_trivial_eq_finsum_artinCoeff`: **Artin's identity** in `G₀(k[G])` over
  a field of characteristic zero.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §9.2 and §12.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.4).
-/

public section

open MulAction
open scoped MonoidAlgebra

namespace TauCeti

universe u

section CommRing

variable (k : Type u) [CommRing k] (G : Type u) [Group G] [Finite G]

/-- **The permutation class of the positive Artin set.** It is the sum over the subgroups `C` of
`a_C⁺` times the class induced from the trivial line of `C`. -/
theorem permK0_artinPositiveSet :
    permK0 k G (ArtinPositiveSet G) = ∑ᶠ C : Subgroup G,
      letI : Module.Finite k[C] (Representation.trivial k C k).asModule :=
        Module.Finite.of_restrictScalars_finite k k[C] _
      (C.artinCoeff * (Nat.card C : ℤ)).toNat •
        indK0 k C (ExactK0.of (FGModuleCat.of k[C] (Representation.trivial k C k).asModule)) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  rw [permK0_congr k (artinPositiveSetEquiv G) (artinPositiveSetEquiv_smul G), permK0_sigma,
    finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [permK0_sigma_fin, indK0_of_trivial]

/-- **The permutation class of the negative Artin set.** It is `|G|` times the trivial class plus
the sum over the subgroups `C` of `a_C⁻` times the class induced from the trivial line of `C`. -/
theorem permK0_artinNegativeSet :
    letI : Module.Finite k[G] (Representation.trivial k G k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    permK0 k G (ArtinNegativeSet G) =
      Nat.card G • ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) +
        ∑ᶠ C : Subgroup G,
          letI : Module.Finite k[C] (Representation.trivial k C k).asModule :=
            Module.Finite.of_restrictScalars_finite k k[C] _
          (-(C.artinCoeff * (Nat.card C : ℤ))).toNat •
            indK0 k C (ExactK0.of (FGModuleCat.of k[C]
              (Representation.trivial k C k).asModule)) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  let : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  rw [permK0_congr k (artinNegativeSetEquiv G) (artinNegativeSetEquiv_smul G), permK0_sum,
    permK0_sigma_fin, permK0_of_subsingleton, permK0_sigma, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [permK0_sigma_fin, indK0_of_trivial]

/-- **The defect of Artin's identity is a difference of permutation classes.** Over any
commutative ring `k`, `|G| • [k] - ∑ᶠ C, a_C • Ind_C^G [k]` is the permutation class of the
negative Artin set minus that of the positive one. -/
theorem natCard_nsmul_of_trivial_sub_finsum_artinCoeff :
    letI : Module.Finite k[G] (Representation.trivial k G k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    Nat.card G • ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) -
        (∑ᶠ C : Subgroup G,
          letI : Module.Finite k[C] (Representation.trivial k C k).asModule :=
            Module.Finite.of_restrictScalars_finite k k[C] _
          (C.artinCoeff * (Nat.card C : ℤ)) •
            indK0 k C (ExactK0.of (FGModuleCat.of k[C]
              (Representation.trivial k C k).asModule))) =
      permK0 k G (ArtinNegativeSet G) - permK0 k G (ArtinPositiveSet G) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  rw [permK0_artinNegativeSet, permK0_artinPositiveSet]
  simp only [finsum_eq_sum_of_fintype]
  -- Each coefficient is the difference of its positive and negative parts.
  have h : ∀ (a : ℤ) (x : ExactK0 (finiteModulesExactStructure k[G])),
      a • x = a.toNat • x - (-a).toNat • x := fun a x ↦ by
    rw [← natCast_zsmul, ← natCast_zsmul, ← sub_smul, Int.toNat_sub_toNat_neg]
  simp only [h _ (indK0 k _ _), Finset.sum_sub_distrib]
  abel

end CommRing

section CharZero

variable (k : Type u) [Field k] [CharZero k] {G : Type u} [Group G] [Finite G]

variable (G) in
/-- **Artin's identity in the Grothendieck group, in characteristic zero.** Over a field of
characteristic zero, `|G|` times the class of the trivial line is the sum over the subgroups `C`
of `C.artinCoeff * |C|` times the class induced from the trivial line of `C`. Only cyclic
subgroups contribute (`Subgroup.artinCoeff_eq_zero_of_not_isCyclic`). -/
theorem natCard_nsmul_of_trivial_eq_finsum_artinCoeff :
    letI : Module.Finite k[G] (Representation.trivial k G k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    Nat.card G • ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) =
      ∑ᶠ C : Subgroup G,
        letI : Module.Finite k[C] (Representation.trivial k C k).asModule :=
          Module.Finite.of_restrictScalars_finite k k[C] _
        (C.artinCoeff * (Nat.card C : ℤ)) •
          indK0 k C (ExactK0.of (FGModuleCat.of k[C] (Representation.trivial k C k).asModule)) := by
  rw [← sub_eq_zero, natCard_nsmul_of_trivial_sub_finsum_artinCoeff,
    permK0_eq_of_natCard_fixedBy_eq k fun g ↦
      (card_fixedBy_artinPositiveSet_eq_card_fixedBy_artinNegativeSet g).symm, sub_self]

end CharZero

end TauCeti
