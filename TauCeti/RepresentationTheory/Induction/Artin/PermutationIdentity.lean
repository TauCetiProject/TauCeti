/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.ArtinCoefficient
public import TauCeti.RepresentationTheory.CharacterTable.FixedPointCount
public import TauCeti.GroupTheory.GroupAction.Burnside
public import TauCeti.RepresentationTheory.BaseChange
public import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Artin's identity as an equivalence of permutation representations

For a finite group `G`, put `a_C = C.artinCoeff * |C|`. Artin's identity says that
`∑ C, a_C * |(G/C)^g| = |G|` for every `g`. Splitting each integer coefficient into its
positive and negative parts gives two actual finite `G`-sets:

* `ArtinPositiveSet G` has `max a_C 0` copies of `G/C` for each subgroup `C`;
* `ArtinNegativeSet G` has `|G|` fixed points and `max (-a_C) 0` copies of `G/C`.

These sets have equal fixed-point counts, hence equivalent permutation representations over
every field of characteristic zero. In particular their integral permutation lattices become
isomorphic over `ℚ`. This turns the signed character identity into an isomorphism to which
lattice-reduction arguments can apply, even when the residue characteristic divides `|G|`.
Only cyclic subgroups contribute copies, since every other Artin coefficient vanishes.

The fixed-point calculation uses `sum_artinCoeff_mul_card_fixedBy`. The criterion
`nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq` supplies the representation equivalence,
and `baseChangeComapEquiv` identifies the rationalizations with those representations.

The actions use Mathlib's fiberwise actions on sigma types and sums: they leave the subgroup and
copy index fixed and translate the coset. The fixed points in `ArtinNegativeSet` are represented
by copies of `G/⊤`, so no extra trivial-action instance is needed. The equivariant equivalences
`artinPositiveSetEquiv` and `artinNegativeSetEquiv` expose these decompositions while leaving the
noncomputable action instances opaque.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §9.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, VII.3.
-/

public section

namespace TauCeti

open MulAction

universe u v

variable (G : Type u) [Group G] [Finite G]

/-- The disjoint union of the positive terms of Artin's permutation identity. A point records
a subgroup, a copy index, and a left coset of that subgroup. -/
def ArtinPositiveSet :=
  Σ C : Subgroup G, Σ _ : Fin (C.artinCoeff * (Nat.card C : ℤ)).toNat, G ⧸ C

instance : Finite (ArtinPositiveSet G) := by
  unfold ArtinPositiveSet
  infer_instance

-- Hide the inherited action too; code generation cannot unfold the hidden carrier.
@[no_expose]
noncomputable instance : MulAction G (ArtinPositiveSet G) := by
  unfold ArtinPositiveSet
  infer_instance

/-- The disjoint union of the negative terms of Artin's permutation identity, together with
`|G|` fixed points. The fixed points are copies of the singleton coset space `G/⊤`. -/
def ArtinNegativeSet :=
  (Σ _ : Fin (Nat.card G), G ⧸ (⊤ : Subgroup G)) ⊕
    (Σ C : Subgroup G, Σ _ : Fin (-(C.artinCoeff * (Nat.card C : ℤ))).toNat, G ⧸ C)

instance : Finite (ArtinNegativeSet G) := by
  unfold ArtinNegativeSet
  infer_instance

@[no_expose]
noncomputable instance : MulAction G (ArtinNegativeSet G) := by
  unfold ArtinNegativeSet
  infer_instance

/-- The positive Artin set as its defining sigma type. This equivalence exposes the decomposition
without exposing the noncomputable action instance on `ArtinPositiveSet`. -/
noncomputable def artinPositiveSetEquiv :
    ArtinPositiveSet G ≃
      Σ C : Subgroup G, Σ _ : Fin (C.artinCoeff * (Nat.card C : ℤ)).toNat, G ⧸ C :=
  Equiv.refl _

/-- `TauCeti.artinPositiveSetEquiv` is equivariant for the fiberwise action. -/
theorem artinPositiveSetEquiv_smul (g : G) (x : ArtinPositiveSet G) :
    artinPositiveSetEquiv G (g • x) = g • artinPositiveSetEquiv G x := by
  rfl

/-- The negative Artin set as the sum of its fixed-point and negative-coefficient sigma types.
This equivalence exposes the decomposition without exposing its noncomputable action instance. -/
noncomputable def artinNegativeSetEquiv :
    ArtinNegativeSet G ≃
      (Σ _ : Fin (Nat.card G), G ⧸ (⊤ : Subgroup G)) ⊕
        (Σ C : Subgroup G,
          Σ _ : Fin (-(C.artinCoeff * (Nat.card C : ℤ))).toNat, G ⧸ C) :=
  Equiv.refl _

/-- `TauCeti.artinNegativeSetEquiv` is equivariant for the fiberwise action. -/
theorem artinNegativeSetEquiv_smul (g : G) (x : ArtinNegativeSet G) :
    artinNegativeSetEquiv G (g • x) = g • artinNegativeSetEquiv G x := by
  rfl

variable {G}

/-- The fixed-point count of the positive Artin set, with its multiplicities explicit. -/
theorem card_fixedBy_artinPositiveSet (g : G) :
    Nat.card (fixedBy (ArtinPositiveSet G) g) =
      ∑ᶠ C : Subgroup G,
        (C.artinCoeff * (Nat.card C : ℤ)).toNat * Nat.card (fixedBy (G ⧸ C) g) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  delta ArtinPositiveSet instMulActionArtinPositiveSet
  rw [card_fixedBy_sigma]
  simp only [card_fixedBy_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, finsum_eq_sum_of_fintype]

/-- The positive Artin fixed-point count with explicit multiplicities, in simp normal form. -/
@[simp]
theorem ncard_fixedBy_artinPositiveSet (g : G) :
    (fixedBy (ArtinPositiveSet G) g).ncard =
      ∑ᶠ C : Subgroup G,
        (C.artinCoeff * (Nat.card C : ℤ)).toNat * (fixedBy (G ⧸ C) g).ncard := by
  simpa only [Nat.card_coe_set_eq] using card_fixedBy_artinPositiveSet g

/-- The fixed-point count of the negative Artin set includes the `|G|` fixed points. -/
theorem card_fixedBy_artinNegativeSet (g : G) :
    Nat.card (fixedBy (ArtinNegativeSet G) g) = Nat.card G +
      ∑ᶠ C : Subgroup G,
        (-(C.artinCoeff * (Nat.card C : ℤ))).toNat * Nat.card (fixedBy (G ⧸ C) g) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  let : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have htop : fixedBy (G ⧸ (⊤ : Subgroup G)) g = Set.univ := by
    ext x
    simp [mem_fixedBy, Subsingleton.elim (g • x) x]
  delta ArtinNegativeSet instMulActionArtinNegativeSet
  rw [card_fixedBy_sum]
  simp only [card_fixedBy_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, htop, Nat.card_congr (Equiv.Set.univ (G ⧸ (⊤ : Subgroup G))),
    Nat.card_unique, mul_one, finsum_eq_sum_of_fintype]

/-- The negative Artin fixed-point count including the fixed points, in simp normal form. -/
@[simp]
theorem ncard_fixedBy_artinNegativeSet (g : G) :
    (fixedBy (ArtinNegativeSet G) g).ncard = Nat.card G +
      ∑ᶠ C : Subgroup G,
        (-(C.artinCoeff * (Nat.card C : ℤ))).toNat * (fixedBy (G ⧸ C) g).ncard := by
  simpa only [Nat.card_coe_set_eq] using card_fixedBy_artinNegativeSet g

/-- The two sides of Artin's permutation identity have the same fixed-point counts. -/
theorem card_fixedBy_artinPositiveSet_eq_card_fixedBy_artinNegativeSet (g : G) :
    Nat.card (fixedBy (ArtinPositiveSet G) g) =
      Nat.card (fixedBy (ArtinNegativeSet G) g) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  rw [card_fixedBy_artinPositiveSet, card_fixedBy_artinNegativeSet]
  have h := sum_artinCoeff_mul_card_fixedBy g
  simp only [finsum_eq_sum_of_fintype] at h ⊢
  apply Int.natCast_inj.mp
  push_cast
  have hsplit : ∀ C : Subgroup G,
      ((C.artinCoeff * (Nat.card C : ℤ)).toNat : ℤ) * Nat.card (fixedBy (G ⧸ C) g) -
        ((-(C.artinCoeff * (Nat.card C : ℤ))).toNat : ℤ) * Nat.card (fixedBy (G ⧸ C) g) =
          C.artinCoeff * Nat.card C * Nat.card (fixedBy (G ⧸ C) g) := by
    intro C
    rw [← sub_mul, Int.toNat_sub_toNat_neg]
  have hdiff := Finset.sum_congr rfl (fun C (_ : C ∈ (Finset.univ : Finset (Subgroup G))) ↦
    hsplit C)
  rw [Finset.sum_sub_distrib, h] at hdiff
  omega

variable (G)

/-- Artin's signed permutation identity is an equivalence of actual representations over any
characteristic-zero field. In particular, at `k = ℚ` it gives the rational isomorphism needed to
compare the reductions of the two integral permutation lattices. -/
theorem nonempty_equiv_artinPermutationRepresentations (k : Type v) [Field k] [CharZero k] :
    Nonempty ((Representation.ofMulAction k G (ArtinPositiveSet G)).Equiv
      (Representation.ofMulAction k G (ArtinNegativeSet G))) :=
  (nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq k).mpr
    card_fixedBy_artinPositiveSet_eq_card_fixedBy_artinNegativeSet

section Lattices

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction Finsupp.comapDistribMulAction
  comapSMulCommClass

/-- The two integral permutation lattices in Artin's identity have isomorphic rationalizations.
The integral lattices themselves need not be isomorphic. -/
theorem nonempty_equiv_rationalized_artinPermutationLattices :
    Nonempty ((Representation.baseChange ℚ
        (Representation.ofDistribMulAction ℤ G (ArtinPositiveSet G →₀ ℤ))).Equiv
      (Representation.baseChange ℚ
        (Representation.ofDistribMulAction ℤ G (ArtinNegativeSet G →₀ ℤ)))) := by
  obtain ⟨e⟩ := nonempty_equiv_artinPermutationRepresentations G ℚ
  exact ⟨((baseChangeComapEquiv ℤ ℚ G (ArtinPositiveSet G)).trans e).trans
    (baseChangeComapEquiv ℤ ℚ G (ArtinNegativeSet G)).symm⟩

end Lattices

end TauCeti
