/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import TauCeti.RepresentationTheory.Homological.Augmentation
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced

/-!
# The Tate dimension shift along the augmentation sequence

For a group `G`, the augmentation sequence `0 ⟶ I_G ⟶ k[G] ⟶ k ⟶ 0` (built in
`TauCeti.RepresentationTheory.Homological.Augmentation`) has a middle term whose Tate cohomology
vanishes for every finite subgroup, because the left regular representation is Tate-acyclic. Its
connecting homomorphisms are therefore isomorphisms `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` in every degree,
for every finite subgroup `S ≤ G`. The ambient group need not be finite; only `S` need be, since
only its Tate cohomology is formed. This is the first of the two dimension shifts behind Tate's
theorem; the second is the splitting module of a two-dimensional class.

## Main definitions

* `TauCeti.TateCohomology.augmentationδIso`: `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` for every finite
  subgroup `S` of a group `G` and every `n : ℤ`.

## Main statements

* `TauCeti.TateCohomology.augmentationδIso_hom`: the shift is the connecting homomorphism.
* `TauCeti.groupCohomology.isZero_H2_augmentationIdeal_res`: `H²(S, I_G) = 0` for a finite
  subgroup `S` when `k` has no additive torsion, since it is `H¹(S, k) = Hom(S, k)`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, proof of Theorem 3.11.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (3.1.4).
* The same dimension shift appears in `ClassFieldTheory/Cohomology/AugmentationModule.lean` in
  `kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509` (Apache-2.0);
  it is reimplemented here on Mathlib's Tate long-exact-sequence API rather than copied.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace TauCeti.TateCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype S]

variable (k) in
/-- **The augmentation dimension shift**: `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` for every finite subgroup
`S` of a group `G` and every `n : ℤ`, given by the connecting homomorphism of the augmentation
sequence. -/
def augmentationδIso (n : ℤ) :
    tateCohomology (res S.subtype (trivial k G k)) n ≅
      tateCohomology (res S.subtype (augmentationIdeal k G)) (n + 1) :=
  -- the restriction of `k[G]` to `S` is Tate-acyclic
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
    (augmentationSES_res_shortExact k G S.subtype)).δIso n (n + 1) rfl
      (isZero_res_leftRegular S n) (isZero_res_leftRegular S (n + 1))

/-- The augmentation dimension shift is the connecting homomorphism. -/
@[simp]
theorem augmentationδIso_hom (n : ℤ) :
    (augmentationδIso k S n).hom =
      _root_.TateCohomology.δ (augmentationSES_res_shortExact k G S.subtype) n := (rfl)

end TauCeti.TateCohomology

namespace TauCeti.groupCohomology

open _root_.groupCohomology Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- **`H²(S, I_G) = 0`** for a finite subgroup `S` of a group `G` and a coefficient ring `k`
without additive torsion. -/
theorem isZero_H2_augmentationIdeal_res (S : Subgroup G) [Finite S] [IsAddTorsionFree k] :
    IsZero (groupCohomology (res S.subtype (augmentationIdeal k G)) 2) :=
  -- the connecting homomorphism of the augmentation sequence identifies `H²(S, I_G)` with
  -- `H¹(S, k)`, which vanishes (Milne II, proof of Theorem 3.11)
  have : Fintype S := Fintype.ofFinite S
  have : (res S.subtype (trivial k G k)).IsTrivial := ⟨fun _ ↦ rfl⟩
  (isZero_H1_of_isTrivial (res S.subtype (trivial k G k))).of_iso <|
    ((_root_.TateCohomology.isoGroupCohomology 2).app (res S.subtype (augmentationIdeal k G))).symm
      ≪≫ (TateCohomology.augmentationδIso k S 1).symm ≪≫
      (_root_.TateCohomology.isoGroupCohomology 1).app (res S.subtype (trivial k G k))

end TauCeti.groupCohomology
