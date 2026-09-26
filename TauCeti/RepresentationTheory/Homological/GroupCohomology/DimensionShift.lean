/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Coinduced
public import TauCeti.RepresentationTheory.Induction.DimensionShift

/-!
# Dimension shifting in ordinary group cohomology

For a representation `A` of a group `G`, the upward dimension-shifting sequence

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0`

has a middle term whose cohomology vanishes in every positive degree (Shapiro's lemma). Its
connecting homomorphism is therefore an isomorphism `Hⁿ⁺¹(G, dimensionShiftUp A) ≅ Hⁿ⁺²(G, A)`,
and surjective in the remaining degree `H⁰(G, dimensionShiftUp A) ⟶ H¹(G, A)`. The same holds
after restriction to any subgroup, so a vanishing hypothesis can be moved between degrees
simultaneously on all subgroups, which is what the inflation-restriction sequence needs.

Only the upward sequence appears here. The downward sequence has `Ind_⊥^G A` as its middle term,
which is acyclic for ordinary cohomology only when `G` is finite; the downward shift is therefore
stated for Tate cohomology instead, in `TauCeti.TateCohomology.dimensionShiftDownIso`.

Each isomorphism below has Mathlib's `groupCohomology.δ` as its forward map, so its naturality is
the existing naturality of `δ` and no abstract choice of isomorphism enters.

## Main definitions

* `TauCeti.groupCohomology.dimensionShiftUpIso`, `dimensionShiftUpResIso`: the shift as an
  isomorphism, over `G` and after restriction to a subgroup.

## Main statements

* `TauCeti.groupCohomology.dimensionShiftUpIso_hom`, `dimensionShiftUpResIso_hom`: the shift is
  Mathlib's connecting homomorphism `groupCohomology.δ` of `Rep.dimensionShiftUpSES`.
* `TauCeti.groupCohomology.isZero_dimensionShiftUp_iff`,
  `TauCeti.groupCohomology.isZero_res_dimensionShiftUp_iff`: the shift moves a vanishing
  hypothesis between degrees, which is the form the inflation-restriction sequence consumes.
* `TauCeti.groupCohomology.epi_δ_dimensionShiftUp_zero`,
  `TauCeti.groupCohomology.epi_δ_res_dimensionShiftUp_zero`: in the remaining degree the
  connecting homomorphism `H⁰(dimensionShiftUp A) ⟶ H¹(A)` is only surjective, over `G` and
  after restriction to a subgroup.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1 (dimension shifting, 1.13).
* K. S. Brown, *Cohomology of Groups*, III §7.
* The same statements appear in `ClassFieldTheory/Cohomology/Functors/UpDown.lean` in
  `kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509` (Apache-2.0), as
  `δ_up_isIso`, `isIso_δ_up_res` and the `epi_δ_*_zero` family; they are reimplemented here on Tau
  Ceti's `dimensionShiftUp*` API and Mathlib's `groupCohomology.δ`, with a different degree
  indexing and without that file's separate `IsIso` declarations.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

-- The sequence is presented through `ShortComplex.mk`, with short exactness transported from
-- `dimensionShiftUpSES_shortExact` along `dimensionShiftUpSES_def`, so that its terms are visible
-- without exposing the body of `dimensionShiftUpSES`. This is the presentation the merged
-- `TauCeti.TateCohomology.dimensionShiftUpIso` uses.

/-- **Dimension shifting** as an isomorphism: `Hⁿ⁺¹(G, dimensionShiftUp A) ≅ Hⁿ⁺²(G, A)`, the
connecting homomorphism of the coinduced sequence, whose middle term has vanishing cohomology
in both degrees (Shapiro's lemma). The forward map is Mathlib's `δ`, so naturality is free;
degree `0` is only an epimorphism, hence the indexing starts at `n + 1`. -/
def dimensionShiftUpIso (n : ℕ) :
    groupCohomology (dimensionShiftUp A) (n + 1) ≅ groupCohomology A (n + 2) :=
  (map_cochainsFunctor_shortExact
    (X := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A))
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A)).δIso
      (n + 1) (n + 2) rfl (isZero_coindBot_succ A.V n) (isZero_coindBot_succ A.V (n + 1))

/-- The dimension-shifting isomorphism is the connecting homomorphism. -/
@[simp]
theorem dimensionShiftUpIso_hom (n : ℕ) :
    (dimensionShiftUpIso A n).hom =
      δ (X := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
          (coindBotUnit_comp_dimensionShiftUpπ A))
        (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A)
        (n + 1) (n + 2) rfl := (rfl)

/-- Vanishing in degree `n + 1` of an upward shift is vanishing in degree `n + 2` of the
original module. This is the form in which the shift is consumed: it moves a vanishing
hypothesis between degrees. -/
@[simp]
theorem isZero_dimensionShiftUp_iff (n : ℕ) :
    IsZero (groupCohomology (dimensionShiftUp A) (n + 1)) ↔
      IsZero (groupCohomology A (n + 2)) :=
  (dimensionShiftUpIso A n).isZero_iff

/-- In the remaining degree the connecting homomorphism `H⁰(G, dimensionShiftUp A) ⟶ H¹(G, A)`
is surjective: Shapiro's lemma only gives vanishing of the coinduced middle term in positive
degrees, so degree `0` has the input an epimorphism needs but not the second input an
isomorphism would need. -/
theorem epi_δ_dimensionShiftUp_zero :
    Epi (δ (X := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
        (coindBotUnit_comp_dimensionShiftUpπ A))
      (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A) 0 1 rfl) :=
  epi_δ_of_isZero _ 0 (isZero_coindBot_succ A.V 0)

variable (S : Subgroup G)

/-- Dimension shifting after restriction to a subgroup, as an isomorphism:
`Hⁿ⁺¹(S, dimensionShiftUp A) ≅ Hⁿ⁺²(S, A)`. The forward map is Mathlib's `δ`, so naturality is
free; degree `0` is only an epimorphism, hence the indexing starts at `n + 1`. -/
def dimensionShiftUpResIso (n : ℕ) :
    groupCohomology (res S.subtype (dimensionShiftUp A)) (n + 1) ≅
      groupCohomology (res S.subtype A) (n + 2) :=
  (map_cochainsFunctor_shortExact
    (X := (ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A)).map (resFunctor S.subtype))
    (by simpa only [dimensionShiftUpSES_def] using
      dimensionShiftUpSES_res_shortExact A S.subtype)).δIso (n + 1) (n + 2) rfl
        (isZero_res_coindBot_succ S A.V n) (isZero_res_coindBot_succ S A.V (n + 1))

/-- The restricted dimension-shifting isomorphism is the connecting homomorphism. -/
@[simp]
theorem dimensionShiftUpResIso_hom (n : ℕ) :
    (dimensionShiftUpResIso A S n).hom =
      δ (X := (ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
          (coindBotUnit_comp_dimensionShiftUpπ A)).map (resFunctor S.subtype))
        (by simpa only [dimensionShiftUpSES_def] using
          dimensionShiftUpSES_res_shortExact A S.subtype) (n + 1) (n + 2) rfl := (rfl)

/-- After restriction to a subgroup, vanishing in degree `n + 1` of an upward shift is
vanishing in degree `n + 2` of the original module. Together with the unrestricted form this
moves a vanishing hypothesis between degrees simultaneously on every subgroup. -/
@[simp]
theorem isZero_res_dimensionShiftUp_iff (n : ℕ) :
    IsZero (groupCohomology (res S.subtype (dimensionShiftUp A)) (n + 1)) ↔
      IsZero (groupCohomology (res S.subtype A) (n + 2)) :=
  (dimensionShiftUpResIso A S n).isZero_iff

/-- After restriction to a subgroup, the connecting homomorphism
`H⁰(S, dimensionShiftUp A) ⟶ H¹(S, A)` is surjective: Shapiro's lemma only gives vanishing of
the coinduced middle term in positive degrees, so degree `0` has the input an epimorphism needs
but not the second input an isomorphism would need. -/
theorem epi_δ_res_dimensionShiftUp_zero :
    Epi (δ (X := (ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
        (coindBotUnit_comp_dimensionShiftUpπ A)).map (resFunctor S.subtype))
      (by simpa only [dimensionShiftUpSES_def] using
        dimensionShiftUpSES_res_shortExact A S.subtype) 0 1 rfl) :=
  epi_δ_of_isZero _ 0 (isZero_res_coindBot_succ S A.V 0)

end TauCeti.groupCohomology
