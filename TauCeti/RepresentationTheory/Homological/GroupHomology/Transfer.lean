/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# Transfer in group homology

Let `S` be a finite-index subgroup of a group `G`. Group homology has a transfer map

`H_n(G, M) ⟶ H_n(S, Resˢᴳ M)`.

Unlike the covariant map induced by the inclusion `S → G`, the transfer goes against the group
homomorphism. It is obtained from the unit `M ⟶ Indˢᴳ Resˢᴳ M` of the finite-index
adjunction, followed by Shapiro's isomorphism
`H_n(G, Indˢᴳ Resˢᴳ M) ≃ H_n(S, Resˢᴳ M)`. Transporting it across the negative-degree
comparison gives restriction in Tate cohomology below degree `-1`.

Followed by corestriction `H_n(S, Resˢᴳ M) ⟶ H_n(G, M)`, the map induced by the inclusion, the
transfer is multiplication by the index `[G : S]`. Read through Shapiro's isomorphism,
corestriction is the map induced by the counit `Indˢᴳ Resˢᴳ M ⟶ M`
(`TauCeti.groupHomology.indIso_inv_comp_map_counit`), and the unit followed by the counit is
`[G : S]`.

## Main definitions

* `TauCeti.groupHomology.transfer`: the transfer from a group to a finite-index subgroup.

## Main results

* `TauCeti.groupHomology.transfer_comp_indIso_inv`: through the inverse of Shapiro's isomorphism,
  transfer is the map induced by the unit of the finite-index adjunction.
* `TauCeti.groupHomology.transfer_comp_map_subtype_id`: corestriction after transfer is
  multiplication by the index `[G : S]`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, Sections 9–10.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.groupHomology

variable {R G : Type u} [CommRing R] [Group G]

open scoped Classical in
/-- The transfer in group homology from a group to a finite-index subgroup. It is the map induced
by the unit `M ⟶ Indˢᴳ Resˢᴳ M`, followed by the homological Shapiro isomorphism. -/
def transfer (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    _root_.groupHomology M n ⟶ _root_.groupHomology (Rep.res S.subtype M) n :=
  (_root_.groupHomology.functor R G n).map ((Rep.resIndAdjunction R S).unit.app M) ≫
    (_root_.groupHomology.indIso S (Rep.res S.subtype M) n).hom

open scoped Classical in
/-- Through the inverse of the homological Shapiro isomorphism, transfer is the map induced by
the unit of the finite-index induction--restriction adjunction. -/
@[reassoc (attr := simp)]
theorem transfer_comp_indIso_inv (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    transfer M S n ≫ (_root_.groupHomology.indIso S (Rep.res S.subtype M) n).inv =
      (_root_.groupHomology.functor R G n).map ((Rep.resIndAdjunction R S).unit.app M) :=
  -- Cancelling Shapiro's isomorphism against the definition, rather than rewriting with
  -- `Iso.hom_inv_id`: the two occurrences of `Resˢᴳ M` carry different `Monoid ↥S` instances, so
  -- the rewrite does not match syntactically, while this equation holds by `rfl`.
  (Iso.comp_inv_eq _).2 rfl

open scoped Classical in
/-- **Corestriction after transfer is multiplication by the index**: for a finite-index subgroup
`S ≤ G`, the composite `Hₙ(G, M) ⟶ Hₙ(S, Res_S M) ⟶ Hₙ(G, M)` of the transfer and corestriction
is `[G : S]` times the identity, in every degree `n`. -/
@[reassoc, elementwise]
theorem transfer_comp_map_subtype_id (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    transfer M S n ≫ _root_.groupHomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n =
      S.index • 𝟙 _ := by
  -- On inhomogeneous chains, the map induced by `[G : S] • 𝟙 M` is `[G : S]` times the identity.
  have hchains : _root_.groupHomology.chainsMap (MonoidHom.id G) (S.index • 𝟙 M) =
      S.index • 𝟙 (_root_.groupHomology.inhomogeneousChains M) := by
    refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext ?_
    rw [_root_.groupHomology.chainsMap_id_f_hom_eq_mapRange]
    refine Finsupp.lhom_ext fun x a => ?_
    simp [Rep.nsmul_hom, Finsupp.smul_single, -nsmul_eq_mul]
  rw [← TauCeti.groupHomology.indIso_inv_comp_map_counit, transfer_comp_indIso_inv_assoc,
    _root_.groupHomology.functor_map, ← _root_.groupHomology.map_id_comp,
    TauCeti.Rep.resIndAdjunction_unit_app_comp_indResAdjunction_counit_app,
    _root_.groupHomology.map, hchains]
  exact (HomologicalComplex.homologyFunctor _ _ n).map_nsmul.trans
    (congrArg (S.index • ·) ((HomologicalComplex.homologyFunctor _ _ n).map_id _))

end TauCeti.groupHomology
