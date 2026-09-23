/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Functoriality
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
* `TauCeti.groupHomology.map_comp_transfer`: the transfer is natural in the coefficients.
* `TauCeti.groupHomology.transfer_comp_map_subtype_id`: corestriction after transfer is
  multiplication by the index `[G : S]`.
* `TauCeti.groupHomology.transfer_zero_H0π`: in degree zero, where group homology is the module of
  coinvariants, the transfer is the relative transfer `Representation.relTransfer`,
  `⟦m⟧ ↦ ⟦∑_{q ∈ G ⧸ S} q⁻¹ • m⟧`.

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

/-- **The transfer is natural in the coefficients**: for a morphism `φ : M ⟶ N` of
`G`-representations, transfer intertwines the map `Hₙ(G, M) ⟶ Hₙ(G, N)` induced by `φ` with the
map `Hₙ(S, Res_S M) ⟶ Hₙ(S, Res_S N)` induced by its restriction to `S`. The cohomological
counterpart, for corestriction, is `TauCeti.groupCohomology.map_comp_corestriction`. -/
@[reassoc, elementwise]
theorem map_comp_transfer {M N : Rep R G} (φ : M ⟶ N) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    _root_.groupHomology.map (MonoidHom.id G) φ n ≫ transfer N S n = transfer M S n ≫
      _root_.groupHomology.map (MonoidHom.id S) ((Rep.resFunctor S.subtype).map φ) n := by
  classical
  -- Cancel Shapiro's isomorphism: both sides become `Hₙ(G, -)` applied to the unit
  -- `M ⟶ Ind_S^G Res_S M` of the finite-index adjunction, which is natural in `φ`.
  rw [← cancel_mono (_root_.groupHomology.indIso S _ n).inv, Category.assoc, Category.assoc,
    indIso_inv_naturality, transfer_comp_indIso_inv, transfer_comp_indIso_inv_assoc]
  -- The universes of `Rep.resIndAdjunction` are pinned: left to unification, the constraint
  -- `max ?w u u = u` makes this definitional check cost seconds.
  exact (Functor.whiskerRight (Rep.resIndAdjunction.{u, u, u} R S).unit
    (_root_.groupHomology.functor R G n)).naturality φ

open scoped Classical in
/-- **Corestriction after transfer is multiplication by the index**: for a finite-index subgroup
`S ≤ G`, the composite `Hₙ(G, M) ⟶ Hₙ(S, Res_S M) ⟶ Hₙ(G, M)` of the transfer and corestriction
is `[G : S]` times the identity, in every degree `n`. -/
@[reassoc, elementwise]
theorem transfer_comp_map_subtype_id (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    transfer M S n ≫ _root_.groupHomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n =
      S.index • 𝟙 _ := by
  have hsmul : _root_.groupHomology.map (MonoidHom.id G) (S.index • 𝟙 M) n =
      (HomologicalComplex.homologyFunctor _ _ n).map
        ((_root_.groupHomology.chainsFunctor R G).map (S.index • 𝟙 M)) := by
    rw [_root_.groupHomology.map, HomologicalComplex.homologyFunctor_map,
      _root_.groupHomology.chainsFunctor_map]
    rfl
  rw [← TauCeti.groupHomology.indIso_inv_comp_map_counit, transfer_comp_indIso_inv_assoc,
    _root_.groupHomology.functor_map, ← _root_.groupHomology.map_id_comp,
    TauCeti.Rep.resIndAdjunction_unit_app_comp_indResAdjunction_counit_app,
    hsmul, Functor.map_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact congrArg (S.index • ·) (CategoryTheory.Functor.map_id _ _)

section DegreeZero

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open scoped Classical in
/-- **In degree zero, the transfer is the relative transfer on coinvariants.** Group homology in
degree zero is the module of coinvariants, and the transfer `H₀(G, M) ⟶ H₀(S, Res_S M)` sends the
class of `m` to the class of `∑_{q ∈ G ⧸ S} q⁻¹ • m`, the relative transfer
`Representation.relTransfer`. -/
-- `simp` reduces the carrier of `ModuleCat.of R M.V` to `M.V` in the implicit arguments of the
-- coercion before looking the term up, so `dsimp% only` states the left-hand side in that form
-- (the idiom of #8315).
@[simp]
theorem transfer_zero_H0π (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (m : M.V) :
    (dsimp% only (transfer M S 0 (_root_.groupHomology.H0π M m))) =
      _root_.groupHomology.H0π (Rep.res S.subtype M) (Representation.relTransfer M.ρ S m) := by
  -- Shapiro's inverse is injective and is the change-of-group map along `S ≤ G` (`indIso_inv`),
  -- so it suffices to compare both sides as classes in `H₀(G, Ind_S^G Res_S M)`.
  apply (ModuleCat.mono_iff_injective
    (_root_.groupHomology.indIso S (Rep.res S.subtype M) 0).inv).1 inferInstance
  rw [← ModuleCat.comp_apply, transfer_comp_indIso_inv, indIso_inv]
  simp only [_root_.groupHomology.functor_map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, _root_.groupHomology.H0π_comp_map,
    _root_.groupHomology.H0π_comp_map]
  simp only [Functor.comp_obj]
  apply (ModuleCat.mono_iff_injective
    (_root_.groupHomology.H0Iso ((indFunctor R S.subtype).obj (res S.subtype M))).hom).1
    inferInstance
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, Category.assoc, Category.assoc,
    _root_.groupHomology.H0π_comp_H0Iso_hom, ModuleCat.comp_apply, ModuleCat.comp_apply]
  -- Both units are explicit by definition: `resIndAdjunction`'s goes through `coindToInd`, and
  -- `indResAdjunction`'s is `a ↦ ⟦1 ⊗ a⟧`.
  -- The ascription elaborates the lemma before matching it against the goal, about ten times
  -- cheaper than propagating the goal into its arguments.
  exact (Rep.coinvariantsMk_coindToInd_unit M S m :)

end DegreeZero

end TauCeti.groupHomology
