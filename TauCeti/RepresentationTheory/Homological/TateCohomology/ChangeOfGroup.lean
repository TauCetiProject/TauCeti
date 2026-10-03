/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupCohomology

/-!
# Change of group in positive Tate degrees

Let `φ : G →* Q` be a homomorphism of finite groups, `M` a representation of `Q`, `N` a
representation of `G` and `f : Res_φ M ⟶ N` a morphism of `G`-representations. Ordinary group
cohomology has the change-of-group map `groupCohomology.map φ f n : Hⁿ(Q, M) ⟶ Hⁿ(G, N)`. In
positive degrees Mathlib identifies Tate cohomology with ordinary cohomology, and this file
transports the change-of-group map across that identification as `TauCeti.TateCohomology.posMap`.

Positive-degree restriction to a subgroup (`TauCeti.TateCohomology.posRes`: `φ` the inclusion,
`f` the identity) and inflation from a quotient (`TauCeti.TateCohomology.infl`: `φ` the quotient
map, `f` the inclusion of invariants) are both of this form. In degree zero there is no such map
in general: for a surjective `φ` the norm of `G` on `Res_φ M` is `|ker φ|` times the norm of `Q`,
so a norm of `Q` need not be a norm of `G`, and the quotient of invariants by norms does not map
along the identity of invariants.

The change-of-group map is natural in both coefficient representations (`posMap_comp_map`,
`map_comp_posMap`), and it commutes with the connecting maps of short exact sequences
(`δ_comp_posMap`). The degree-zero source of a connecting map is a quotient of the ordinary
invariants, so the compatibility is stated on ordinary cohomology classes through the comparison
`Rep.fromGroupCohomology`, which also covers the connecting map from degree zero to degree one
(`fromGroupCohomology_δ_comp_posMap`). This is what allows a statement about change of group to
be moved across degrees by dimension shifting, as in the compatibility of the Tate cup product
with inflation.

## Main definitions

* `TauCeti.TateCohomology.posMap`: the change-of-group map in a positive Tate degree.

## Main results

* `TauCeti.TateCohomology.fromGroupCohomology_comp_posMap`: through the comparison with ordinary
  cohomology, `posMap` is `groupCohomology.map`.
* `TauCeti.TateCohomology.posMap_comp_map`, `TauCeti.TateCohomology.map_comp_posMap`: naturality
  in the two coefficient representations.
* `TauCeti.TateCohomology.posMap_id`, `TauCeti.TateCohomology.posMap_comp`: functoriality in the
  group homomorphism.
* `TauCeti.TateCohomology.fromGroupCohomology_δ_comp_posMap`,
  `TauCeti.TateCohomology.δ_comp_posMap`: compatibility with connecting maps.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §8 and Chapter VI, §5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {k G Q : Type u} [CommRing k] [Group G] [Group Q] [Fintype G] [Fintype Q]
  (φ : G →* Q) {M : Rep k Q} {N : Rep k G}

/-- **Change of group in a positive Tate degree.** For `φ : G →* Q` and a morphism
`f : Res_φ M ⟶ N`, this is the ordinary change-of-group map `groupCohomology.map φ f n` read
through Mathlib's identification `TateCohomology.isoGroupCohomology` of Tate cohomology with
ordinary cohomology in degree `n ≠ 0`. On a cochain it is `c ↦ (g₁, …, gₙ) ↦ f (c (φ g₁, …, φ gₙ))`.
-/
def posMap (f : Rep.res φ M ⟶ N) (n : ℕ) [NeZero n] :
    tateCohomology M n ⟶ tateCohomology N n :=
  (_root_.TateCohomology.isoGroupCohomology n).hom.app M ≫ groupCohomology.map φ f n ≫
    (_root_.TateCohomology.isoGroupCohomology n).inv.app N

/-- Positive-degree change of group is ordinary change of group between Mathlib's comparisons of
Tate with ordinary cohomology. -/
theorem posMap_def (f : Rep.res φ M ⟶ N) (n : ℕ) [NeZero n] :
    posMap φ f n = (_root_.TateCohomology.isoGroupCohomology n).hom.app M ≫
      groupCohomology.map φ f n ≫ (_root_.TateCohomology.isoGroupCohomology n).inv.app N :=
  (rfl)

/-- Positive-degree change of group, read through the comparison with ordinary cohomology, is the
ordinary change-of-group map. -/
@[reassoc]
theorem posMap_comp_isoGroupCohomology_hom (f : Rep.res φ M ⟶ N) (n : ℕ) [NeZero n] :
    posMap φ f n ≫ (_root_.TateCohomology.isoGroupCohomology n).hom.app N =
      (_root_.TateCohomology.isoGroupCohomology n).hom.app M ≫ groupCohomology.map φ f n := by
  -- As for `posRes_comp_isoGroupCohomology_hom`, the components of the comparison land in the
  -- objects of `groupCohomology.functor`, which agree with `groupCohomology` only after unfolding,
  -- so the comparison is cancelled against its own inverse rather than rewritten.
  exact (Iso.eq_comp_inv ((_root_.TateCohomology.isoGroupCohomology n).app N)).1 (by rfl)

/-- Through the comparison `Rep.fromGroupCohomology` of ordinary with Tate cohomology,
positive-degree change of group is the ordinary change-of-group map. -/
@[reassoc]
theorem fromGroupCohomology_comp_posMap (f : Rep.res φ M ⟶ N) (n : ℕ) [NeZero n] :
    fromGroupCohomology M n ≫ posMap φ f n =
      groupCohomology.map φ f n ≫ fromGroupCohomology N n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [fromGroupCohomology_succ, fromGroupCohomology_succ]
  exact (Iso.inv_comp_eq _).2 (by rfl)

/-- Positive-degree change of group followed by a map of `G`-representations is change of group
along the composite coefficient map. -/
@[reassoc]
theorem posMap_comp_map (f : Rep.res φ M ⟶ N) {N' : Rep k G} (g : N ⟶ N') (n : ℕ) [NeZero n] :
    posMap φ f n ≫ (tateCohomologyFunctor n).map g = posMap φ (f ≫ g) n := by
  refine (cancel_mono ((_root_.TateCohomology.isoGroupCohomology n).hom.app N')).1 ?_
  rw [Category.assoc, NatTrans.naturality, posMap_comp_isoGroupCohomology_hom_assoc,
    posMap_comp_isoGroupCohomology_hom]
  exact congrArg (_ ≫ ·) (groupCohomology.map_comp φ (MonoidHom.id G) f g n).symm

/-- A map of `Q`-representations followed by positive-degree change of group is change of group
along the composite coefficient map. -/
@[reassoc]
theorem map_comp_posMap {M' : Rep k Q} (g : M' ⟶ M) (f : Rep.res φ M ⟶ N) (n : ℕ) [NeZero n] :
    (tateCohomologyFunctor n).map g ≫ posMap φ f n =
      posMap φ ((Rep.resFunctor φ).map g ≫ f) n := by
  refine (cancel_mono ((_root_.TateCohomology.isoGroupCohomology n).hom.app N)).1 ?_
  rw [Category.assoc, posMap_comp_isoGroupCohomology_hom, posMap_comp_isoGroupCohomology_hom]
  -- The comparison lands in the objects of `groupCohomology.functor`, so its naturality square is
  -- composed as a term rather than rewritten into the goal.
  exact ((reassoc_of% (_root_.TateCohomology.isoGroupCohomology n).hom.naturality g) _).trans
    (congrArg (_ ≫ ·) (groupCohomology.map_comp (MonoidHom.id Q) φ g f n).symm)

/-- Change of group along the identity homomorphism with the identity coefficient map is the
identity. -/
@[simp]
theorem posMap_id (n : ℕ) [NeZero n] : posMap (MonoidHom.id G) (𝟙 N) n = 𝟙 _ := by
  refine (cancel_mono ((_root_.TateCohomology.isoGroupCohomology n).hom.app N)).1 ?_
  rw [posMap_comp_isoGroupCohomology_hom, Category.id_comp]
  -- The comparison lands in the objects of `groupCohomology.functor`, so `map_id` is applied as a
  -- term rather than rewritten into the goal.
  exact (congrArg (_ ≫ ·) (groupCohomology.map_id n)).trans (Category.comp_id _)

/-- **Change of group is transitive.** For `ψ : H →* G` and `φ : G →* Q`, changing the group
along `φ` with `f : Res_φ M ⟶ N` and then along `ψ` with `g : Res_ψ N ⟶ L` is change of group
along `φ.comp ψ` with the composite coefficient map `Res_ψ f ≫ g`. -/
@[reassoc]
theorem posMap_comp {H : Type u} [Group H] [Fintype H] (ψ : H →* G) {L : Rep k H}
    (f : Rep.res φ M ⟶ N) (g : Rep.res ψ N ⟶ L) (n : ℕ) [NeZero n] :
    posMap (φ.comp ψ) ((Rep.resFunctor ψ).map f ≫ g) n = posMap φ f n ≫ posMap ψ g n := by
  refine (cancel_mono ((_root_.TateCohomology.isoGroupCohomology n).hom.app L)).1 ?_
  rw [Category.assoc, posMap_comp_isoGroupCohomology_hom, posMap_comp_isoGroupCohomology_hom]
  -- As in `map_comp_posMap`, the comparison lands in the objects of `groupCohomology.functor`, so
  -- the remaining square is composed as a term rather than rewritten into the goal.
  exact (congrArg (_ ≫ ·) (groupCohomology.map_comp φ ψ f g n)).trans
    (posMap_comp_isoGroupCohomology_hom_assoc φ f n _).symm

/-- **Change of group commutes with connecting maps, from degree zero on.** Let `S` be a short
exact sequence of `Q`-representations, `S'` one of `G`-representations and `Φ : Res_φ S ⟶ S'`.
On an ordinary cohomology class `z` of `S.X₃` in degree `n`, changing the group of the Tate
connecting image of `z` gives the Tate connecting image of the changed class. In degree zero the
class `z` is an invariant of `S.X₃`, and its Tate class is its image in the norm quotient. -/
@[reassoc]
theorem fromGroupCohomology_δ_comp_posMap {S : ShortComplex (Rep k Q)} (hS : S.ShortExact)
    {S' : ShortComplex (Rep k G)} (hS' : S'.ShortExact) (Φ : S.map (Rep.resFunctor φ) ⟶ S')
    (n : ℕ) :
    fromGroupCohomology S.X₃ n ≫ _root_.TateCohomology.δ hS n ≫
        posMap φ (M := S.X₁) Φ.τ₁ (n + 1) =
      groupCohomology.map φ Φ.τ₃ n ≫ fromGroupCohomology S'.X₃ n ≫
        _root_.TateCohomology.δ hS' n := by
  rw [← δ_comp_fromGroupCohomology_assoc hS n, fromGroupCohomology_comp_posMap,
    TauCeti.groupCohomology.δ_naturality_assoc φ hS hS' Φ, δ_comp_fromGroupCohomology]

/-- **Change of group commutes with connecting maps in positive degrees.** For short exact
sequences `S` of `Q`-representations and `S'` of `G`-representations and a morphism
`Φ : Res_φ S ⟶ S'`, the connecting maps `Hⁿ(Q, S.X₃) ⟶ Hⁿ⁺¹(Q, S.X₁)` and
`Hⁿ(G, S'.X₃) ⟶ Hⁿ⁺¹(G, S'.X₁)` commute with change of group along `Φ`, for `n ≠ 0`. -/
@[reassoc]
theorem δ_comp_posMap {S : ShortComplex (Rep k Q)} (hS : S.ShortExact)
    {S' : ShortComplex (Rep k G)} (hS' : S'.ShortExact) (Φ : S.map (Rep.resFunctor φ) ⟶ S')
    (n : ℕ) [NeZero n] :
    _root_.TateCohomology.δ hS n ≫ posMap φ (M := S.X₁) Φ.τ₁ (n + 1) =
      posMap φ (M := S.X₃) Φ.τ₃ n ≫ _root_.TateCohomology.δ hS' n := by
  refine (cancel_epi (fromGroupCohomology S.X₃ n)).1 ?_
  rw [fromGroupCohomology_δ_comp_posMap, fromGroupCohomology_comp_posMap_assoc]

end TauCeti.TateCohomology
