/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Functoriality of relative singular homology with local coefficients

A map of topological pairs `f : (X, A) ⟶ (Y, B)` and a local coefficient system `L` on `Y`
induce maps from the relative twisted chains and homology of `(X, A)` with coefficients in
`f⁎L` to those of `(Y, B)` with coefficients in `L`.  The construction descends the map on
ambient twisted chains through the quotient by the subspace chains. When the ambient map is
injective and sends no point outside `A` into `B`, for instance for an inclusion `(X, A) ⟶ (Y, A)`,
the relative map is injective in every degree (`TopPair.twistedChainComplexMap_f_injective`).

The coefficient system on `A` obtained by first pulling `L` back to `X` and then restricting to
`A` is canonically isomorphic to the pullback to `A` of the restriction of `L` to `B`.  This
comparison makes the maps on subspace and ambient chains into a morphism of the short exact
sequences of a pair.  Consequently the relative map commutes with the connecting morphism in the
long exact sequence, and by the five lemma it is a quasi-isomorphism when the maps on ambient and
subspace chains are (`TopPair.quasiIso_twistedChainComplexMap_of_quasiIso`).

Together with `TauCeti.AlgebraicTopology.Singular.Twisted.Basic`, this supplies functoriality of
twisted singular homology for maps of spaces and maps of pairs.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapters VII--VIII.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti
open scoped Simplicial

universe u v w

namespace TopPair

variable {R : Type u} [Ring R] {P Q : TopPair.{v}} (f : P ⟶ Q)
  (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)

/-- Restricting a pulled-back local coefficient system to the subspace agrees canonically with
pulling the restricted system back along the subspace component of a map of pairs. -/
def subspaceSystemPullbackIso :
    P.subspaceSystem ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ≅
      (LocalCoefficientSystem.pullback (Hom.snd f).hom).obj (Q.subspaceSystem L) :=
  (LocalCoefficientSystem.pullbackSquareIso P.map.hom (Hom.fst f).hom (Hom.snd f).hom Q.map.hom
    (congrArg (·.hom) (Hom.w f).symm)).app L

/-- On every fibre, the comparison `TopPair.subspaceSystemPullbackIso` is the identification of
the fibres of `L` over the two equal images of a point under `P.map ≫ Hom.fst f` and
`Hom.snd f ≫ Q.map`. -/
@[simp]
lemma subspaceSystemPullbackIso_hom_app (x : FundamentalGroupoid P.snd) :
    (subspaceSystemPullbackIso f L).hom.app x =
      eqToHom (Functor.congr_obj (congrArg (fun g : P.snd ⟶ Q.fst ↦
        (LocalCoefficientSystem.pullback g.hom).obj L) (Hom.w f).symm) x) :=
  LocalCoefficientSystem.pullbackSquareIso_hom_app_app P.map.hom (Hom.fst f).hom (Hom.snd f).hom
    Q.map.hom L (congrArg (·.hom) (Hom.w f).symm) x

/-- On every fibre, the inverse of the comparison `TopPair.subspaceSystemPullbackIso` is the
identification of the fibres of `L` over the two equal images of a point. -/
@[simp]
lemma subspaceSystemPullbackIso_inv_app (x : FundamentalGroupoid P.snd) :
    (subspaceSystemPullbackIso f L).inv.app x =
      eqToHom (Functor.congr_obj (congrArg (fun g : P.snd ⟶ Q.fst ↦
        (LocalCoefficientSystem.pullback g.hom).obj L) (Hom.w f)) x) :=
  LocalCoefficientSystem.pullbackSquareIso_inv_app_app P.map.hom (Hom.fst f).hom (Hom.snd f).hom
    Q.map.hom L (congrArg (·.hom) (Hom.w f).symm) x

/-- The map on twisted chains of the subspaces induced by a map of pairs.  Its source is first
identified with the pullback of the target subspace system. -/
def twistedSubspaceChainComplexMap :
    (P.subspaceSystem
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)).twistedChainComplex ⟶
      (Q.subspaceSystem L).twistedChainComplex :=
  LocalCoefficientSystem.twistedChainComplexCoefficientMap (subspaceSystemPullbackIso f L).hom ≫
    LocalCoefficientSystem.twistedChainComplexMap (Hom.snd f) (Q.subspaceSystem L)

/-- The subspace chain map is coefficient change along the restriction-pullback comparison,
followed by the chain map of the subspace component. -/
lemma twistedSubspaceChainComplexMap_def :
    twistedSubspaceChainComplexMap f L =
      LocalCoefficientSystem.twistedChainComplexCoefficientMap
          (subspaceSystemPullbackIso f L).hom ≫
        LocalCoefficientSystem.twistedChainComplexMap (Hom.snd f) (Q.subspaceSystem L) :=
  (rfl)

/-- The maps induced by a map of pairs on subspace and ambient twisted chains form a commutative
square. -/
@[reassoc]
lemma twistedChainComplexMap_naturality_pair :
    LocalCoefficientSystem.twistedChainComplexMap P.map
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ≫
        LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L =
      twistedSubspaceChainComplexMap f L ≫
        LocalCoefficientSystem.twistedChainComplexMap Q.map L := by
  exact LocalCoefficientSystem.twistedChainComplexMap_naturality_square
    P.map (Hom.fst f) (Hom.snd f) Q.map L (Hom.w f).symm

/-- The map on relative twisted chain complexes induced by a map of topological pairs. -/
def twistedChainComplexMap :
    P.twistedChainComplex ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ⟶
      Q.twistedChainComplex L :=
  P.twistedChainComplexDesc _
    (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L ≫
      Q.twistedChainComplexπ L)
    (by
      calc
        _ = (LocalCoefficientSystem.twistedChainComplexMap P.map _ ≫
              LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L) ≫
            Q.twistedChainComplexπ L := Category.assoc _ _ _ |>.symm
        _ = (twistedSubspaceChainComplexMap f L ≫
              LocalCoefficientSystem.twistedChainComplexMap Q.map L) ≫
            Q.twistedChainComplexπ L := by
              rw [twistedChainComplexMap_naturality_pair]
        _ = twistedSubspaceChainComplexMap f L ≫
            (LocalCoefficientSystem.twistedChainComplexMap Q.map L ≫
              Q.twistedChainComplexπ L) := Category.assoc _ _ _
        _ = 0 := by rw [Q.twistedChainComplexMap_comp_twistedChainComplexπ, comp_zero])

/-- The relative twisted chain map is characterized by compatibility with the quotient maps from
the ambient twisted chain complexes. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_twistedChainComplexMap :
    P.twistedChainComplexπ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ≫
        twistedChainComplexMap f L =
      LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L ≫
        Q.twistedChainComplexπ L :=
  P.twistedChainComplexπ_comp_twistedChainComplexDesc _ _ _

/-- In each degree, the relative twisted chain map sends the class of an ambient chain to the class
of its image. -/
@[simp]
lemma twistedChainComplexMap_f_twistedChainComplexπ_f_apply {k : ℕ}
    (c : ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L).twistedChainComplex.X k) :
    (twistedChainComplexMap f L).f k
        ((P.twistedChainComplexπ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)).f k
          c) =
      (Q.twistedChainComplexπ L).f k
        ((LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f k c) := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    twistedChainComplexπ_comp_twistedChainComplexMap, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply]

/-- Evaluating the coefficient of a relative chain on an image simplex after a map of pairs with
injective ambient component agrees with evaluating on the original simplex. -/
@[reassoc]
lemma twistedChainComplexMap_f_comp_twistedChainComplexCoeff [Mono (Hom.fst f)] {k : ℕ}
    (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌) (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map)
    (hσ' : ¬Set.range (TopCat.simplexMap ((TopCat.toSSet.map (Hom.fst f)).app _ σ)) ⊆
      Set.range Q.map) :
    (twistedChainComplexMap f L).f k ≫ Q.twistedChainComplexCoeff L _ hσ' =
      P.twistedChainComplexCoeff ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) σ
        hσ := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun z ↦ ?_
  obtain ⟨a, rfl⟩ := P.twistedChainComplexπ_f_surjective _ z
  -- The fibres of `((pullback (Hom.fst f).hom).obj L)` at `initialVertex σ` and of `L` at
  -- `initialVertex ((toSSet.map (Hom.fst f)).app _ σ)` agree only definitionally, so `Eq.trans`
  -- bridges them across the rewrite steps.
  exact (congrArg (fun x ↦ (Q.twistedChainComplexCoeff L _ hσ').hom x)
      (twistedChainComplexMap_f_twistedChainComplexπ_f_apply f L a)).trans <|
    (Q.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L _ hσ' _).trans <|
    (LocalCoefficientSystem.twistedChainComplexCoeff_twistedChainComplexMap_f_apply
      (Hom.fst f) L σ a).trans
      (P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) σ hσ a).symm

/-- **Relative twisted chains of a subpair inject.** If the ambient component of a map of pairs
`f : (X, A) ⟶ (Y, B)` is injective and every point of `X` sent into `B` lies in `A`, then `f`
induces an injective map of relative twisted chains in every degree. For instance, this applies
to the inclusion `(X, A) ⟶ (Y, A)` for subspaces `A ⊆ X ⊆ Y`. -/
theorem twistedChainComplexMap_f_injective [Mono (Hom.fst f)]
    (hf : Hom.fst f ⁻¹' Set.range Q.map ⊆ Set.range P.map) (k : ℕ) :
    Function.Injective ((twistedChainComplexMap f L).f k).hom := by
  intro y y' h
  refine P.twistedChainComplex_ext_coeff _ fun σ hσ ↦ ?_
  -- The image of `σ` does not lie in `B` either.
  have hσ' : ¬Set.range (TopCat.simplexMap ((TopCat.toSSet.map (Hom.fst f)).app _ σ)) ⊆
      Set.range Q.map := fun h' ↦ hσ fun x ⟨p, hp⟩ ↦ hf (h' ⟨p, by
        rw [TopCat.simplexMap_app, ContinuousMap.comp_apply, hp]⟩)
  -- So the coefficient on `σ` is the coefficient of the image on the image simplex.
  have key (z : (P.twistedChainComplex
      ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)).X k) :
      (P.twistedChainComplexCoeff _ σ hσ).hom z =
        (Q.twistedChainComplexCoeff L _ hσ').hom (((twistedChainComplexMap f L).f k).hom z) :=
    (congrArg (fun φ ↦ φ.hom z)
      (twistedChainComplexMap_f_comp_twistedChainComplexCoeff f L σ hσ hσ')).symm
  rw [key, key, h]

/-- Evaluating a coefficient on a simplex outside the subspace commutes with a change of local
coefficients. -/
@[reassoc]
lemma twistedChainComplexCoefficientMap_f_comp_twistedChainComplexCoeff
    {L K : LocalCoefficientSystem.{u, v, max v w} R P.fst} (η : L ⟶ K) {k : ℕ}
    (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌)
    (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map) :
    (P.twistedChainComplexCoefficientMap η).f k ≫ P.twistedChainComplexCoeff K σ hσ =
      P.twistedChainComplexCoeff L σ hσ ≫ η.app (LocalCoefficientSystem.initialVertex σ) := by
  apply (cancel_epi ((P.twistedChainComplexπ L).f k)).1
  have hπ := congrArg (fun φ ↦ φ.f k)
    (P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η)
  simp only [HomologicalComplex.comp_f] at hπ
  rw [← Category.assoc, hπ, Category.assoc, P.twistedChainComplexπ_f_twistedChainComplexCoeff,
    P.twistedChainComplexπ_f_twistedChainComplexCoeff_assoc]
  refine LocalCoefficientSystem.twistedChainComplex_hom_ext L fun τ ↦ ?_
  rw [LocalCoefficientSystem.ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc]
  by_cases hτ : τ = σ
  · subst hτ
    simp [LocalCoefficientSystem.ιTwistedChainComplex_twistedChainComplexCoeff]
  · simp [LocalCoefficientSystem.ιTwistedChainComplex_twistedChainComplexCoeff_of_ne, hτ]

/-- Relative maps of pairs commute with a change of coefficients on the target pair. -/
@[reassoc]
lemma twistedChainComplexMap_naturality
    {K : LocalCoefficientSystem.{u, v, max v w} R Q.fst} (η : L ⟶ K) :
    twistedChainComplexMap f L ≫ Q.twistedChainComplexCoefficientMap η =
      P.twistedChainComplexCoefficientMap
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).map η) ≫
        twistedChainComplexMap f K := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L))).1
  calc
    _ = (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L ≫
          Q.twistedChainComplexπ L) ≫ Q.twistedChainComplexCoefficientMap η := by
        rw [← Category.assoc, twistedChainComplexπ_comp_twistedChainComplexMap]
    _ = LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L ≫
          (Q.twistedChainComplexπ L ≫ Q.twistedChainComplexCoefficientMap η) :=
        Category.assoc _ _ _
    _ = (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L ≫
          LocalCoefficientSystem.twistedChainComplexCoefficientMap η) ≫
          Q.twistedChainComplexπ K := by
        rw [Q.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap]
        exact (Category.assoc _ _ _).symm
    _ = (LocalCoefficientSystem.twistedChainComplexCoefficientMap
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).map η) ≫
          LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) K) ≫
          Q.twistedChainComplexπ K := by
        rw [LocalCoefficientSystem.twistedChainComplexMap_naturality]
    _ = LocalCoefficientSystem.twistedChainComplexCoefficientMap
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).map η) ≫
          (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) K ≫
            Q.twistedChainComplexπ K) := Category.assoc _ _ _
    _ = (LocalCoefficientSystem.twistedChainComplexCoefficientMap
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).map η) ≫
          P.twistedChainComplexπ
            ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K)) ≫
          twistedChainComplexMap f K := by
        rw [← twistedChainComplexπ_comp_twistedChainComplexMap]
        exact (Category.assoc _ _ _).symm
    _ = _ := by
      rw [← Category.assoc,
        P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap]

/-- The pullback along the ambient component of the identity map of a pair is canonically
isomorphic to the original coefficient system. -/
def fstPullbackIdIso (P : TopPair.{v})
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) :
    (LocalCoefficientSystem.pullback (Hom.fst (𝟙 P)).hom).obj L ≅ L :=
  eqToIso (congrArg (fun k : P.fst ⟶ P.fst ↦
    (LocalCoefficientSystem.pullback k.hom).obj L)
      (Hom.fst_id P)) ≪≫
    (LocalCoefficientSystem.pullbackIdIso P.fst).app L

/-- The comparison `TopPair.fstPullbackIdIso` is the identity on every fibre. -/
@[simp]
lemma fstPullbackIdIso_hom_app (P : TopPair.{v})
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (x : FundamentalGroupoid P.fst) :
    (fstPullbackIdIso P L).hom.app x = 𝟙 _ := by
  -- What remains composes an identity with an `eqToHom` between definitionally equal fibres.
  simp only [fstPullbackIdIso, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
    LocalCoefficientSystem.pullbackIdIso_hom_app_app, eqToIso.hom, eqToHom_app]
  rfl

/-- The identity map of a pair induces the coefficient-change map coming from the canonical
identification of a system with its pullback along the identity. -/
@[simp]
lemma twistedChainComplexMap_id (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) :
    twistedChainComplexMap (𝟙 P) L =
      P.twistedChainComplexCoefficientMap (fstPullbackIdIso P L).hom := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.pullback (Hom.fst (𝟙 P)).hom).obj L))).1
  rw [twistedChainComplexπ_comp_twistedChainComplexMap,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap]
  congr 1
  rw [fstPullbackIdIso, Iso.trans_hom,
    LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp]
  rw [LocalCoefficientSystem.twistedChainComplexMap_congr (Hom.fst (𝟙 P)) L
    (Hom.fst_id P),
    LocalCoefficientSystem.twistedChainComplexMap_id]
  rw [Iso.app_hom]

variable {f} in
/-- Two maps of pairs with the same ambient component induce the same map of relative twisted
chains, after the canonical identification of their pulled-back coefficient systems. -/
lemma twistedChainComplexMap_congr {f' : P ⟶ Q} (h : Hom.fst f = Hom.fst f') :
    twistedChainComplexMap f L =
      P.twistedChainComplexCoefficientMap
          (eqToHom (congrArg (fun g : P.fst ⟶ Q.fst ↦
            (LocalCoefficientSystem.pullback g.hom).obj L) h)) ≫
        twistedChainComplexMap f' L := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L))).1
  rw [twistedChainComplexπ_comp_twistedChainComplexMap,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexMap,
    LocalCoefficientSystem.twistedChainComplexMap_congr _ L h, eqToIso.hom, Category.assoc]

variable {S : TopPair.{v}} (g : Q ⟶ S)
  (K : LocalCoefficientSystem.{u, v, max v w} R S.fst)

/-- Pullback along the ambient component of a composite of pair maps agrees canonically with
iterated pullback along their ambient components. -/
def fstPullbackCompIso :
    (LocalCoefficientSystem.pullback (Hom.fst (f ≫ g)).hom).obj K ≅
      (LocalCoefficientSystem.pullback (Hom.fst f).hom).obj
        ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) :=
  eqToIso (congrArg (fun k : P.fst ⟶ S.fst ↦
    (LocalCoefficientSystem.pullback k.hom).obj K)
      (Hom.fst_comp f g)) ≪≫
    (LocalCoefficientSystem.pullbackCompIso (Hom.fst f).hom (Hom.fst g).hom).app K

/-- The comparison `TopPair.fstPullbackCompIso` is the identity on every fibre. -/
@[simp]
lemma fstPullbackCompIso_hom_app (x : FundamentalGroupoid P.fst) :
    (fstPullbackCompIso f g K).hom.app x = 𝟙 _ := by
  -- What remains composes an identity with an `eqToHom` between definitionally equal fibres.
  simp only [fstPullbackCompIso, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
    LocalCoefficientSystem.pullbackCompIso_hom_app_app, eqToIso.hom, eqToHom_app]
  rfl

/-- The inverse of the comparison `TopPair.fstPullbackCompIso` is the identity on every fibre. -/
@[simp]
lemma fstPullbackCompIso_inv_app (x : FundamentalGroupoid P.fst) :
    (fstPullbackCompIso f g K).inv.app x = 𝟙 _ := by
  -- What remains composes an identity with an `eqToHom` between definitionally equal fibres.
  simp only [fstPullbackCompIso, Iso.trans_inv, NatTrans.comp_app, Iso.app_inv,
    LocalCoefficientSystem.pullbackCompIso_inv_app_app, eqToIso.inv, eqToHom_app]
  rfl

/-- Maps of relative twisted chain complexes respect composition of maps of pairs, after the
canonical comparison between pullback along a composite and iterated pullback. -/
@[simp, reassoc]
lemma twistedChainComplexMap_comp :
    twistedChainComplexMap (f ≫ g) K =
      P.twistedChainComplexCoefficientMap (fstPullbackCompIso f g K).hom ≫
        twistedChainComplexMap f
          ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) ≫
        twistedChainComplexMap g K := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.pullback (Hom.fst (f ≫ g)).hom).obj K))).1
  rw [twistedChainComplexπ_comp_twistedChainComplexMap,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexMap]
  simp only [fstPullbackCompIso, Iso.trans_hom,
    LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp]
  rw [LocalCoefficientSystem.twistedChainComplexMap_congr (Hom.fst (f ≫ g)) K
    (Hom.fst_comp f g),
    LocalCoefficientSystem.twistedChainComplexMap_comp]
  simp only [Iso.app_hom, Category.assoc]

/-- The morphism between the short exact sequences of twisted chains induced by a map of
topological pairs. -/
def twistedChainComplexShortComplexMap :
    P.twistedChainComplexShortComplex
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ⟶
      Q.twistedChainComplexShortComplex L :=
  ShortComplex.homMk (twistedSubspaceChainComplexMap f L)
    (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L)
    (twistedChainComplexMap f L)
    (twistedChainComplexMap_naturality_pair f L).symm
    (twistedChainComplexπ_comp_twistedChainComplexMap f L).symm

@[simp]
lemma twistedChainComplexShortComplexMap_τ₁ :
    (twistedChainComplexShortComplexMap f L).τ₁ = twistedSubspaceChainComplexMap f L :=
  (rfl)

@[simp]
lemma twistedChainComplexShortComplexMap_τ₂ :
    (twistedChainComplexShortComplexMap f L).τ₂ =
      LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L :=
  (rfl)

@[simp]
lemma twistedChainComplexShortComplexMap_τ₃ :
    (twistedChainComplexShortComplexMap f L).τ₃ = twistedChainComplexMap f L :=
  (rfl)

/-- The map on relative twisted singular homology induced by a map of topological pairs. -/
abbrev twistedHomologyMap (k : ℕ) :
    P.twistedHomology ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k ⟶
      Q.twistedHomology L k :=
  HomologicalComplex.homologyMap (twistedChainComplexMap f L) k

/-- The homology maps of pairs commute with a change of coefficients on the target pair. -/
@[reassoc]
lemma twistedHomologyMap_naturality
    {K : LocalCoefficientSystem.{u, v, max v w} R Q.fst} (η : L ⟶ K)
    (k : ℕ) :
    twistedHomologyMap f L k ≫ Q.twistedHomologyCoefficientMap η k =
      P.twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).map η) k ≫
        twistedHomologyMap f K k :=
  ((HomologicalComplex.homologyMap_comp _ _ _).symm).trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
      (twistedChainComplexMap_naturality f L η)).trans
      (HomologicalComplex.homologyMap_comp _ _ _))

/-- The quotient maps from ambient to relative twisted homology are natural in maps of
topological pairs. -/
@[reassoc (attr := simp)]
lemma twistedHomologyπ_naturality (k : ℕ) :
    LocalCoefficientSystem.twistedHomologyMap (Hom.fst f) L k ≫
        Q.twistedHomologyπ L k =
      P.twistedHomologyπ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k ≫
        twistedHomologyMap f L k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    twistedChainComplexπ_comp_twistedChainComplexMap]

/-- The identity law for maps on relative twisted homology. -/
@[simp]
lemma twistedHomologyMap_id
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : ℕ) :
    twistedHomologyMap (𝟙 P) L k =
      P.twistedHomologyCoefficientMap (fstPullbackIdIso P L).hom k :=
  congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
    (twistedChainComplexMap_id L)

variable {f} in
/-- Two maps of pairs with the same ambient component induce the same map on relative twisted
homology, after the canonical identification of their pulled-back coefficient systems. -/
lemma twistedHomologyMap_congr {f' : P ⟶ Q} (h : Hom.fst f = Hom.fst f') (k : ℕ) :
    twistedHomologyMap f L k =
      P.twistedHomologyCoefficientMap
          (eqToHom (congrArg (fun g : P.fst ⟶ Q.fst ↦
            (LocalCoefficientSystem.pullback g.hom).obj L) h)) k ≫
        twistedHomologyMap f' L k :=
  (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k) (twistedChainComplexMap_congr L h)).trans
    (HomologicalComplex.homologyMap_comp _ _ _)

/-- The composition law for maps on relative twisted homology. -/
@[simp, reassoc]
lemma twistedHomologyMap_comp (k : ℕ) :
    twistedHomologyMap (f ≫ g) K k =
      P.twistedHomologyCoefficientMap (fstPullbackCompIso f g K).hom k ≫
        twistedHomologyMap f ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) k ≫
        twistedHomologyMap g K k :=
  (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
      (twistedChainComplexMap_comp f g K)).trans
    (by rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp])

/-- The homology map induced by the map on subspace chains is the coefficient comparison followed
by the map induced by the subspace component. -/
lemma homologyMap_twistedSubspaceChainComplexMap (k : ℕ) :
    HomologicalComplex.homologyMap (twistedSubspaceChainComplexMap f L) k =
      LocalCoefficientSystem.twistedHomologyCoefficientMap
          (subspaceSystemPullbackIso f L).hom k ≫
        LocalCoefficientSystem.twistedHomologyMap (Hom.snd f) (Q.subspaceSystem L) k := by
  rw [twistedSubspaceChainComplexMap, HomologicalComplex.homologyMap_comp]

/-- A property of morphisms of modules that respects isomorphisms holds for the map induced by a
map of pairs on the twisted homology of the subspaces, through the comparison of the pulled-back
coefficient systems, as soon as it holds for the map induced by the subspace component. -/
lemma homologyMap_twistedChainComplexShortComplexMap_τ₁_mem
    (Pr : MorphismProperty (ModuleCat.{max v w} R)) [Pr.RespectsIso] (k : ℕ)
    (h : Pr (LocalCoefficientSystem.twistedHomologyMap (Hom.snd f) (Q.subspaceSystem L) k)) :
    Pr (HomologicalComplex.homologyMap (twistedChainComplexShortComplexMap f L).τ₁ k) := by
  rw [twistedChainComplexShortComplexMap_τ₁, homologyMap_twistedSubspaceChainComplexMap,
    Pr.cancel_left_of_respectsIso]
  exact h

/-- A property of morphisms of modules holds for the map induced by a map of pairs on the
twisted homology of the ambient spaces as soon as it holds for the map induced by the ambient
component. -/
lemma homologyMap_twistedChainComplexShortComplexMap_τ₂_mem
    (Pr : MorphismProperty (ModuleCat.{max v w} R)) (k : ℕ)
    (h : Pr (LocalCoefficientSystem.twistedHomologyMap (Hom.fst f) L k)) :
    Pr (HomologicalComplex.homologyMap (twistedChainComplexShortComplexMap f L).τ₂ k) := by
  rw [twistedChainComplexShortComplexMap_τ₂]
  exact h

/-- The homology maps induced by a map of pairs commute with the inclusions of the subspaces,
after the canonical comparison of their pulled-back coefficient systems. -/
lemma twistedHomologyMap_naturality_pair (k : ℕ) :
    LocalCoefficientSystem.twistedHomologyMap P.map
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k ≫
        LocalCoefficientSystem.twistedHomologyMap (Hom.fst f) L k =
      LocalCoefficientSystem.twistedHomologyCoefficientMap
          (subspaceSystemPullbackIso f L).hom k ≫
        LocalCoefficientSystem.twistedHomologyMap (Hom.snd f) (Q.subspaceSystem L) k ≫
          LocalCoefficientSystem.twistedHomologyMap Q.map L k :=
  ((HomologicalComplex.homologyMap_comp _ _ _).symm.trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
      (twistedChainComplexMap_naturality_pair f L)).trans
      (HomologicalComplex.homologyMap_comp _ _ _))).trans
    (by rw [homologyMap_twistedSubspaceChainComplexMap, Category.assoc])

/-- The connecting morphism in relative twisted homology is natural in maps of topological
pairs. -/
@[reassoc]
lemma twistedHomologyδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    P.twistedHomologyδ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) n m h ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
            (subspaceSystemPullbackIso f L).hom m ≫
          LocalCoefficientSystem.twistedHomologyMap (Hom.snd f) (Q.subspaceSystem L) m =
      twistedHomologyMap f L n ≫ Q.twistedHomologyδ L n m h :=
  by
    have hδ := HomologicalComplex.HomologySequence.δ_naturality
      (twistedChainComplexShortComplexMap f L)
      (P.shortExact_twistedChainComplexShortComplex _)
      (Q.shortExact_twistedChainComplexShortComplex L) n m (by simpa)
    rw [twistedChainComplexShortComplexMap_τ₁,
      twistedChainComplexShortComplexMap_τ₃,
      homologyMap_twistedSubspaceChainComplexMap] at hδ
    exact hδ

/-- A map of pairs which induces quasi-isomorphisms on the twisted chains of the ambient spaces
and of the subspaces induces a quasi-isomorphism on relative twisted chains. -/
lemma quasiIso_twistedChainComplexMap_of_quasiIso
    [QuasiIso (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L)]
    [QuasiIso (LocalCoefficientSystem.twistedChainComplexMap (Hom.snd f) (Q.subspaceSystem L))] :
    QuasiIso (twistedChainComplexMap f L) := by
  have : QuasiIso (twistedSubspaceChainComplexMap f L) := by
    rw [twistedSubspaceChainComplexMap_def]
    infer_instance
  have := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (twistedChainComplexShortComplexMap f L) (P.shortExact_twistedChainComplexShortComplex _)
    (Q.shortExact_twistedChainComplexShortComplex L)
    (by rw [twistedChainComplexShortComplexMap_τ₁]; infer_instance)
    (by rw [twistedChainComplexShortComplexMap_τ₂]; infer_instance)
  rwa [twistedChainComplexShortComplexMap_τ₃] at this

section AmbientComponent

/-! ### Composites of maps of pairs with the same ambient component

The relative twisted homology map of a composite of maps of pairs only depends on its ambient
component. -/

variable {P' Q' : TopPair.{v}} {N : LocalCoefficientSystem.{u, v, max v w} R P.fst}
  {S : LocalCoefficientSystem.{u, v, max v w} R Q.fst}

/-- Two composites of maps of pairs with the same composite ambient component induce the same map
of relative twisted homology, when the coefficient systems are identified along equalities. -/
lemma twistedHomologyMap_comp_twistedHomologyMap_eq_of_fst_comp_eq
    (g₁ : P ⟶ P') (g₂ : P' ⟶ Q) (h₁ : P ⟶ Q') (h₂ : Q' ⟶ Q)
    (hw : Hom.fst g₁ ≫ Hom.fst g₂ = Hom.fst h₁ ≫ Hom.fst h₂)
    {M₁ : LocalCoefficientSystem.{u, v, max v w} R P'.fst}
    {M₂ : LocalCoefficientSystem.{u, v, max v w} R Q'.fst}
    (e₁ : N = (LocalCoefficientSystem.pullback (Hom.fst g₁).hom).obj M₁)
    (e₂ : M₁ = (LocalCoefficientSystem.pullback (Hom.fst g₂).hom).obj S)
    (e₃ : N = (LocalCoefficientSystem.pullback (Hom.fst h₁).hom).obj M₂)
    (e₄ : M₂ = (LocalCoefficientSystem.pullback (Hom.fst h₂).hom).obj S) (k : ℕ) :
    P.twistedHomologyCoefficientMap (eqToHom e₁) k ≫ twistedHomologyMap g₁ M₁ k ≫
        P'.twistedHomologyCoefficientMap (eqToHom e₂) k ≫ twistedHomologyMap g₂ S k =
      P.twistedHomologyCoefficientMap (eqToHom e₃) k ≫ twistedHomologyMap h₁ M₂ k ≫
        Q'.twistedHomologyCoefficientMap (eqToHom e₄) k ≫ twistedHomologyMap h₂ S k := by
  simp only [← HomologicalComplex.homologyMap_comp]
  congr 1
  apply (cancel_epi (P.twistedChainComplexπ N)).1
  simp only [twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexMap]
  rw [LocalCoefficientSystem.twistedChainComplexMap_naturality_assoc,
    LocalCoefficientSystem.twistedChainComplexMap_naturality_assoc,
    reassoc_of% (LocalCoefficientSystem.twistedChainComplexMap_naturality_square (Hom.fst g₁)
      (Hom.fst g₂) (Hom.fst h₁) (Hom.fst h₂) S hw)]
  simp only [← LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp_assoc]
  congr 2
  ext x : 2
  simp only [eqToHom_map, eqToHom_app, NatTrans.comp_app,
    LocalCoefficientSystem.pullbackSquareIso_hom_app_app, eqToHom_trans]
  -- Every component is now a composite of `eqToHom`s between fibres of `S` over equal points,
  -- matching up to unfolding of whiskered functors, so `erw` closes it.
  erw [eqToHom_trans, eqToHom_trans]

end AmbientComponent

section EqualMaps

/-! ### Maps of pairs equal to an identity or a composite

When a map of pairs is only propositionally equal to an identity or to a composite, the
coefficient systems are matched along equalities of local systems, and the identity and
composition laws hold after the corresponding `eqToHom` coefficient maps. -/

variable {P' : TopPair.{v}}

/-- A map of pairs equal to the identity induces the identity on twisted homology, once the
coefficient systems are matched along equalities. -/
lemma twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_id (g : P ⟶ P)
    (hg : g = 𝟙 P) {N S : LocalCoefficientSystem.{u, v, max v w} R P.fst}
    (e : N = (LocalCoefficientSystem.pullback (Hom.fst g).hom).obj S) (e' : N = S) (k : ℕ) :
    P.twistedHomologyCoefficientMap (eqToHom e) k ≫ twistedHomologyMap g S k =
      P.twistedHomologyCoefficientMap (eqToHom e') k := by
  subst hg e
  rw [twistedHomologyMap_id, eqToHom_refl, twistedHomologyCoefficientMap_id, Category.id_comp]
  congr 1
  ext x : 2
  rw [fstPullbackIdIso_hom_app, eqToHom_app]
  -- Both sides identify the same fibre of `S` with itself up to unfolding the pullback.
  rfl

/-- A map of pairs equal to a composite induces the composite of the induced maps on twisted
homology, once the coefficient systems are matched along equalities. -/
lemma twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_comp (g₁ : P ⟶ P')
    (g₂ : P' ⟶ Q) (h : P ⟶ Q) (hw : h = g₁ ≫ g₂)
    {N N' : LocalCoefficientSystem.{u, v, max v w} R P.fst}
    {M : LocalCoefficientSystem.{u, v, max v w} R P'.fst}
    {S : LocalCoefficientSystem.{u, v, max v w} R Q.fst}
    (e₀ : N = N') (e : N' = (LocalCoefficientSystem.pullback (Hom.fst h).hom).obj S)
    (e₁ : N = (LocalCoefficientSystem.pullback (Hom.fst g₁).hom).obj M)
    (e₂ : M = (LocalCoefficientSystem.pullback (Hom.fst g₂).hom).obj S) (k : ℕ) :
    P.twistedHomologyCoefficientMap (eqToHom e₀) k ≫
        P.twistedHomologyCoefficientMap (eqToHom e) k ≫ twistedHomologyMap h S k =
      (P.twistedHomologyCoefficientMap (eqToHom e₁) k ≫ twistedHomologyMap g₁ M k) ≫
        P'.twistedHomologyCoefficientMap (eqToHom e₂) k ≫ twistedHomologyMap g₂ S k := by
  subst hw e₂ e₁ e₀
  simp only [eqToHom_refl, twistedHomologyCoefficientMap_id, Category.id_comp,
    twistedHomologyMap_comp, ← twistedHomologyCoefficientMap_comp_assoc]
  convert Category.id_comp _
  rw [← twistedHomologyCoefficientMap_id]
  congr 1
  ext x : 2
  rw [NatTrans.comp_app, fstPullbackCompIso_hom_app]
  -- The fibres of the iterated pullback and of the pullback along the composite agree only up to
  -- unfolding, so `Category.comp_id` is applied by unification rather than by rewriting.
  refine (Category.comp_id _).trans ?_
  rw [eqToHom_app]
  rfl

end EqualMaps

section FstEq

/-! ### Transport along an ambient-component equality

When a map of pairs `f : P ⟶ Q` has an opaque ambient component equal to `g : P.fst ⟶ Q.fst`
only propositionally (`hg : Hom.fst f = g`), `TopPair.twistedChainComplexMapOfFstEq` transports
`TopPair.twistedChainComplexMap f L` to a chain map out of the pullback along `g`. -/

/-- The relative twisted chain map induced by `f : P ⟶ Q`, transported along `hg : Hom.fst f = g`
so its source uses the pullback along `g`. -/
def twistedChainComplexMapOfFstEq {P Q : TopPair.{v}} (f : P ⟶ Q) {g : P.fst ⟶ Q.fst}
    (hg : Hom.fst f = g) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst) :
    P.twistedChainComplex ((LocalCoefficientSystem.pullback g.hom).obj L) ⟶
      Q.twistedChainComplex L :=
  eqToHom (congrArg (fun k : P.fst ⟶ Q.fst ↦
    P.twistedChainComplex ((LocalCoefficientSystem.pullback k.hom).obj L)) hg.symm) ≫
    twistedChainComplexMap f L

/-- Transporting `TopPair.twistedChainComplexMap` along `rfl` recovers the original map. -/
@[simp]
lemma twistedChainComplexMapOfFstEq_rfl {P Q : TopPair.{v}} (f : P ⟶ Q)
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst) :
    twistedChainComplexMapOfFstEq f rfl L = twistedChainComplexMap f L := by
  simp [twistedChainComplexMapOfFstEq]

/-- Compatibility of `TopPair.twistedChainComplexMapOfFstEq` with the quotient maps from ambient
twisted chains. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq {P Q : TopPair.{v}} (f : P ⟶ Q)
    {g : P.fst ⟶ Q.fst} (hg : Hom.fst f = g)
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst) :
    P.twistedChainComplexπ ((LocalCoefficientSystem.pullback g.hom).obj L) ≫
        twistedChainComplexMapOfFstEq f hg L =
      LocalCoefficientSystem.twistedChainComplexMap g L ≫ Q.twistedChainComplexπ L := by
  subst hg
  simp [twistedChainComplexMapOfFstEq]

/-- Naturality of `TopPair.twistedChainComplexMapOfFstEq` in morphisms of local coefficients. -/
@[reassoc]
lemma twistedChainComplexMapOfFstEq_naturality {P Q : TopPair.{v}} (f : P ⟶ Q)
    {g : P.fst ⟶ Q.fst} (hg : Hom.fst f = g)
    {L K : LocalCoefficientSystem.{u, v, max v w} R Q.fst} (η : L ⟶ K) :
    twistedChainComplexMapOfFstEq f hg L ≫ Q.twistedChainComplexCoefficientMap η =
      P.twistedChainComplexCoefficientMap ((LocalCoefficientSystem.pullback g.hom).map η) ≫
        twistedChainComplexMapOfFstEq f hg K := by
  subst hg
  simp [twistedChainComplexMapOfFstEq, twistedChainComplexMap_naturality]

/-- Evaluating the coefficient of a relative chain on an image simplex after
`TopPair.twistedChainComplexMapOfFstEq` agrees with evaluating on the original simplex. -/
@[reassoc]
lemma twistedChainComplexMapOfFstEq_f_comp_twistedChainComplexCoeff {P Q : TopPair.{v}}
    (f : P ⟶ Q) {g : P.fst ⟶ Q.fst} (hg : Hom.fst f = g) [Mono g]
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst) {k : ℕ}
    (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌) (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map)
    (hσ' : ¬Set.range (TopCat.simplexMap ((TopCat.toSSet.map g).app _ σ)) ⊆ Set.range Q.map) :
    (twistedChainComplexMapOfFstEq f hg L).f k ≫ Q.twistedChainComplexCoeff L _ hσ' =
      P.twistedChainComplexCoeff ((LocalCoefficientSystem.pullback g.hom).obj L) σ hσ := by
  subst hg
  unfold twistedChainComplexMapOfFstEq
  rw [eqToHom_refl, Category.id_comp]
  exact twistedChainComplexMap_f_comp_twistedChainComplexCoeff f L σ hσ hσ'

/-- Transporting a quasi-isomorphism of relative twisted chains along `Hom.fst f = g` preserves
being a quasi-isomorphism. -/
lemma quasiIso_twistedChainComplexMapOfFstEq {P Q : TopPair.{v}} (f : P ⟶ Q)
    {g : P.fst ⟶ Q.fst} (hg : Hom.fst f = g)
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
    (h : QuasiIso (twistedChainComplexMap f L)) :
    QuasiIso (twistedChainComplexMapOfFstEq f hg L) := by
  subst hg
  unfold twistedChainComplexMapOfFstEq
  rw [eqToHom_refl, Category.id_comp]
  exact h

end FstEq

end TopPair
