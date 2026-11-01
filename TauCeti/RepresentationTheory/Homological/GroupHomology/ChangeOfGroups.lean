/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupHomology.BarMap
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Resolution
public import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor

/-!
# Change of groups for group homology computed by resolutions

Let `f : G →* H` be a group homomorphism and `φ : A ⟶ Res(f)(B)` a compatible map of coefficient
representations. A chain map `α : P ⟶ Res(f)(Q)` from a complex of `G`-representations to the
restriction of a complex of `H`-representations induces the chain map
`MonoidHom.coinvariantsTensorChainMap f φ α : (A ⊗ P)_G ⟶ (B ⊗ Q)_H`, which sends the class of
`a ⊗ c` to the class of `φ a ⊗ α c`. In each degree it is the map
`MonoidHom.coinvariantsTensorMap` on tensor coinvariants of representations.

When `P` and `Q` are projective resolutions of the trivial representations and `α` lies over the
identity of `k`, Mathlib's identifications `groupHomologyIso` of group homology with the homology
of `(A ⊗ P)_G` and `(B ⊗ Q)_H` carry Mathlib's change-of-group map `groupHomology.map f φ n` to the
map induced by `coinvariantsTensorChainMap f φ α` (`MonoidHom.groupHomologyIso_hom_naturality`).
No hypothesis on `f` is needed. Restriction along `f` need not preserve projective
representations, so `α` is in general not a map of projective resolutions in `Rep k G`; only the
exactness of the restricted target is used. This computes change-of-group maps with geometric
resolutions, such as the singular chains of a contractible free `G`-space, without passing
through the bar resolution.

The proof computes `groupHomologyIso` through comparison maps from the bar resolutions
(`Rep.groupHomologyIso_hom_eq_homologyMap`), uses that the two composites from the bar
resolution of `G` to `Res(f)(Q)` are homotopic (`MonoidHom.barResolutionComparisonHomotopy`), and
that on bar coinvariants the change-of-group map is `groupHomology.map`
(`MonoidHom.inhomogeneousChainsIso_homologyMap_barCoinvariantsMap`).

## Main definitions

* `MonoidHom.coinvariantsTensorChainMap`: the chain map `(A ⊗ P)_G ⟶ (B ⊗ Q)_H` induced by
  `f`, `φ` and `α`.

## Main results

* `MonoidHom.groupHomologyIso_hom_naturality`, `MonoidHom.groupHomologyIso_inv_naturality`: group
  homology computed by projective resolutions is natural in the group.
* `MonoidHom.barCoinvariantsMap_eq_coinvariantsTensorChainMap`: on bar resolutions the chain map
  is the existing change of groups on bar coinvariants.
* `MonoidHom.homologyMap_coinvariantsTensorChainMap_eq_of_homotopy`: homotopic chain maps induce
  the same map on homology.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, §8, and Chapter I, §7.

The group homology comparisons and change-of-group maps used here are Mathlib's constructions by
Amelia Livingston; no alternative group homology is introduced.
-/

public section

noncomputable section

open CategoryTheory Rep Representation

universe u

namespace MonoidHom

section ChainMap

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k G} {B : Rep.{u} k H}
  (f : G →* H) (φ : A ⟶ res f B)

/-- **Change of groups on tensor coinvariants of complexes.** For `f : G →* H`, a compatible
coefficient map `φ : A ⟶ Res(f)(B)` and a chain map `α : P ⟶ Res(f)(Q)`, this is the chain map
`(A ⊗ P)_G ⟶ (B ⊗ Q)_H` sending the class of `a ⊗ c` to the class of `φ a ⊗ α c`. -/
def coinvariantsTensorChainMap {P : ChainComplex (Rep.{u} k G) ℕ}
    {Q : ChainComplex (Rep.{u} k H) ℕ} (α : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q) :
    P.coinvariantsTensorObj A ⟶ Q.coinvariantsTensorObj B where
  f n := f.coinvariantsTensorMap φ (α.f n)
  comm' i j _ := by
    have h := α.comm i j
    rw [Functor.mapHomologicalComplex_obj_d] at h
    rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d]
    exact (coinvariantsTensorMap_naturality f φ (α.f i) (α.f j) (P.d i j) (Q.d i j) h).symm

variable {P P' : ChainComplex (Rep.{u} k G) ℕ} {Q Q' : ChainComplex (Rep.{u} k H) ℕ}
  (α : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q)

/-- The chain map sends the class of `a ⊗ c` to the class of `φ a ⊗ α c`. -/
-- Match before simplification changes the presentation of the dependent tensor carrier.
@[simp↓]
theorem coinvariantsTensorChainMap_f_mk (n : ℕ) (a : A) (c : P.X n) :
    ((f.coinvariantsTensorChainMap φ α).f n).hom (coinvariantsTensorMk A (P.X n) a c) =
      coinvariantsTensorMk B (Q.X n) (φ.hom a) ((α.f n).hom c) :=
  f.coinvariantsTensorMap_mk φ (α.f n) a c

/-- Precomposing with the map induced by a chain map `β : P' ⟶ P` amounts to precomposing `α`
with `β`. -/
@[reassoc]
theorem mapHomologicalComplex_map_comp_coinvariantsTensorChainMap (β : P' ⟶ P) :
    (((coinvariantsTensor k G).obj A).mapHomologicalComplex _).map β ≫
        f.coinvariantsTensorChainMap φ α =
      f.coinvariantsTensorChainMap φ (β ≫ α) :=
  -- Both sides evaluate on a tensor class `⟦a ⊗ c⟧` to `⟦φ a ⊗ α (β c)⟧`.
  HomologicalComplex.hom_ext _ _ fun n ↦
    coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a c ↦
      (f.coinvariantsTensorChainMap_f_mk φ α n a ((β.f n).hom c)).trans
        (f.coinvariantsTensorChainMap_f_mk φ (β ≫ α) n a c).symm)

/-- Postcomposing with the map induced by a chain map `γ : Q ⟶ Q'` amounts to postcomposing `α`
with the restriction of `γ`. -/
@[reassoc]
theorem coinvariantsTensorChainMap_comp_mapHomologicalComplex_map (γ : Q ⟶ Q') :
    f.coinvariantsTensorChainMap φ α ≫
        (((coinvariantsTensor k H).obj B).mapHomologicalComplex _).map γ =
      f.coinvariantsTensorChainMap φ (α ≫ ((resFunctor f).mapHomologicalComplex _).map γ) :=
  -- Both sides evaluate on a tensor class `⟦a ⊗ c⟧` to `⟦φ a ⊗ γ (α c)⟧`.
  HomologicalComplex.hom_ext _ _ fun n ↦
    coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a c ↦
      (congrArg _ (f.coinvariantsTensorChainMap_f_mk φ α n a c)).trans
        (f.coinvariantsTensorChainMap_f_mk φ
          (α ≫ ((resFunctor f).mapHomologicalComplex _).map γ) n a c).symm)

/-- Homotopic chain maps induce the same map on the homology of tensor coinvariants. -/
theorem homologyMap_coinvariantsTensorChainMap_eq_of_homotopy
    {α β : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q} (h : Homotopy α β) (n : ℕ) :
    HomologicalComplex.homologyMap (f.coinvariantsTensorChainMap φ α) n =
      HomologicalComplex.homologyMap (f.coinvariantsTensorChainMap φ β) n := by
  have hα := f.mapHomologicalComplex_map_comp_coinvariantsTensorChainMap φ (𝟙 _) α
  have hβ := f.mapHomologicalComplex_map_comp_coinvariantsTensorChainMap φ (𝟙 _) β
  rw [Category.comp_id] at hα hβ
  rw [← hα, ← hβ, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    (((coinvariantsTensor k G).obj A).mapHomotopy h).homologyMap_eq]

end ChainMap

section Bar

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  {A : Rep.{u} k G} {B : Rep.{u} k H} (f : G →* H) (φ : A ⟶ res f B)

/-- Change of groups on bar coinvariants is the coinvariant map of the relabelling chain map
`TauCeti.Rep.barComplex.resChainMap` of the bar resolutions. -/
theorem barCoinvariantsMap_eq_coinvariantsTensorChainMap :
    f.barCoinvariantsMap φ =
      f.coinvariantsTensorChainMap φ (TauCeti.Rep.barComplex.resChainMap f) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦
    coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a c ↦ ?_)
  -- Evaluate both chain maps on the tensor class, as stated by their tensor formulas.
  change ((f.barCoinvariantsMap φ).f n).hom (Coinvariants.mk _ (a ⊗ₜ[k] c)) =
    ((f.coinvariantsTensorChainMap φ _).f n).hom (coinvariantsTensorMk A _ a c)
  rw [coinvariantsTensorChainMap_f_mk]
  exact barCoinvariantsMap_f_mk_tmul f φ n a c

end Bar

section Naturality

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  {A : Rep.{u} k G} {B : Rep.{u} k H} (f : G →* H) (φ : A ⟶ res f B)
  (P : ProjectiveResolution (Rep.trivial k G k)) (Q : ProjectiveResolution (Rep.trivial k H k))
  (α : P.complex ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q.complex)
  (hα : α.f 0 ≫ (resFunctor f).map (Q.π.f 0) = P.π.f 0)

/-- The naturality square, for arbitrary comparison maps from the bar resolutions lying over the
identity and a homotopy between the two composites into the restriction of `Q`. -/
private theorem groupHomologyIso_hom_naturality_of_homotopy (n : ℕ)
    (β : Rep.barComplex k G ⟶ P.complex) (hβ : β.f 0 ≫ P.π.f 0 = (Rep.barResolution k G).π.f 0)
    (γ : Rep.barComplex k H ⟶ Q.complex) (hγ : γ.f 0 ≫ Q.π.f 0 = (Rep.barResolution k H).π.f 0)
    (h : Homotopy (β ≫ α)
      (TauCeti.Rep.barComplex.resChainMap f ≫ ((resFunctor f).mapHomologicalComplex _).map γ)) :
    groupHomology.map f φ n ≫ (groupHomologyIso B n Q).hom =
      (groupHomologyIso A n P).hom ≫
        HomologicalComplex.homologyMap (f.coinvariantsTensorChainMap φ α) n := by
  have key : HomologicalComplex.homologyMap ((groupHomology.inhomogeneousChainsIso A).hom ≫
        (((coinvariantsTensor k G).obj A).mapHomologicalComplex _).map β) n ≫
        HomologicalComplex.homologyMap (f.coinvariantsTensorChainMap φ α) n =
      (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
        HomologicalComplex.homologyMap (f.barCoinvariantsMap φ) n) ≫
        HomologicalComplex.homologyMap
          ((((coinvariantsTensor k H).obj B).mapHomologicalComplex _).map γ) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, Category.assoc, Category.assoc,
      mapHomologicalComplex_map_comp_coinvariantsTensorChainMap,
      barCoinvariantsMap_eq_coinvariantsTensorChainMap,
      coinvariantsTensorChainMap_comp_mapHomologicalComplex_map,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
      homologyMap_coinvariantsTensorChainMap_eq_of_homotopy f φ h n]
  -- `groupHomology A n` is the homology of the inhomogeneous chains only up to unfolding its
  -- definition, so the composite is assembled from the equations above in term mode, where
  -- these objects are compared by definitional unfolding.
  exact (congrArg (groupHomology.map f φ n ≫ ·)
    ((Rep.groupHomologyIso_hom_eq_homologyMap B Q γ hγ n).trans
      (HomologicalComplex.homologyMap_comp _ _ n))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (inhomogeneousChainsIso_homologyMap_barCoinvariantsMap f φ n).symm).trans <|
    key.symm.trans
      (congrArg (· ≫ _) (Rep.groupHomologyIso_hom_eq_homologyMap A P β hβ n).symm)

include hα in
/-- **Group homology computed by resolutions is natural in the group.** For `f : G →* H`, a
compatible coefficient map `φ : A ⟶ Res(f)(B)`, projective resolutions `P` and `Q` of the trivial
representations and an augmentation-preserving chain map `α : P ⟶ Res(f)(Q)`, the identifications
`groupHomologyIso` carry Mathlib's change-of-group map `groupHomology.map f φ n` to the map induced
on the homology of tensor coinvariants by `⟦a ⊗ c⟧ ↦ ⟦φ a ⊗ α c⟧`. No hypothesis on `f` is
needed: restriction along `f` need not preserve projective representations. -/
@[reassoc]
theorem groupHomologyIso_hom_naturality (n : ℕ) :
    groupHomology.map f φ n ≫ (groupHomologyIso B n Q).hom =
      (groupHomologyIso A n P).hom ≫
        HomologicalComplex.homologyMap (f.coinvariantsTensorChainMap φ α) n :=
  groupHomologyIso_hom_naturality_of_homotopy f φ P Q α n _
    ((ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k G) P).trans
      (Category.comp_id _)) _
    ((ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k H) Q).trans
      (Category.comp_id _))
    (f.barResolutionComparisonHomotopy P Q α hα)

include hα in
/-- The inverse identifications are also natural in the group. -/
@[reassoc]
theorem groupHomologyIso_inv_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (f.coinvariantsTensorChainMap φ α) n ≫
        (groupHomologyIso B n Q).inv =
      (groupHomologyIso A n P).inv ≫ groupHomology.map f φ n := by
  rw [Iso.comp_inv_eq, Category.assoc, groupHomologyIso_hom_naturality f φ P Q α hα,
    Iso.inv_hom_id_assoc]

end Naturality

end MonoidHom
