/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.RepresentationTheory.Homological.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Resolution

/-!
# Change of groups for group cohomology computed by resolutions

Let `f : G →* H` be a group homomorphism and `φ : Res(f)(A) ⟶ B` a compatible map of coefficient
representations. A chain map `α : P ⟶ Res(f)(Q)` from a complex of `G`-representations to the
restriction of a complex of `H`-representations induces the cochain map
`MonoidHom.linearYonedaObjMap f φ α : Hom_H(Q, A) ⟶ Hom_G(P, B)`, which sends `g : Q ⟶ A` to
`φ ∘ g ∘ α`. This cochain map and its composition and homotopy lemmas only need `G` and `H` to be
monoids.

When `P` and `Q` are projective resolutions of the trivial representations and `α` lies over the
identity of `k`, Mathlib's identifications `groupCohomologyIso` of group cohomology with the
cohomology of `Hom_H(Q, A)` and `Hom_G(P, B)` carry Mathlib's change-of-group map
`groupCohomology.map f φ n` to the map induced by `linearYonedaObjMap f φ α`
(`MonoidHom.groupCohomologyIso_inv_naturality`). No hypothesis on `f` is needed. Restriction
along `f` need not preserve projective representations, so `α` is in general not a map of
projective resolutions in `Rep k G`; only the exactness of the restricted target is used. This
computes change-of-group maps with geometric resolutions, such as the singular chains of a
contractible free `G`-space, without passing through the bar resolution.

The proof computes `groupCohomologyIso` through comparison maps from the bar resolutions
(`TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap`), uses that the two composites from the bar
resolution of `G` to `Res(f)(Q)` are homotopic (`MonoidHom.barResolutionComparisonHomotopy`), and
that on the bar resolutions the cochain map is Mathlib's inhomogeneous `groupCohomology.cochainsMap`
(`MonoidHom.inhomogeneousCochainsIso_hom_linearYonedaObjMap_resChainMap`).

## Main definitions

* `MonoidHom.linearYonedaObjMap`: the cochain map `Hom_H(Q, A) ⟶ Hom_G(P, B)` induced by `f`,
  `φ` and `α`.

## Main results

* `MonoidHom.groupCohomologyIso_hom_naturality`, `MonoidHom.groupCohomologyIso_inv_naturality`:
  group cohomology computed by projective resolutions is natural in the group.
* `MonoidHom.inhomogeneousCochainsIso_hom_linearYonedaObjMap_resChainMap`: on bar resolutions the
  cochain map is Mathlib's inhomogeneous change of groups.
* `MonoidHom.homologyMap_linearYonedaObjMap_eq_of_homotopy`: homotopic chain maps induce the same
  map on cohomology.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, §8, and Chapter I, §7.

The group cohomology comparisons and change-of-group maps used here are Mathlib's constructions by
Amelia Livingston; no alternative group cohomology is introduced. This file is the cohomological
counterpart of `TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups`.
-/

public section

noncomputable section

open CategoryTheory Rep

universe u

namespace MonoidHom

section CochainMap

variable {k G H : Type u} [CommRing k] [Monoid G] [Monoid H] {A : Rep.{u} k H} {B : Rep.{u} k G}
  (f : G →* H) (φ : res f A ⟶ B)

/-- **Change of groups on morphism complexes.** For `f : G →* H`, a compatible coefficient map
`φ : Res(f)(A) ⟶ B` and a chain map `α : P ⟶ Res(f)(Q)`, this is the cochain map
`Hom_H(Q, A) ⟶ Hom_G(P, B)` sending `g : Q ⟶ A` to `φ ∘ g ∘ α`. -/
def linearYonedaObjMap {P : ChainComplex (Rep.{u} k G) ℕ} {Q : ChainComplex (Rep.{u} k H) ℕ}
    (α : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k B where
  f n := ModuleCat.ofHom <| Linear.leftComp k B (α.f n) ∘ₗ Linear.rightComp k _ φ ∘ₗ
    (resFunctor f).mapLinearMap k
  comm' i j _ := by
    ext (g : Q.X i ⟶ A)
    have h := α.comm j i
    rw [Functor.mapHomologicalComplex_obj_d] at h
    -- Both sides are `g` precomposed with `d ∘ α` and postcomposed with `φ`. The components of
    -- `Hom(-, -)` are the hom-modules only by unfolding `ChainComplex.linearYonedaObj`, so the
    -- simp lemmas for composites in `ModuleCat` do not fire, and the equation is stated directly.
    exact (show P.d j i ≫ α.f i ≫ (resFunctor f).map g ≫ φ =
      α.f j ≫ (resFunctor f).map (Q.d j i ≫ g) ≫ φ by
        rw [Functor.map_comp, Category.assoc, ← Category.assoc (α.f j), h, Category.assoc])

variable {P P' : ChainComplex (Rep.{u} k G) ℕ} {Q Q' : ChainComplex (Rep.{u} k H) ℕ}
  (α : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q)

/-- The cochain map sends `g : Q ⟶ A` to `φ ∘ g ∘ α`. -/
@[simp]
theorem linearYonedaObjMap_f_apply (n : ℕ) (g : Q.X n ⟶ A) :
    (f.linearYonedaObjMap φ α).f n g = α.f n ≫ (resFunctor f).map g ≫ φ :=
  (rfl)

/-- Postcomposing with the map induced by a chain map `β : P' ⟶ P` amounts to precomposing `α`
with `β`. -/
@[reassoc]
theorem linearYonedaObjMap_comp_linearYonedaFunctor_map (β : P' ⟶ P) :
    f.linearYonedaObjMap φ α ≫ (TauCeti.ChainComplex.linearYonedaFunctor k B).map β.op =
      f.linearYonedaObjMap φ (β ≫ α) :=
  -- Both sides send `g` to `φ ∘ g ∘ α ∘ β`. The components of the composite live in
  -- `P'.linearYonedaObj k B` and in `(linearYonedaFunctor k B).obj (op P')`, which agree only by
  -- unfolding, so `simp` cannot split it and the component equation is given directly.
  HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun (g : Q.X n ⟶ A) ↦
    (Category.assoc (β.f n) (α.f n) ((resFunctor f).map g ≫ φ)).symm

/-- Precomposing with the map induced by a chain map `γ : Q ⟶ Q'` amounts to postcomposing `α`
with the restriction of `γ`. -/
@[reassoc]
theorem linearYonedaFunctor_map_comp_linearYonedaObjMap (γ : Q ⟶ Q') :
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map γ.op ≫ f.linearYonedaObjMap φ α =
      f.linearYonedaObjMap φ (α ≫ ((resFunctor f).mapHomologicalComplex _).map γ) :=
  -- Both sides send `g` to `φ ∘ g ∘ γ ∘ α`, stated directly for the reason given in
  -- `linearYonedaObjMap_comp_linearYonedaFunctor_map`.
  HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun (g : Q'.X n ⟶ A) ↦
    show α.f n ≫ (resFunctor f).map (γ.f n ≫ g) ≫ φ =
      (α.f n ≫ (resFunctor f).map (γ.f n)) ≫ (resFunctor f).map g ≫ φ by
    rw [Functor.map_comp]
    simp only [Category.assoc]

/-- Homotopic chain maps induce the same map on the cohomology of morphism complexes. -/
theorem homologyMap_linearYonedaObjMap_eq_of_homotopy
    {α β : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q} (h : Homotopy α β) (n : ℕ) :
    HomologicalComplex.homologyMap (f.linearYonedaObjMap φ α) n =
      HomologicalComplex.homologyMap (f.linearYonedaObjMap φ β) n := by
  -- Both maps factor through the map induced by the identity of the restriction of `Q`.
  have hα := f.linearYonedaObjMap_comp_linearYonedaFunctor_map φ (𝟙 _) α
  have hβ := f.linearYonedaObjMap_comp_linearYonedaFunctor_map φ (𝟙 _) β
  rw [Category.comp_id] at hα hβ
  exact (congrArg (HomologicalComplex.homologyMap · n) hα.symm).trans <|
    (HomologicalComplex.homologyMap_comp _ _ n).trans <|
    (congrArg (_ ≫ ·) ((h.linearYonedaFunctorMap k B).homologyMap_eq n)).trans <|
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      (congrArg (HomologicalComplex.homologyMap · n) hβ)

end CochainMap

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k H} {B : Rep.{u} k G}
  (f : G →* H) (φ : res f A ⟶ B)

section Bar

/-- On the bar resolutions, the cochain map of the relabelling chain map
`TauCeti.Rep.barComplex.resChainMap` is Mathlib's change of groups on inhomogeneous cochains. -/
@[reassoc]
theorem inhomogeneousCochainsIso_hom_linearYonedaObjMap_resChainMap :
    (groupCohomology.inhomogeneousCochainsIso A).hom ≫
        f.linearYonedaObjMap φ (TauCeti.Rep.barComplex.resChainMap f) =
      groupCohomology.cochainsMap f φ ≫ (groupCohomology.inhomogeneousCochainsIso B).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun c ↦ ?_
  refine free_ext _ _ _ _ _ fun x ↦ ?_
  -- Unfolding the cochain isomorphisms, both sides evaluate `freeLift` on a basis element: on the
  -- left, `φ ∘ freeLift c` on the relabelled basis element `f ∘ x`; on the right,
  -- `freeLift (φ ∘ c ∘ (f ∘ ·))` on `x`.
  refine Eq.trans (b := φ.hom ((freeLift k H A c).hom
      (((TauCeti.Rep.barComplex.resChainMap (k := k) f).f n).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1))))) rfl ?_
  refine Eq.trans ?_ (b := (freeLift k G B fun y ↦ φ.hom (c (f ∘ y))).hom
      (Finsupp.single x (MonoidAlgebra.single 1 1))) rfl
  rw [TauCeti.Rep.barComplex.resChainMap_f, TauCeti.Rep.barComplex.resHom_single]
  simp only [res_obj_ρ, ConcreteCategory.hom_ofHom, map_one,
    Representation.freeLift_single_single, Module.End.one_apply, one_smul]

/-- The inverse form of `inhomogeneousCochainsIso_hom_linearYonedaObjMap_resChainMap`. -/
@[reassoc]
theorem linearYonedaObjMap_resChainMap_inhomogeneousCochainsIso_inv :
    f.linearYonedaObjMap φ (TauCeti.Rep.barComplex.resChainMap f) ≫
        (groupCohomology.inhomogeneousCochainsIso B).inv =
      (groupCohomology.inhomogeneousCochainsIso A).inv ≫ groupCohomology.cochainsMap f φ := by
  rw [Iso.comp_inv_eq, Category.assoc,
    ← inhomogeneousCochainsIso_hom_linearYonedaObjMap_resChainMap, Iso.inv_hom_id_assoc]

end Bar

section Naturality

variable (P : ProjectiveResolution (Rep.trivial k G k))
  (Q : ProjectiveResolution (Rep.trivial k H k))
  (α : P.complex ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q.complex)
  (hα : α.f 0 ≫ (resFunctor f).map (Q.π.f 0) = P.π.f 0)

/-- The naturality square, for arbitrary comparison maps from the bar resolutions lying over the
identity and a homotopy between the two composites into the restriction of `Q`. -/
private theorem groupCohomologyIso_inv_naturality_of_homotopy (n : ℕ)
    (β : Rep.barComplex k G ⟶ P.complex) (hβ : β.f 0 ≫ P.π.f 0 = (Rep.barResolution k G).π.f 0)
    (γ : Rep.barComplex k H ⟶ Q.complex) (hγ : γ.f 0 ≫ Q.π.f 0 = (Rep.barResolution k H).π.f 0)
    (h : Homotopy (β ≫ α)
      (TauCeti.Rep.barComplex.resChainMap f ≫ ((resFunctor f).mapHomologicalComplex _).map γ)) :
    HomologicalComplex.homologyMap (f.linearYonedaObjMap φ α) n ≫
        (groupCohomologyIso B n P).inv =
      (groupCohomologyIso A n Q).inv ≫ groupCohomology.map f φ n := by
  rw [TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap B P β hβ n,
    TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap A Q γ hγ n]
  -- The comparison maps are the maps induced by `β` and `γ` on `Hom(-, B)` and `Hom(-, A)`,
  -- which are those of `TauCeti.ChainComplex.linearYonedaFunctor` by definition. The composites
  -- are not type-correct at reducible transparency, so the chain is assembled in term mode.
  let iA := (groupCohomology.inhomogeneousCochainsIso A).inv
  let iB := (groupCohomology.inhomogeneousCochainsIso B).inv
  let LA : Q.complex.linearYonedaObj k A ⟶ (Rep.barComplex k H).linearYonedaObj k A :=
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map γ.op
  let LB : P.complex.linearYonedaObj k B ⟶ (Rep.barComplex k G).linearYonedaObj k B :=
    (TauCeti.ChainComplex.linearYonedaFunctor k B).map β.op
  let ρ := TauCeti.Rep.barComplex.resChainMap (k := k) f
  calc HomologicalComplex.homologyMap (f.linearYonedaObjMap φ α) n ≫
        HomologicalComplex.homologyMap (LB ≫ iB) n
      = HomologicalComplex.homologyMap (f.linearYonedaObjMap φ α ≫ LB ≫ iB) n :=
        (HomologicalComplex.homologyMap_comp _ _ n).symm
    _ = HomologicalComplex.homologyMap (f.linearYonedaObjMap φ (β ≫ α) ≫ iB) n :=
        congrArg (HomologicalComplex.homologyMap · n)
          (f.linearYonedaObjMap_comp_linearYonedaFunctor_map_assoc φ α β iB)
    _ = HomologicalComplex.homologyMap (f.linearYonedaObjMap φ (β ≫ α)) n ≫
          HomologicalComplex.homologyMap iB n :=
        HomologicalComplex.homologyMap_comp _ _ n
    _ = HomologicalComplex.homologyMap
          (f.linearYonedaObjMap φ (ρ ≫ ((resFunctor f).mapHomologicalComplex _).map γ)) n ≫
          HomologicalComplex.homologyMap iB n :=
        congrArg (· ≫ _) (f.homologyMap_linearYonedaObjMap_eq_of_homotopy φ h n)
    _ = HomologicalComplex.homologyMap (LA ≫ f.linearYonedaObjMap φ ρ) n ≫
          HomologicalComplex.homologyMap iB n :=
        congrArg (fun t ↦ HomologicalComplex.homologyMap t n ≫ _)
          (f.linearYonedaFunctor_map_comp_linearYonedaObjMap φ ρ γ).symm
    _ = HomologicalComplex.homologyMap (LA ≫ f.linearYonedaObjMap φ ρ ≫ iB) n :=
        (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
          (congrArg (HomologicalComplex.homologyMap · n) (Category.assoc _ _ _))
    _ = HomologicalComplex.homologyMap (LA ≫ iA ≫ groupCohomology.cochainsMap f φ) n :=
        congrArg (fun t ↦ HomologicalComplex.homologyMap (LA ≫ t) n)
          (f.linearYonedaObjMap_resChainMap_inhomogeneousCochainsIso_inv φ)
    _ = HomologicalComplex.homologyMap (LA ≫ iA) n ≫
          HomologicalComplex.homologyMap (groupCohomology.cochainsMap f φ) n :=
        (congrArg (HomologicalComplex.homologyMap · n) (Category.assoc _ _ _).symm).trans
          (HomologicalComplex.homologyMap_comp _ _ n)

include hα in
/-- **Group cohomology computed by resolutions is natural in the group.** For `f : G →* H`, a
compatible coefficient map `φ : Res(f)(A) ⟶ B`, projective resolutions `P` and `Q` of the trivial
representations and an augmentation-preserving chain map `α : P ⟶ Res(f)(Q)`, the identifications
`groupCohomologyIso` carry the map induced on cohomology by `g ↦ φ ∘ g ∘ α` to Mathlib's
change-of-group map `groupCohomology.map f φ n`. No hypothesis on `f` is needed: restriction along
`f` need not preserve projective representations. -/
@[reassoc]
theorem groupCohomologyIso_inv_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (f.linearYonedaObjMap φ α) n ≫
        (groupCohomologyIso B n P).inv =
      (groupCohomologyIso A n Q).inv ≫ groupCohomology.map f φ n :=
  groupCohomologyIso_inv_naturality_of_homotopy f φ P Q α n _
    ((ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k G) P).trans
      (Category.comp_id _)) _
    ((ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k H) Q).trans
      (Category.comp_id _))
    (f.barResolutionComparisonHomotopy P Q α hα)

include hα in
/-- The forward identifications are also natural in the group. -/
@[reassoc]
theorem groupCohomologyIso_hom_naturality (n : ℕ) :
    groupCohomology.map f φ n ≫ (groupCohomologyIso B n P).hom =
      (groupCohomologyIso A n Q).hom ≫
        HomologicalComplex.homologyMap (f.linearYonedaObjMap φ α) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← groupCohomologyIso_inv_naturality f φ P Q α hα,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Naturality

end MonoidHom
