/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Resolution

/-!
# Change of groups for group cohomology computed by resolutions

Let `f : G →* H` be a group homomorphism and `φ : Res(f)(A) ⟶ B` a compatible map of coefficient
representations, with `A` a representation of `H` and `B` one of `G`. A chain map
`α : P ⟶ Res(f)(Q)` from a complex of `G`-representations to the restriction of a complex of
`H`-representations induces the cochain map
`MonoidHom.linearYonedaObjCochainMap f φ α : Hom_H(Q, A) ⟶ Hom_G(P, B)`, which sends `u` to the
composite `α ≫ Res(f)(u) ≫ φ`.

When `P` and `Q` are projective resolutions of the trivial representations and `α` lies over the
identity of `k`, Mathlib's identifications `groupCohomologyIso` of group cohomology with the
cohomology of `Hom_H(Q, A)` and `Hom_G(P, B)` carry Mathlib's change-of-group map
`groupCohomology.map f φ n : Hⁿ(H, A) ⟶ Hⁿ(G, B)` to the map induced by
`linearYonedaObjCochainMap f φ α` (`MonoidHom.groupCohomologyIso_hom_naturality`). No hypothesis
on `f` is needed: restriction along `f` need not preserve projective representations, so `α` is
in general not a map of projective resolutions in `Rep k G`, and only the exactness of the
restricted target is used. This computes change-of-group maps with geometric resolutions, such as
the singular chains of a contractible free `G`-space, without passing through the bar resolution.

This is the cohomological counterpart of `MonoidHom.groupHomologyIso_hom_naturality`, and the proof
follows the same plan: `groupCohomologyIso` is computed through comparison maps from the bar
resolutions (`TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap`), the two composites from the bar
resolution of `G` to `Res(f)(Q)` are homotopic (`MonoidHom.barResolutionComparisonHomotopy`), and
on the bar resolutions the cochain map is Mathlib's `groupCohomology.cochainsMap f φ`
(`MonoidHom.linearYonedaObjCochainMap_resChainMap_comp_inhomogeneousCochainsIso_inv`).

## Main definitions

* `MonoidHom.linearYonedaObjCochainMap`: the cochain map `Hom_H(Q, A) ⟶ Hom_G(P, B)` induced by
  `f`, `φ` and `α`.

## Main results

* `MonoidHom.groupCohomologyIso_hom_naturality`, `MonoidHom.groupCohomologyIso_inv_naturality`:
  group cohomology computed by projective resolutions is natural in the group.
* `MonoidHom.linearYonedaObjCochainMap_resChainMap_comp_inhomogeneousCochainsIso_inv`: on bar
  resolutions the cochain map is Mathlib's change of groups on inhomogeneous cochains.
* `MonoidHom.homologyMap_linearYonedaObjCochainMap_eq_of_homotopy`: homotopic chain maps induce
  the same map on cohomology.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, §8, and Chapter I, §7.

The group cohomology comparisons and change-of-group maps used here are Mathlib's constructions by
Amelia Livingston; no alternative group cohomology is introduced.
-/

public section

noncomputable section

open CategoryTheory Rep

universe u

namespace MonoidHom

section CochainMap

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k H} {B : Rep.{u} k G}
  (f : G →* H) (φ : res f A ⟶ B)

/-- **Change of groups on complexes of morphisms.** For `f : G →* H`, a compatible coefficient
map `φ : Res(f)(A) ⟶ B` and a chain map `α : P ⟶ Res(f)(Q)`, this is the cochain map
`Hom_H(Q, A) ⟶ Hom_G(P, B)` sending `u` to `α ≫ Res(f)(u) ≫ φ`. -/
def linearYonedaObjCochainMap {P : ChainComplex (Rep.{u} k G) ℕ}
    {Q : ChainComplex (Rep.{u} k H) ℕ} (α : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k B where
  f n := ModuleCat.ofHom <| Linear.leftComp k B (α.f n) ∘ₗ Linear.rightComp k _ φ ∘ₗ
    (resFunctor f).mapLinearMap k
  comm' i j (h : i + 1 = j) := by
    subst h
    refine ModuleCat.hom_ext <| LinearMap.ext fun (u : Q.X i ⟶ A) ↦ ?_
    have hα := α.comm (i + 1) i
    rw [Functor.mapHomologicalComplex_obj_d] at hα
    -- Both sides send `u` to `P.d ≫ α ≫ Res(f)(u) ≫ φ`, the right one after moving the
    -- differential of `Q` across `α`. The components are stated as maps between the modules of
    -- morphisms, while the differentials act on the terms of `linearYonedaObj` complexes; these
    -- agree only by unfolding, so the goal is restated rather than rewritten by `simp`.
    change P.d (i + 1) i ≫ α.f i ≫ (resFunctor f).map u ≫ φ =
      α.f (i + 1) ≫ (resFunctor f).map (Q.d (i + 1) i ≫ u) ≫ φ
    rw [Functor.map_comp, Category.assoc, reassoc_of% hα]

variable {P P' : ChainComplex (Rep.{u} k G) ℕ} {Q Q' : ChainComplex (Rep.{u} k H) ℕ}
  (α : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q)

/-- The cochain map sends `u` to `α ≫ Res(f)(u) ≫ φ`. -/
@[simp↓]
theorem linearYonedaObjCochainMap_f_hom_apply (n : ℕ) (u : Q.X n ⟶ A) :
    (f.linearYonedaObjCochainMap φ α).f n u = α.f n ≫ (resFunctor f).map u ≫ φ :=
  (rfl)

/-- Precomposing with a chain map `β : P' ⟶ P` amounts to precomposing `α` with `β`. -/
theorem linearYonedaObjCochainMap_comp_linearYonedaFunctor_map (β : P' ⟶ P) :
    f.linearYonedaObjCochainMap φ α ≫ (TauCeti.ChainComplex.linearYonedaFunctor k B).map β.op =
      f.linearYonedaObjCochainMap φ (β ≫ α) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun (u : Q.X n ⟶ A) ↦ ?_
  -- Both sides send `u` to `β ≫ α ≫ Res(f)(u) ≫ φ`. The components are stated between
  -- `linearYonedaObj` complexes and `linearYonedaFunctor` objects, which agree only by unfolding,
  -- so `simp` cannot split the composite into its components.
  exact (Category.assoc (β.f n) (α.f n) ((resFunctor f).map u ≫ φ)).symm

/-- Postcomposing with a chain map `γ : Q ⟶ Q'` on the source amounts to postcomposing `α` with the
restriction of `γ`. -/
theorem linearYonedaFunctor_map_comp_linearYonedaObjCochainMap (γ : Q ⟶ Q') :
    (TauCeti.ChainComplex.linearYonedaFunctor k A).map γ.op ≫ f.linearYonedaObjCochainMap φ α =
      f.linearYonedaObjCochainMap φ (α ≫ ((resFunctor f).mapHomologicalComplex _).map γ) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun (u : Q'.X n ⟶ A) ↦ ?_
  -- Both sides send `u` to `α ≫ Res(f)(γ) ≫ Res(f)(u) ≫ φ`; the components agree only by
  -- unfolding, as in `linearYonedaObjCochainMap_comp_linearYonedaFunctor_map`.
  exact congrArg (α.f n ≫ ·) ((congrArg (· ≫ φ) ((resFunctor f).map_comp (γ.f n) u)).trans
    (Category.assoc ((resFunctor f).map (γ.f n)) ((resFunctor f).map u) φ))

/-- Homotopic chain maps induce the same map on the cohomology of complexes of morphisms. -/
theorem homologyMap_linearYonedaObjCochainMap_eq_of_homotopy
    {α β : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q} (h : Homotopy α β) (n : ℕ) :
    HomologicalComplex.homologyMap (f.linearYonedaObjCochainMap φ α) n =
      HomologicalComplex.homologyMap (f.linearYonedaObjCochainMap φ β) n := by
  have hα := f.linearYonedaObjCochainMap_comp_linearYonedaFunctor_map φ (𝟙 _) α
  have hβ := f.linearYonedaObjCochainMap_comp_linearYonedaFunctor_map φ (𝟙 _) β
  rw [Category.comp_id] at hα hβ
  rw [← hα, ← hβ]
  -- `Hom(-, B)` takes the homotopy between `α` and `β` to a cochain homotopy. The composites are
  -- stated between `linearYonedaObj` complexes and `linearYonedaFunctor` objects, which agree only
  -- by unfolding, so `homologyMap_comp` is applied in term mode rather than by `rw`.
  exact (HomologicalComplex.homologyMap_comp _ _ n).trans <|
    (congrArg (_ ≫ ·) ((h.linearYonedaFunctorMap k B).homologyMap_eq n)).trans
      (HomologicalComplex.homologyMap_comp _ _ n).symm

end CochainMap

section Bar

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k H} {B : Rep.{u} k G}
  (f : G →* H) (φ : res f A ⟶ B)

/-- On the bar resolutions, the cochain map induced by the relabelling chain map
`TauCeti.Rep.barComplex.resChainMap` is Mathlib's change of groups
`groupCohomology.cochainsMap f φ` on inhomogeneous cochains. -/
@[reassoc]
theorem linearYonedaObjCochainMap_resChainMap_comp_inhomogeneousCochainsIso_inv :
    f.linearYonedaObjCochainMap φ (TauCeti.Rep.barComplex.resChainMap f) ≫
        (groupCohomology.inhomogeneousCochainsIso B).inv =
      (groupCohomology.inhomogeneousCochainsIso A).inv ≫ groupCohomology.cochainsMap f φ := by
  ext i (u : (barComplex k H).X i ⟶ A) x
  -- Both sides evaluate `u` on the basis element `f ∘ x` and apply `φ`. The inverse of
  -- `inhomogeneousCochainsIso` is evaluation on basis elements, by definition: it is built by
  -- `isoOfComponents` between complexes whose shapes agree only by unfolding, so its simp lemmas
  -- do not fire on these components.
  change ((TauCeti.Rep.barComplex.resChainMap f).f i ≫ (resFunctor f).map u ≫ φ).hom
      (Finsupp.single x (MonoidAlgebra.single 1 1)) =
    φ.hom (u.hom (Finsupp.single (f ∘ x) (MonoidAlgebra.single 1 1)))
  rw [TauCeti.Rep.barComplex.resChainMap_f]
  simpa using congrArg φ.hom (Rep.resMap_hom_apply f u _)

end Bar

section Naturality

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k H} {B : Rep.{u} k G}
  (f : G →* H) (φ : res f A ⟶ B)
  (P : ProjectiveResolution (Rep.trivial k G k)) (Q : ProjectiveResolution (Rep.trivial k H k))
  (α : P.complex ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q.complex)
  (hα : α.f 0 ≫ (resFunctor f).map (Q.π.f 0) = P.π.f 0)

include hα in
/-- **Group cohomology computed by resolutions is natural in the group**, inverse form. For
`f : G →* H`, a compatible coefficient map `φ : Res(f)(A) ⟶ B`, projective resolutions `P` and `Q`
of the trivial representations and an augmentation-preserving chain map `α : P ⟶ Res(f)(Q)`, the
inverses of the identifications `groupCohomologyIso` carry the map induced on the cohomology of
complexes of morphisms by `u ↦ α ≫ Res(f)(u) ≫ φ` to Mathlib's change-of-group map
`groupCohomology.map f φ n`. No hypothesis on `f` is needed. -/
@[reassoc]
theorem groupCohomologyIso_inv_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (f.linearYonedaObjCochainMap φ α) n ≫
        (groupCohomologyIso B n P).inv =
      (groupCohomologyIso A n Q).inv ≫ groupCohomology.map f φ n := by
  have hG := (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k G) P).trans
    (Category.comp_id _)
  have hH := (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k H) Q).trans
    (Category.comp_id _)
  -- Precomposing with the comparison map of `G` after `α` is homotopic to precomposing with the
  -- relabelling of the bar resolutions followed by the comparison map of `H`.
  have hhtpy := f.homologyMap_linearYonedaObjCochainMap_eq_of_homotopy φ
    (f.barResolutionComparisonHomotopy P Q α hα) n
  -- On the bar resolutions the cochain map is `cochainsMap f φ`.
  have hbar : ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
        (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k H) Q).op ≫
        (groupCohomology.inhomogeneousCochainsIso A).inv) ≫ groupCohomology.cochainsMap f φ =
      f.linearYonedaObjCochainMap φ (TauCeti.Rep.barComplex.resChainMap f ≫
        ((resFunctor f).mapHomologicalComplex _).map
          (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k H) Q)) ≫
        (groupCohomology.inhomogeneousCochainsIso B).inv :=
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      (f.linearYonedaObjCochainMap_resChainMap_comp_inhomogeneousCochainsIso_inv φ).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (f.linearYonedaFunctor_map_comp_linearYonedaObjCochainMap φ _ _)))
  -- The complexes of `ProjectiveResolution.complex` and of `Rep.barResolution` are the given and
  -- bar complexes only by unfolding, so the steps are assembled in term mode, where they are
  -- identified.
  calc _ = HomologicalComplex.homologyMap (f.linearYonedaObjCochainMap φ α) n ≫
        HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k B).map
          (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P).op ≫
          (groupCohomology.inhomogeneousCochainsIso B).inv) n := by
        rw [TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap B P _ hG]; rfl
    _ = HomologicalComplex.homologyMap (f.linearYonedaObjCochainMap φ
          (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P ≫ α)) n ≫
        HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).inv n :=
        (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
          (congrArg (HomologicalComplex.homologyMap · n) ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (groupCohomology.inhomogeneousCochainsIso B).inv)
              (f.linearYonedaObjCochainMap_comp_linearYonedaFunctor_map φ α _)))).trans
          (HomologicalComplex.homologyMap_comp _ _ n)
    _ = (HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
          (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k H) Q).op ≫
          (groupCohomology.inhomogeneousCochainsIso A).inv) n ≫ groupCohomology.map f φ n :
            (Q.complex.linearYonedaObj k A).homology n ⟶
              (groupCohomology.inhomogeneousCochains B).homology n) :=
        (congrArg (· ≫ _) hhtpy).trans <| (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
          (congrArg (HomologicalComplex.homologyMap · n) hbar.symm).trans
          (HomologicalComplex.homologyMap_comp _ _ n)
    _ = _ := by rw [TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap A Q _ hH]; rfl

include hα in
/-- **Group cohomology computed by resolutions is natural in the group.** For `f : G →* H`, a
compatible coefficient map `φ : Res(f)(A) ⟶ B`, projective resolutions `P` and `Q` of the trivial
representations and an augmentation-preserving chain map `α : P ⟶ Res(f)(Q)`, the identifications
`groupCohomologyIso` carry Mathlib's change-of-group map `groupCohomology.map f φ n` to the map
induced on the cohomology of complexes of morphisms by `u ↦ α ≫ Res(f)(u) ≫ φ`. -/
@[reassoc]
theorem groupCohomologyIso_hom_naturality (n : ℕ) :
    groupCohomology.map f φ n ≫ (groupCohomologyIso B n P).hom =
      (groupCohomologyIso A n Q).hom ≫
        HomologicalComplex.homologyMap (f.linearYonedaObjCochainMap φ α) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    groupCohomologyIso_inv_naturality f φ P Q α hα]

end Naturality

end MonoidHom
