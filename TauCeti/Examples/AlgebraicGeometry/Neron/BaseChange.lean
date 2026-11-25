/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Neron.BaseChange
public import TauCeti.AlgebraicGeometry.SpecialFiber.Basic
public import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# Examples for the smooth base change of Néron models

These are examples checking `TauCeti.AlgebraicGeometry.Neron.NeronModel.baseChange`:

* **Base change along the identity.** For `S' = S`, the canonical isomorphism
  `M.model ×_S S ≅ M.model` identifies the base change of a Néron model `M` with `M`: it is
  compatible with the generic isomorphisms, up to the identification `A ×_η η ≅ A`.
* **Fibres of the base change.** For a point `s' ⟶ S'` lying over a point `s ⟶ S` through
  `t : s' ⟶ s`, the fibre of the base-changed model at `s'` is the base change along `t` of the
  fibre of the model at `s` (`CategoryTheory.Over.pullbackPullbackIsoOfComm`). For an extension
  `R → R'` of discrete valuation rings with `Spec R' ⟶ Spec R` étale, this says that the special
  fibre of the base-changed model is the base change of the special fibre along the extension
  `κ(R) → κ(R')` of residue fields; the statement below needs only a local homomorphism of local
  rings whose `Spec` map is smooth.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Neron

namespace TauCeti.NeronBaseChangeExamples

universe u

section Identity

variable {η S : Scheme.{u}} {j : η ⟶ S} {A : Over η}

/-- **Base change along the identity.** The canonical isomorphism
`Over.pullbackId.app M.model : M.model ×_S S ≅ M.model` from the base change of `M` along `𝟙 S`
to `M` is compatible with the generic isomorphisms, through `Over.pullbackId.app A`. -/
example (M : NeronModel j A) :
    (Over.pullback j).map (Over.pullbackId.hom.app M.model) ≫ M.genericIso.hom =
      (M.baseChange (IsPullback.id_vert j)).genericIso.hom ≫ Over.pullbackId.hom.app A := by
  -- The identity is proved for an arbitrary `S`-scheme `X` and isomorphism `e : X ×_S η ≅ A`,
  -- since the goal's composites typecheck only up to unfolding the base-changed model.
  have key (X : Over S) (e : (Over.pullback j).obj X ≅ A) :
      (Over.pullback j).map (Over.pullbackId.hom.app X) ≫ e.hom =
        ((Over.pullbackComp j (𝟙 S)).inv.app X ≫ eqToHom (by simp) ≫
          (Over.pullbackComp (𝟙 η) j).hom.app X ≫ (Over.pullback (𝟙 η)).map e.hom) ≫
            Over.pullbackId.hom.app A := by
    simp only [Category.assoc]
    rw [Over.pullbackId.hom.naturality e.hom, Functor.id_map,
      Over.pullbackComp_id_left_hom_app_comp_pullbackId_assoc, eqToHom_trans_assoc,
      Over.pullbackComp_id_inv_app_comp_eqToHom_assoc]
  rw [NeronModel.baseChange_genericIso_hom, Over.pullbackPullbackIsoOfComm_hom_app]
  exact key M.model M.genericIso

end Identity

section Fibre

variable {η S η' S' s s' : Scheme.{u}} {j : η ⟶ S} {g : S' ⟶ S} {j' : η' ⟶ S'} {g' : η' ⟶ η}
  {A : Over η}

/-- **Fibres of the base change of a Néron model.** The fibre at `i'` of the base change of a
Néron model `M` along a smooth `g : S' ⟶ S` is the base change along `t` of the fibre of `M` at
`i`. -/
example [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A) {i : s ⟶ S} {i' : s' ⟶ S'}
    {t : s' ⟶ s} (h : i' ≫ g = t ≫ i) :
    (Over.pullback i').obj (M.baseChange sq).model ≅
      (Over.pullback t).obj ((Over.pullback i).obj M.model) :=
  (Over.pullbackPullbackIsoOfComm h).app M.model

end Fibre

section SpecialFibre

variable {η η' : Scheme.{u}} {R R' : Type u} [CommRing R] [CommRing R'] [IsLocalRing R]
  [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ]
  {j : η ⟶ Spec (.of R)} {j' : η' ⟶ Spec (.of R')} {g' : η' ⟶ η} {A : Over η}

/-- **Special fibre of the base change.** For a local homomorphism `R → R'` of local rings with
smooth `Spec R' ⟶ Spec R` (for instance an extension of discrete valuation rings with étale `Spec`
map), the
special fibre of the base change of a Néron model `M` over `Spec R` is the base change of the
special fibre of `M` along `Spec κ(R') ⟶ Spec κ(R)`. -/
example [Smooth (Spec.map (CommRingCat.ofHom φ))]
    (sq : IsPullback j' g' (Spec.map (CommRingCat.ofHom φ)) j) (M : NeronModel j A) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R')))).obj
        (M.baseChange sq).model ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj M.model) :=
  (Over.pullbackPullbackIsoOfComm (specMap_residue_comp_specMap φ)).app M.model

end SpecialFibre

end TauCeti.NeronBaseChangeExamples
