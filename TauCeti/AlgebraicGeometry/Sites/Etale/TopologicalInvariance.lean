/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.UniversalHomeomorphism
public import TauCeti.AlgebraicGeometry.Sites.Etale.BaseChange
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.RingTheory.Etale.Field
import TauCeti.RingTheory.Etale.Torsor.GaloisMap

/-!
# Base change of étale schemes along a universal homeomorphism

For a morphism `f : X ⟶ Y`, base change along `f` gives a functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` between the categories of étale schemes
(`TauCeti/AlgebraicGeometry/Sites/Etale/BaseChange.lean`). When `f` is a universal homeomorphism,
this functor is fully faithful: base change along `f` is bijective on morphisms into an étale
`Y`-scheme (`TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.overPullback_map_bijective`),
because universal homeomorphisms have the unique left lifting property with respect to étale
morphisms. This is the full faithfulness half of the topological invariance of the small étale site
(Stacks, Theorem 04DZ); essential surjectivity is not proved here.

The universality hypothesis cannot be weakened to `f` being a mere homeomorphism: for any
separable field extension `L / K`, `f = Spec.algebraMap K L` is a homeomorphism of one-point
schemes whose base-change functor `f.smallEtaleBaseChange` is full if and only if
`algebraMap K L` is surjective (`full_smallEtaleBaseChange_specAlgebraMap_iff`). Quantitatively,
for a finite Galois extension `L / K` of degree `n > 1`, `Etale.mk f` has `n` endomorphisms over
`Spec K` while its base change `Spec (L ⊗[K] L)` over `Spec L` splits into `n` copies of `Spec L`
and has `n ^ n` endomorphisms over `Spec L`. For instance, for `Spec (𝔽_{p²}) ⟶ Spec 𝔽_p`, the
cover has `2` endomorphisms over `𝔽_p` and `4` after base change to `𝔽_{p²}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.faithful_smallEtaleBaseChange` and
  `AlgebraicGeometry.Scheme.Hom.full_smallEtaleBaseChange`: `f.smallEtaleBaseChange` is fully
  faithful when `f` is a universal homeomorphism.
* `AlgebraicGeometry.Scheme.isHomeomorph_specAlgebraMap_of_field`: for any field extension `L / K`,
  `Spec.algebraMap K L` is a homeomorphism.
* `AlgebraicGeometry.Scheme.full_smallEtaleBaseChange_specAlgebraMap_iff`,
  `AlgebraicGeometry.Scheme.not_full_smallEtaleBaseChange_specAlgebraMap`, and
  `AlgebraicGeometry.Scheme.not_full_smallEtaleBaseChange_galoisField_two`: for a separable field
  extension `L / K`, `(Spec.algebraMap K L).smallEtaleBaseChange` is full if and only if
  `algebraMap K L` is surjective; in particular it is not full whenever `1 < Module.finrank K L`,
  such as `Spec (GaloisField p 2) ⟶ Spec (ZMod p)`.
* `AlgebraicGeometry.Scheme.natCard_end_etaleMk_specAlgebraMap` and
  `AlgebraicGeometry.Scheme.natCard_end_smallEtaleBaseChange_specAlgebraMap`: for a finite Galois
  extension `L / K` of degree `n`, `Etale.mk (Spec.algebraMap K L)` has `n` endomorphisms before
  base change and `n ^ n` after base change along `Spec.algebraMap K L`.

## References

* The Stacks Project, [Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ), topological
  invariance of the small étale site.
-/

public section

open CategoryTheory Limits MorphismProperty
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is faithful on schemes étale over
`Y`. -/
instance faithful_smallEtaleBaseChange : f.smallEtaleBaseChange.Faithful :=
  have : (Etale.forget Y ⋙ CategoryTheory.Over.pullback f).Faithful := ⟨fun {_ B} _ _ h ↦
    have : Etale ((Etale.forget Y).obj B).hom := B.prop
    (Etale.forget Y).map_injective ((IsUniversalHomeomorphism.overPullback_map_bijective f).1 h)⟩
  .of_comp_iso f.smallEtaleBaseChangeCompForgetIso

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is full on schemes étale over `Y`. -/
instance full_smallEtaleBaseChange : f.smallEtaleBaseChange.Full :=
  have : (Etale.forget Y ⋙ CategoryTheory.Over.pullback f).Full := ⟨fun {_ B} c ↦
    have : Etale ((Etale.forget Y).obj B).hom := B.prop
    have ⟨a, ha⟩ := (IsUniversalHomeomorphism.overPullback_map_bijective f).2 c
    ⟨(Etale.forget Y).preimage a, by simpa using ha⟩⟩
  .of_comp_faithful_iso f.smallEtaleBaseChangeCompForgetIso

end AlgebraicGeometry.Scheme.Hom

/-! ### Failure of fullness without universal injectivity -/

namespace AlgebraicGeometry.Scheme

open TauCeti.Algebra TauCeti.AlgebraicGeometry

/-- For a finite separable field extension `L / K`, `Spec.algebraMap K L` is étale. -/
instance etale_specAlgebraMap_of_isSeparable (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] : Etale (Spec.algebraMap K L) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isSeparable K L))

/-- Between spectra of fields, `Spec.algebraMap K L` is a homeomorphism of one-point topological
spaces, even when `L / K` is nontrivial and therefore not universally injective. -/
theorem isHomeomorph_specAlgebraMap_of_field (K L : Type u) [Field K] [Field L] [Algebra K L] :
    IsHomeomorph (Spec.algebraMap K L) :=
  ({ toFun := Spec.algebraMap K L
     invFun := fun _ ↦ default
     left_inv := fun _ ↦ Subsingleton.elim _ _
     right_inv := fun _ ↦ Subsingleton.elim _ _
     continuous_toFun := (Spec.algebraMap K L).continuous
     continuous_invFun := continuous_const } :
    (Spec (.of L) : Type u) ≃ₜ (Spec (.of K) : Type u)).isHomeomorph

/-- Morphisms in `(Spec (.of R)).Etale` between affine étale `R`-schemes `Spec A` and `Spec B`
correspond bijectively to `R`-algebra homomorphisms `B →ₐ[R] A`. -/
private noncomputable def etaleSpecAlgebraMapHomEquiv (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Etale (Spec.algebraMap R A)]
    [Etale (Spec.algebraMap R B)] :
    (Etale.mk (Spec.algebraMap R A) ⟶ Etale.mk (Spec.algebraMap R B)) ≃ (B →ₐ[R] A) :=
  (Etale.forgetFullyFaithful (Spec (.of R))).homEquiv.trans <|
    ({ toFun := fun φ ↦ ⟨φ.left, CategoryTheory.Over.w φ⟩
       invFun := fun φ ↦ CategoryTheory.Over.homMk φ.1 φ.2
       left_inv := fun _ ↦ by ext1; rfl
       right_inv := fun _ ↦ rfl } :
      (CategoryTheory.Over.mk (Spec.algebraMap R A) ⟶
        CategoryTheory.Over.mk (Spec.algebraMap R B)) ≃
      { f : Spec (.of A) ⟶ Spec (.of B) //
        f ≫ Spec.algebraMap R B = Spec.algebraMap R A }).trans Spec.homEquivAlgHom

section SeparableExtension

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- For a separable field extension `L / K`, base change along `Spec.algebraMap K L` is full on
small étale sites if and only if `algebraMap K L` is surjective. -/
theorem full_smallEtaleBaseChange_specAlgebraMap_iff :
    (Spec.algebraMap K L).smallEtaleBaseChange.Full ↔ Function.Surjective (algebraMap K L) := by
  refine ⟨fun hFull y ↦ ?_, fun hsurj ↦ ?_⟩
  · -- Adjoin `y` to obtain a finite separable subextension `E = K⟮y⟯`; fullness lifts the
    -- tautological `L`-point of `Spec E` to a `K`-section `E →ₐ[K] K`.
    let E := IntermediateField.adjoin K ({y} : Set L)
    have : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral K y)
    have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
    let f := Spec.algebraMap K L
    let U : (Spec (.of K)).Etale := Etale.mk (Spec.algebraMap K K)
    let V : (Spec (.of K)).Etale := Etale.mk (Spec.algebraMap K E)
    obtain ⟨ι, hι⟩ := Spec.homEquivAlgHom.symm E.val
    let s : f.smallEtaleBaseChange.obj U ⟶ f.smallEtaleBaseChange.obj V :=
      MorphismProperty.Over.homMk
        (pullback.lift (pullback.snd U.hom f ≫ ι) (pullback.snd U.hom f)
          ((Category.assoc _ _ _).trans (congrArg (pullback.snd U.hom f ≫ ·) hι)))
        (pullback.lift_snd _ _ _)
    obtain ⟨g, -⟩ := hFull.map_surjective s
    let φ : E →ₐ[K] K := etaleSpecAlgebraMapHomEquiv K K E g
    obtain ⟨z, hz⟩ :=
      ((Algebra.ofId K E).comp φ).bijective.2 ⟨y, IntermediateField.mem_adjoin_simple_self K y⟩
    exact ⟨φ z, by simpa using congrArg Subtype.val hz⟩
  · let e :=
      (RingEquiv.ofBijective (algebraMap K L) ⟨(algebraMap K L).injective, hsurj⟩).toCommRingCatIso
    have : IsIso (Spec.algebraMap K L) := inferInstanceAs (IsIso (Spec.map e.hom))
    infer_instance

/-- For a nontrivial separable field extension `L / K` (`1 < Module.finrank K L`), base change
along the étale homeomorphism `Spec.algebraMap K L` is not full on small étale sites. -/
theorem not_full_smallEtaleBaseChange_specAlgebraMap (h : 1 < Module.finrank K L) :
    ¬ (Spec.algebraMap K L).smallEtaleBaseChange.Full := by
  rw [full_smallEtaleBaseChange_specAlgebraMap_iff]
  intro hsurj
  have heq := LinearEquiv.finrank_eq
    (LinearEquiv.ofBijective (Algebra.linearMap K L) ⟨(algebraMap K L).injective, hsurj⟩)
  rw [Module.finrank_self] at heq
  omega

/-- For a finite separable field extension `L / K`, the endomorphisms of
`Etale.mk (Spec.algebraMap K L)` over `Spec K` are in bijection with `Gal(L/K)`. -/
noncomputable def endEtaleMkSpecAlgebraMapEquiv [FiniteDimensional K L] :
    (Etale.mk (Spec.algebraMap K L) ⟶ Etale.mk (Spec.algebraMap K L)) ≃ Gal(L/K) :=
  (etaleSpecAlgebraMapHomEquiv K L L).trans
    { toFun := fun φ ↦ AlgEquiv.ofBijective φ φ.bijective
      invFun := AlgEquiv.toAlgHom
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ by ext; rfl }

end SeparableExtension

section GaloisExtension

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- For a finite Galois extension `L / K`, `Etale.mk (Spec.algebraMap K L)` has `Module.finrank K L`
endomorphisms in `(Spec (.of K)).Etale`. -/
theorem natCard_end_etaleMk_specAlgebraMap :
    Nat.card (Etale.mk (Spec.algebraMap K L) ⟶ Etale.mk (Spec.algebraMap K L)) =
      Module.finrank K L := by
  rw [Nat.card_congr (endEtaleMkSpecAlgebraMapEquiv K L), IsGalois.card_aut_eq_finrank]

/-- For a finite Galois extension `L / K`, the endomorphisms of the base change of
`Etale.mk (Spec.algebraMap K L)` along `Spec.algebraMap K L` are in bijection with self-maps
`Gal(L/K) → Gal(L/K)` of the Galois group. -/
noncomputable def endSmallEtaleBaseChangeSpecAlgebraMapEquiv :
    (let f := Spec.algebraMap K L
     f.smallEtaleBaseChange.obj (Etale.mk f) ⟶ f.smallEtaleBaseChange.obj (Etale.mk f)) ≃
      (Gal(L/K) → Gal(L/K)) := by
  -- Identify `(Spec L ×_{Spec K} Spec L) ⟶ Spec L` with `Spec (Gal(L/K) → L) ⟶ Spec L` via the
  -- Galois torsor isomorphism `L ⊗[K] L ≃ₐ[L] (Gal(L/K) → L)`.
  have hGal := IsFiniteEtaleTorsor.galoisMap Gal(L/K) K L
  have : Algebra.Etale K L := Algebra.Etale.of_isSeparable K L
  have : Etale (Spec.algebraMap L (L ⊗[K] L)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let eOver :
      ((Etale.forget (Spec (.of L))).obj
        ((Spec.algebraMap K L).smallEtaleBaseChange.obj (Etale.mk (Spec.algebraMap K L)))) ≅
      (Etale.forget (Spec (.of L))).obj (Etale.mk (Spec.algebraMap L (L ⊗[K] L))) :=
    pullbackSpecIsoOfAlgEquiv K L L (L ⊗[K] L) AlgEquiv.refl
  let eEtale :
      (Spec.algebraMap K L).smallEtaleBaseChange.obj (Etale.mk (Spec.algebraMap K L)) ≅
      Etale.mk (Spec.algebraMap L (L ⊗[K] L)) :=
    (Etale.forgetFullyFaithful (Spec (.of L))).preimageIso eOver
  -- `L`-algebra endomorphisms of `L ⊗[K] L` correspond to `K`-algebra maps `L →ₐ[K] (L ⊗[K] L)`
  -- and hence, through `hGal`, to families of `K`-embeddings `Gal(L/K) → (L →ₐ[K] L) ≃ Gal(L/K)`.
  let ePi : (L →ₐ[K] (Gal(L/K) → L)) ≃ (Gal(L/K) → (L →ₐ[K] L)) :=
    { toFun := fun φ σ ↦ (Pi.evalAlgHom K (fun _ : Gal(L/K) ↦ L) σ).comp φ
      invFun := fun ψ ↦ AlgHom.pi ψ
      left_inv := fun _ ↦ by ext; rfl
      right_inv := fun _ ↦ by ext; rfl }
  exact (Iso.homCongr eEtale eEtale).trans <|
    (etaleSpecAlgebraMapHomEquiv L (L ⊗[K] L) (L ⊗[K] L)).trans <|
      (Algebra.TensorProduct.liftEquivRight K L L (L ⊗[K] L)).symm.trans <|
        ((AlgEquiv.refl : L ≃ₐ[K] L).arrowCongr (hGal.restrictScalars K)).trans <|
          ePi.trans (Equiv.arrowCongr (Equiv.refl _) (Normal.algHomEquivAut K L L))

/-- After base change along `Spec.algebraMap K L`, `Etale.mk (Spec.algebraMap K L)` has
`(Module.finrank K L) ^ (Module.finrank K L)` endomorphisms over `Spec L`. -/
theorem natCard_end_smallEtaleBaseChange_specAlgebraMap :
    Nat.card
      (let f := Spec.algebraMap K L
       f.smallEtaleBaseChange.obj (Etale.mk f) ⟶ f.smallEtaleBaseChange.obj (Etale.mk f)) =
      Module.finrank K L ^ Module.finrank K L := by
  have : Finite Gal(L/K) := inferInstance
  rw [Nat.card_congr (endSmallEtaleBaseChangeSpecAlgebraMapEquiv K L), Nat.card_fun,
    IsGalois.card_aut_eq_finrank]

end GaloisExtension

section GaloisField

variable (p : ℕ) [Fact p.Prime]

/-- `Etale.mk (Spec.algebraMap (ZMod p) (GaloisField p 2))` has `2` endomorphisms over
`Spec (ZMod p)`. -/
theorem natCard_end_etaleMk_galoisField_two :
    Nat.card (Etale.mk (Spec.algebraMap (ZMod p) (GaloisField p 2)) ⟶
      Etale.mk (Spec.algebraMap (ZMod p) (GaloisField p 2))) = 2 := by
  rw [natCard_end_etaleMk_specAlgebraMap, GaloisField.finrank p (by decide)]

/-- After base change to `Spec (GaloisField p 2)`,
`Etale.mk (Spec.algebraMap (ZMod p) (GaloisField p 2))` has `4` endomorphisms. -/
theorem natCard_end_smallEtaleBaseChange_galoisField_two :
    Nat.card
      (let f := Spec.algebraMap (ZMod p) (GaloisField p 2)
       f.smallEtaleBaseChange.obj (Etale.mk f) ⟶ f.smallEtaleBaseChange.obj (Etale.mk f)) = 4 := by
  rw [natCard_end_smallEtaleBaseChange_specAlgebraMap, GaloisField.finrank p (by decide)]
  rfl

/-- Although `Spec.algebraMap (ZMod p) (GaloisField p 2)` is a homeomorphism of one-point schemes,
its base-change functor on small étale sites is not full. -/
theorem not_full_smallEtaleBaseChange_galoisField_two :
    ¬ (Spec.algebraMap (ZMod p) (GaloisField p 2)).smallEtaleBaseChange.Full :=
  not_full_smallEtaleBaseChange_specAlgebraMap (ZMod p) (GaloisField p 2)
    (by rw [GaloisField.finrank p (by decide)]; decide)

end GaloisField

end AlgebraicGeometry.Scheme
