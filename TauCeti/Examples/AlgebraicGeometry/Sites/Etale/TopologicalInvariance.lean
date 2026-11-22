/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import TauCeti.AlgebraicGeometry.Sites.Etale.TopologicalInvariance
public import TauCeti.RingTheory.Etale.Field
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.RingTheory.Etale.Torsor.GaloisMap

/-!
# Counterexamples to topological invariance for non-universal homeomorphisms

In `TauCeti/AlgebraicGeometry/Sites/Etale/TopologicalInvariance.lean`, base change along a
universal homeomorphism `f : X ⟶ Y` is shown to be fully faithful on small étale sites. This file
shows that the universality hypothesis cannot be weakened to `f` being a mere homeomorphism:
between spectra of fields, `Spec.algebraMap K L` is always a homeomorphism of one-point schemes
(see `TauCeti.AlgebraicGeometry.isHomeomorph_Spec_algebraMap` in
`TauCeti/Examples/AlgebraicGeometry/Morphisms/UniversalHomeomorphism.lean`), yet for any separable
field extension `L / K`, `(Spec.algebraMap K L).smallEtaleBaseChange` is full if and only if
`algebraMap K L` is surjective (`full_smallEtaleBaseChange_specAlgebraMap_iff_of_isSeparable`).

In particular, `(Spec.algebraMap K L).smallEtaleBaseChange` fails to be full whenever
`Module.finrank K L ≠ 1`
(`not_full_smallEtaleBaseChange_specAlgebraMap_of_isSeparable_of_finrank_ne_one`).
Quantitatively, for a finite Galois extension `L / K` of degree `n`,
`Etale.mk (Spec.algebraMap K L)` has `n` endomorphisms over `Spec K` while its base change
`Spec (L ⊗[K] L)` over `Spec L` splits into `n` copies of `Spec L` and has `n ^ n` endomorphisms
over `Spec L`. For instance, for `Spec (𝔽_{p²}) ⟶ Spec 𝔽_p`, the cover has `2` endomorphisms over
`𝔽_p` and `4` after base change to `𝔽_{p²}`.

## Main results

* `TauCeti.AlgebraicGeometry.full_smallEtaleBaseChange_specAlgebraMap_iff_of_isSeparable` and
  `not_full_smallEtaleBaseChange_specAlgebraMap_of_isSeparable_of_finrank_ne_one`: for a separable
  field extension `L / K`, `(Spec.algebraMap K L).smallEtaleBaseChange` is full iff
  `algebraMap K L` is surjective; in particular it is not full whenever `Module.finrank K L ≠ 1`.
* `TauCeti.AlgebraicGeometry.endEtaleMkSpecAlgebraMapEquiv`,
  `TauCeti.AlgebraicGeometry.natCard_end_etaleMk_specAlgebraMap_eq_finrank_of_isGalois`, and
  `natCard_end_smallEtaleBaseChange_specAlgebraMap_eq_finrank_pow_of_isGalois`: for a finite Galois
  extension `L / K` of degree `n`, `Etale.mk (Spec.algebraMap K L)` has `n` endomorphisms before
  base change and `n ^ n` after base change along `Spec.algebraMap K L`.
* `TauCeti.AlgebraicGeometry.natCard_end_etaleMk_galoisField_two`,
  `TauCeti.AlgebraicGeometry.natCard_end_smallEtaleBaseChange_galoisField_two`, and
  `TauCeti.AlgebraicGeometry.not_full_smallEtaleBaseChange_galoisField_two`: concrete checks for
  `Spec (GaloisField p 2) ⟶ Spec (ZMod p)`.

## References

* The Stacks Project, [Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ), topological
  invariance of the small étale site.
-/

public section

open CategoryTheory Limits MorphismProperty _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  TauCeti.Algebra
open scoped TensorProduct

universe u

namespace TauCeti.AlgebraicGeometry

attribute [local instance] Algebra.Etale.of_isSeparable

section SeparableExtension

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- For a separable field extension `L / K`, base change along `Spec.algebraMap K L` is full on
small étale sites if and only if `algebraMap K L` is surjective. -/
theorem full_smallEtaleBaseChange_specAlgebraMap_iff_of_isSeparable :
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
  · have : IsIso (CommRingCat.ofHom (algebraMap K L)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(algebraMap K L).injective, hsurj⟩
    have : IsIso (Spec.algebraMap K L) := by
      rw [Spec.algebraMap]
      infer_instance
    infer_instance

/-- For a separable field extension `L / K` with `Module.finrank K L ≠ 1` (covering both finite
nontrivial and infinite-dimensional separable extensions), base change along `Spec.algebraMap K L`
is not full on small étale sites. -/
theorem not_full_smallEtaleBaseChange_specAlgebraMap_of_isSeparable_of_finrank_ne_one
    (h : Module.finrank K L ≠ 1) :
    ¬ (Spec.algebraMap K L).smallEtaleBaseChange.Full := by
  rw [full_smallEtaleBaseChange_specAlgebraMap_iff_of_isSeparable]
  intro hsurj
  exact h (Module.finrank_of_bijective_algebraMap (R := K) (S := L)
    ⟨(algebraMap K L).injective, hsurj⟩)

/-- For a finite separable field extension `L / K`, the endomorphisms of
`Etale.mk (Spec.algebraMap K L)` over `Spec K` are in bijection with `Gal(L/K)`. -/
noncomputable def endEtaleMkSpecAlgebraMapEquiv [FiniteDimensional K L] :
    (Etale.mk (Spec.algebraMap K L) ⟶ Etale.mk (Spec.algebraMap K L)) ≃ Gal(L/K) :=
  (etaleSpecAlgebraMapHomEquiv K L L).trans (algEquivEquivAlgHom K L).toEquiv.symm

/-- The inverse of `endEtaleMkSpecAlgebraMapEquiv` applies `Spec.map` on underlying schemes. -/
@[simp]
theorem endEtaleMkSpecAlgebraMapEquiv_symm_apply_left [FiniteDimensional K L] (σ : Gal(L/K)) :
    ((endEtaleMkSpecAlgebraMapEquiv K L).symm σ).left =
      Spec.map (CommRingCat.ofHom (σ : L →+* L)) :=
  etaleSpecAlgebraMapHomEquiv_symm_apply_left K L L σ.toAlgHom

/-- Applying `Spec.map` to the automorphism associated to an endomorphism of
`Etale.mk (Spec.algebraMap K L)` recovers its underlying morphism of schemes. -/
@[simp]
theorem spec_map_endEtaleMkSpecAlgebraMapEquiv [FiniteDimensional K L]
    (f : Etale.mk (Spec.algebraMap K L) ⟶ Etale.mk (Spec.algebraMap K L)) :
    Spec.map (CommRingCat.ofHom (endEtaleMkSpecAlgebraMapEquiv K L f : L →+* L)) =
      f.left := by
  rw [← endEtaleMkSpecAlgebraMapEquiv_symm_apply_left, Equiv.symm_apply_apply]

end SeparableExtension

section GaloisExtension

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- For a finite Galois extension `L / K`, `Etale.mk (Spec.algebraMap K L)` has `Module.finrank K L`
endomorphisms in `(Spec (.of K)).Etale`. -/
theorem natCard_end_etaleMk_specAlgebraMap_eq_finrank_of_isGalois :
    Nat.card (Etale.mk (Spec.algebraMap K L) ⟶ Etale.mk (Spec.algebraMap K L)) =
      Module.finrank K L := by
  rw [Nat.card_congr (endEtaleMkSpecAlgebraMapEquiv K L), IsGalois.card_aut_eq_finrank]

/-- For a finite Galois extension `L / K`, the endomorphisms of the base change of
`Etale.mk (Spec.algebraMap K L)` along `Spec.algebraMap K L` are in bijection with self-maps
`Gal(L/K) → Gal(L/K)` of the Galois group. -/
private noncomputable def endSmallEtaleBaseChangeSpecAlgebraMapEquiv :
    ((Spec.algebraMap K L).smallEtaleBaseChange.obj (Etale.mk (Spec.algebraMap K L)) ⟶
      (Spec.algebraMap K L).smallEtaleBaseChange.obj (Etale.mk (Spec.algebraMap K L))) ≃
      (Gal(L/K) → Gal(L/K)) := by
  -- Identify `(Spec L ×_{Spec K} Spec L) ⟶ Spec L` with `Spec (Gal(L/K) → L) ⟶ Spec L` via the
  -- Galois torsor isomorphism `L ⊗[K] L ≃ₐ[L] (Gal(L/K) → L)`.
  have hGal := IsFiniteEtaleTorsor.galoisMap Gal(L/K) K L
  let eOver := pullbackSpecIsoOfAlgEquiv K L L (L ⊗[K] L) AlgEquiv.refl
  let eEtale :
      (Spec.algebraMap K L).smallEtaleBaseChange.obj (Etale.mk (Spec.algebraMap K L)) ≅
      Etale.mk (Spec.algebraMap L (L ⊗[K] L)) :=
    MorphismProperty.Over.isoMk ((CategoryTheory.Over.forget _).mapIso eOver)
      (CategoryTheory.Over.w eOver.hom)
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
theorem natCard_end_smallEtaleBaseChange_specAlgebraMap_eq_finrank_pow_of_isGalois :
    Nat.card
      ((Spec.algebraMap K L).smallEtaleBaseChange.obj (Etale.mk (Spec.algebraMap K L)) ⟶
        (Spec.algebraMap K L).smallEtaleBaseChange.obj (Etale.mk (Spec.algebraMap K L))) =
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
  rw [natCard_end_etaleMk_specAlgebraMap_eq_finrank_of_isGalois, GaloisField.finrank p (by decide)]

/-- After base change to `Spec (GaloisField p 2)`,
`Etale.mk (Spec.algebraMap (ZMod p) (GaloisField p 2))` has `4` endomorphisms. -/
theorem natCard_end_smallEtaleBaseChange_galoisField_two :
    Nat.card
      ((Spec.algebraMap (ZMod p) (GaloisField p 2)).smallEtaleBaseChange.obj
          (Etale.mk (Spec.algebraMap (ZMod p) (GaloisField p 2))) ⟶
        (Spec.algebraMap (ZMod p) (GaloisField p 2)).smallEtaleBaseChange.obj
          (Etale.mk (Spec.algebraMap (ZMod p) (GaloisField p 2)))) = 4 := by
  rw [natCard_end_smallEtaleBaseChange_specAlgebraMap_eq_finrank_pow_of_isGalois,
    GaloisField.finrank p (by decide)]
  rfl

/-- Although `Spec.algebraMap (ZMod p) (GaloisField p 2)` is a homeomorphism of one-point schemes,
its base-change functor on small étale sites is not full. -/
theorem not_full_smallEtaleBaseChange_galoisField_two :
    ¬ (Spec.algebraMap (ZMod p) (GaloisField p 2)).smallEtaleBaseChange.Full :=
  not_full_smallEtaleBaseChange_specAlgebraMap_of_isSeparable_of_finrank_ne_one
    (ZMod p) (GaloisField p 2) (by rw [GaloisField.finrank p (by decide)]; decide)

end GaloisField

end TauCeti.AlgebraicGeometry
