/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Comma.Over.StrictInitial
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.AlgebraicGeometry.RationalPoint.Affine
import TauCeti.RingTheory.TotallySplit

/-!
# Étale morphisms: open immersions, `X.Etale` basics, and rational points over a field

A morphism of schemes is an open immersion exactly when it is étale and universally injective
(`AlgebraicGeometry.isOpenImmersion_iff_etale_and_universallyInjective`): an unramified
universally injective morphism is a monomorphism, and a flat monomorphism locally of finite
presentation is an open immersion (Mathlib's `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`).
In particular an étale morphism that is universally injective and surjective, for instance an
étale universal homeomorphism, is an isomorphism
(`AlgebraicGeometry.isIso_of_etale_of_universallyInjective_of_surjective`).

Let `f : X ⟶ Spec R` be a morphism from an affine scheme to the spectrum of a commutative ring.
Then `f` is étale exactly when `Γ(X, ⊤)` is an étale `R`-algebra. In particular, for any étale
`R`-algebra `A`, `Spec.algebraMap R A` is étale (`TauCeti.AlgebraicGeometry.etale_specAlgebraMap`),
and morphisms in `(Spec (.of R)).Etale` between `Spec A` and `Spec B` correspond bijectively to
`R`-algebra homomorphisms `B →ₐ[R] A` (`TauCeti.AlgebraicGeometry.etaleSpecAlgebraMapHomEquiv`).
The points of `X` with values in `Spec R` are the characters `Γ(X, ⊤) →ₐ[R] R` of its coordinate
ring (`AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom`, in
`TauCeti.AlgebraicGeometry.RationalPoint.Affine`).

For any scheme `X`, this file also collects basic categorical API for `X.Etale` (`Etale.id_left`,
`Etale.comp_left`, `Etale.hom_ext`), including its collapse to a point when `X` is empty
(`AlgebraicGeometry.Scheme.etaleEquivOfIsEmpty`).

Now let `f : X ⟶ Spec K` be a finite morphism to the spectrum of a field. A finite-dimensional
`K`-algebra has at most as many characters as its dimension, which is the rank of `f`
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`).
When `X` has at least that many points over `Spec K`, its coordinate ring is a finite product of
copies of `K` (`Algebra.IsFiniteSplit.of_finrank_le_card_algHom`), so `f` is étale. Conversely,
over a separably closed field a finite étale `K`-algebra is a finite product of copies of `K`, so a
finite étale scheme over `Spec K` has exactly as many points over `Spec K` as its rank, and as many
points of its underlying set.

Points over `Spec K` are written as morphisms `𝟙_ (Over (Spec K)) ⟶ Over.mk f` of the cartesian
monoidal category `Over (Spec K)`, as for the points of group schemes over `Spec K`.

Finally, let `A` be a local ring with residue field `κ` and `B` an `A`-algebra whose closed fibre
`κ ⊗[A] B` is a finite étale `κ`-algebra. A field-valued point `Spec L ⟶ Spec A` of the closed
point factors through `κ`, so the base change `L ⊗[A] B` is the base change of `κ ⊗[A] B` along
`κ → L`; hence the base change of `Spec B ⟶ Spec A` to `Spec L` is finite étale of rank
`dim_κ (κ ⊗[A] B)`.

Étaleness of a morphism is local on the target
(`TauCeti.AlgebraicGeometry.isZariskiLocalAtTarget_etale`); this is recorded as an instance because
instance search does not derive it from Mathlib's ring-map description of `Etale`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_iff_etale_and_universallyInjective`: the open immersions are
  the étale universally injective morphisms.
* `AlgebraicGeometry.isIso_of_etale_of_universallyInjective_of_surjective`: an étale universally
  injective surjective morphism is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.etale_iff_algebraEtale`: for affine `X`, `f : X ⟶ Spec R` is
  étale exactly when `Γ(X, ⊤)` is an étale `R`-algebra.
* `TauCeti.AlgebraicGeometry.etale_specAlgebraMap`: for any étale `R`-algebra `A`,
  `Spec.algebraMap R A` is étale.
* `TauCeti.AlgebraicGeometry.etaleSpecAlgebraMapHomEquiv`: morphisms in `(Spec (.of R)).Etale`
  between affine étale `R`-schemes `Spec A` and `Spec B` correspond to `B →ₐ[R] A`.
* `AlgebraicGeometry.Scheme.etaleEquivOfIsEmpty`: equivalence `X.Etale ≌ Discrete PUnit` when `X`
  is empty.
* `AlgebraicGeometry.Scheme.Hom.etale_of_finrank_le_natCard`: a finite morphism `f : X ⟶ Spec K`
  with at least `f.finrank s` points of `X` over `Spec K` is étale.
* `AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_etale`: over a separably closed field `K`,
  a finite étale morphism `f : X ⟶ Spec K` has exactly `f.finrank s` points of `X` over `Spec K`.
* `AlgebraicGeometry.Scheme.Hom.natCard_source_eq_finrank_of_etale` and
  `AlgebraicGeometry.Scheme.Hom.natCard_preimage_singleton_eq_finrank`: the underlying set of such
  an `X` has `f.finrank s` elements, and a finite étale morphism has `f.finrank y` points over
  each point `y` with separably closed residue field.
* `TauCeti.AlgebraicGeometry.etale_isFinite_finrank_of_isPullback_SpecMap`: for a local ring `A`
  and an `A`-algebra `B` whose closed fibre is finite étale, the base change of
  `Spec B ⟶ Spec A` along a field-valued point of the closed point is finite étale of the same
  rank.
-/

public section

open CategoryTheory MonoidalCategory

universe w u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- **The open immersions are the étale universally injective morphisms.** Stacks, Tag 025G. -/
theorem isOpenImmersion_iff_etale_and_universallyInjective {Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ Etale f ∧ UniversallyInjective f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, hf⟩ ↦ ?_⟩
  have := (FormallyUnramified.mono_iff_universallyInjective f).2 hf
  exact .of_flat_of_mono f

/-- An étale universally injective morphism is an open immersion. -/
theorem IsOpenImmersion.of_etale_of_universallyInjective {Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    [UniversallyInjective f] : IsOpenImmersion f :=
  (isOpenImmersion_iff_etale_and_universallyInjective f).2 ⟨‹_›, ‹_›⟩

/-- An étale universally injective surjective morphism is an isomorphism. -/
theorem isIso_of_etale_of_universallyInjective_of_surjective {Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] [UniversallyInjective f] [Surjective f] : IsIso f :=
  (isIso_iff_isOpenImmersion_and_surjective f).2
    ⟨.of_etale_of_universallyInjective f, ‹_›⟩

/-- A morphism `f : X ⟶ Spec R` from an affine scheme is étale exactly when its coordinate ring
`Γ(X, ⊤)` is an étale `R`-algebra, for the `R`-algebra structure given by the map of global
sections of `f`. -/
theorem Scheme.Hom.etale_iff_algebraEtale (f : X ⟶ Spec (.of R)) [IsAffine X] [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) :
    Etale f ↔ Algebra.Etale R Γ(X, ⊤) := by
  -- the map of global sections of `f` is `algebraMap R Γ(X, ⊤)` up to `Γ(Spec R, ⊤) ≅ R`
  have hf' : f.appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) := by
    simp [hf]
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), hf', CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso, CommRingCat.hom_ofHom, RingHom.etale_algebraMap]

variable {K : Type u} [Field K]

/-- **A finite scheme over a field with as many rational points as its degree is étale.** Let
`f : X ⟶ Spec K` be finite. If `X` has at least `f.finrank s` points over `Spec K`, then `f` is
étale: the coordinate ring of `X` is a finite product of copies of `K`. -/
theorem Scheme.Hom.etale_of_finrank_le_natCard (f : X ⟶ Spec (.of K)) [IsFinite f]
    (s : Spec (.of K)) (h : f.finrank s ≤ Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f)) :
    Etale f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have : Algebra.IsFiniteSplit K Γ(X, ⊤) := .of_finrank_le_card_algHom <| by
    rw [← f.finrank_eq_finrank_of_field hf s, ← Nat.card_congr (f.pointsEquivAlgHom hf)]
    exact h
  exact (f.etale_iff_algebraEtale hf).2 inferInstance

/-- **A finite étale scheme over a separably closed field has as many rational points as its
degree.** Let `K` be separably closed and `f : X ⟶ Spec K` finite étale. Then `X` has exactly
`f.finrank s` points over `Spec K`: its coordinate ring is a finite product of copies of `K`. -/
theorem Scheme.Hom.natCard_eq_finrank_of_etale [IsSepClosed K] (f : X ⟶ Spec (.of K))
    [IsFinite f] [Etale f] (s : Spec (.of K)) :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) = f.finrank s := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have : Algebra.Etale K Γ(X, ⊤) := (f.etale_iff_algebraEtale hf).1 ‹_›
  -- so `Γ(X, ⊤) ≃ₐ[K] Fin m → K`, which has the `m` characters given by the coordinates
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K Γ(X, ⊤)
  rw [Nat.card_congr (f.pointsEquivAlgHom hf), f.finrank_eq_finrank_of_field hf s]
  refine le_antisymm (card_algHom_le_finrank K Γ(X, ⊤) K) ?_
  have := Finite.algHom K Γ(X, ⊤) K
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  refine (Nat.card_fin m).symm.le.trans
    (Nat.card_le_card_of_injective (fun i ↦ (Pi.evalAlgHom K (fun _ ↦ K) i).comp e.toAlgHom) ?_)
  intro i j hij
  have := congr($hij (e.symm (Pi.single i 1)))
  by_contra hne
  simp [hne] at this

/-- **A finite étale scheme over a separably closed field has as many points as its degree.** Let
`K` be separably closed and `f : X ⟶ Spec K` finite étale. Then the underlying set of `X` has
exactly `f.finrank s` elements: its coordinate ring is the product of copies of `K` indexed by
its prime ideals. -/
theorem Scheme.Hom.natCard_source_eq_finrank_of_etale [IsSepClosed K]
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] (s : Spec (.of K)) :
    Nat.card X = f.finrank s := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have : Algebra.Etale K Γ(X, ⊤) := (f.etale_iff_algebraEtale hf).1 ‹_›
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower K inferInstance
  have := Fintype.ofFinite (PrimeSpectrum Γ(X, ⊤))
  rw [f.finrank_eq_finrank_of_field hf s,
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K Γ(X, ⊤)).toLinearEquiv.finrank_eq,
    Module.finrank_pi, Nat.card_congr X.isoSpec.hom.homeomorph.toEquiv]
  exact Nat.card_eq_fintype_card (α := PrimeSpectrum Γ(X, ⊤))

/-- **The fibres of a finite étale morphism over separably closed points.** If `f` is finite étale
and the residue field of `y` is separably closed, then exactly `f.finrank y` points of `X` lie
over `y`. -/
theorem Scheme.Hom.natCard_preimage_singleton_eq_finrank {Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Etale f] (y : Y) [IsSepClosed (Y.residueField y)] :
    Nat.card (f ⁻¹' {y}) = f.finrank y := by
  let g : f.fiber y ⟶ Spec (.of (Y.residueField y)) := f.fiberToSpecResidueField y
  obtain ⟨s⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
  rw [← Nat.card_congr (f.fiberHomeo y).toEquiv, g.natCard_source_eq_finrank_of_etale s]
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) s).trans
      (by rw [Scheme.fromSpecResidueField_apply])

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

-- Instance search does not unfold the étale predicate to recover the parent instance of
-- `IsMultiplicative`, so register composition stability explicitly here for its consumers.
/-- Étale morphisms contain identities. -/
instance etale_containsIdentities :
    CategoryTheory.MorphismProperty.ContainsIdentities @AlgebraicGeometry.Etale :=
  CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities

/-- Étale morphisms are stable under composition. -/
instance etale_isStableUnderComposition :
    CategoryTheory.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale :=
  CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Being étale is invariant under isomorphisms of source and target. -/
instance etale_respectsIso :
    CategoryTheory.MorphismProperty.RespectsIso @AlgebraicGeometry.Etale :=
  CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition
    fun _ _ _ (_ : CategoryTheory.IsIso _) ↦ inferInstance

-- For the same reason, instance search does not derive these from the general instances for
-- categories with pullbacks and for properties stable under base change, so register them here
-- for base change of étale schemes along `f`.
/-- Étale schemes over `Y` can be pulled back along any `f : X ⟶ Y`. -/
instance etale_hasPullbacksAlong {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) :
    CategoryTheory.MorphismProperty.HasPullbacksAlong @AlgebraicGeometry.Etale f :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- Étale morphisms are stable under base change along any `f : X ⟶ Y`. -/
instance etale_isStableUnderBaseChangeAlong {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong @AlgebraicGeometry.Etale f :=
  ⟨CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback⟩

/-- For any étale `R`-algebra `A`, the induced morphism `Spec.algebraMap R A : Spec A ⟶ Spec R` is
étale. -/
instance etale_specAlgebraMap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] :
    _root_.AlgebraicGeometry.Etale (_root_.AlgebraicGeometry.Spec.algebraMap R A) :=
  (_root_.AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @_root_.AlgebraicGeometry.Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

/-- Morphisms in `(Spec (.of R)).Etale` between affine étale `R`-schemes `Spec A` and `Spec B`
correspond bijectively to `R`-algebra homomorphisms `B →ₐ[R] A`. -/
noncomputable def etaleSpecAlgebraMapHomEquiv (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [_root_.AlgebraicGeometry.Etale (_root_.AlgebraicGeometry.Spec.algebraMap R A)]
    [_root_.AlgebraicGeometry.Etale (_root_.AlgebraicGeometry.Spec.algebraMap R B)] :
    (_root_.AlgebraicGeometry.Scheme.Etale.mk (_root_.AlgebraicGeometry.Spec.algebraMap R A) ⟶
      _root_.AlgebraicGeometry.Scheme.Etale.mk (_root_.AlgebraicGeometry.Spec.algebraMap R B)) ≃
      (B →ₐ[R] A) :=
  (_root_.AlgebraicGeometry.Scheme.Etale.forgetFullyFaithful
      (_root_.AlgebraicGeometry.Spec (.of R))).homEquiv.trans <|
    ({ toFun := fun φ ↦ ⟨φ.left, CategoryTheory.Over.w φ⟩
       invFun := fun φ ↦ CategoryTheory.Over.homMk φ.val φ.property
       left_inv := fun _ ↦ by ext1; rfl
       right_inv := fun _ ↦ rfl } :
      (CategoryTheory.Over.mk (_root_.AlgebraicGeometry.Spec.algebraMap R A) ⟶
        CategoryTheory.Over.mk (_root_.AlgebraicGeometry.Spec.algebraMap R B)) ≃
      { f : _root_.AlgebraicGeometry.Spec (.of A) ⟶ _root_.AlgebraicGeometry.Spec (.of B) //
        f ≫ _root_.AlgebraicGeometry.Spec.algebraMap R B =
          _root_.AlgebraicGeometry.Spec.algebraMap R A }).trans
      _root_.AlgebraicGeometry.Spec.homEquivAlgHom

/-- The inverse of `etaleSpecAlgebraMapHomEquiv` applies `Spec.map` on underlying schemes. -/
@[simp]
theorem etaleSpecAlgebraMapHomEquiv_symm_apply_left (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [_root_.AlgebraicGeometry.Etale (_root_.AlgebraicGeometry.Spec.algebraMap R A)]
    [_root_.AlgebraicGeometry.Etale (_root_.AlgebraicGeometry.Spec.algebraMap R B)]
    (φ : B →ₐ[R] A) :
    ((etaleSpecAlgebraMapHomEquiv R A B).symm φ).left =
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (φ : B →+* A)) :=
  (rfl)

/-- Applying `Spec.map` to the algebra homomorphism associated to a morphism in
`(Spec (.of R)).Etale` recovers its underlying morphism of schemes. -/
@[simp]
theorem spec_map_etaleSpecAlgebraMapHomEquiv {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [_root_.AlgebraicGeometry.Etale (_root_.AlgebraicGeometry.Spec.algebraMap R A)]
    [_root_.AlgebraicGeometry.Etale (_root_.AlgebraicGeometry.Spec.algebraMap R B)]
    (f : _root_.AlgebraicGeometry.Scheme.Etale.mk (_root_.AlgebraicGeometry.Spec.algebraMap R A) ⟶
      _root_.AlgebraicGeometry.Scheme.Etale.mk (_root_.AlgebraicGeometry.Spec.algebraMap R B)) :
    _root_.AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (etaleSpecAlgebraMapHomEquiv R A B f : B →+* A)) =
      f.left := by
  rw [← etaleSpecAlgebraMapHomEquiv_symm_apply_left, Equiv.symm_apply_apply]

/-- Étaleness of a morphism of schemes is local on the target. Instance search does not find
this from Mathlib's ring-map description of `Etale`, so it is recorded here. -/
instance isZariskiLocalAtTarget_etale :
    AlgebraicGeometry.IsZariskiLocalAtTarget @AlgebraicGeometry.Etale.{u} :=
  AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Etale)

section ClosedFibre

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry IsLocalRing
open scoped TensorProduct

variable {A L B : Type u} [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]
  [IsLocalHom (algebraMap A L)] [CommRing B] [Algebra A B]

/-- If the closed fibre `κ ⊗[A] B` of `A → B` is a finite étale `κ`-algebra, then the base change of
`Spec B ⟶ Spec A` along a field-valued point of the closed point of `Spec A` is finite étale, of
the same rank. -/
theorem etale_isFinite_finrank_of_isPullback_SpecMap
    [Algebra.Etale (ResidueField A) (ResidueField A ⊗[A] B)]
    [Module.Finite (ResidueField A) (ResidueField A ⊗[A] B)] {P : Scheme.{u}}
    {fst : P ⟶ Spec (.of B)} {snd : P ⟶ Spec (.of L)}
    (h : IsPullback fst snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A L)))) :
    Etale snd ∧ IsFinite snd ∧ ∀ y, snd.finrank y =
      Module.finrank (ResidueField A) (ResidueField A ⊗[A] B) := by
  -- The base change `L ⊗[A] B` is the base change of the closed fibre along `κ → L`.
  let := (ResidueField.lift (algebraMap A L)).toAlgebra
  have : IsScalarTower A (ResidueField A) L := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  let e : L ⊗[ResidueField A] (ResidueField A ⊗[A] B) ≃ₐ[L] L ⊗[A] B :=
    Algebra.TensorProduct.cancelBaseChange A (ResidueField A) L L B
  have : Algebra.Etale L (L ⊗[A] B) := .of_equiv e
  have : Module.Finite L (L ⊗[A] B) := .equiv e.toLinearEquiv
  have hsnd := h.isoIsPullback_hom_snd _ _
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A L B)).flip
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[A] B)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[A] B)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  refine ⟨hsnd ▸ inferInstance, hsnd ▸ inferInstance, fun y ↦ ?_⟩
  rw [← hsnd, Scheme.Hom.finrank_comp_left_of_isIso]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap L (L ⊗[A] B) y).trans ?_
  rw [Module.rankAtStalk_eq_finrank_of_free, ← e.toLinearEquiv.finrank_eq,
    Module.finrank_baseChange]
  exact Pi.natCast_apply _ _

end ClosedFibre

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Etale

/-- The underlying morphism of the identity in `X.Etale` is the identity on `V.left`. -/
@[simp]
theorem id_left {X : Scheme.{u}} (V : X.Etale) : (𝟙 V : V ⟶ V).left = 𝟙 V.left :=
  rfl

/-- Composition in `X.Etale` composes the underlying morphisms of schemes. -/
@[simp]
theorem comp_left {X : Scheme.{u}} {U V W : X.Etale} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).left = f.left ≫ g.left :=
  rfl

/-- Two morphisms in `X.Etale` are equal if their underlying scheme morphisms are equal. -/
@[ext]
theorem hom_ext {X : Scheme.{u}} {U V : X.Etale} {f g : U ⟶ V} (h : f.left = g.left) :
    f = g :=
  MorphismProperty.Over.Hom.ext h

/-- Forgetting to `Over X` preserves the underlying scheme morphism. -/
@[simp]
theorem forget_map_left {X : Scheme.{u}} {U V : X.Etale} (f : U ⟶ V) :
    ((Etale.forget X).map f).left = f.left :=
  rfl

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme

/-- Every scheme étale over an empty scheme is itself empty. -/
instance isEmpty_etale_left {X : Scheme.{u}} [IsEmpty X] (W : X.Etale) : IsEmpty W.left :=
  Function.isEmpty (β := X) W.hom

/-- From an empty étale `X`-scheme to any étale `X`-scheme, there is a unique `X`-morphism. -/
noncomputable instance uniqueEtaleHomOfIsEmpty {X : Scheme.{u}} (W₁ W₂ : X.Etale)
    [IsEmpty W₁.left] : Unique (W₁ ⟶ W₂) where
  default := MorphismProperty.Over.homMk (isInitialOfIsEmpty.to W₂.left)
    (isInitialOfIsEmpty.hom_ext _ _)
  uniq φ := by
    ext1
    exact isInitialOfIsEmpty.hom_ext _ _

/-- When `X` is an empty scheme, `X.Etale` is equivalent to the terminal category
`Discrete PUnit`. -/
@[pp_with_univ]
noncomputable def etaleEquivOfIsEmpty (X : Scheme.{u}) [IsEmpty X] :
    X.Etale ≌ Discrete PUnit.{w + 1} :=
  MorphismProperty.overEquivOfIsInitial (@Etale : MorphismProperty Scheme.{u}) ⊤ X
    isInitialOfIsEmpty

/-- The forward functor of `X.etaleEquivOfIsEmpty` is `Functor.star X.Etale`. -/
@[simp]
theorem etaleEquivOfIsEmpty_functor (X : Scheme.{u}) [IsEmpty X] :
    (X.etaleEquivOfIsEmpty : X.Etale ≌ Discrete PUnit.{w + 1}).functor = Functor.star _ :=
  (rfl)

/-- The inverse functor of `X.etaleEquivOfIsEmpty` is the constant functor at `Etale.mk (𝟙 X)`. -/
@[simp]
theorem etaleEquivOfIsEmpty_inverse (X : Scheme.{u}) [IsEmpty X] :
    (X.etaleEquivOfIsEmpty : X.Etale ≌ Discrete PUnit.{w + 1}).inverse =
      Functor.fromPUnit (Etale.mk (𝟙 X)) :=
  (rfl)

end AlgebraicGeometry.Scheme
