/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.AlgebraicGeometry.RationalPoint.Affine
import TauCeti.RingTheory.TotallySplit

/-!
# Étale morphisms: open immersions, and rational points of finite schemes over a field

A morphism of schemes is an open immersion exactly when it is étale and universally injective
(`AlgebraicGeometry.isOpenImmersion_iff_etale_and_universallyInjective`): an unramified
universally injective morphism is a monomorphism, and a flat monomorphism locally of finite
presentation is an open immersion (Mathlib's `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`).
In particular an étale morphism that is universally injective and surjective, for instance an
étale universal homeomorphism, is an isomorphism
(`AlgebraicGeometry.isIso_of_etale_of_universallyInjective_of_surjective`).

Let `f : X ⟶ Spec R` be a morphism from an affine scheme to the spectrum of a commutative ring.
Then `f` is étale exactly when `Γ(X, ⊤)` is an étale `R`-algebra. Its points with values in
`Spec R` are the characters `Γ(X, ⊤) →ₐ[R] R` of its coordinate ring
(`AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom`, in
`TauCeti.AlgebraicGeometry.RationalPoint.Affine`).

Now let `f : X ⟶ Spec K` be a finite morphism to the spectrum of a field. A finite-dimensional
`K`-algebra has at most as many characters as its dimension, which is the rank of `f`
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`).
When `X` has at least that many points over `Spec K`, its coordinate ring is a finite product of
copies of `K` (`Algebra.IsFiniteSplit.of_finrank_le_card_algHom`), so `f` is étale. Conversely,
over a separably closed field a finite étale `K`-algebra is a finite product of copies of `K`, so a
finite étale scheme over `Spec K` has exactly as many points over `Spec K` as its rank.

Points over `Spec K` are written as morphisms `𝟙_ (Over (Spec K)) ⟶ Over.mk f` of the cartesian
monoidal category `Over (Spec K)`, as for the points of group schemes over `Spec K`.

Finally, let `A` be a local ring with residue field `κ` and `B` an `A`-algebra whose closed fibre
`κ ⊗[A] B` is a finite étale `κ`-algebra. A field-valued point `Spec L ⟶ Spec A` of the closed
point factors through `κ`, so the base change `L ⊗[A] B` is the base change of `κ ⊗[A] B` along
`κ → L`; hence the base change of `Spec B ⟶ Spec A` to `Spec L` is finite étale of rank
`dim_κ (κ ⊗[A] B)`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_iff_etale_and_universallyInjective`: the open immersions are
  the étale universally injective morphisms.
* `AlgebraicGeometry.isIso_of_etale_of_universallyInjective_of_surjective`: an étale universally
  injective surjective morphism is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.etale_iff_algebraEtale`: for affine `X`, `f : X ⟶ Spec R` is
  étale exactly when `Γ(X, ⊤)` is an étale `R`-algebra.
* `AlgebraicGeometry.Scheme.Hom.etale_of_finrank_le_natCard`: a finite morphism `f : X ⟶ Spec K`
  with at least `f.finrank s` points of `X` over `Spec K` is étale.
* `AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_etale`: over a separably closed field `K`,
  a finite étale morphism `f : X ⟶ Spec K` has exactly `f.finrank s` points of `X` over `Spec K`.
* `TauCeti.AlgebraicGeometry.etale_isFinite_finrank_of_isPullback_SpecMap`: for a local ring `A`
  and an `A`-algebra `B` whose closed fibre is finite étale, the base change of
  `Spec B ⟶ Spec A` along a field-valued point of the closed point is finite étale of the same
  rank.
-/

public section

open CategoryTheory MonoidalCategory

universe u

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

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

-- Instance search does not unfold the étale predicate to recover the parent instance of
-- `IsMultiplicative`, so register composition stability explicitly here for its consumers.
/-- Étale morphisms are stable under composition. -/
instance etale_isStableUnderComposition :
    CategoryTheory.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale :=
  CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Being étale is invariant under isomorphisms of source and target. -/
instance etale_respectsIso :
    CategoryTheory.MorphismProperty.RespectsIso @AlgebraicGeometry.Etale :=
  CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition
    fun _ _ _ (_ : CategoryTheory.IsIso _) ↦ inferInstance

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
