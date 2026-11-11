/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# Geometric irreducibility over a separably closed field, images, and dense opens

Over a separably closed field `K`, irreducibility is geometric: if `Spec A` is irreducible, then
`Spec A ⟶ Spec K` is geometrically irreducible, that is, `Spec (A ⊗[K] M)` is irreducible for every
field `M` over `K`. Consequently, for every scheme `X` over `K` and every base change `X'` of `X` to
a field extension of `K`, the projection `X' ⟶ X` is geometrically irreducible and open, so taking
preimages identifies the irreducible components of `X` with those of `X'`: every irreducible
component of a scheme over a separably closed field is geometrically irreducible. Thus, once the
ground field is separably closed, no further field extension splits the irreducible components of
a scheme; this is the input for splitting the components of a scheme of finite type over a finite
separable extension of the ground field.

The proof has three steps.

* Over an algebraically closed field the tensor product of two domains is a domain
  (`TauCeti.isDomain_tensorProduct_of_isAlgClosed`), so the spectrum of a domain is geometrically
  irreducible. If only `Spec A` is irreducible, the reduced quotient `A ⧸ nilradical A` is a domain
  and `Spec (A ⧸ nilradical A) ⟶ Spec A` is surjective; surjections reflect geometric
  irreducibility (`AlgebraicGeometry.GeometricallyIrreducible.of_comp_of_surjective`).
* A purely inseparable extension `L / K` gives a universal homeomorphism `Spec L ⟶ Spec K`
  (`PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`), which is therefore geometrically
  irreducible.
* The algebraic closure `Ω` of a separably closed field `K` is purely inseparable over `K`, so
  `Spec (Ω ⊗[K] A) ⟶ Spec A` is a homeomorphism, and the composite
  `Spec (Ω ⊗[K] A) ⟶ Spec A ⟶ Spec K` equals `Spec (Ω ⊗[K] A) ⟶ Spec Ω ⟶ Spec K`, a composite of
  geometrically irreducible open morphisms.

Mathlib's `AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv` turns a geometrically
irreducible open morphism into a bijection of irreducible components.

The file also transports geometric irreducibility through dominant maps over a field, and supplies
geometric connectedness. Mathlib supplies the corresponding transport to nonempty open
subschemes.

## Main results

* `AlgebraicGeometry.GeometricallyIrreducible.of_comp_of_surjective`: if `f ≫ g` is geometrically
  irreducible and `f` is surjective, then `g` is geometrically irreducible.
* `TauCeti.AlgebraicGeometry.geometricallyIrreducible_Spec_of_isPurelyInseparable`: a purely
  inseparable field extension gives a geometrically irreducible morphism of spectra.
* `TauCeti.AlgebraicGeometry.geometricallyIrreducible_Spec_of_isSepClosed`: over a separably closed
  field, a morphism from an irreducible affine scheme is geometrically irreducible.
* `TauCeti.AlgebraicGeometry.bijOn_preimage_irreducibleComponents_of_isSepClosed`: over a separably
  closed field, preimage under a base change `X' ⟶ X` to a `K`-algebra with irreducible spectrum is
  a bijection from the irreducible components of `X` to those of `X'`.
* `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected`: the low-priority
  instance that geometric irreducibility implies geometric connectedness.
* `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.of_comp_isDominant`: geometric irreducibility
  descends along a dominant morphism over a field.

The dense-open and connectedness results are adapted from Axel Delaval, Jie Xu, and Shitan Xu's
Jacobian library, release `baef7723da528551b7d2f93bd9a9a53303b04dbc`,
`Jacobian/AlgebraicGeometry/Geometrically/Irreducible.lean`, declarations
`GeometricallyIrreducible.geometricallyConnected`, `GeometricallyIrreducible.of_surjective`,
`GeometricallyIrreducible.of_dense_open`.

## References

* The Stacks Project, Chapter *Commutative Algebra*, Section *Geometrically irreducible
  algebras*, and Chapter *Varieties*, Section *Geometrically irreducible schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

/-- Geometric irreducibility descends along surjections: if `f ≫ g` is geometrically irreducible
and `f` is surjective, then `g` is geometrically irreducible. -/
theorem GeometricallyIrreducible.of_comp_of_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Surjective f] [GeometricallyIrreducible (f ≫ g)] :
    GeometricallyIrreducible g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  -- The base change of `f` maps `X ×_Z Spec K` onto `Y ×_Z Spec K`.
  have : IrreducibleSpace ↥(pullback f (pullback.fst g x)) :=
    (pullbackRightPullbackFstIso g x f).hom.homeomorph.irreducibleSpace_iff.mpr
      (geometrically_iff_of_isClosedUnderIsomorphisms.mp
        (GeometricallyIrreducible.geometrically_irreducibleSpace (f := f ≫ g)) K x)
  exact (pullback.snd f (pullback.fst g x)).surjective.irreducibleSpace
    (pullback.snd f (pullback.fst g x)).continuous

end AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

/-- Over an algebraically closed field `K`, every morphism `Spec A ⟶ Spec K` from the spectrum of a
domain is geometrically irreducible. -/
private theorem geometricallyIrreducible_Spec_of_isAlgClosed_of_isDomain {K A : Type u} [Field K]
    [IsAlgClosed K] [CommRing A] [IsDomain A] (g : Spec (.of A) ⟶ Spec (.of K)) :
    GeometricallyIrreducible g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  -- The fibre product is `Spec (A ⊗[K] M)`, the spectrum of a domain.
  exact (pullbackSpecIso K A M).inv.homeomorph.irreducibleSpace_iff.mp inferInstance

/-- Over an algebraically closed field `K`, every morphism `Spec A ⟶ Spec K` from an irreducible
affine scheme is geometrically irreducible. -/
private theorem geometricallyIrreducible_Spec_of_isAlgClosed {K A : Type u} [Field K]
    [IsAlgClosed K] [CommRing A] [IrreducibleSpace (PrimeSpectrum A)]
    (g : Spec (.of A) ⟶ Spec (.of K)) : GeometricallyIrreducible g := by
  -- The reduced quotient of `A` is a domain whose spectrum maps onto `Spec A`.
  have : (nilradical A).IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp ‹_›
  let f : Spec (.of (A ⧸ nilradical A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
  have : Surjective f := ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).2⟩
  have := geometricallyIrreducible_Spec_of_isAlgClosed_of_isDomain (f ≫ g)
  exact GeometricallyIrreducible.of_comp_of_surjective f g

/-- A purely inseparable field extension `L / K` gives a geometrically irreducible morphism
`Spec L ⟶ Spec K`: its base change to every field is a homeomorphism onto a point. -/
instance geometricallyIrreducible_Spec_of_isPurelyInseparable {K L : Type u} [Field K] [Field L]
    [Algebra K L] [IsPurelyInseparable K L] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  -- `Spec (M ⊗[K] L) ⟶ Spec M` is a homeomorphism, and `Spec M` is irreducible.
  have : IrreducibleSpace (PrimeSpectrum (M ⊗[K] L)) :=
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable K L M).homeomorph.symm
      |>.irreducibleSpace_iff.mp inferInstance
  have : IrreducibleSpace (PrimeSpectrum (L ⊗[K] M)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv (Algebra.TensorProduct.comm K L M).toRingEquiv)
      |>.irreducibleSpace_iff.mpr this
  exact (pullbackSpecIso K L M).inv.homeomorph.irreducibleSpace_iff.mp this

/-- Over a separably closed field `K`, every morphism `Spec A ⟶ Spec K` from an irreducible affine
scheme is geometrically irreducible: `Spec (A ⊗[K] M)` is irreducible for every field `M` over
`K`. In particular this holds when `A` is a domain, or a field extension of `K`. -/
instance geometricallyIrreducible_Spec_of_isSepClosed {K A : Type u} [Field K] [IsSepClosed K]
    [CommRing A] [IrreducibleSpace (PrimeSpectrum A)] {g : Spec (.of A) ⟶ Spec (.of K)} :
    GeometricallyIrreducible g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  let Ω := AlgebraicClosure K
  -- `Spec (Ω ⊗[K] A)` is homeomorphic to `Spec A`, since `Ω / K` is purely inseparable.
  let p : Spec (.of (Ω ⊗[K] A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  have hp : IsHomeomorph
      (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight.toRingHom : A →+* Ω ⊗[K] A)) := by
    have h : (Algebra.TensorProduct.includeRight.toRingHom : A →+* Ω ⊗[K] A) =
        (Algebra.TensorProduct.comm K A Ω).toRingHom.comp (algebraMap A (A ⊗[K] Ω)) := by
      ext a
      simp
    rw [h, PrimeSpectrum.comap_comp]
    exact (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable K Ω A).comp
      (PrimeSpectrum.isHomeomorph_comap_of_bijective (Algebra.TensorProduct.comm K A Ω).bijective)
  have : IrreducibleSpace (PrimeSpectrum (Ω ⊗[K] A)) :=
    hp.homeomorph.irreducibleSpace_iff.mpr inferInstance
  have : Surjective p := ⟨hp.surjective⟩
  -- Over `Ω`, the irreducible scheme `Spec (Ω ⊗[K] A)` is geometrically irreducible.
  have := geometricallyIrreducible_Spec_of_isAlgClosed (K := Ω)
    (Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] A))))
  have : GeometricallyIrreducible (p ≫ Spec.map φ) := by
    have h : p ≫ Spec.map φ = Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      simp only [p, ← Spec.map_comp]
      congr 1
      ext x
      simp [Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]
    rw [h]
    exact GeometricallyIrreducible.comp _ _
  exact GeometricallyIrreducible.of_comp_of_surjective p _

/-- **The irreducible components of a scheme over a separably closed field are geometrically
irreducible.** Let `X` be a scheme over a separably closed field `K` and `X'` its base change to a
`K`-algebra `M` with irreducible spectrum, for instance a field extension of `K`, with projection
`g : X' ⟶ X`. Then `Z ↦ g ⁻¹' Z` is a bijection from the irreducible components of `X` onto those of
`X'`. -/
theorem bijOn_preimage_irreducibleComponents_of_isSepClosed {K M : Type u} [Field K]
    [IsSepClosed K] [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M)))) :
    Set.BijOn (g ⁻¹' ·) (irreducibleComponents X) (irreducibleComponents X') := by
  have : GeometricallyIrreducible g := MorphismProperty.of_isPullback H.flip inferInstance
  have : UniversallyOpen g := MorphismProperty.of_isPullback H.flip inferInstance
  let e := g.irreducibleComponentsEquiv g.isOpenMap
  refine ⟨fun Z hZ ↦ ?_, fun Z _ W _ h ↦ Set.preimage_injective.mpr g.surjective h,
    fun Z' hZ' ↦ ⟨e ⟨Z', hZ'⟩, (e ⟨Z', hZ'⟩).2, ?_⟩⟩
  · have := (e.symm ⟨Z, hZ⟩).2
    rwa [g.irreducibleComponentsEquiv_symm_apply_coe] at this
  · dsimp only
    rw [← g.irreducibleComponentsEquiv_symm_apply_coe g.isOpenMap, e.symm_apply_apply]

/-! ### Images and dense opens -/

/-- Every geometrically irreducible morphism is geometrically connected. -/
instance (priority := low) GeometricallyIrreducible.geometricallyConnected
    {source target : Scheme.{u}} (morphism : source ⟶ target)
    [GeometricallyIrreducible morphism] : GeometricallyConnected morphism := by
  refine ⟨fun field _ point fiber first second square ↦ ?_⟩
  have : IrreducibleSpace fiber :=
    GeometricallyIrreducible.geometrically_irreducibleSpace point first second square
  infer_instance

/-- Base-changing the source of a geometrically irreducible composite to a field gives an
irreducible scheme. -/
lemma GeometricallyIrreducible.irreducibleSpace_pullback_of_comp
    {source target base fiber : Scheme.{u}} (f : source ⟶ target) (g : target ⟶ base)
    [GeometricallyIrreducible (f ≫ g)] {field : Type u} [Field field]
    {point : Spec (.of field) ⟶ base} {first : fiber ⟶ target}
    {second : fiber ⟶ Spec (.of field)} (square : IsPullback first second g point) :
    IrreducibleSpace (pullback f first : Scheme.{u}) :=
  GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _
    ((IsPullback.of_hasPullback f first).paste_vert square)

/-- Geometric irreducibility of a composite over a field descends along a dominant morphism. -/
lemma GeometricallyIrreducible.of_comp_isDominant {field : Type u} [Field field]
    {source target : Scheme.{u}} (morphism : source ⟶ target) [IsDominant morphism]
    (structureMap : target ⟶ Spec (.of field))
    [GeometricallyIrreducible (morphism ≫ structureMap)] :
    GeometricallyIrreducible structureMap := by
  refine ⟨fun extensionField _ point fiber first second square ↦ ?_⟩
  have : IrreducibleSpace (pullback morphism first : Scheme.{u}) :=
    GeometricallyIrreducible.irreducibleSpace_pullback_of_comp morphism structureMap square
  have : UniversallyOpen first := MorphismProperty.of_isPullback square.flip inferInstance
  have denseImage : Dense (Set.range (pullback.snd morphism first)) := by
    rw [Scheme.Pullback.range_snd]
    exact morphism.denseRange.preimage first.isOpenMap
  have irreducibleImage : IsIrreducible (Set.range (pullback.snd morphism first)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (pullback morphism first : Scheme.{u})).image
        (pullback.snd morphism first) (pullback.snd morphism first).continuous.continuousOn
  apply (irreducibleSpace_def fiber).mpr
  simpa only [denseImage.closure_eq, Set.top_eq_univ] using irreducibleImage.closure

end AlgebraicGeometry

end TauCeti
