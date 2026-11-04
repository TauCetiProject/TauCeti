/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood

import all TauCeti.RingTheory.AdicRing.CompletedAway
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Localization.LocalizationLocalization
import TauCeti.RingTheory.AdicCompletion.Localization
import TauCeti.RingTheory.Flat.Colimit
import TauCeti.RingTheory.Ideal.Maps

/-!
# Noetherianity of the completed localisations at an open prime

Let `A` be a noetherian adic ring with ideal of definition `I`, and let `p` be an open prime of
`A`, corresponding to a prime ideal `𝔭 ⊇ I`. This file proves that the colimit
`colim_{f ∉ 𝔭} A_{f}` of the completed localisations of `A` over the basic open neighbourhoods
`D(f)` of `p` in `Spf A` is a noetherian ring (EGA I, Ch. 0, 7.6.17). This colimit is the algebraic
model of the stalk of `Spf A` at `p` (EGA I, Ch. I, 10.1.6).

A filtered colimit of noetherian rings need not be noetherian. Here noetherianity descends from
the completion `Â_𝔭` of the local ring `A_𝔭` along `I A_𝔭`, which is noetherian:

* for each `f ∉ 𝔭`, the completion of the localisation map `A_f → A_𝔭` is a map `A_{f} → Â_𝔭`, and
  `Â_𝔭` is flat over `A_{f}` (`AdicCompletion.flat_mapₐ_of_isLocalization`);
* these maps are compatible with the restriction maps, so they induce a map from the colimit to
  `Â_𝔭`, which is flat because every finite family of elements of the colimit comes from a single
  `A_{f}` (`RingHom.Flat.of_isColimit`);
* the residue map of the local ring `colim_{f ∉ 𝔭} A_{f}` onto `Frac(A ⧸ 𝔭)` factors through
  `Â_𝔭`, so the maximal ideal of the colimit does not generate the unit ideal of `Â_𝔭`, and `Â_𝔭`
  is faithfully flat over the colimit.

A ring with a faithfully flat noetherian algebra is noetherian.

## Main results

* `TauCeti.FormalScheme.Spf.completedNeighbourhood_noetherian`: for noetherian `A`, the colimit
  `colim_{f ∉ 𝔭} A_{f}` is a noetherian ring.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.17, and
  Ch. I, 10.1.6.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-- The completion `Â_𝔭` of the local ring `A_𝔭` along the ideal of definition `I`, for the open
prime `𝔭` of `A` corresponding to `p`. -/
private abbrev LocalCompletion : Type u :=
  AdicCompletion
    ((IsAdicRing.ideal A).map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
    (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)

omit [IsTopologicalRing A] [IsAdicRing A] in
/-- For `f ∉ 𝔭`, inverting `f` inverts only elements of `A ∖ 𝔭`. -/
private theorem powers_le_primeCompl (f : BasicNeighbourhood p) :
    Submonoid.powers f.elem ≤ (p : PrimeSpectrum A).asIdeal.primeCompl :=
  Submonoid.powers_le.mpr f.notMem

/-- For `f ∉ 𝔭`, the local ring `A_𝔭` is an algebra over `A_f`. -/
private noncomputable abbrev awayAlgebra (f : BasicNeighbourhood p) :
    Algebra (Localization.Away f.elem) (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ (powers_le_primeCompl p f)

omit [IsTopologicalRing A] [IsAdicRing A] in
attribute [local instance] awayAlgebra in
/-- The algebra structure of `A_𝔭` over `A_f` is compatible with those over `A`. -/
private theorem isScalarTower_away (f : BasicNeighbourhood p) :
    IsScalarTower A (Localization.Away f.elem)
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ (powers_le_primeCompl p f)

attribute [local instance] awayAlgebra in
/-- The ideal of definition of `A_𝔭` is the extension of that of `A_f`. -/
private theorem map_ideal_away (f : BasicNeighbourhood p) :
    ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f.elem))).map
        (algebraMap (Localization.Away f.elem)
          (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) =
      (IsAdicRing.ideal A).map
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) := by
  have := isScalarTower_away p f
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

attribute [local instance] awayAlgebra in
/-- For `f ∉ 𝔭`, the map `A_{f} → Â_𝔭`: the completion of the localisation map `A_f → A_𝔭`. -/
private noncomputable def toLocalCompletion (f : BasicNeighbourhood p) :
    CompletedAway A f.elem →ₐ[A] LocalCompletion p :=
  haveI := isScalarTower_away p f
  (AdicCompletion.mapₐ (Algebra.ofId (Localization.Away f.elem) _)
    ((map_ideal_away p f) ▸ Ideal.le_comap_map)).restrictScalars A

attribute [local instance] awayAlgebra in
/-- For noetherian `A` and `f ∉ 𝔭`, the completion `Â_𝔭` is flat over `A_{f}`. -/
private theorem flat_toLocalCompletion [IsNoetherianRing A] (f : BasicNeighbourhood p) :
    (toLocalCompletion p f).toRingHom.Flat := by
  have := isScalarTower_away p f
  have : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away f.elem)
      (p : PrimeSpectrum A).asIdeal.primeCompl)
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ (powers_le_primeCompl p f)
  exact AdicCompletion.flat_mapₐ_of_isLocalization _
    (Algebra.algebraMapSubmonoid (Localization.Away f.elem)
      (p : PrimeSpectrum A).asIdeal.primeCompl) (map_ideal_away p f)

/-- The cocone of the maps `A_{f} → Â_𝔭` over the diagram of completed localisations. -/
private noncomputable def localCompletionCocone : Cocone (completedNeighbourhoodDiagram p) where
  pt := CommRingCat.of (LocalCompletion p)
  ι.app f := CommRingCat.ofHom (toLocalCompletion p f).toRingHom
  ι.naturality {f g} h := by
    -- both composites are `A`-algebra homomorphisms into the completion of `A_𝔭`
    have := CompletedAway.algHom_ext_adicCompletion le_rfl ((toLocalCompletion p g).comp
      (CompletedAway.restrict ((BasicNeighbourhood.le_iff_mem_radical
        (IsAdicRing.ideal_spec A).2.1).mp h.le))) (toLocalCompletion p f)
    -- in `CommRingCat`, a composite of morphisms acts on elements as the composite of functions
    ext x
    exact congr($this x)

/-- The map `colim_{f ∉ 𝔭} A_{f} → Â_𝔭` induced by the maps `A_{f} → Â_𝔭`. -/
private noncomputable def fromColimit :
    (colimit (completedNeighbourhoodDiagram p) : CommRingCat) →+* LocalCompletion p :=
  (colimit.desc _ (localCompletionCocone p)).hom

/-- On `A_{f}`, the map `colim_{f ∉ 𝔭} A_{f} → Â_𝔭` is the map `A_{f} → Â_𝔭`. -/
private theorem fromColimit_ι (f : BasicNeighbourhood p)
    (x : ToType ((completedNeighbourhoodDiagram p).obj f)) :
    fromColimit p (colimit.ι (completedNeighbourhoodDiagram p) f x) = toLocalCompletion p f x :=
  colimit.ι_desc_apply (localCompletionCocone p) f x

/-- For noetherian `A`, the completion `Â_𝔭` is flat over `colim_{f ∉ 𝔭} A_{f}`, being flat over
every `A_{f}`. -/
private theorem flat_fromColimit [IsNoetherianRing A] : (fromColimit p).Flat :=
  RingHom.Flat.of_isColimit (colimit.isColimit _) (fromColimit p) fun f ↦
    (congrArg RingHom.Flat (RingHom.ext (fromColimit_ι p f))).mpr (flat_toLocalCompletion p f)

omit [IsTopologicalRing A] [IsAdicRing A] in
/-- The elements of `A ∖ 𝔭` are units in `Frac(A ⧸ 𝔭)`. -/
private theorem isUnit_algebraMap_residue (s : (p : PrimeSpectrum A).asIdeal.primeCompl) :
    IsUnit (algebraMap A (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) s) := by
  rw [IsScalarTower.algebraMap_apply A (A ⧸ (p : PrimeSpectrum A).asIdeal), isUnit_iff_ne_zero,
    ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact s.2

/-- The ideal of definition vanishes in `Frac(A ⧸ 𝔭)`. -/
private theorem map_ideal_residue :
    (IsAdicRing.ideal A).map (algebraMap A (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal))) =
      ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A (A ⧸ (p : PrimeSpectrum A).asIdeal),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr
      ((mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mp p.2 ha), map_zero]

/-- The value at `𝔭` of an element of `A_𝔭`, in `Frac(A ⧸ 𝔭)`. -/
private noncomputable def residueLocalization :
    Localization.AtPrime (p : PrimeSpectrum A).asIdeal →ₐ[A]
      FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  IsLocalization.liftAlgHom (M := (p : PrimeSpectrum A).asIdeal.primeCompl)
    (f := Algebra.ofId A _) (isUnit_algebraMap_residue p)

/-- The value at `𝔭` of an element of `Â_𝔭`: its image under `Â_𝔭 → A_𝔭 ⧸ I A_𝔭 → Frac(A ⧸ 𝔭)`,
which is defined since `I ⊆ 𝔭`. -/
private noncomputable def residueLocalCompletion :
    LocalCompletion p →ₐ[A] FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  (Ideal.Quotient.liftₐ _ (residueLocalization p) fun _ hx ↦
    (Ideal.map_eq_bot_iff_le_ker (residueLocalization p)).mp
      ((Ideal.map_map_algebraMap _ _).trans (map_ideal_residue p)) hx).comp
    ((AdicCompletion.evalOneₐ _).restrictScalars A)

/-- On the colimit, the value at `𝔭` through `Â_𝔭` is the residue map of the local ring
`colim_{f ∉ 𝔭} A_{f}`, identified with `Frac(A ⧸ 𝔭)` by `stalkResidueIso`. -/
private theorem residueLocalCompletion_fromColimit
    (x : (colimit (completedNeighbourhoodDiagram p) : CommRingCat)) :
    residueLocalCompletion p (fromColimit p x) = stalkResidueIso p (IsLocalRing.residue _ x) := by
  obtain ⟨f, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  rw [fromColimit_ι]
  -- both sides are `A`-algebra homomorphisms out of `A_{f}` into `Frac(A ⧸ 𝔭)`
  let g : CompletedAway A f.elem →ₐ[A] FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
    { toRingHom := (stalkResidueIso p).toRingHom.comp
        ((IsLocalRing.residue _).comp (colimit.ι (completedNeighbourhoodDiagram p) f).hom)
      commutes' a := (stalkResidueIso_coeff p f a).trans
        (IsScalarTower.algebraMap_apply A (A ⧸ (p : PrimeSpectrum A).asIdeal) _ a).symm }
  exact congr($(CompletedAway.algHom_ext_of_map_pow_eq_bot (n := 1)
    (by rw [pow_one, map_ideal_residue p]) ((residueLocalCompletion p).comp
      (toLocalCompletion p f)) g) y)

/-- For noetherian `A`, the completion `Â_𝔭` is faithfully flat over `colim_{f ∉ 𝔭} A_{f}`: it is
flat, and the maximal ideal of the colimit maps into the kernel of the value at `𝔭`. -/
private theorem faithfullyFlat_fromColimit [IsNoetherianRing A] :
    (fromColimit p).FaithfullyFlat := by
  algebraize [fromColimit p]
  have : Module.Flat _ (LocalCompletion p) := flat_fromColimit p
  refine ⟨fun m hm hmtop ↦ ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm, Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff,
    Ideal.eq_top_iff_one] at hmtop
  have hle : (IsLocalRing.maximalIdeal
      (colimit (completedNeighbourhoodDiagram p) : CommRingCat)).map
        (algebraMap _ (LocalCompletion p)) ≤
      RingHom.ker (residueLocalCompletion p) := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.algebraMap_toAlgebra,
      residueLocalCompletion_fromColimit, (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
  exact one_ne_zero (α := FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal))
    (by simpa using hle hmtop)

/-- The colimit `colim_{f ∉ p} A_{f}` of the completed localisations of a noetherian adic ring `A`
over the basic open neighbourhoods of an open prime `p` is a noetherian ring (EGA I, Ch. 0,
7.6.17). -/
instance completedNeighbourhood_noetherian [IsNoetherianRing A] :
    IsNoetherianRing (colimit (completedNeighbourhoodDiagram p) : CommRingCat) := by
  -- noetherianity descends along the faithfully flat map to the noetherian ring `Â_𝔭`
  algebraize [fromColimit p]
  have : Module.FaithfullyFlat _ (LocalCompletion p) := faithfullyFlat_fromColimit p
  exact isNoetherianRing_iff.mpr
    (Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (A := LocalCompletion p)
      (isNoetherian_of_linearEquiv (TensorProduct.AlgebraTensorModule.rid _ _ _).symm))

end TauCeti.FormalScheme.Spf
