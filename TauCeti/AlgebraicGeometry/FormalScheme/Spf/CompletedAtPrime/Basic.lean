/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import TauCeti.RingTheory.AdicCompletion.Localization
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Flat.Colimit
import TauCeti.RingTheory.Ideal.Maps

/-!
# The completed localisations of an adic ring at its open primes

Let `A` be an adic ring with ideal of definition `I`, and let `p` be an open prime of `A`,
corresponding to a prime ideal `𝔭 ⊇ I`. This file defines the completed localisation
`Â_𝔭 = lim_n (A ⧸ Iⁿ)_𝔭`, the completion of the local ring `A_𝔭` along `I A_𝔭` (EGA I, Ch. 0,
7.6.15), and compares it with the colimit `colim_{f ∉ 𝔭} A_{f}` of the completed localisations of
`A` over the basic open neighbourhoods `D(f)` of `p` in `Spf A`, the algebraic model of the stalk of
`Spf A` at `p` (EGA I, Ch. I, 10.1.6).

* For each `f ∉ 𝔭`, the completion of the localisation map `A_f → A_𝔭` is a map `A_{f} → Â_𝔭`.
  These maps are compatible with the restriction maps, so they induce a map from the colimit to
  `Â_𝔭`.
* The residue map of the local ring `colim_{f ∉ 𝔭} A_{f}` onto `Frac(A ⧸ 𝔭)` factors through
  `Â_𝔭`, so this map is a local homomorphism.
* For noetherian `A`, the completion `Â_𝔭` is flat over every `A_{f}`
  (`AdicCompletion.flat_mapₐ_of_isLocalization`), hence over the colimit, because every finite
  family of elements of the colimit comes from a single `A_{f}` (`RingHom.Flat.of_isColimit`).
  Its maximal ideal maps into the kernel of the residue map of `Â_𝔭`, so it is faithfully flat.
* Since `I ⊆ 𝔭`, the ring `Â_𝔭` is local with maximal ideal `𝔭 Â_𝔭`, and for noetherian `A` it has
  the Krull dimension of `A_𝔭` and is regular exactly when `A_𝔭` is.

## Main definitions

* `TauCeti.FormalScheme.Spf.CompletedAtPrime p`: the completed localisation `Â_𝔭`, the completion
  of `A_𝔭` along `I A_𝔭`.
* `TauCeti.FormalScheme.Spf.toCompletedAtPrime p f`: for `f ∉ 𝔭`, the map `A_{f} → Â_𝔭`.
* `TauCeti.FormalScheme.Spf.colimitToCompletedAtPrime p`: the induced map
  `colim_{f ∉ 𝔭} A_{f} → Â_𝔭`.

## Main results

* `TauCeti.FormalScheme.Spf.isLocalHom_colimitToCompletedAtPrime`: the map
  `colim_{f ∉ 𝔭} A_{f} → Â_𝔭` is a local homomorphism.
* `TauCeti.FormalScheme.Spf.faithfullyFlat_colimitToCompletedAtPrime`: for noetherian `A`, the
  completed localisation `Â_𝔭` is faithfully flat over `colim_{f ∉ 𝔭} A_{f}`.
* `TauCeti.FormalScheme.Spf.maximalIdeal_completedAtPrime`: `Â_𝔭` is a local ring with maximal
  ideal `𝔭 Â_𝔭`.
* `TauCeti.FormalScheme.Spf.ringKrullDim_completedAtPrime`,
  `TauCeti.FormalScheme.Spf.isRegularLocalRing_completedAtPrime_iff`: for noetherian `A`, the rings
  `Â_𝔭` and `A_𝔭` have the same Krull dimension, and one is regular if and only if the other is.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.17,
  and Ch. I, 10.1.6.
* [Stacks Project, Lemma 15.44.1](https://stacks.math.columbia.edu/tag/07NV) and
  [Stacks Project, Lemma 15.44.4](https://stacks.math.columbia.edu/tag/07NY), the dimension and
  regularity of the completion of a noetherian local ring along an ideal.
-/

public section

universe u

open CategoryTheory Limits IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-- The **completed localisation** `Â_𝔭 = lim_n (A ⧸ Iⁿ)_𝔭` of `A` at the open prime `𝔭`
corresponding to `p`: the completion of the local ring `A_𝔭` along the ideal of definition `I`. It
is the completed localisation `A_{A ∖ 𝔭}` of EGA I, Ch. 0, 7.6.15. -/
abbrev CompletedAtPrime : Type u :=
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
noncomputable def toCompletedAtPrime (f : BasicNeighbourhood p) :
    CompletedAway A f.elem →ₐ[A] CompletedAtPrime p :=
  haveI := isScalarTower_away p f
  ((AdicCompletion.mapₐ (Algebra.ofId (Localization.Away f.elem) _)
    ((map_ideal_away p f) ▸ Ideal.le_comap_map)).comp
      (CompletedAway.equivAdicCompletion A f.elem).toAlgHom).restrictScalars A

attribute [local instance] awayAlgebra in
/-- For noetherian `A` and `f ∉ 𝔭`, the completion `Â_𝔭` is flat over `A_{f}`. -/
private theorem flat_toCompletedAtPrime [IsNoetherianRing A] (f : BasicNeighbourhood p) :
    (toCompletedAtPrime p f).toRingHom.Flat := by
  have := isScalarTower_away p f
  have : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away f.elem)
      (p : PrimeSpectrum A).asIdeal.primeCompl)
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ (powers_le_primeCompl p f)
  -- the completion of `A_f → A_𝔭`, after the identification of `A_{f}` with that completion
  exact (RingHom.Flat.of_bijective (CompletedAway.equivAdicCompletion A f.elem).bijective).comp
    (AdicCompletion.flat_mapₐ_of_isLocalization _
      (Algebra.algebraMapSubmonoid (Localization.Away f.elem)
        (p : PrimeSpectrum A).asIdeal.primeCompl) (map_ideal_away p f))

/-- The cocone of the maps `A_{f} → Â_𝔭` over the diagram of completed localisations. -/
private noncomputable def completedAtPrimeCocone : Cocone (completedNeighbourhoodDiagram p) where
  pt := CommRingCat.of (CompletedAtPrime p)
  ι.app f := CommRingCat.ofHom (toCompletedAtPrime p f).toRingHom
  ι.naturality {f g} h := by
    -- both composites are `A`-algebra homomorphisms into the completion of `A_𝔭`
    have := CompletedAway.algHom_ext_adicCompletion le_rfl ((toCompletedAtPrime p g).comp
      (CompletedAway.restrict ((BasicNeighbourhood.le_iff_mem_radical
        (IsAdicRing.ideal_spec A).2.1).mp h.le))) (toCompletedAtPrime p f)
    -- in `CommRingCat`, a composite of morphisms acts on elements as the composite of functions
    ext x
    exact congr($this x)

/-- The map `colim_{f ∉ 𝔭} A_{f} → Â_𝔭` induced by the maps `A_{f} → Â_𝔭`. -/
noncomputable def colimitToCompletedAtPrime :
    (colimit (completedNeighbourhoodDiagram p) : CommRingCat) →+* CompletedAtPrime p :=
  (colimit.desc _ (completedAtPrimeCocone p)).hom

/-- On `A_{f}`, the map `colim_{f ∉ 𝔭} A_{f} → Â_𝔭` is the map `A_{f} → Â_𝔭`. -/
@[simp]
theorem colimitToCompletedAtPrime_ι (f : BasicNeighbourhood p)
    (x : ToType ((completedNeighbourhoodDiagram p).obj f)) :
    colimitToCompletedAtPrime p (colimit.ι (completedNeighbourhoodDiagram p) f x) =
      toCompletedAtPrime p f x :=
  colimit.ι_desc_apply (completedAtPrimeCocone p) f x

/-- For noetherian `A`, the completion `Â_𝔭` is flat over `colim_{f ∉ 𝔭} A_{f}`, being flat over
every `A_{f}`. -/
private theorem flat_colimitToCompletedAtPrime [IsNoetherianRing A] :
    (colimitToCompletedAtPrime p).Flat :=
  RingHom.Flat.of_isColimit (colimit.isColimit _) (colimitToCompletedAtPrime p) fun f ↦
    (congrArg RingHom.Flat (RingHom.ext (colimitToCompletedAtPrime_ι p f))).mpr
      (flat_toCompletedAtPrime p f)

omit [IsTopologicalRing A] [IsAdicRing A] in
/-- The elements of `A ∖ 𝔭` are units in `Frac(A ⧸ 𝔭)`. -/
private theorem isUnit_algebraMap_residue (s : (p : PrimeSpectrum A).asIdeal.primeCompl) :
    IsUnit (algebraMap A (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) s) := by
  rw [IsScalarTower.algebraMap_apply A (A ⧸ (p : PrimeSpectrum A).asIdeal), isUnit_iff_ne_zero,
    ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact s.property

/-- The ideal of definition vanishes in `Frac(A ⧸ 𝔭)`. -/
private theorem map_ideal_residue :
    (IsAdicRing.ideal A).map (algebraMap A (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal))) =
      ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A (A ⧸ (p : PrimeSpectrum A).asIdeal),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr
      ((mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mp p.property ha), map_zero]

/-- The value at `𝔭` of an element of `A_𝔭`, in `Frac(A ⧸ 𝔭)`. -/
private noncomputable def residueLocalization :
    Localization.AtPrime (p : PrimeSpectrum A).asIdeal →ₐ[A]
      FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  IsLocalization.liftAlgHom (M := (p : PrimeSpectrum A).asIdeal.primeCompl)
    (f := Algebra.ofId A _) (isUnit_algebraMap_residue p)

/-- The value at `𝔭` of an element of `Â_𝔭`: its image under `Â_𝔭 → A_𝔭 ⧸ I A_𝔭 → Frac(A ⧸ 𝔭)`,
which is defined since `I ⊆ 𝔭`. -/
private noncomputable def residueCompletedAtPrime :
    CompletedAtPrime p →ₐ[A] FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  (Ideal.Quotient.liftₐ _ (residueLocalization p) fun _ hx ↦
    (Ideal.map_eq_bot_iff_le_ker (residueLocalization p)).mp
      ((Ideal.map_map_algebraMap _ _).trans (map_ideal_residue p)) hx).comp
    ((AdicCompletion.evalOneₐ _).restrictScalars A)

/-- On the colimit, the value at `𝔭` through `Â_𝔭` is the residue map of the local ring
`colim_{f ∉ 𝔭} A_{f}`, identified with `Frac(A ⧸ 𝔭)` by `stalkResidueIso`. -/
private theorem residueCompletedAtPrime_colimitToCompletedAtPrime
    (x : (colimit (completedNeighbourhoodDiagram p) : CommRingCat)) :
    residueCompletedAtPrime p (colimitToCompletedAtPrime p x) =
      stalkResidueIso p (IsLocalRing.residue _ x) := by
  obtain ⟨f, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  rw [colimitToCompletedAtPrime_ι]
  -- both sides are `A`-algebra homomorphisms out of `A_{f}` into `Frac(A ⧸ 𝔭)`
  let g : CompletedAway A f.elem →ₐ[A] FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
    { toRingHom := (stalkResidueIso p).toRingHom.comp
        ((IsLocalRing.residue _).comp (colimit.ι (completedNeighbourhoodDiagram p) f).hom)
      commutes' a := (stalkResidueIso_coeff p f a).trans
        (IsScalarTower.algebraMap_apply A (A ⧸ (p : PrimeSpectrum A).asIdeal) _ a).symm }
  exact congr($(CompletedAway.algHom_ext_of_map_pow_eq_bot (n := 1)
    (by rw [pow_one, map_ideal_residue p]) ((residueCompletedAtPrime p).comp
      (toCompletedAtPrime p f)) g) y)

/-- The map `colim_{f ∉ 𝔭} A_{f} → Â_𝔭` is a local homomorphism: an element whose image is a unit
has a nonzero value at `𝔭`, so it is a unit of the local ring `colim_{f ∉ 𝔭} A_{f}`. -/
instance isLocalHom_colimitToCompletedAtPrime : IsLocalHom (colimitToCompletedAtPrime p) := by
  refine ⟨fun x hx ↦ ?_⟩
  have h := hx.map (residueCompletedAtPrime p)
  rw [residueCompletedAtPrime_colimitToCompletedAtPrime, isUnit_map_iff] at h
  exact isUnit_of_map_unit (IsLocalRing.residue _) x h

/-- For noetherian `A`, the completion `Â_𝔭` is faithfully flat over `colim_{f ∉ 𝔭} A_{f}`: it is
flat, and the maximal ideal of the colimit maps into the kernel of the value at `𝔭`. -/
theorem faithfullyFlat_colimitToCompletedAtPrime [IsNoetherianRing A] :
    (colimitToCompletedAtPrime p).FaithfullyFlat := by
  algebraize [colimitToCompletedAtPrime p]
  have : Module.Flat _ (CompletedAtPrime p) := flat_colimitToCompletedAtPrime p
  refine ⟨fun m hm hmtop ↦ ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm, Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff,
    Ideal.eq_top_iff_one] at hmtop
  have hle : (IsLocalRing.maximalIdeal
      (colimit (completedNeighbourhoodDiagram p) : CommRingCat)).map
        (algebraMap _ (CompletedAtPrime p)) ≤
      RingHom.ker (residueCompletedAtPrime p) := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.algebraMap_toAlgebra,
      residueCompletedAtPrime_colimitToCompletedAtPrime, (IsLocalRing.residue_eq_zero_iff x).mpr hx,
      map_zero]
  exact one_ne_zero (α := FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal))
    (by simpa using hle hmtop)

/-! ### The completed localisation as a local ring -/

/-- The ideal of definition of `A_𝔭` lies in its maximal ideal, since `I ⊆ 𝔭`. -/
private theorem map_ideal_le_maximalIdeal :
    (IsAdicRing.ideal A).map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono ((mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mp p.property)

/-- The completed localisation `Â_𝔭` is a local ring. -/
instance isLocalRing_completedAtPrime : IsLocalRing (CompletedAtPrime p) :=
  TauCeti.AdicCompletion.isLocalRing_of_le (map_ideal_le_maximalIdeal p)
    ((IsAdicRing.ideal_spec A).1.map _)

/-- The maximal ideal of the completed localisation `Â_𝔭` is generated by `𝔭`. -/
theorem maximalIdeal_completedAtPrime :
    maximalIdeal (CompletedAtPrime p) =
      (p : PrimeSpectrum A).asIdeal.map (algebraMap A (CompletedAtPrime p)) := by
  rw [TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le (map_ideal_le_maximalIdeal p)
    ((IsAdicRing.ideal_spec A).1.map _), ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- For a noetherian adic ring `A`, the completed localisation `Â_𝔭` has the Krull dimension of
`A_𝔭`. -/
theorem ringKrullDim_completedAtPrime [IsNoetherianRing A] :
    ringKrullDim (CompletedAtPrime p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  TauCeti.AdicCompletion.ringKrullDim_eq (map_ideal_le_maximalIdeal p)

/-- For a noetherian adic ring `A`, the completed localisation `Â_𝔭` is a regular local ring if
and only if `A_𝔭` is. -/
theorem isRegularLocalRing_completedAtPrime_iff [IsNoetherianRing A] :
    IsRegularLocalRing (CompletedAtPrime p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  TauCeti.AdicCompletion.isRegularLocalRing_iff (map_ideal_le_maximalIdeal p)

end TauCeti.FormalScheme.Spf
