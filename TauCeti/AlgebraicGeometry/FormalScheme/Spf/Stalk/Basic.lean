/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Basic
public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.Localization.AtPrime.Basic

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood.Noetherian
import TauCeti.RingTheory.CohenMacaulay.Flat
import TauCeti.RingTheory.Flat.Colimit
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# The stalks of a formal spectrum and the localisations of its ring

Let `A` be a noetherian adic ring and `p` a point of `Spf A`, an open prime `𝔭` of `A`. The stalk
`O_{Spf A, p}` is the colimit of the completed localisations `A_{f}` over the basic open
neighbourhoods `D(f)` of `p`, and the elements of `A ∖ 𝔭` become units in it, so it receives a
canonical map from the local ring `A_𝔭` (EGA I, Ch. 0, 7.6.17; Ch. I, 10.1.6). This file shows
that `A_𝔭 → O_{Spf A, p}` is a faithfully flat local homomorphism of noetherian local rings under
which `𝔭 A_𝔭` generates the maximal ideal of the stalk:

* flatness holds because every `A_{f}` is flat over `A`, and a filtered colimit of flat
  `A`-algebras is flat (`RingHom.Flat.of_isColimit_codomain`); flatness over `A` and over its
  localisation `A_𝔭` agree;
* an element of `A_{f}` vanishing at `p` is, modulo `I A_{f}`, a fraction `a / fⁿ` with `a ∈ 𝔭`,
  and `I ⊆ 𝔭`, so it lies in `𝔭 A_{f}`.

The closed fibre of `A_𝔭 → O_{Spf A, p}` is therefore the residue field of the stalk. Along such a
homomorphism the Krull dimension, regularity and the Cohen–Macaulay property are unchanged, so
the stalk and `A_𝔭` share these invariants. This is how the local dimension, regularity and the
Cohen–Macaulay condition at a point of a formal spectrum are computed from its ring.

## Main definitions

* `TauCeti.FormalScheme.Spf.toStalk p`: the canonical map `A → O_{Spf A, p}`.
* `TauCeti.FormalScheme.Spf.localizationToStalk p`: the canonical map `A_𝔭 → O_{Spf A, p}`.

## Main results

* `TauCeti.FormalScheme.Spf.flat_localizationToStalk`,
  `TauCeti.FormalScheme.Spf.faithfullyFlat_localizationToStalk`: the map `A_𝔭 → O_{Spf A, p}` is
  flat and faithfully flat.
* `TauCeti.FormalScheme.Spf.map_maximalIdeal_localizationToStalk`: the maximal ideal of `A_𝔭`
  generates the maximal ideal of the stalk.
* `TauCeti.FormalScheme.Spf.ringKrullDim_stalk`: the stalk `O_{Spf A, p}` and `A_𝔭` have the same
  Krull dimension.
* `TauCeti.FormalScheme.Spf.ringKrullDim_stalk_eq_height`: the stalk `O_{Spf A, p}` has Krull
  dimension the height of `𝔭`.
* `TauCeti.FormalScheme.Spf.isRegularLocalRing_stalk_iff`: the stalk is regular if and only if
  `A_𝔭` is.
* `TauCeti.FormalScheme.Spf.isCohenMacaulay_stalk_iff`: the stalk is Cohen–Macaulay if and only if
  `A_𝔭` is.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
* H. Matsumura, *Commutative Ring Theory*, Theorem 15.1, Theorem 23.7 and the Corollary of
  Theorem 23.3, for the invariance of the dimension, of regularity and of the Cohen–Macaulay
  property along a flat local homomorphism whose closed fibre is a field.
-/

public section

universe u

open CategoryTheory Limits IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-! ### The map from `A_𝔭` to the colimit of the completed localisations -/

/-- The leg `A_{f} → colim_{f ∉ 𝔭} A_{f}` of the colimit, as a ring homomorphism out of the
completed localisation `A_{f}`. -/
private noncomputable abbrev leg (f : BasicNeighbourhood p) :
    CompletedAway A f.elem →+* (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
  (colimit.ι (completedNeighbourhoodDiagram p) f).hom

/-- Every element of the colimit comes from some completed localisation `A_{f}`. -/
private theorem exists_leg_eq (x : (colimit (completedNeighbourhoodDiagram p) : CommRingCat)) :
    ∃ (f : BasicNeighbourhood p) (y : CompletedAway A f.elem), leg p f y = x :=
  Concrete.colimit_exists_rep _ x

/-- The image of `A` in `colim_{f ∉ 𝔭} A_{f}`, through the completed localisation at `1`. -/
private noncomputable def toColimit :
    A →+* (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
  (leg p ⊥).comp (algebraMap A (CompletedAway A 1))

/-- The image of `a ∈ A` in the colimit does not depend on the completed localisation it is read
in. -/
private theorem leg_algebraMap (f : BasicNeighbourhood p) (a : A) :
    leg p f (algebraMap A (CompletedAway A f.elem) a) = toColimit p a := by
  let t := homOfLE (bot_le : ⊥ ≤ f)
  rw [← completedNeighbourhoodDiagram_map_algebraMap p t a]
  exact colimit.w_apply (completedNeighbourhoodDiagram p) t (algebraMap A (CompletedAway A 1) a)

private theorem leg_comp_algebraMap (f : BasicNeighbourhood p) :
    (leg p f).comp (algebraMap A (CompletedAway A f.elem)) = toColimit p :=
  RingHom.ext (leg_algebraMap p f)

/-- The elements of `A ∖ 𝔭` become units in the colimit. -/
private theorem isUnit_toColimit (s : (p : PrimeSpectrum A).asIdeal.primeCompl) :
    IsUnit (toColimit p s) := by
  rw [← leg_algebraMap p ⟨s, s.property⟩]
  exact (CompletedAway.isUnit_algebraMap_self A (s : A)).map _

/-- The map `A_𝔭 → colim_{f ∉ 𝔭} A_{f}`. -/
private noncomputable def fromLocalization :
    Localization.AtPrime (p : PrimeSpectrum A).asIdeal →+*
      (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
  IsLocalization.lift (M := (p : PrimeSpectrum A).asIdeal.primeCompl) (isUnit_toColimit p)

private theorem fromLocalization_comp_algebraMap :
    (fromLocalization p).comp (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) =
      toColimit p :=
  IsLocalization.lift_comp _

/-- For noetherian `A`, the colimit `colim_{f ∉ 𝔭} A_{f}` is flat over `A`, being a filtered
colimit of the flat `A`-algebras `A_{f}`. -/
private theorem flat_toColimit [IsNoetherianRing A] : (toColimit p).Flat :=
  RingHom.Flat.of_isColimit_codomain (colimit.isColimit _) (toColimit p)
    (fun f ↦ algebraMap A (CompletedAway A f.elem))
    (fun t ↦ RingHom.ext (completedNeighbourhoodDiagram_map_algebraMap p t))
    (leg_comp_algebraMap p)
    (fun f ↦ (RingHom.flat_algebraMap_iff (R := A) (S := CompletedAway A f.elem)).mpr inferInstance)

/-- For noetherian `A`, the colimit `colim_{f ∉ 𝔭} A_{f}` is flat over `A_𝔭`. -/
private theorem flat_fromLocalization [IsNoetherianRing A] : (fromLocalization p).Flat := by
  let P := (p : PrimeSpectrum A).asIdeal
  algebraize [fromLocalization p, (fromLocalization p).comp (algebraMap A (Localization.AtPrime P))]
  have : Module.Flat A (colimit (completedNeighbourhoodDiagram p) : CommRingCat) := by
    have := flat_toColimit p
    rwa [← fromLocalization_comp_algebraMap p] at this
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl _).mpr this

/-- The residue isomorphism of the colimit sends the class of `a ∈ A` to its image in
`Frac(A ⧸ 𝔭)`. -/
private theorem stalkResidueIso_toColimit (a : A) :
    stalkResidueIso p (residue _ (toColimit p a)) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal) _ (Ideal.Quotient.mk _ a) := by
  rw [← leg_algebraMap p ⊥]
  exact stalkResidueIso_coeff p _ a

/-- The image of `a ∈ A` lies in the maximal ideal of the colimit exactly when `a ∈ 𝔭`. -/
private theorem toColimit_mem_maximalIdeal_iff {a : A} :
    toColimit p a ∈ maximalIdeal (colimit (completedNeighbourhoodDiagram p) : CommRingCat) ↔
      a ∈ (p : PrimeSpectrum A).asIdeal := by
  rw [← residue_eq_zero_iff, ← EmbeddingLike.map_eq_zero_iff (f := stalkResidueIso p),
    stalkResidueIso_toColimit, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The ideal generated by `𝔭` in the colimit `colim_{f ∉ 𝔭} A_{f}` lies in its maximal ideal. -/
private theorem map_toColimit_le_maximalIdeal :
    (p : PrimeSpectrum A).asIdeal.map (toColimit p) ≤
      maximalIdeal (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
  Ideal.map_le_iff_le_comap.mpr fun _ ha ↦ (toColimit_mem_maximalIdeal_iff p).mpr ha

/-- The ideal generated by `𝔭` in the colimit `colim_{f ∉ 𝔭} A_{f}` contains its maximal ideal: an
element of `A_{f}` vanishing at `p` is, modulo `I A_{f}`, a fraction `a / fⁿ` with `a ∈ 𝔭`. -/
private theorem maximalIdeal_le_map_toColimit :
    maximalIdeal (colimit (completedNeighbourhoodDiagram p) : CommRingCat) ≤
      (p : PrimeSpectrum A).asIdeal.map (toColimit p) := by
  intro x hx
  set P := (p : PrimeSpectrum A).asIdeal
  obtain ⟨f, y, rfl⟩ := exists_leg_eq p x
  -- modulo `I A_{f}`, `y` is a fraction `a / fⁿ`
  obtain ⟨z, hz⟩ := CompletedAway.exists_sub_mem_map A f.elem y
  obtain ⟨n, a, hza⟩ := IsLocalization.Away.surj f.elem z
  -- the error term lies in `I A_{f}`, hence maps into `𝔭` times the colimit
  have herr : leg p f (y - algebraMap _ _ z) ∈ P.map (toColimit p) := by
    have hIP : IsAdicRing.ideal A ≤ P :=
      (mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mp p.property
    have := Ideal.mem_map_of_mem (leg p f) (Ideal.map_mono hIP hz)
    rwa [Ideal.map_map, leg_comp_algebraMap] at this
  -- the fraction itself has numerator `a` and the unit denominator `fⁿ`
  have hfrac : leg p f (algebraMap _ _ z) * toColimit p (f.elem ^ n) = toColimit p a := by
    have := congrArg (leg p f ∘ algebraMap _ (CompletedAway A f.elem)) hza
    simpa only [Function.comp_apply, map_mul, map_pow, ← IsScalarTower.algebraMap_apply,
      leg_algebraMap] using this
  obtain ⟨v, hv⟩ := isUnit_toColimit p ⟨f.elem ^ n, P.primeCompl.pow_mem f.notMem n⟩
  have hz' : leg p f (algebraMap _ _ z) = toColimit p a * ↑v⁻¹ := by
    rw [← hfrac, ← hv, Units.mul_inv_cancel_right]
  -- the numerator lies in `𝔭`, as `y` vanishes at `p`
  have ha : a ∈ P := by
    refine (toColimit_mem_maximalIdeal_iff p).mp ?_
    have : leg p f (algebraMap _ _ z) ∈ maximalIdeal _ := by
      rw [← sub_sub_cancel (leg p f y) (leg p f (algebraMap _ _ z)), ← map_sub]
      exact sub_mem hx (map_toColimit_le_maximalIdeal p herr)
    rw [← hfrac]
    exact Ideal.mul_mem_right _ _ this
  rw [← sub_add_cancel y (algebraMap _ _ z), map_add, hz']
  exact add_mem herr (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha))

/-- The maximal ideal of `A_𝔭` generates the maximal ideal of `colim_{f ∉ 𝔭} A_{f}`. -/
private theorem map_maximalIdeal_fromLocalization :
    (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)).map (fromLocalization p) =
      maximalIdeal (colimit (completedNeighbourhoodDiagram p) : CommRingCat) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    fromLocalization_comp_algebraMap]
  exact le_antisymm (map_toColimit_le_maximalIdeal p) (maximalIdeal_le_map_toColimit p)

/-! ### The map from `A_𝔭` to the stalk -/

/-- The identification of `colim_{f ∉ 𝔭} A_{f}` with the stalk of `Spf A` at `p`. -/
private noncomputable abbrev colimitIso :
    colimit (completedNeighbourhoodDiagram p) ≅ (Spf A).presheaf.stalk p :=
  completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1

/-- The canonical map `A_𝔭 → O_{Spf A, p}` from the localisation of `A` at the open prime `𝔭`
corresponding to `p` to the stalk of `Spf A` at `p`. It sends `a ∈ A` to the germ at `p` of the
section `a` over any basic open neighbourhood of `p`, see
`TauCeti.FormalScheme.Spf.localizationToStalk_algebraMap`. -/
noncomputable def localizationToStalk :
    Localization.AtPrime (p : PrimeSpectrum A).asIdeal →+* (Spf A).presheaf.stalk p :=
  (colimitIso p).hom.hom.comp (fromLocalization p)

/-- The map `A_𝔭 → O_{Spf A, p}` sends `a ∈ A` to the germ at `p` of the section over any basic
open neighbourhood `D(f)` of `p` given by the image of `a` in `A_{f}`. Since `A_𝔭` is a
localisation of `A`, this determines the map. -/
theorem localizationToStalk_algebraMap (f : BasicNeighbourhood p) (a : A) :
    localizationToStalk p (algebraMap A _ a) =
      (Spf A).presheaf.germ (basicOpen f.elem) p (mem_basicOpen.mpr f.notMem)
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          f.elem).inv (algebraMap A (CompletedAway A f.elem) a)) := by
  rw [localizationToStalk, RingHom.comp_apply, ← RingHom.comp_apply (fromLocalization p),
    fromLocalization_comp_algebraMap, ← leg_algebraMap p f]
  exact ConcreteCategory.congr_hom (completedNeighbourhoodColimitIso_germ p _ _ f) _

/-- The canonical ring homomorphism `A →+* 𝒪_{Spf A, p}` sending `a ∈ A` to the germ at `p` of the
corresponding global section of `Spf A`. -/
noncomputable def toStalk : A →+* (Spf A).presheaf.stalk p :=
  have := (IsAdicRing.ideal_spec A).2.1.isAdicComplete
  ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
    (Spf A).presheaf.germ ⊤ p trivial).hom

/-- Defining formula for `toStalk p`: the germ at `p` of the global section corresponding to
`a ∈ A`. -/
theorem toStalk_def (a : A) :
    toStalk p a =
      have := (IsAdicRing.ideal_spec A).2.1.isAdicComplete
      (Spf A).presheaf.germ ⊤ p trivial
        ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv a) := by
  rfl

/-- On any basic open neighbourhood `D(f)` of `p`, `toStalk p a` is the germ at `p` of the image
of `a` in `A_{f}`. -/
theorem toStalk_eq_germ (f : BasicNeighbourhood p) (a : A) :
    toStalk p a = (Spf A).presheaf.germ (basicOpen f.elem) p (mem_basicOpen.mpr f.notMem)
      ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f.elem).inv
        (algebraMap A (CompletedAway A f.elem) a)) := by
  have := (IsAdicRing.ideal_spec A).2.1.isAdicComplete
  have h1 := globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f.elem
  have h2 : (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
      TopCat.Presheaf.germ (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj ⊤ p trivial =
      CommRingCat.ofHom (algebraMap A (CompletedAway A f.elem)) ≫
        (basicOpenSectionsIso _ (IsAdicRing.ideal_spec A).1 f.elem).inv ≫
        TopCat.Presheaf.germ (structureSheaf _).obj (basicOpen f.elem) p
          (mem_basicOpen.mpr f.notMem) := by
    rw [← h1, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((globalSectionsIso _).inv ≫ ·)
      (TopCat.Presheaf.germ_res (structureSheaf _).obj (homOfLE (le_top : basicOpen f.elem ≤ ⊤)) p
        (mem_basicOpen.mpr f.notMem)).symm
  exact ConcreteCategory.congr_hom h2 a

/-- Through the identification of the stalk with `colim_{f ∉ 𝔭} A_{f}`, `toStalk p a` is the image
of `a ∈ A` from any completed localisation `A_{f}` with `f ∉ 𝔭`. -/
theorem toStalk_eq_completedNeighbourhoodColimitIso (f : BasicNeighbourhood p) (a : A) :
    toStalk p a =
      (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).hom
        (colimit.ι (completedNeighbourhoodDiagram p) f
          (algebraMap A (CompletedAway A f.elem) a)) :=
  (toStalk_eq_germ p f a).trans
    (ConcreteCategory.congr_hom (completedNeighbourhoodColimitIso_germ p _ _ f) _).symm

/-- Every germ in the stalk `𝒪_{Spf A, p}` is represented by an element of `CompletedAway A f.elem`
for some basic open neighbourhood `f` of `p`. -/
theorem exists_completedAway_rep (s : (Spf A).presheaf.stalk p) :
    ∃ (f : BasicNeighbourhood p) (x : CompletedAway A f.elem),
      (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).hom
        (colimit.ι (completedNeighbourhoodDiagram p) f x) = s := by
  obtain ⟨f, x, hx⟩ := Concrete.colimit_exists_rep (completedNeighbourhoodDiagram p)
    ((completedNeighbourhoodColimitIso p _ _).inv s)
  exact ⟨f, x, hx ▸ ConcreteCategory.congr_hom
    (completedNeighbourhoodColimitIso p _ _).inv_hom_id s⟩

/-- Every element of `A ∖ 𝔭` maps to a unit in the stalk `𝒪_{Spf A, p}`. -/
theorem isUnit_toStalk {a : A} (ha : a ∉ (p : PrimeSpectrum A).asIdeal) :
    IsUnit (toStalk p a) := by
  rw [toStalk_eq_germ p ⟨a, ha⟩ a]
  exact ((CompletedAway.isUnit_algebraMap_self A a).map _).map _

/-- `localizationToStalk p` extends `toStalk p` along `A → A_𝔭`. -/
@[simp]
theorem localizationToStalk_algebraMap_eq_toStalk (a : A) :
    localizationToStalk p (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) a) =
      toStalk p a := by
  rw [localizationToStalk_algebraMap p ⊥ a, toStalk_eq_germ p ⊥ a]

/-- The composite `A → A_𝔭 → 𝒪_{Spf A, p}` is `toStalk p`. -/
@[simp]
theorem localizationToStalk_comp_algebraMap :
    (localizationToStalk p).comp
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) =
      toStalk p :=
  RingHom.ext (localizationToStalk_algebraMap_eq_toStalk p)

/-- Through the identification of the stalk with `colim_{f ∉ 𝔭} A_{f}`, `localizationToStalk p`
sends an element of `A_f` (`f ∉ 𝔭`) to its image from the completed localisation `A_{f}`. -/
theorem localizationToStalk_away (f : BasicNeighbourhood p)
    (y : Localization.Away f.elem) :
    localizationToStalk p
        ((p : PrimeSpectrum A).asIdeal.localizationAwayToAtPrime f.elem f.notMem y) =
      (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).hom
        (colimit.ι (completedNeighbourhoodDiagram p) f
          (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) y)) := by
  let lhs : Localization.Away f.elem →+* (Spf A).presheaf.stalk p :=
    (localizationToStalk p).comp
      ((p : PrimeSpectrum A).asIdeal.localizationAwayToAtPrime f.elem f.notMem)
  let rhs : Localization.Away f.elem →+* (Spf A).presheaf.stalk p :=
    ((completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1).hom.hom.comp
      (colimit.ι (completedNeighbourhoodDiagram p) f).hom).comp
      (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem))
  refine RingHom.congr_fun
    (IsLocalization.ringHom_ext (Submonoid.powers f.elem) (j := lhs) (k := rhs)
      (RingHom.ext fun a ↦ ?_)) y
  have hl : lhs (algebraMap A _ a) = toStalk p a := by
    simp only [lhs, RingHom.comp_apply, Ideal.localizationAwayToAtPrime_algebraMap,
      localizationToStalk_algebraMap_eq_toStalk]
  have hr : rhs (algebraMap A _ a) =
      (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).hom
        (colimit.ι (completedNeighbourhoodDiagram p) f
          (algebraMap A (CompletedAway A f.elem) a)) :=
    congrArg ((completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).hom.hom.comp
        (colimit.ι (completedNeighbourhoodDiagram p) f).hom)
      (IsScalarTower.algebraMap_apply A (Localization.Away f.elem) (CompletedAway A f.elem) a).symm
  exact hl.trans ((toStalk_eq_completedNeighbourhoodColimitIso p f a).trans hr.symm)

/-- Pushing an ideal of `A` to `A_𝔭` and then along `localizationToStalk p` agrees with pushing
it along `toStalk p`. -/
@[simp]
theorem map_localizationToStalk_map (J : Ideal A) :
    (J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (localizationToStalk p) =
      J.map (toStalk p) := by
  rw [Ideal.map_map, localizationToStalk_comp_algebraMap]

/-- The stalks of the formal spectrum of a noetherian adic ring are noetherian (EGA I, Ch. 0,
7.6.17; Ch. I, 10.1.6). -/
instance isNoetherianRing_stalk [IsNoetherianRing A] :
    IsNoetherianRing ((Spf A).presheaf.stalk p) :=
  isNoetherianRing_of_ringEquiv _ (colimitIso p).commRingCatIsoToRingEquiv

/-- For a noetherian adic ring `A`, the map `A_𝔭 → O_{Spf A, p}` is flat. -/
theorem flat_localizationToStalk [IsNoetherianRing A] : (localizationToStalk p).Flat :=
  (flat_fromLocalization p).comp
    (RingHom.Flat.of_bijective (colimitIso p).commRingCatIsoToRingEquiv.bijective)

/-- The maximal ideal of `A_𝔭` generates the maximal ideal of the stalk `O_{Spf A, p}`: the closed
fibre of `A_𝔭 → O_{Spf A, p}` is the residue field of the stalk. -/
theorem map_maximalIdeal_localizationToStalk :
    (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)).map
        (localizationToStalk p) =
      maximalIdeal ((Spf A).presheaf.stalk p) := by
  rw [localizationToStalk, ← Ideal.map_map, map_maximalIdeal_fromLocalization]
  exact map_maximalIdeal_of_surjective _ (colimitIso p).commRingCatIsoToRingEquiv.surjective

/-- The map `A_𝔭 → O_{Spf A, p}` is a local homomorphism. -/
instance isLocalHom_localizationToStalk : IsLocalHom (localizationToStalk p) :=
  ((local_hom_tfae (localizationToStalk p)).out 1 3).mpr
    (map_maximalIdeal_localizationToStalk p).le

/-- For noetherian `A`, `A_𝔭 → 𝒪_{Spf A, p}` is faithfully flat. -/
theorem faithfullyFlat_localizationToStalk [IsNoetherianRing A] :
    (localizationToStalk p).FaithfullyFlat := by
  algebraize [localizationToStalk p]
  have : Module.Flat _ _ := flat_localizationToStalk p
  have : IsLocalHom (algebraMap _ ((Spf A).presheaf.stalk p)) := isLocalHom_localizationToStalk p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The map `A_𝔭 → O_{Spf A, p}` as an algebra structure, used to apply results about flat
algebras to it. -/
private noncomputable abbrev localizationToStalkAlgebra :
    Algebra (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ((Spf A).presheaf.stalk p) :=
  (localizationToStalk p).toAlgebra

attribute [local instance] localizationToStalkAlgebra

private theorem flat_localizationToStalkAlgebra [IsNoetherianRing A] :
    Module.Flat (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ((Spf A).presheaf.stalk p) :=
  flat_localizationToStalk p

attribute [local instance] flat_localizationToStalkAlgebra

/-- The stalk of the formal spectrum of a noetherian adic ring `A` at an open prime `𝔭` has the
Krull dimension of `A_𝔭`. -/
theorem ringKrullDim_stalk [IsNoetherianRing A] :
    ringKrullDim ((Spf A).presheaf.stalk p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq (map_maximalIdeal_localizationToStalk p)

/-- The stalk of the formal spectrum of a noetherian adic ring `A` at an open prime `𝔭` has
Krull dimension the height of `𝔭`. -/
theorem ringKrullDim_stalk_eq_height [IsNoetherianRing A] :
    ringKrullDim ((Spf A).presheaf.stalk p) = (p : PrimeSpectrum A).asIdeal.height :=
  (ringKrullDim_stalk p).trans (IsLocalization.AtPrime.ringKrullDim_eq_height _ _)

/-- The stalk of the formal spectrum of a noetherian adic ring `A` at an open prime `𝔭` is a
regular local ring if and only if `A_𝔭` is. -/
theorem isRegularLocalRing_stalk_iff [IsNoetherianRing A] :
    IsRegularLocalRing ((Spf A).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq (map_maximalIdeal_localizationToStalk p)

/-- The stalk of the formal spectrum of a noetherian adic ring `A` at an open prime `𝔭` is a
Cohen–Macaulay local ring if and only if `A_𝔭` is. -/
theorem isCohenMacaulay_stalk_iff [IsNoetherianRing A] :
    Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_localizationToStalk p)

end TauCeti.FormalScheme.Spf
