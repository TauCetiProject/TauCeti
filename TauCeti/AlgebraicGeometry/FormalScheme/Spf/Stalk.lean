/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood.Noetherian
public import TauCeti.RingTheory.CohenMacaulay.Basic

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Ideal
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Flat.Tower

/-!
# Stalks of `Spf A`, localisations of `A`, and completed localisations

Let `A` be an adic ring of finite ideal type with an ideal of definition `I`, and let `p` be an
open prime of `A`, i.e. a point of the formal spectrum `Spf A` corresponding to a prime ideal
`𝔭 ⊇ I`. This file compares the three local rings attached to `p`:

* the ordinary localisation `A_𝔭 = Localization.AtPrime 𝔭`,
* the stalk `𝒪_{Spf A, p} = (Spf A).presheaf.stalk p ≃ colim_{f ∉ 𝔭} A_{f}`, and
* the `I`-adic completion `Â_𝔭 = LocalCompletion p` of `A_𝔭` along `I A_𝔭`.

They fit into a canonical triangle of ring homomorphisms `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` whose composite
is the completion map `A_𝔭 → Â_𝔭`. Without any noetherianity hypothesis (and for any ideal of
definition `I`, not necessarily finitely generated), every step induces isomorphisms modulo `I ^ n`
for all `n` (matching `(A ⧸ I ^ n)_{𝔭 / I ^ n}` for `n ≥ 1`), so the `I`-adic completion of
`𝒪_{Spf A, p}` is canonically isomorphic to `Â_𝔭`, both maps are local homomorphisms sending maximal
ideals onto maximal ideals, and all three local rings have canonically isomorphic maximal-ideal-adic
completions.

When `A` is noetherian, `𝒪_{Spf A, p}` is noetherian, both `A_𝔭 → 𝒪_{Spf A, p}` and
`𝒪_{Spf A, p} → Â_𝔭` are faithfully flat (flatness of `A_𝔭 → 𝒪_{Spf A, p}` descends from
`A_𝔭 → Â_𝔭` along the faithfully flat map `𝒪_{Spf A, p} → Â_𝔭`), and the shared maximal-ideal-adic
completion implies that `A_𝔭`, `𝒪_{Spf A, p}`, and `Â_𝔭` have the same Krull dimension, and agree
with respect to regularity and the Cohen–Macaulay property.

## Main definitions

* `TauCeti.FormalScheme.Spf.localCompletionIdealEquiv`: independence of `LocalCompletion p` from the
  ideal of definition.
* `TauCeti.FormalScheme.Spf.toStalk`: the canonical map `A → 𝒪_{Spf A, p}` via global sections.
* `TauCeti.FormalScheme.Spf.localizationToStalk`: the canonical map `A_𝔭 → 𝒪_{Spf A, p}`.
* `TauCeti.FormalScheme.Spf.stalkToLocalCompletion`,
  `TauCeti.FormalScheme.Spf.stalkToAdicCompletion`: the canonical maps `𝒪_{Spf A, p} → Â_𝔭`.
* `TauCeti.FormalScheme.Spf.localizationQuotientIdealEquiv`,
  `TauCeti.FormalScheme.Spf.localizationQuotientEquivStalkQuotient`,
  `TauCeti.FormalScheme.Spf.stalkQuotientEquivAdicCompletionQuotient`,
  `TauCeti.FormalScheme.Spf.stalkQuotientPowEquivLocalizationQuotient`: isomorphisms between the
  quotients of `A_𝔭`, `𝒪_{Spf A, p}`, and `Â_𝔭` modulo `I ^ n`, and `(A ⧸ I ^ n)_{𝔭 / I ^ n}` for
  `n ≥ 1`.
* `TauCeti.FormalScheme.Spf.stalkAdicCompletionEquiv`,
  `TauCeti.FormalScheme.Spf.stalkLocalCompletionEquiv`: the `I`-adic completion of `𝒪_{Spf A, p}` is
  `Â_𝔭`.
* `TauCeti.FormalScheme.Spf.localizationMaximalCompletionEquivStalk`,
  `TauCeti.FormalScheme.Spf.stalkMaximalCompletionEquivLocalCompletion`,
  `TauCeti.FormalScheme.Spf.localizationMaximalCompletionEquivLocalCompletion`: the canonical
  isomorphisms between the maximal-ideal-adic completions of `A_𝔭`, `𝒪_{Spf A, p}`, and `Â_𝔭`.

## Main results

* `TauCeti.FormalScheme.Spf.isLocalRing_localCompletion`,
  `TauCeti.FormalScheme.Spf.maximalIdeal_localCompletion`,
  `TauCeti.FormalScheme.Spf.isLocalHom_algebraMap_localCompletion`: `LocalCompletion p` is a local
  ring with maximal ideal `𝔭 Â_𝔭`, and `A_𝔭 → Â_𝔭` is local.
* `TauCeti.FormalScheme.Spf.quotientMap_localizationToStalk_bijective`,
  `TauCeti.FormalScheme.Spf.quotientMap_stalkToAdicCompletion_bijective`: the maps
  `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` induce bijections modulo `I ^ n` for all `n`.
* `TauCeti.FormalScheme.Spf.isLocalHom_localizationToStalk`,
  `TauCeti.FormalScheme.Spf.map_maximalIdeal_localizationToStalk`,
  `TauCeti.FormalScheme.Spf.isLocalHom_stalkToLocalCompletion`,
  `TauCeti.FormalScheme.Spf.map_maximalIdeal_stalkToLocalCompletion`: both maps are local and extend
  maximal ideals to maximal ideals.
* `TauCeti.FormalScheme.Spf.stalk_isNoetherianRing`,
  `TauCeti.FormalScheme.Spf.flat_localizationToStalk`,
  `TauCeti.FormalScheme.Spf.faithfullyFlat_localizationToStalk`,
  `TauCeti.FormalScheme.Spf.flat_stalkToLocalCompletion`,
  `TauCeti.FormalScheme.Spf.faithfullyFlat_stalkToLocalCompletion`: when `A` is noetherian, the
  stalk is noetherian and the maps `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` are faithfully flat.
* `TauCeti.FormalScheme.Spf.ringKrullDim_stalk_eq_localization`,
  `TauCeti.FormalScheme.Spf.isRegularLocalRing_stalk_iff_localization`,
  `TauCeti.FormalScheme.Spf.isCohenMacaulay_stalk_iff_localization` (and their counterparts
  involving `LocalCompletion p`): Krull dimension, regularity, and Cohen–Macaulayness agree among
  `A_𝔭`, `𝒪_{Spf A, p}`, and `Â_𝔭`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.6 (7.6.17) and
  Ch. I, §10.1 (10.1.5–10.1.6).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY),
  [Tag 07NX](https://stacks.math.columbia.edu/tag/07NX).
-/

public section

universe u

open CategoryTheory Limits Topology TopologicalSpace Opposite AlgebraicGeometry IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

section QuotientLocalization

variable {A : Type u} [CommRing A] [TopologicalSpace A] (p : carrier A)

/-- For an ideal of definition `J`, the image of `A ∖ 𝔭` in `A ⧸ J` is the complement of the image
prime `𝔭 / J`. -/
private theorem algebraMapSubmonoid_primeCompl_eq {J : Ideal A} (hJ : IsAdic J) :
    Algebra.algebraMapSubmonoid (A ⧸ J) (p : PrimeSpectrum A).asIdeal.primeCompl =
      (homeomorphSpecQuotient hJ p).asIdeal.primeCompl := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.mem_primeCompl_iff, homeomorphSpecQuotient_apply_asIdeal]
  have hmem (c : A) : Ideal.Quotient.mk J c ∈ (p : PrimeSpectrum A).asIdeal.map
      (Ideal.Quotient.mk J) ↔ c ∈ (p : PrimeSpectrum A).asIdeal := by
    change c ∈ ((p : PrimeSpectrum A).asIdeal.map (Ideal.Quotient.mk J)).comap
      (Ideal.Quotient.mk J) ↔ _
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr ((mem_carrier_iff_le hJ).mp p.2)]
  constructor
  · rintro ⟨b, hb, hba⟩ h
    exact hb ((hmem b).mp (hba.symm ▸ h))
  · intro ha
    exact ⟨a, fun h ↦ ha ((hmem a).mpr h), rfl⟩

/-- For any ideal of definition `I` and open prime `p`, the extension `I A_𝔭` lies in the maximal
ideal of `A_𝔭`. -/
theorem map_ideal_le_maximalIdeal_atPrime {I : Ideal A} (hI : IsAdic I) :
    I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono ((mem_carrier_iff_le hI).mp p.2)

/-- The completion of `A_𝔭` along any ideal of definition `I` is a local ring. -/
theorem isLocalRing_adicCompletion_atPrime {I : Ideal A} (hI : IsAdic I) :
    IsLocalRing (AdicCompletion
      (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :=
  TauCeti.AdicCompletion.isLocalRing_of_le_maximalIdeal (map_ideal_le_maximalIdeal_atPrime p hI)

/-- For an ideal of definition `J` of `A` and an open prime `p`, the localisation of `A ⧸ J` at the
image prime `𝔭 / J` is canonically isomorphic to `A_𝔭 ⧸ J A_𝔭`. -/
noncomputable def localizationQuotientIdealEquiv {J : Ideal A} (hJ : IsAdic J) :
    Localization.AtPrime (homeomorphSpecQuotient hJ p).asIdeal ≃ₐ[A ⧸ J]
      Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
        J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) := by
  have : IsLocalization (homeomorphSpecQuotient hJ p).asIdeal.primeCompl
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
        J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) := by
    rw [← algebraMapSubmonoid_primeCompl_eq p hJ]
    infer_instance
  exact IsLocalization.algEquiv (homeomorphSpecQuotient hJ p).asIdeal.primeCompl _ _

end QuotientLocalization

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-! ### Completed localisations: ideal independence and local ring structure -/

section LocalCompletion

/-- The canonical `A_𝔭`-algebra isomorphism from `LocalCompletion p` (formed with the chosen ideal
of definition) to the completion of `A_𝔭` along any ideal of definition `I`. -/
noncomputable def localCompletionIdealEquiv {I : Ideal A} (hI : IsAdic I) :
    LocalCompletion p ≃ₐ[Localization.AtPrime (p : PrimeSpectrum A).asIdeal]
      AdicCompletion
        (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  AdicCompletion.equivOfExistsPowLe
    (by
      obtain ⟨m, hm⟩ :=
        (IsAdicRing.ideal_spec A).2.1.exists_pow_succ_le (pow_one I ▸ hI.isOpen_pow 1)
      exact ⟨m + 1, (Ideal.map_pow _ _ _).symm.trans_le (Ideal.map_mono hm)⟩)
    (by
      obtain ⟨k, hk⟩ :=
        hI.exists_pow_succ_le
          (pow_one (IsAdicRing.ideal A) ▸ (IsAdicRing.ideal_spec A).2.1.isOpen_pow 1)
      exact ⟨k + 1, (Ideal.map_pow _ _ _).symm.trans_le (Ideal.map_mono hk)⟩)

/-- Comparing `LocalCompletion p` with the completion along the chosen ideal of definition is the
identity. -/
@[simp]
theorem localCompletionIdealEquiv_self :
    localCompletionIdealEquiv p (IsAdicRing.ideal_spec A).2.1 = AlgEquiv.refl := by
  unfold localCompletionIdealEquiv
  exact AdicCompletion.equivOfExistsPowLe_self _

/-- The completed localisation `Â_𝔭 = LocalCompletion p` is a local ring. -/
instance isLocalRing_localCompletion : IsLocalRing (LocalCompletion p) :=
  isLocalRing_adicCompletion_atPrime p (IsAdicRing.ideal_spec A).2.1

/-- The maximal ideal of `LocalCompletion p` is the extension of the maximal ideal of `A_𝔭`. -/
theorem maximalIdeal_localCompletion :
    maximalIdeal (LocalCompletion p) =
      (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)).map
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) :=
  TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le_maximalIdeal
    (map_ideal_le_maximalIdeal_atPrime p (IsAdicRing.ideal_spec A).2.1)
    ((IsAdicRing.ideal_spec A).1.map _)

/-- The canonical completion map `A_𝔭 → LocalCompletion p` is a local homomorphism. -/
theorem isLocalHom_algebraMap_localCompletion :
    IsLocalHom
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) :=
  TauCeti.AdicCompletion.algebraMap_isLocalHom_of_le_maximalIdeal
    (map_ideal_le_maximalIdeal_atPrime p (IsAdicRing.ideal_spec A).2.1)

end LocalCompletion

/-! ### The canonical maps `A → A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` -/

section CanonicalMaps

/-- The canonical ring homomorphism `A → 𝒪_{Spf A, p}` sending `a ∈ A` to the germ at `p` of the
corresponding global section of `Spf A`. -/
noncomputable def toStalk : A →+* (Spf A).presheaf.stalk p :=
  have := (IsAdicRing.ideal_spec A).2.2
  ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
    (Spf A).presheaf.germ ⊤ p trivial).hom

/-- Under the identification of the stalk with `colim_{f ∉ 𝔭} A_{f}`, `toStalk p a` is represented
in every basic open neighbourhood `D(f)` of `p` by `algebraMap A A_{f} a`. -/
theorem toStalk_eq_colimitIso_ι (f : BasicNeighbourhood p) (a : A) :
    toStalk p a = (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1).hom
      (colimit.ι (completedNeighbourhoodDiagram p) f
        (algebraMap A (CompletedAway A f.elem) a)) := by
  have := (IsAdicRing.ideal_spec A).2.2
  have h1 := globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f.elem
  have h2 := completedNeighbourhoodColimitIso_germ p
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
  have hgerm : (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
      TopCat.Presheaf.germ (C := CommRingCat)
        (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj ⊤ p (Opens.mem_top p) =
      CommRingCat.ofHom (algebraMap A (CompletedAway A f.elem)) ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec A).1 f.elem).inv ≫
          TopCat.Presheaf.germ (C := CommRingCat)
            (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj
            (basicOpen f.elem) p (mem_basicOpen.mpr f.notMem) := by
    rw [← h1, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg _ (TopCat.Presheaf.germ_res
      (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj
      (homOfLE (le_top : basicOpen f.elem ≤ ⊤)) p (mem_basicOpen.mpr f.notMem)).symm
  exact (ConcreteCategory.congr_hom hgerm a).trans
    (ConcreteCategory.congr_hom h2 (algebraMap A (CompletedAway A f.elem) a)).symm

/-- The residue field isomorphism sends the residue class of `toStalk p a` to the image of `a` in
`Frac(A ⧸ 𝔭)`. -/
@[simp]
theorem stalkResidueFieldEquiv_residue_toStalk (a : A) :
    stalkResidueFieldEquiv p ((Spf A).residue p (toStalk p a)) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal)
        (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) (Ideal.Quotient.mk _ a) := by
  let f1 : BasicNeighbourhood p := ⟨1, (p : PrimeSpectrum A).asIdeal.one_notMem⟩
  have hgerm : toStalk p a =
      (Spf A).presheaf.germ (basicOpen f1.elem) p (mem_basicOpen.mpr f1.notMem)
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec A).1 f1.elem).inv
          (algebraMap A (CompletedAway A f1.elem) a)) :=
    (toStalk_eq_colimitIso_ι p f1 a).trans
      (ConcreteCategory.congr_hom
        (completedNeighbourhoodColimitIso_germ p (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec A).1 f1) (algebraMap A (CompletedAway A f1.elem) a))
  exact (congrArg (fun x ↦ stalkResidueFieldEquiv p ((Spf A).residue p x)) hgerm).trans
    (stalkResidueFieldEquiv_residue_germ f1 a)

/-- Every element `s ∉ 𝔭` maps to a unit in the stalk `𝒪_{Spf A, p}`. -/
private theorem isUnit_toStalk (s : (p : PrimeSpectrum A).asIdeal.primeCompl) :
    IsUnit (toStalk p s) := by
  rw [toStalk_eq_colimitIso_ι p ⟨s.1, s.2⟩ s.1]
  exact ((CompletedAway.isUnit_algebraMap_self A s.1).map
    (colimit.ι (completedNeighbourhoodDiagram p) ⟨s.1, s.2⟩).hom).map
    (completedNeighbourhoodColimitIso p _ _).hom.hom

/-- The canonical ring homomorphism `A_𝔭 → 𝒪_{Spf A, p}` from the localisation of `A` at `𝔭` to
the stalk of `Spf A` at `p`. -/
noncomputable def localizationToStalk :
    Localization.AtPrime (p : PrimeSpectrum A).asIdeal →+* (Spf A).presheaf.stalk p :=
  IsLocalization.lift (isUnit_toStalk p)

@[simp]
theorem localizationToStalk_algebraMap (a : A) :
    localizationToStalk p
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) a) =
      toStalk p a :=
  IsLocalization.lift_eq (isUnit_toStalk p) a

/-- On the image of an element of `A_f` inside `A_𝔭`, `localizationToStalk` agrees with the
colimit inclusion `A_f → A_{f} → 𝒪_{Spf A, p}`. -/
theorem localizationToStalk_map_away (f : BasicNeighbourhood p) (y : Localization.Away f.elem) :
    localizationToStalk p
        (IsLocalization.map (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (RingHom.id A)
          (Submonoid.powers_le.mpr f.notMem :
            Submonoid.powers f.elem ≤ (p : PrimeSpectrum A).asIdeal.primeCompl.comap (RingHom.id A))
          y) =
      (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).hom
        (colimit.ι (completedNeighbourhoodDiagram p) f
          (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) y)) := by
  let ιf : CompletedAway A f.elem →+* (Spf A).presheaf.stalk p :=
    (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1).hom.hom.comp
        (colimit.ι (completedNeighbourhoodDiagram p) f).hom
  let g₁ : Localization.Away f.elem →+* (Spf A).presheaf.stalk p :=
    (localizationToStalk p).comp
      (IsLocalization.map (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr f.notMem :
          Submonoid.powers f.elem ≤ (p : PrimeSpectrum A).asIdeal.primeCompl.comap (RingHom.id A)))
  let g₂ : Localization.Away f.elem →+* (Spf A).presheaf.stalk p :=
    ιf.comp (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem))
  have h : g₁ = g₂ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f.elem) (RingHom.ext fun a ↦ ?_)
    simp only [g₁, g₂, RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply,
      localizationToStalk_algebraMap, ← IsScalarTower.algebraMap_apply]
    exact toStalk_eq_colimitIso_ι p f a
  exact DFunLike.congr_fun h y

/-- The canonical ring homomorphism `𝒪_{Spf A, p} → LocalCompletion p` from the stalk of `Spf A`
at `p` to the completion `Â_𝔭` of `A_𝔭` along the chosen ideal of definition. -/
noncomputable def stalkToLocalCompletion :
    (Spf A).presheaf.stalk p →+* LocalCompletion p :=
  (colimitToLocalCompletion p).comp
    (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1).inv.hom

@[simp]
theorem stalkToLocalCompletion_colimitIso_hom
    (x : (colimit (completedNeighbourhoodDiagram p) : CommRingCat)) :
    stalkToLocalCompletion p
        ((completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec A).1).hom x) =
      colimitToLocalCompletion p x :=
  congrArg (colimitToLocalCompletion p)
    (ConcreteCategory.congr_hom (completedNeighbourhoodColimitIso p _ _).hom_inv_id x)

@[simp]
theorem stalkToLocalCompletion_toStalk (a : A) :
    stalkToLocalCompletion p (toStalk p a) = algebraMap A (LocalCompletion p) a := by
  rw [toStalk_eq_colimitIso_ι p ⟨1, (p : PrimeSpectrum A).asIdeal.one_notMem⟩ a,
    stalkToLocalCompletion_colimitIso_hom, colimitToLocalCompletion_ι_algebraMap]

/-- The composite `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` is the canonical completion map `A_𝔭 → Â_𝔭`. -/
@[simp]
theorem stalkToLocalCompletion_comp_localizationToStalk :
    (stalkToLocalCompletion p).comp (localizationToStalk p) =
      algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p) := by
  refine IsLocalization.ringHom_ext (p : PrimeSpectrum A).asIdeal.primeCompl
    (RingHom.ext fun a ↦ ?_)
  simp [← IsScalarTower.algebraMap_apply]

@[simp]
theorem stalkToLocalCompletion_localizationToStalk
    (y : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    stalkToLocalCompletion p (localizationToStalk p y) =
      algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p) y :=
  DFunLike.congr_fun (stalkToLocalCompletion_comp_localizationToStalk p) y

/-- The canonical ring homomorphism from the stalk `𝒪_{Spf A, p}` to the `I`-adic completion of
`A_𝔭`, for any ideal of definition `I`. -/
noncomputable def stalkToAdicCompletion {I : Ideal A} (hI : IsAdic I) :
    (Spf A).presheaf.stalk p →+*
      AdicCompletion
        (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (localCompletionIdealEquiv p hI).toRingHom.comp (stalkToLocalCompletion p)

@[simp]
theorem stalkToAdicCompletion_self :
    stalkToAdicCompletion p (IsAdicRing.ideal_spec A).2.1 = stalkToLocalCompletion p := by
  simp [stalkToAdicCompletion]

@[simp]
theorem stalkToAdicCompletion_comp_localizationToStalk {I : Ideal A} (hI : IsAdic I) :
    (stalkToAdicCompletion p hI).comp (localizationToStalk p) =
      algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (AdicCompletion
          (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
          (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) := by
  ext y
  simp [stalkToAdicCompletion]

@[simp]
theorem stalkToAdicCompletion_localizationToStalk {I : Ideal A} (hI : IsAdic I)
    (y : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    stalkToAdicCompletion p hI (localizationToStalk p y) =
      algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) _ y :=
  DFunLike.congr_fun (stalkToAdicCompletion_comp_localizationToStalk p hI) y

@[simp]
theorem stalkToAdicCompletion_toStalk {I : Ideal A} (hI : IsAdic I) (a : A) :
    stalkToAdicCompletion p hI (toStalk p a) =
      algebraMap A
        (AdicCompletion
          (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
          (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) a := by
  rw [← localizationToStalk_algebraMap, stalkToAdicCompletion_localizationToStalk,
    ← IsScalarTower.algebraMap_apply]

end CanonicalMaps

/-! ### Quotients modulo `I ^ n` and `I`-adic completion of the stalk -/

section IdealQuotients

/-- Pushing an ideal `I` of `A` from `A_𝔭` along `A_𝔭 → 𝒪_{Spf A, p}` gives `I 𝒪_{Spf A, p}`. -/
theorem map_localizationToStalk_ideal (I : Ideal A) :
    (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (localizationToStalk p) =
      I.map (toStalk p) := by
  rw [Ideal.map_map]
  congr 1
  ext a
  simp

/-- Pushing `I 𝒪_{Spf A, p}` along `𝒪_{Spf A, p} → Â_𝔭(I)` gives `(I A_𝔭) Â_𝔭(I)`. -/
theorem map_stalkToAdicCompletion_ideal {I : Ideal A} (hI : IsAdic I) :
    (I.map (toStalk p)).map (stalkToAdicCompletion p hI) =
      (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
          (AdicCompletion
            (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
            (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) := by
  rw [← map_localizationToStalk_ideal, Ideal.map_map,
    stalkToAdicCompletion_comp_localizationToStalk]

/-- Pushing `I 𝒪_{Spf A, p}` along `𝒪_{Spf A, p} → LocalCompletion p` gives `I Â_𝔭`. -/
theorem map_stalkToLocalCompletion_ideal (I : Ideal A) :
    (I.map (toStalk p)).map (stalkToLocalCompletion p) =
      (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) := by
  rw [← map_localizationToStalk_ideal, Ideal.map_map,
    stalkToLocalCompletion_comp_localizationToStalk]

/-- Every element of the stalk `𝒪_{Spf A, p}` is congruent modulo `(I 𝒪_{Spf A, p}) ^ n` to the
image of an element of `A_𝔭`, for any ideal of definition `I`. -/
theorem exists_sub_localizationToStalk_mem_pow {I : Ideal A} (hI : IsAdic I) (n : ℕ)
    (s : (Spf A).presheaf.stalk p) :
    ∃ y : Localization.AtPrime (p : PrimeSpectrum A).asIdeal,
      s - localizationToStalk p y ∈ (I.map (toStalk p)) ^ n := by
  let I₀ := IsAdicRing.ideal A
  have hI₀fg : I₀.FG := (IsAdicRing.ideal_spec A).1
  have hI₀ : IsAdic I₀ := (IsAdicRing.ideal_spec A).2.1
  obtain ⟨m, hm⟩ := hI₀.exists_pow_succ_le (pow_one I ▸ hI.isOpen_pow 1)
  let e := completedNeighbourhoodColimitIso p hI₀ hI₀fg
  obtain ⟨f, x, hx⟩ := Concrete.colimit_exists_rep (completedNeighbourhoodDiagram p) (e.inv s)
  let x' : CompletedAway A f.elem := x
  have hs : s = e.hom (colimit.ι (completedNeighbourhoodDiagram p) f x') := by
    rw [show colimit.ι (completedNeighbourhoodDiagram p) f x' = e.inv s from hx]
    exact (ConcreteCategory.congr_hom e.inv_hom_id s).symm
  -- Approximate `x' ∈ A_{f}` modulo `I₀ ^ ((m + 1) * n) ≤ I ^ n` by an element `z ∈ A_f`.
  let φ := CompletedAway.idealEquiv f.elem I₀ hI₀ hI₀fg
  obtain ⟨z, hz⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow (hI₀fg.map _) ((m + 1) * n)
    (φ x')
  rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hz
  have hz' : x' - algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) z ∈
      (I₀ ^ ((m + 1) * n)).map (algebraMap A (CompletedAway A f.elem)) := by
    let φ' : AdicCompletion (I₀.map (algebraMap A (Localization.Away f.elem)))
        (Localization.Away f.elem) →+* CompletedAway A f.elem := φ.symm.toRingEquiv.toRingHom
    have hmem := Ideal.mem_map_of_mem φ' hz
    rw [map_sub, Ideal.map_map,
      show φ' (φ x') = x' from φ.symm_apply_apply x',
      show φ' (algebraMap (Localization.Away f.elem) _ z) =
        algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) z from
        CompletedAway.idealEquiv_symm_algebraMap_away f.elem I₀ hI₀ hI₀fg z,
      show φ'.comp (algebraMap A _) = algebraMap A (CompletedAway A f.elem) from
        RingHom.ext fun a ↦ φ.symm.commutes a] at hmem
    exact hmem
  -- Push the approximation into the stalk along `colimit.ι _ f` and `e.hom`.
  let ψ : CompletedAway A f.elem →+* (Spf A).presheaf.stalk p :=
    e.hom.hom.comp (colimit.ι (completedNeighbourhoodDiagram p) f).hom
  refine ⟨IsLocalization.map (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (RingHom.id A)
    (Submonoid.powers_le.mpr f.notMem :
      Submonoid.powers f.elem ≤ (p : PrimeSpectrum A).asIdeal.primeCompl.comap (RingHom.id A))
    z, ?_⟩
  have hmem := Ideal.mem_map_of_mem ψ hz'
  rw [map_sub, Ideal.map_map,
    show ψ.comp (algebraMap A (CompletedAway A f.elem)) = toStalk p from
      RingHom.ext fun a ↦ (toStalk_eq_colimitIso_ι p f a).symm] at hmem
  rw [hs, localizationToStalk_map_away, ← Ideal.map_pow]
  exact Ideal.map_mono ((pow_mul I₀ (m + 1) n).symm ▸ Ideal.pow_right_mono hm n) hmem

/-- For every ideal of definition `I` and every `n`, the map `A_𝔭 → 𝒪_{Spf A, p}` induces a
bijection `A_𝔭 ⧸ (I A_𝔭) ^ n → 𝒪_{Spf A, p} ⧸ (I 𝒪_{Spf A, p}) ^ n`. -/
theorem quotientMap_localizationToStalk_bijective {I : Ideal A} (hI : IsAdic I) (n : ℕ)
    {H : (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ n ≤
      ((I.map (toStalk p)) ^ n).comap (localizationToStalk p)} :
    Function.Bijective (Ideal.quotientMap ((I.map (toStalk p)) ^ n) (localizationToStalk p) H) := by
  refine ⟨Ideal.quotientMap_injective' fun y hy ↦ ?_, fun x ↦ ?_⟩
  · have hmem := Ideal.mem_map_of_mem (stalkToAdicCompletion p hI) hy
    rw [Ideal.map_pow, map_stalkToAdicCompletion_ideal, ← Ideal.map_pow,
      stalkToAdicCompletion_localizationToStalk] at hmem
    exact (AdicCompletion.algebraMap_mem_map_pow_iff n).mp hmem
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := exists_sub_localizationToStalk_mem_pow p hI n s
    exact ⟨Ideal.Quotient.mk _ y, (Ideal.Quotient.eq.mpr hy).symm⟩

private theorem quotientMap_algebraMap_adicCompletion_bijective {I : Ideal A} (hI : IsAdic I)
    (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        (((I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
          (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
            (AdicCompletion
              (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
              (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))) ^ n)
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
          (AdicCompletion
            (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
            (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
        (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])) := by
  refine ⟨Ideal.quotientMap_injective' fun y hy ↦ ?_, fun x ↦ ?_⟩
  · rw [Ideal.mem_comap, ← Ideal.map_pow] at hy
    exact (AdicCompletion.algebraMap_mem_map_pow_iff n).mp hy
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨m, hm⟩ :=
      (IsAdicRing.ideal_spec A).2.1.exists_pow_succ_le (pow_one I ▸ hI.isOpen_pow 1)
    let e := localCompletionIdealEquiv p hI
    obtain ⟨y, hy⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow
      ((IsAdicRing.ideal_spec A).1.map _) ((m + 1) * n) (e.symm x)
    have hmem : e (e.symm x - algebraMap _ _ y) ∈
        ((((IsAdicRing.ideal A).map
          (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ ((m + 1) * n)).map
            (algebraMap _ (LocalCompletion p))).map e.toRingHom :=
      Ideal.mem_map_of_mem e.toRingHom hy
    rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, Ideal.map_map,
      show e.toRingHom.comp (algebraMap _ _) = algebraMap _ _ from
        RingHom.ext fun z ↦ e.commutes z] at hmem
    have hle : ((IsAdicRing.ideal A).map
          (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ ((m + 1) * n) ≤
        (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ n := by
      rw [pow_mul]
      exact Ideal.pow_right_mono ((Ideal.map_pow _ _ _).symm.trans_le (Ideal.map_mono hm)) n
    have hmem' := Ideal.map_mono hle hmem
    rw [Ideal.map_pow] at hmem'
    exact ⟨Ideal.Quotient.mk _ y, (Ideal.Quotient.eq.mpr hmem').symm⟩

/-- For every ideal of definition `I` and every `n`, the map `𝒪_{Spf A, p} → Â_𝔭(I)` induces a
bijection `𝒪_{Spf A, p} ⧸ (I 𝒪_{Spf A, p}) ^ n → Â_𝔭(I) ⧸ (I Â_𝔭(I)) ^ n`. -/
theorem quotientMap_stalkToAdicCompletion_bijective {I : Ideal A} (hI : IsAdic I) (n : ℕ)
    {H : (I.map (toStalk p)) ^ n ≤
      (((I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
          (AdicCompletion
            (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
            (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))) ^ n).comap
        (stalkToAdicCompletion p hI)} :
    Function.Bijective (Ideal.quotientMap _ (stalkToAdicCompletion p hI) H) := by
  have hH₁ : (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ n ≤
      ((I.map (toStalk p)) ^ n).comap (localizationToStalk p) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_localizationToStalk_ideal]
  have hcomp : (Ideal.quotientMap _ (stalkToAdicCompletion p hI) H).comp
      (Ideal.quotientMap _ (localizationToStalk p) hH₁) =
      Ideal.quotientMap _ (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) _)
        (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]) := by
    ext y
    simp
  have hbij := quotientMap_algebraMap_adicCompletion_bijective p hI n
  rw [← hcomp] at hbij
  have h1 := quotientMap_localizationToStalk_bijective p hI n (H := hH₁)
  refine ⟨fun x y hxy ↦ ?_, Function.Surjective.of_comp hbij.2⟩
  obtain ⟨a, rfl⟩ := h1.2 x
  obtain ⟨b, rfl⟩ := h1.2 y
  exact congrArg _ (hbij.1 hxy)

/-- For the chosen ideal of definition `I`, `𝒪_{Spf A, p} → LocalCompletion p` induces a bijection
modulo `I ^ n` for every `n`. -/
theorem quotientMap_stalkToLocalCompletion_bijective (n : ℕ)
    {H : ((IsAdicRing.ideal A).map (toStalk p)) ^ n ≤
      ((((IsAdicRing.ideal A).map
          (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
          (LocalCompletion p))) ^ n).comap (stalkToLocalCompletion p)} :
    Function.Bijective (Ideal.quotientMap _ (stalkToLocalCompletion p) H) := by
  have h := quotientMap_stalkToAdicCompletion_bijective p
    (IsAdicRing.ideal_spec A).2.1 n
    (H := by simpa only [stalkToAdicCompletion_self] using H)
  simpa only [stalkToAdicCompletion_self] using h

/-- The canonical ring isomorphism `A_𝔭 ⧸ (I A_𝔭) ^ n ≃+* 𝒪_{Spf A, p} ⧸ (I 𝒪_{Spf A, p}) ^ n`. -/
noncomputable def localizationQuotientEquivStalkQuotient {I : Ideal A} (hI : IsAdic I) (n : ℕ) :
    Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
        (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ n ≃+*
      (Spf A).presheaf.stalk p ⧸ (I.map (toStalk p)) ^ n :=
  RingEquiv.ofBijective
    (Ideal.quotientMap ((I.map (toStalk p)) ^ n) (localizationToStalk p)
      (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_localizationToStalk_ideal]))
    (quotientMap_localizationToStalk_bijective p hI n)

@[simp]
theorem localizationQuotientEquivStalkQuotient_mk {I : Ideal A} (hI : IsAdic I) (n : ℕ)
    (y : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    localizationQuotientEquivStalkQuotient p hI n (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (localizationToStalk p y) := by
  simp [localizationQuotientEquivStalkQuotient]

/-- The canonical ring isomorphism
`𝒪_{Spf A, p} ⧸ (I 𝒪_{Spf A, p}) ^ n ≃+* Â_𝔭(I) ⧸ (I Â_𝔭(I)) ^ n`. -/
noncomputable def stalkQuotientEquivAdicCompletionQuotient {I : Ideal A} (hI : IsAdic I) (n : ℕ) :
    (Spf A).presheaf.stalk p ⧸ (I.map (toStalk p)) ^ n ≃+*
      AdicCompletion
        (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ⧸
        ((I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
          (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
            (AdicCompletion
              (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
              (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))) ^ n :=
  RingEquiv.ofBijective
    (Ideal.quotientMap _ (stalkToAdicCompletion p hI)
      (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_stalkToAdicCompletion_ideal]))
    (quotientMap_stalkToAdicCompletion_bijective p hI n)

@[simp]
theorem stalkQuotientEquivAdicCompletionQuotient_mk {I : Ideal A} (hI : IsAdic I) (n : ℕ)
    (s : (Spf A).presheaf.stalk p) :
    stalkQuotientEquivAdicCompletionQuotient p hI n (Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ (stalkToAdicCompletion p hI s) := by
  simp [stalkQuotientEquivAdicCompletionQuotient]

/-- For `n ≥ 1`, the quotient `𝒪_{Spf A, p} ⧸ (I 𝒪_{Spf A, p}) ^ n` is canonically isomorphic to
the localisation `(A ⧸ I ^ n)_{𝔭 / I ^ n}` of the thickening `A ⧸ I ^ n` at `𝔭 / I ^ n`. -/
noncomputable def stalkQuotientPowEquivLocalizationQuotient {I : Ideal A} (hI : IsAdic I)
    {n : ℕ} (hn : 0 < n) :
    (Spf A).presheaf.stalk p ⧸ (I.map (toStalk p)) ^ n ≃+*
      Localization.AtPrime (homeomorphSpecQuotient (is_ideal_adic_pow hI hn) p).asIdeal :=
  (localizationQuotientEquivStalkQuotient p hI n).symm.trans
    ((Ideal.quotEquivOfEq (Ideal.map_pow _ _ _).symm).trans
      (localizationQuotientIdealEquiv p (is_ideal_adic_pow hI hn)).toRingEquiv.symm)

@[simp]
theorem stalkQuotientPowEquivLocalizationQuotient_mk_toStalk {I : Ideal A} (hI : IsAdic I)
    {n : ℕ} (hn : 0 < n) (a : A) :
    stalkQuotientPowEquivLocalizationQuotient p hI hn (Ideal.Quotient.mk _ (toStalk p a)) =
      algebraMap (A ⧸ I ^ n) _ (Ideal.Quotient.mk (I ^ n) a) := by
  rw [← localizationToStalk_algebraMap, ← localizationQuotientEquivStalkQuotient_mk p hI n]
  simp only [stalkQuotientPowEquivLocalizationQuotient, RingEquiv.trans_apply,
    RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
  exact (localizationQuotientIdealEquiv p (is_ideal_adic_pow hI hn)).symm_apply_eq.mpr
    ((localizationQuotientIdealEquiv p (is_ideal_adic_pow hI hn)).commutes
      (Ideal.Quotient.mk _ a)).symm

/-- `localizationToStalk` viewed as a `ℤ`-algebra homomorphism using the canonical `ℤ`-algebra
instances on both sides. -/
private noncomputable def localizationToStalkIntAlgHom :
    Localization.AtPrime (p : PrimeSpectrum A).asIdeal →ₐ[ℤ] (Spf A).presheaf.stalk p :=
  { localizationToStalk p with
    commutes' n := by
      change localizationToStalk p (algebraMap ℤ _ n) = algebraMap ℤ _ n
      rw [eq_intCast, eq_intCast, map_intCast] }

/-- The `I`-adic completion of the stalk `𝒪_{Spf A, p}` is canonically isomorphic to the `I`-adic
completion `Â_𝔭(I)` of `A_𝔭`. -/
noncomputable def stalkAdicCompletionEquiv {I : Ideal A} (hI : IsAdic I) :
    AdicCompletion (I.map (toStalk p)) ((Spf A).presheaf.stalk p) ≃+*
      AdicCompletion
        (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (RingEquiv.ofBijective
    (AdicCompletion.mapₐ (localizationToStalkIntAlgHom p)
      (by
        change I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
          (I.map (toStalk p)).comap (localizationToStalk p)
        rw [← Ideal.map_le_iff_le_comap, map_localizationToStalk_ideal])).toRingHom
    (AdicCompletion.mapₐ_bijective (localizationToStalkIntAlgHom p)
      (by
        change I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
          (I.map (toStalk p)).comap (localizationToStalk p)
        rw [← Ideal.map_le_iff_le_comap, map_localizationToStalk_ideal])
      (fun n ↦ quotientMap_localizationToStalk_bijective p hI n))).symm

@[simp]
theorem stalkAdicCompletionEquiv_symm_of {I : Ideal A} (hI : IsAdic I)
    (y : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    (stalkAdicCompletionEquiv p hI).symm (AdicCompletion.of _ _ y) =
      AdicCompletion.of (I.map (toStalk p)) ((Spf A).presheaf.stalk p)
        (localizationToStalk p y) :=
  AdicCompletion.mapₐ_of (localizationToStalkIntAlgHom p) _ y

/-- On elements of the stalk, `stalkAdicCompletionEquiv` agrees with `stalkToAdicCompletion`. -/
@[simp]
theorem stalkAdicCompletionEquiv_of {I : Ideal A} (hI : IsAdic I)
    (s : (Spf A).presheaf.stalk p) :
    stalkAdicCompletionEquiv p hI
        (AdicCompletion.of (I.map (toStalk p)) ((Spf A).presheaf.stalk p) s) =
      stalkToAdicCompletion p hI s := by
  refine (stalkAdicCompletionEquiv p hI).symm.injective ?_
  rw [RingEquiv.symm_apply_apply]
  refine (AdicCompletion.ext_evalₐ fun n ↦ ?_).symm
  obtain ⟨y, hy⟩ := exists_sub_localizationToStalk_mem_pow p hI n s
  have heval : AdicCompletion.evalₐ
      (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) n
      (stalkToAdicCompletion p hI s) = Ideal.Quotient.mk _ y := by
    have hmem : stalkToAdicCompletion p hI s -
        algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) _ y ∈
        ((I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ n).map
          (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) _) := by
      have h := Ideal.mem_map_of_mem (stalkToAdicCompletion p hI) hy
      rw [map_sub, stalkToAdicCompletion_localizationToStalk, Ideal.map_pow,
        map_stalkToAdicCompletion_ideal, ← Ideal.map_pow] at h
      exact h
    have hker :
        ((I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ^ n).map
          (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) _) ≤
        RingHom.ker (AdicCompletion.evalₐ
          (I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) n) := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      simp [Ideal.Quotient.eq_zero_iff_mem, hz]
    have heq := hker hmem
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at heq
    exact heq.trans (AdicCompletion.evalₐ_of _ n y)
  change AdicCompletion.evalₐ _ n
    (AdicCompletion.mapₐ (localizationToStalkIntAlgHom p) _
      (stalkToAdicCompletion p hI s)) = _
  rw [AdicCompletion.evalₐ_mapₐ, heval, Ideal.quotientMap_mk, AdicCompletion.evalₐ_of]
  exact (Ideal.Quotient.eq.mpr hy).symm

/-- The completion of the stalk `𝒪_{Spf A, p}` along the chosen ideal of definition is canonically
isomorphic to `LocalCompletion p`. -/
noncomputable def stalkLocalCompletionEquiv :
    AdicCompletion ((IsAdicRing.ideal A).map (toStalk p)) ((Spf A).presheaf.stalk p) ≃+*
      LocalCompletion p :=
  stalkAdicCompletionEquiv p (IsAdicRing.ideal_spec A).2.1

@[simp]
theorem stalkLocalCompletionEquiv_of (s : (Spf A).presheaf.stalk p) :
    stalkLocalCompletionEquiv p
        (AdicCompletion.of ((IsAdicRing.ideal A).map (toStalk p)) ((Spf A).presheaf.stalk p) s) =
      stalkToLocalCompletion p s := by
  simp [stalkLocalCompletionEquiv]

end IdealQuotients

/-! ### Local homomorphisms and maximal-ideal-adic completions -/

section MaximalIdealCompletion

/-- For any ideal of definition `I`, `I 𝒪_{Spf A, p}` lies in the maximal ideal of the stalk. -/
theorem map_ideal_toStalk_le_maximalIdeal {I : Ideal A} (hI : IsAdic I) :
    I.map (toStalk p) ≤ maximalIdeal ((Spf A).presheaf.stalk p) := by
  refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
  rw [Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff]
  refine (stalkResidueFieldEquiv p).injective ?_
  refine (stalkResidueFieldEquiv_residue_toStalk p a).trans ?_
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_carrier_iff_le hI).mp p.2 ha), map_zero]
  exact (map_zero (stalkResidueFieldEquiv p)).symm

/-- The canonical map `A_𝔭 → 𝒪_{Spf A, p}` is a local homomorphism. -/
theorem isLocalHom_localizationToStalk : IsLocalHom (localizationToStalk p) :=
  TauCeti.AdicCompletion.isLocalHom_of_quotientMap_surjective (localizationToStalk p)
    ((pow_one _).le.trans (map_ideal_toStalk_le_maximalIdeal p (IsAdicRing.ideal_spec A).2.1))
    (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_localizationToStalk_ideal])
    (quotientMap_localizationToStalk_bijective p (IsAdicRing.ideal_spec A).2.1 1).2

/-- The maximal ideal of `𝒪_{Spf A, p}` is the extension of the maximal ideal of `A_𝔭`. -/
theorem map_maximalIdeal_localizationToStalk :
    (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)).map
        (localizationToStalk p) =
      maximalIdeal ((Spf A).presheaf.stalk p) := by
  have hle : ((IsAdicRing.ideal A).map
      (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (localizationToStalk p) ≤ maximalIdeal ((Spf A).presheaf.stalk p) := by
    rw [map_localizationToStalk_ideal]
    exact map_ideal_toStalk_le_maximalIdeal p (IsAdicRing.ideal_spec A).2.1
  have hsurj : Function.Surjective
      (Ideal.quotientMap
        (((IsAdicRing.ideal A).map
          (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
            (localizationToStalk p))
        (localizationToStalk p) Ideal.le_comap_map) := fun x ↦ by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := exists_sub_localizationToStalk_mem_pow p (IsAdicRing.ideal_spec A).2.1 1 s
    rw [pow_one, ← map_localizationToStalk_ideal] at hy
    exact ⟨Ideal.Quotient.mk _ y, (Ideal.Quotient.eq.mpr hy).symm⟩
  exact TauCeti.AdicCompletion.map_maximalIdeal_eq_of_quotientMap_surjective
    (localizationToStalk p) hle hsurj

/-- The canonical map `𝒪_{Spf A, p} → LocalCompletion p` is a local homomorphism. -/
theorem isLocalHom_stalkToLocalCompletion : IsLocalHom (stalkToLocalCompletion p) := by
  have hle : ((IsAdicRing.ideal A).map
      (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) ≤
      maximalIdeal (LocalCompletion p) := by
    rw [maximalIdeal_localCompletion]
    exact Ideal.map_mono (map_ideal_le_maximalIdeal_atPrime p (IsAdicRing.ideal_spec A).2.1)
  exact TauCeti.AdicCompletion.isLocalHom_of_quotientMap_surjective (stalkToLocalCompletion p)
    ((pow_one _).le.trans hle)
    (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_stalkToLocalCompletion_ideal])
    (quotientMap_stalkToLocalCompletion_bijective p 1).2

/-- The maximal ideal of `LocalCompletion p` is the extension of the maximal ideal of
`𝒪_{Spf A, p}`. -/
theorem map_maximalIdeal_stalkToLocalCompletion :
    (maximalIdeal ((Spf A).presheaf.stalk p)).map (stalkToLocalCompletion p) =
      maximalIdeal (LocalCompletion p) := by
  rw [← map_maximalIdeal_localizationToStalk, Ideal.map_map,
    stalkToLocalCompletion_comp_localizationToStalk, maximalIdeal_localCompletion]

/-- The canonical ring isomorphism between the maximal-ideal-adic completions of `A_𝔭` and
`𝒪_{Spf A, p}`. -/
noncomputable def localizationMaximalCompletionEquivStalk :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) :=
  TauCeti.AdicCompletion.maximalIdealCompletionEquiv (localizationToStalk p)
    (map_ideal_toStalk_le_maximalIdeal p (IsAdicRing.ideal_spec A).2.1)
    (by rw [← Ideal.map_le_iff_le_comap, map_localizationToStalk_ideal])
    (fun n _ ↦ quotientMap_localizationToStalk_bijective p (IsAdicRing.ideal_spec A).2.1 n)

@[simp]
theorem localizationMaximalCompletionEquivStalk_of
    (y : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    localizationMaximalCompletionEquivStalk p (AdicCompletion.of _ _ y) =
      AdicCompletion.of (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p)
        (localizationToStalk p y) :=
  TauCeti.AdicCompletion.maximalIdealCompletionEquiv_of _ _ _ _ y

/-- The canonical ring isomorphism between the maximal-ideal-adic completions of `𝒪_{Spf A, p}` and
`LocalCompletion p`. -/
noncomputable def stalkMaximalCompletionEquivLocalCompletion :
    AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) ≃+*
      AdicCompletion (maximalIdeal (LocalCompletion p)) (LocalCompletion p) :=
  TauCeti.AdicCompletion.maximalIdealCompletionEquiv (stalkToLocalCompletion p)
    (by
      rw [maximalIdeal_localCompletion]
      exact Ideal.map_mono (map_ideal_le_maximalIdeal_atPrime p (IsAdicRing.ideal_spec A).2.1))
    (by rw [← Ideal.map_le_iff_le_comap, map_stalkToLocalCompletion_ideal])
    (fun n _ ↦ quotientMap_stalkToLocalCompletion_bijective p n)

@[simp]
theorem stalkMaximalCompletionEquivLocalCompletion_of (s : (Spf A).presheaf.stalk p) :
    stalkMaximalCompletionEquivLocalCompletion p (AdicCompletion.of _ _ s) =
      AdicCompletion.of (maximalIdeal (LocalCompletion p)) (LocalCompletion p)
        (stalkToLocalCompletion p s) :=
  TauCeti.AdicCompletion.maximalIdealCompletionEquiv_of _ _ _ _ s

/-- The canonical ring isomorphism between the maximal-ideal-adic completions of `A_𝔭` and
`LocalCompletion p`. -/
noncomputable def localizationMaximalCompletionEquivLocalCompletion :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal (LocalCompletion p)) (LocalCompletion p) :=
  (localizationMaximalCompletionEquivStalk p).trans
    (stalkMaximalCompletionEquivLocalCompletion p)

@[simp]
theorem localizationMaximalCompletionEquivLocalCompletion_of
    (y : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    localizationMaximalCompletionEquivLocalCompletion p (AdicCompletion.of _ _ y) =
      AdicCompletion.of (maximalIdeal (LocalCompletion p)) (LocalCompletion p)
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
          (LocalCompletion p) y) := by
  simp [localizationMaximalCompletionEquivLocalCompletion]

end MaximalIdealCompletion

/-! ### Noetherian adic rings: flatness, Krull dimension, regularity, and Cohen–Macaulayness -/

section Noetherian

variable [IsNoetherianRing A]

/-- The stalk of `Spf A` at an open prime `p` is a noetherian ring when `A` is noetherian
(EGA I, Ch. 0, 7.6.17; Ch. I, 10.1.6). -/
instance stalk_isNoetherianRing : IsNoetherianRing ((Spf A).presheaf.stalk p) :=
  isNoetherianRing_of_ringEquiv _
    (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1).commRingCatIsoToRingEquiv

/-- For noetherian `A`, `𝒪_{Spf A, p} → LocalCompletion p` is flat. -/
theorem flat_stalkToLocalCompletion : (stalkToLocalCompletion p).Flat :=
  (RingHom.Flat.of_bijective ((completedNeighbourhoodColimitIso p
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1).symm.commRingCatIsoToRingEquiv
      ).bijective).comp (flat_colimitToLocalCompletion p)

/-- For noetherian `A`, `𝒪_{Spf A, p} → LocalCompletion p` is faithfully flat. -/
theorem faithfullyFlat_stalkToLocalCompletion : (stalkToLocalCompletion p).FaithfullyFlat := by
  algebraize [stalkToLocalCompletion p]
  have : Module.Flat _ _ := flat_stalkToLocalCompletion p
  have : IsLocalHom (algebraMap ((Spf A).presheaf.stalk p) (LocalCompletion p)) :=
    isLocalHom_stalkToLocalCompletion p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For noetherian `A`, `A_𝔭 → LocalCompletion p` is faithfully flat. -/
theorem faithfullyFlat_algebraMap_localCompletion :
    (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      (LocalCompletion p)).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  have : IsLocalHom (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      (LocalCompletion p)) := isLocalHom_algebraMap_localCompletion p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For noetherian `A`, `A_𝔭 → 𝒪_{Spf A, p}` is flat, by descent from `A_𝔭 → Â_𝔭` along the
faithfully flat map `𝒪_{Spf A, p} → Â_𝔭`. -/
theorem flat_localizationToStalk : (localizationToStalk p).Flat := by
  algebraize [localizationToStalk p, stalkToLocalCompletion p]
  have : IsScalarTower (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    IsScalarTower.of_algebraMap_eq' (stalkToLocalCompletion_comp_localizationToStalk p).symm
  have : Module.FaithfullyFlat ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    faithfullyFlat_stalkToLocalCompletion p
  exact Module.Flat.of_faithfullyFlat_of_flat
    (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ((Spf A).presheaf.stalk p)
    (LocalCompletion p)

/-- For noetherian `A`, `A_𝔭 → 𝒪_{Spf A, p}` is faithfully flat. -/
theorem faithfullyFlat_localizationToStalk : (localizationToStalk p).FaithfullyFlat := by
  algebraize [localizationToStalk p]
  have : Module.Flat _ _ := flat_localizationToStalk p
  have : IsLocalHom (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p)) := isLocalHom_localizationToStalk p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For noetherian `A`, `𝒪_{Spf A, p}` and `A_𝔭` have the same Krull dimension. -/
theorem ringKrullDim_stalk_eq_localization :
    ringKrullDim ((Spf A).presheaf.stalk p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (TauCeti.AdicCompletion.ringKrullDim_eq_of_maximalIdealCompletionEquiv
    (localizationMaximalCompletionEquivStalk p)).symm

/-- For noetherian `A`, `LocalCompletion p` and `𝒪_{Spf A, p}` have the same Krull dimension. -/
theorem ringKrullDim_localCompletion_eq_stalk :
    ringKrullDim (LocalCompletion p) = ringKrullDim ((Spf A).presheaf.stalk p) :=
  (TauCeti.AdicCompletion.ringKrullDim_eq_of_maximalIdealCompletionEquiv
    (stalkMaximalCompletionEquivLocalCompletion p)).symm

/-- For noetherian `A`, `LocalCompletion p` and `A_𝔭` have the same Krull dimension. -/
theorem ringKrullDim_localCompletion_eq_localization :
    ringKrullDim (LocalCompletion p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (TauCeti.AdicCompletion.ringKrullDim_eq_of_maximalIdealCompletionEquiv
    (localizationMaximalCompletionEquivLocalCompletion p)).symm

/-- For noetherian `A`, `𝒪_{Spf A, p}` is regular if and only if `A_𝔭` is regular. -/
theorem isRegularLocalRing_stalk_iff_localization :
    IsRegularLocalRing ((Spf A).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (TauCeti.AdicCompletion.isRegularLocalRing_iff_of_maximalIdealCompletionEquiv
    (localizationMaximalCompletionEquivStalk p)).symm

/-- For noetherian `A`, `LocalCompletion p` is regular if and only if `𝒪_{Spf A, p}` is regular. -/
theorem isRegularLocalRing_localCompletion_iff_stalk :
    IsRegularLocalRing (LocalCompletion p) ↔ IsRegularLocalRing ((Spf A).presheaf.stalk p) :=
  (TauCeti.AdicCompletion.isRegularLocalRing_iff_of_maximalIdealCompletionEquiv
    (stalkMaximalCompletionEquivLocalCompletion p)).symm

/-- For noetherian `A`, `LocalCompletion p` is regular if and only if `A_𝔭` is regular. -/
theorem isRegularLocalRing_localCompletion_iff_localization :
    IsRegularLocalRing (LocalCompletion p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (TauCeti.AdicCompletion.isRegularLocalRing_iff_of_maximalIdealCompletionEquiv
    (localizationMaximalCompletionEquivLocalCompletion p)).symm

/-- For noetherian `A`, `𝒪_{Spf A, p}` is Cohen–Macaulay if and only if `A_𝔭` is
Cohen–Macaulay. -/
theorem isCohenMacaulay_stalk_iff_localization :
    Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (TauCeti.AdicCompletion.isCohenMacaulay_self_iff_of_maximalIdealCompletionEquiv
    (localizationMaximalCompletionEquivStalk p)).symm

/-- For noetherian `A`, `LocalCompletion p` is Cohen–Macaulay if and only if `𝒪_{Spf A, p}` is
Cohen–Macaulay. -/
theorem isCohenMacaulay_localCompletion_iff_stalk :
    Module.IsCohenMacaulay (LocalCompletion p) (LocalCompletion p) ↔
      Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) :=
  (TauCeti.AdicCompletion.isCohenMacaulay_self_iff_of_maximalIdealCompletionEquiv
    (stalkMaximalCompletionEquivLocalCompletion p)).symm

/-- For noetherian `A`, `LocalCompletion p` is Cohen–Macaulay if and only if `A_𝔭` is
Cohen–Macaulay. -/
theorem isCohenMacaulay_localCompletion_iff_localization :
    Module.IsCohenMacaulay (LocalCompletion p) (LocalCompletion p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (TauCeti.AdicCompletion.isCohenMacaulay_self_iff_of_maximalIdealCompletionEquiv
    (localizationMaximalCompletionEquivLocalCompletion p)).symm

end Noetherian

end TauCeti.FormalScheme.Spf
