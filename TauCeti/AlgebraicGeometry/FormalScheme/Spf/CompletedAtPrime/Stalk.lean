/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood.Noetherian
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Basic
public import TauCeti.RingTheory.CohenMacaulay.Basic

import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.CohenMacaulay.Flat
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.Localization.AtPrime.Quotient
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# The stalks of a formal spectrum and the completed localisations of its ring

Let `A` be an adic ring with ideal of definition `I` and `p` a point of `Spf A`, an open prime `𝔭`
of `A`. The completed localisation `Â_𝔭 = lim_n (A ⧸ Iⁿ)_𝔭`
(`TauCeti.FormalScheme.Spf.CompletedAtPrime`) is the completion of the local ring `A_𝔭` along
`I A_𝔭`. Since `I ⊆ 𝔭`, it is a local ring with maximal ideal `𝔭 Â_𝔭`. The stalk `O_{Spf A, p}` is
the colimit of the completed localisations `A_{f}` over the basic open neighbourhoods `D(f)` of `p`,
and the maps `A_{f} → Â_𝔭` induce a canonical map `O_{Spf A, p} → Â_𝔭` (EGA I, Ch. 0, 7.6.15–7.6.18;
Ch. I, 10.1.5–10.1.6).

This file shows that `O_{Spf A, p} → Â_𝔭` is a local homomorphism compatible with
`A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭`, under which the maximal ideal of the stalk generates the maximal ideal
of `Â_𝔭`, and that without any noetherian hypothesis:

* for every open ideal `J` of `A` (in particular every power `I ^ n` of an ideal of definition `I`),
  both maps induce ring isomorphisms
  `A_𝔭 ⧸ J A_𝔭 ≃+* 𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} ≃+* Â_𝔭 ⧸ J Â_𝔭`, compatible with reduction
  between open ideals `J ≤ K`, and for any prime `Q` of `A ⧸ J` lying over `𝔭`, both
  `A_𝔭 ⧸ J A_𝔭` and `𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}` are canonically isomorphic to `(A ⧸ J)_Q`;
* for every ideal of definition `I` of `A`, `stalkToCompletedAtPrime p` identifies `Â_𝔭` with the
  `I`-adic completion of `𝒪_{Spf A, p}`.

For noetherian `A`, `O_{Spf A, p} → Â_𝔭` is flat and faithfully flat. Its closed fibre is then
the residue field of `Â_𝔭`, so the stalk and `Â_𝔭` have the same Krull dimension, and regularity
and the Cohen–Macaulay property agree for both. Completion of the noetherian local ring `A_𝔭` along
`I A_𝔭 ⊆ 𝔭 A_𝔭` likewise preserves the dimension, regularity, and the Cohen–Macaulay property
(`TauCeti.FormalScheme.Spf.ringKrullDim_completedAtPrime`,
`TauCeti.FormalScheme.Spf.isRegularLocalRing_completedAtPrime_iff`,
`TauCeti.FormalScheme.Spf.isCohenMacaulay_completedAtPrime_iff`), so `A_𝔭`, the stalk and `Â_𝔭`
share these invariants. This is how the local dimension, regularity and the Cohen–Macaulay
property at a point of a formal spectrum are computed from its ring.

For maximal-ideal-adic completion comparisons and discrete and complete local special cases, see
`TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Comparison`.

## Main definitions

* `TauCeti.FormalScheme.Spf.stalkToCompletedAtPrime p`: the canonical map `O_{Spf A, p} → Â_𝔭`.
* `TauCeti.FormalScheme.Spf.localizationQuotientEquivStalkQuotient`,
  `TauCeti.FormalScheme.Spf.stalkQuotientEquivCompletedAtPrimeQuotient`: canonical quotient
  isomorphisms modulo open ideals `J` of `A`.
* `TauCeti.FormalScheme.Spf.localizationQuotientEquivQuotientLocalization`,
  `TauCeti.FormalScheme.Spf.stalkQuotientEquivQuotientLocalization`: identifications of the
  quotients modulo `J` with `(A ⧸ J)_Q`.
* `TauCeti.FormalScheme.Spf.stalkAdicCompletionEquivCompletedAtPrime`: identification of `Â_𝔭` with
  the `I`-adic completion of `𝒪_{Spf A, p}`.

## Main results

* `TauCeti.FormalScheme.Spf.stalkToCompletedAtPrime_germ`: on the germ of a section over `D(f)`,
  the map `O_{Spf A, p} → Â_𝔭` is the map `A_{f} → Â_𝔭`.
* `TauCeti.FormalScheme.Spf.stalkToCompletedAtPrime_comp_localizationToStalk`: compatibility of
  `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` with `A_𝔭 → Â_𝔭`.
* `TauCeti.FormalScheme.Spf.map_maximalIdeal_stalkToCompletedAtPrime`: the maximal ideal of the
  stalk generates the maximal ideal of `Â_𝔭`.
* `TauCeti.FormalScheme.Spf.quotientMap_localizationToStalk_bijective_of_isOpen`,
  `TauCeti.FormalScheme.Spf.quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen`,
  `TauCeti.FormalScheme.Spf.quotientMap_algebraMap_completedAtPrime_bijective_of_isOpen`: quotient
  bijections modulo open ideals.
* `TauCeti.FormalScheme.Spf.flat_stalkToCompletedAtPrime`,
  `TauCeti.FormalScheme.Spf.faithfullyFlat_stalkToCompletedAtPrime`: for noetherian `A`, the map
  `O_{Spf A, p} → Â_𝔭` is flat and faithfully flat.
* `TauCeti.FormalScheme.Spf.ringKrullDim_completedAtPrime_eq_stalk`,
  `TauCeti.FormalScheme.Spf.isRegularLocalRing_completedAtPrime_iff_stalk`,
  `TauCeti.FormalScheme.Spf.isCohenMacaulay_completedAtPrime_iff_stalk`: for noetherian `A`,
  the rings `Â_𝔭` and `O_{Spf A, p}` have the same Krull dimension, and regularity and the
  Cohen–Macaulay property agree for both.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
* H. Matsumura, *Commutative Ring Theory*, Theorems 15.1, Theorem 23.7 and the Corollary of
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

/-! ### The map from the stalk to the completed localisation -/

/-- The identification of `colim_{f ∉ 𝔭} A_{f}` with the stalk of `Spf A` at `p`. -/
private noncomputable abbrev colimitIso :
    colimit (completedNeighbourhoodDiagram p) ≅ (Spf A).presheaf.stalk p :=
  completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1

/-- The canonical map `O_{Spf A, p} → Â_𝔭` from the stalk of `Spf A` at `p` to the completed
localisation of `A` at the corresponding open prime `𝔭`. On the germ of a section over a basic open
neighbourhood `D(f)` of `p` it is the map `A_{f} → Â_𝔭`, see
`TauCeti.FormalScheme.Spf.stalkToCompletedAtPrime_germ`. -/
noncomputable def stalkToCompletedAtPrime : (Spf A).presheaf.stalk p →+* CompletedAtPrime p :=
  (colimitToCompletedAtPrime p).comp (colimitIso p).inv.hom

/-- The map `O_{Spf A, p} → Â_𝔭` sends the germ at `p` of the section over a basic open
neighbourhood `D(f)` given by `x ∈ A_{f}` to the image of `x` under `A_{f} → Â_𝔭`. Since every
element of the stalk is such a germ, this determines the map. -/
@[simp]
theorem stalkToCompletedAtPrime_germ (f : BasicNeighbourhood p) (x : CompletedAway A f.elem) :
    stalkToCompletedAtPrime p ((Spf A).presheaf.germ (basicOpen f.elem) p
        (mem_basicOpen.mpr f.notMem)
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          f.elem).inv x)) =
      toCompletedAtPrime p f x := by
  -- the inverse of the comparison of the colimit with the stalk sends the germ back to `x`
  have h : (colimitIso p).inv.hom ((Spf A).presheaf.germ (basicOpen f.elem) p
      (mem_basicOpen.mpr f.notMem) ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1 f.elem).inv x)) =
      colimit.ι (completedNeighbourhoodDiagram p) f x :=
    ConcreteCategory.congr_hom ((Iso.comp_inv_eq _).mpr (completedNeighbourhoodColimitIso_germ p
      (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f).symm) x
  rw [stalkToCompletedAtPrime, RingHom.comp_apply]
  exact (congrArg (colimitToCompletedAtPrime p) h).trans (colimitToCompletedAtPrime_ι p f x)

/-- The map `O_{Spf A, p} → Â_𝔭` is a local homomorphism. -/
instance isLocalHom_stalkToCompletedAtPrime : IsLocalHom (stalkToCompletedAtPrime p) :=
  inferInstanceAs (IsLocalHom ((colimitToCompletedAtPrime p).comp (colimitIso p).inv.hom))

/-- The maximal ideal of the stalk `O_{Spf A, p}` generates the maximal ideal of the completed
localisation `Â_𝔭`: the closed fibre of `O_{Spf A, p} → Â_𝔭` is the residue field of `Â_𝔭`. -/
theorem map_maximalIdeal_stalkToCompletedAtPrime :
    haveI := (Spf A).isLocalRing p
    (maximalIdeal ((Spf A).presheaf.stalk p)).map (stalkToCompletedAtPrime p) =
      maximalIdeal (CompletedAtPrime p) := by
  have := (Spf A).isLocalRing p
  refine le_antisymm (map_maximalIdeal_le (stalkToCompletedAtPrime p)) ?_
  -- `𝔭 Â_𝔭` is generated by the images of the germs of the elements of `𝔭`, which vanish at `p`
  rw [maximalIdeal_completedAtPrime, Ideal.map_le_iff_le_comap]
  intro a ha
  let f : BasicNeighbourhood p := ⟨1, (p : PrimeSpectrum A).asIdeal.primeCompl.one_mem⟩
  let x := (Spf A).presheaf.germ (basicOpen f.elem) p (mem_basicOpen.mpr f.notMem)
    ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f.elem).inv
      (algebraMap A (CompletedAway A f.elem) a))
  have hx : x ∈ maximalIdeal ((Spf A).presheaf.stalk p) := by
    have h := stalkResidueFieldEquiv_residue_germ f a
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero,
      map_eq_zero_iff _ (stalkResidueFieldEquiv p).injective] at h
    -- the residue map `(Spf A).residue p` of a locally ringed space is by definition the residue
    -- map of the local ring `O_{Spf A, p}`
    exact (residue_eq_zero_iff x).mp h
  have := Ideal.mem_map_of_mem (stalkToCompletedAtPrime p) hx
  rwa [stalkToCompletedAtPrime_germ, AlgHom.commutes] at this

/-- For a noetherian adic ring `A`, the map `O_{Spf A, p} → Â_𝔭` is faithfully flat. -/
theorem faithfullyFlat_stalkToCompletedAtPrime [IsNoetherianRing A] :
    (stalkToCompletedAtPrime p).FaithfullyFlat := by
  rw [stalkToCompletedAtPrime]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (f := (colimitIso p).inv.hom)
      (ConcreteCategory.bijective_of_isIso (colimitIso p).inv))
    (faithfullyFlat_colimitToCompletedAtPrime p)

/-- For a noetherian adic ring `A`, the map `O_{Spf A, p} → Â_𝔭` is flat. -/
theorem flat_stalkToCompletedAtPrime [IsNoetherianRing A] :
    (stalkToCompletedAtPrime p).Flat :=
  (faithfullyFlat_stalkToCompletedAtPrime p).flat

/-! ### Dimension, regularity, and Cohen–Macaulay property of the stalk -/

/-- The map `O_{Spf A, p} → Â_𝔭` as an algebra structure, used to apply results about flat local
algebras to it. -/
private noncomputable abbrev stalkAlgebra :
    Algebra ((Spf A).presheaf.stalk p) (CompletedAtPrime p) :=
  (stalkToCompletedAtPrime p).toAlgebra

attribute [local instance] stalkAlgebra

private theorem flat_stalkAlgebra [IsNoetherianRing A] :
    Module.Flat ((Spf A).presheaf.stalk p) (CompletedAtPrime p) :=
  flat_stalkToCompletedAtPrime p

/-- For a noetherian adic ring `A`, the completed localisation `Â_𝔭` has the Krull dimension of the
stalk `O_{Spf A, p}`. -/
theorem ringKrullDim_completedAtPrime_eq_stalk [IsNoetherianRing A] :
    ringKrullDim (CompletedAtPrime p) = ringKrullDim ((Spf A).presheaf.stalk p) :=
  haveI := (Spf A).isLocalRing p
  haveI := flat_stalkAlgebra p
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToCompletedAtPrime p)

/-- For a noetherian adic ring `A`, the completed localisation `Â_𝔭` is a regular local ring if and
only if the stalk `O_{Spf A, p}` is. -/
theorem isRegularLocalRing_completedAtPrime_iff_stalk [IsNoetherianRing A] :
    IsRegularLocalRing (CompletedAtPrime p) ↔ IsRegularLocalRing ((Spf A).presheaf.stalk p) :=
  haveI := (Spf A).isLocalRing p
  haveI := flat_stalkAlgebra p
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToCompletedAtPrime p)

/-- For a noetherian adic ring `A`, `Â_𝔭` is Cohen–Macaulay if and only if `𝒪_{Spf A, p}` is. -/
theorem isCohenMacaulay_completedAtPrime_iff_stalk [IsNoetherianRing A] :
    Module.IsCohenMacaulay (CompletedAtPrime p) (CompletedAtPrime p) ↔
      Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) :=
  haveI := (Spf A).isLocalRing p
  haveI := flat_stalkAlgebra p
  Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToCompletedAtPrime p)

/-! ### Compatibility of `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` -/

section Compatibility

/-- On images of elements of `A`, `stalkToCompletedAtPrime p` is `algebraMap A Â_𝔭`. -/
@[simp]
theorem stalkToCompletedAtPrime_toStalk (a : A) :
    stalkToCompletedAtPrime p (toStalk p a) = algebraMap A (CompletedAtPrime p) a := by
  let f : BasicNeighbourhood p := ⟨1, (p : PrimeSpectrum A).asIdeal.one_notMem⟩
  rw [toStalk_eq_germ p f a, stalkToCompletedAtPrime_germ]
  exact (toCompletedAtPrime p f).commutes a

/-- The composite `A → 𝒪_{Spf A, p} → Â_𝔭` is `algebraMap A Â_𝔭`. -/
@[simp]
theorem stalkToCompletedAtPrime_comp_toStalk :
    (stalkToCompletedAtPrime p).comp (toStalk p) = algebraMap A (CompletedAtPrime p) :=
  RingHom.ext (stalkToCompletedAtPrime_toStalk p)

/-- The composite `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` is the canonical completion map `A_𝔭 → Â_𝔭`. -/
@[simp]
theorem stalkToCompletedAtPrime_comp_localizationToStalk :
    (stalkToCompletedAtPrime p).comp (localizationToStalk p) =
      algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p) :=
  IsLocalization.ringHom_ext (p : PrimeSpectrum A).asIdeal.primeCompl
    (RingHom.ext fun _ ↦ by simp [← IsScalarTower.algebraMap_apply])

/-- Applied pointwise, `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` is the canonical completion map `A_𝔭 → Â_𝔭`. -/
@[simp]
theorem stalkToCompletedAtPrime_localizationToStalk
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    stalkToCompletedAtPrime p (localizationToStalk p x) =
      algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p) x :=
  RingHom.congr_fun (stalkToCompletedAtPrime_comp_localizationToStalk p) x

end Compatibility

/-! ### Isomorphisms modulo open ideals and powers of ideals of definition -/

section Quotients

/-- Pushing an ideal of `A` to `𝒪_{Spf A, p}` and then along `stalkToCompletedAtPrime p` agrees
with pushing it directly to `Â_𝔭`. -/
@[simp]
theorem map_stalkToCompletedAtPrime_map (J : Ideal A) :
    (J.map (toStalk p)).map (stalkToCompletedAtPrime p) =
      J.map (algebraMap A (CompletedAtPrime p)) := by
  rw [Ideal.map_map, stalkToCompletedAtPrime_comp_toStalk]

private theorem quotientMap_localizationToStalk_surjective_ideal_pow (n : ℕ) :
    Function.Surjective (Ideal.quotientMap ((IsAdicRing.ideal A ^ n).map (toStalk p))
      (localizationToStalk p)
      (map_localizationToStalk_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)) := by
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨f, x, rfl⟩ := exists_completedAway_rep p s
  let φ : CompletedAway A f.elem →+* (Spf A).presheaf.stalk p :=
    (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1).hom.hom.comp
      (colimit.ι (completedNeighbourhoodDiagram p) f).hom
  let eAway := CompletedAway.equivAdicCompletion A f.elem
  obtain ⟨y, hy⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow
    ((IsAdicRing.ideal_spec A).1.map (algebraMap A (Localization.Away f.elem))) n (eAway x)
  have hy' : x - algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) y ∈
      (IsAdicRing.ideal A ^ n).map (algebraMap A (CompletedAway A f.elem)) := by
    have hmem : eAway.symm (eAway x - algebraMap (Localization.Away f.elem) _ y) ∈ _ :=
      Ideal.mem_map_of_mem eAway.symm.toAlgHom.toRingHom hy
    rw [map_sub, AlgEquiv.symm_apply_apply, eAway.symm.commutes, ← Ideal.map_pow, Ideal.map_map,
      Ideal.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower,
      ← IsScalarTower.algebraMap_eq] at hmem
    exact hmem
  refine ⟨Ideal.Quotient.mk _
    ((p : PrimeSpectrum A).asIdeal.localizationAwayToAtPrime f.elem f.notMem y), ?_⟩
  rw [Ideal.quotientMap_mk]
  have hcomp : φ.comp (algebraMap A (CompletedAway A f.elem)) = toStalk p :=
    RingHom.ext fun a ↦ (toStalk_eq_completedNeighbourhoodColimitIso p f a).symm
  have hmem := Ideal.mem_map_of_mem φ hy'
  rw [Ideal.map_map, hcomp] at hmem
  have hsub : localizationToStalk p
        ((p : PrimeSpectrum A).asIdeal.localizationAwayToAtPrime f.elem f.notMem y) - φ x =
      -φ (x - algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) y) := by
    rw [map_sub, neg_sub]
    exact congrArg (· - φ x) (localizationToStalk_away p f y)
  exact Ideal.Quotient.eq.mpr (hsub.symm ▸ neg_mem hmem)

private theorem quotientMap_ideal_pow_bijective (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((IsAdicRing.ideal A ^ n).map (toStalk p))
      (localizationToStalk p)
      (map_localizationToStalk_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)) ∧
    Function.Bijective (Ideal.quotientMap
      ((IsAdicRing.ideal A ^ n).map (algebraMap A (CompletedAtPrime p)))
      (stalkToCompletedAtPrime p)
      (map_stalkToCompletedAtPrime_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)) := by
  let q₁ := Ideal.quotientMap ((IsAdicRing.ideal A ^ n).map (toStalk p)) (localizationToStalk p)
    (map_localizationToStalk_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)
  let q₂ := Ideal.quotientMap
    ((IsAdicRing.ideal A ^ n).map (algebraMap A (CompletedAtPrime p)))
    (stalkToCompletedAtPrime p)
    (map_stalkToCompletedAtPrime_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)
  have hcomp_bij : Function.Bijective (q₂ ∘ q₁) := by
    have hbij' := RingHom.quotientMap_bijective_congr
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p))
      (Ideal.map_pow _ _ _).symm
      (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, ← Ideal.map_pow])
      (AdicCompletion.quotientMap_algebraMap_bijective ((IsAdicRing.ideal_spec A).1.map _) n
        (H := (Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))
      (H₂ := Ideal.map_le_iff_le_comap.mpr fun _ ha ↦ by
        rw [Ideal.mem_comap, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
        exact Ideal.mem_map_of_mem _ ha)
    convert hbij' using 1
    ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [q₁, q₂, stalkToCompletedAtPrime_localizationToStalk]
  have hq₁_bij : Function.Bijective q₁ :=
    ⟨Function.Injective.of_comp hcomp_bij.1,
      quotientMap_localizationToStalk_surjective_ideal_pow p n⟩
  exact ⟨hq₁_bij, (Function.Bijective.of_comp_iff q₂ hq₁_bij).mp hcomp_bij⟩

private theorem quotientMap_bijective_of_isOpen {R S : Type*} [CommRing R] [CommRing S]
    {φ : A →+* R} {g : R →+* S} {ψ : A →+* S} (hcomp : g.comp φ = ψ)
    (hpow : ∀ n : ℕ, Function.Bijective (Ideal.quotientMap ((IsAdicRing.ideal A ^ n).map ψ) g
      ((by rw [Ideal.map_map, hcomp] : ((IsAdicRing.ideal A ^ n).map φ).map g = _) ▸
        Ideal.le_comap_map)))
    {J : Ideal A} (hJ : IsOpen (J : Set A))
    {H : J.map φ ≤ (J.map ψ).comap g} :
    Function.Bijective (Ideal.quotientMap (J.map ψ) g H) := by
  obtain ⟨n, hn⟩ :=
    (isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).2 (J : Set A) (hJ.mem_nhds J.zero_mem)
  have hmap (K : Ideal A) : (K.map φ).map g = K.map ψ := by rw [Ideal.map_map, hcomp]
  exact g.quotientMap_bijective_congr rfl (hmap J)
    (g.quotientMap_bijective_of_le (Ideal.map_mono hn)
      (g.quotientMap_bijective_congr rfl (hmap _).symm (hpow n) (H₂ := Ideal.le_comap_map))
      (HJ := Ideal.le_comap_map))

/-- For every open ideal `J` of `A`, `A_𝔭 → 𝒪_{Spf A, p}` induces a bijection
`A_𝔭 ⧸ J A_𝔭 → 𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}`. -/
theorem quotientMap_localizationToStalk_bijective_of_isOpen {J : Ideal A} (hJ : IsOpen (J : Set A))
    {H : J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      (J.map (toStalk p)).comap (localizationToStalk p)} :
    Function.Bijective (Ideal.quotientMap (J.map (toStalk p)) (localizationToStalk p) H) :=
  quotientMap_bijective_of_isOpen (localizationToStalk_comp_algebraMap p)
    (fun n ↦ (quotientMap_ideal_pow_bijective p n).1) hJ

/-- For every open ideal `J` of `A`, `𝒪_{Spf A, p} → Â_𝔭` induces a bijection
`𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} → Â_𝔭 ⧸ J Â_𝔭`. -/
theorem quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen {J : Ideal A}
    (hJ : IsOpen (J : Set A))
    {H : J.map (toStalk p) ≤
      (J.map (algebraMap A (CompletedAtPrime p))).comap (stalkToCompletedAtPrime p)} :
    Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap A (CompletedAtPrime p)))
        (stalkToCompletedAtPrime p) H) :=
  quotientMap_bijective_of_isOpen (stalkToCompletedAtPrime_comp_toStalk p)
    (fun n ↦ (quotientMap_ideal_pow_bijective p n).2) hJ

/-- For every open ideal `J` of `A`, `A_𝔭 → Â_𝔭` induces a bijection
`A_𝔭 ⧸ J A_𝔭 → Â_𝔭 ⧸ J Â_𝔭`. -/
theorem quotientMap_algebraMap_completedAtPrime_bijective_of_isOpen {J : Ideal A}
    (hJ : IsOpen (J : Set A))
    {H : J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      (J.map (algebraMap A (CompletedAtPrime p))).comap
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p))} :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap A (CompletedAtPrime p)))
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p))
      H) := by
  convert (quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen p hJ
    (H := map_stalkToCompletedAtPrime_map p J ▸ Ideal.le_comap_map)).comp
    (quotientMap_localizationToStalk_bijective_of_isOpen p hJ
      (H := map_localizationToStalk_map p J ▸ Ideal.le_comap_map))
  ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [stalkToCompletedAtPrime_localizationToStalk]

/-- For every open ideal `J` of `A`, the canonical ring isomorphism
`A_𝔭 ⧸ J A_𝔭 ≃+* 𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}`. In particular this applies to `J = I ^ n` for
every ideal of definition `I` of `A` and every `n : ℕ`. -/
noncomputable def localizationQuotientEquivStalkQuotient {J : Ideal A} (hJ : IsOpen (J : Set A)) :
    (Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
        J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ≃+*
      ((Spf A).presheaf.stalk p ⧸ J.map (toStalk p)) :=
  RingEquiv.ofBijective _ (quotientMap_localizationToStalk_bijective_of_isOpen p hJ
    (H := map_localizationToStalk_map p J ▸ Ideal.le_comap_map))

/-- `localizationQuotientEquivStalkQuotient` acts by `localizationToStalk p` on cosets. -/
@[simp]
theorem localizationQuotientEquivStalkQuotient_mk {J : Ideal A} (hJ : IsOpen (J : Set A))
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    localizationQuotientEquivStalkQuotient p hJ (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (localizationToStalk p x) := by
  rfl

/-- For open ideals `J ≤ K` of `A`, `localizationQuotientEquivStalkQuotient` commutes with the
canonical reduction maps `Ideal.Quotient.factor`. -/
@[simp]
theorem factor_localizationQuotientEquivStalkQuotient {J K : Ideal A} (hJ : IsOpen (J : Set A))
    (hK : IsOpen (K : Set A)) (hJK : J ≤ K)
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
      J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) :
    Ideal.Quotient.factor (Ideal.map_mono hJK)
        (localizationQuotientEquivStalkQuotient p hJ x) =
      localizationQuotientEquivStalkQuotient p hK
        (Ideal.Quotient.factor (Ideal.map_mono hJK) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- Ring-homomorphism form of `factor_localizationQuotientEquivStalkQuotient`. -/
theorem factor_comp_localizationQuotientEquivStalkQuotient {J K : Ideal A}
    (hJ : IsOpen (J : Set A)) (hK : IsOpen (K : Set A)) (hJK : J ≤ K) :
    (Ideal.Quotient.factor (Ideal.map_mono hJK)).comp
        (localizationQuotientEquivStalkQuotient p hJ).toRingHom =
      (localizationQuotientEquivStalkQuotient p hK).toRingHom.comp
        (Ideal.Quotient.factor (Ideal.map_mono hJK)) :=
  RingHom.ext (factor_localizationQuotientEquivStalkQuotient p hJ hK hJK)

/-- For every open ideal `J` of `A`, the canonical ring isomorphism
`𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} ≃+* Â_𝔭 ⧸ J Â_𝔭`. In particular this applies to `J = I ^ n` for
every ideal of definition `I` of `A` and every `n : ℕ`. -/
noncomputable def stalkQuotientEquivCompletedAtPrimeQuotient {J : Ideal A}
    (hJ : IsOpen (J : Set A)) :
    ((Spf A).presheaf.stalk p ⧸ J.map (toStalk p)) ≃+*
      (CompletedAtPrime p ⧸ J.map (algebraMap A (CompletedAtPrime p))) :=
  RingEquiv.ofBijective _ (quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen p hJ
    (H := map_stalkToCompletedAtPrime_map p J ▸ Ideal.le_comap_map))

/-- `stalkQuotientEquivCompletedAtPrimeQuotient` acts by `stalkToCompletedAtPrime p` on cosets. -/
@[simp]
theorem stalkQuotientEquivCompletedAtPrimeQuotient_mk {J : Ideal A} (hJ : IsOpen (J : Set A))
    (x : (Spf A).presheaf.stalk p) :
    stalkQuotientEquivCompletedAtPrimeQuotient p hJ (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (stalkToCompletedAtPrime p x) := by
  rfl

/-- For open ideals `J ≤ K` of `A`, `stalkQuotientEquivCompletedAtPrimeQuotient` commutes with the
canonical reduction maps `Ideal.Quotient.factor`. -/
@[simp]
theorem factor_stalkQuotientEquivCompletedAtPrimeQuotient {J K : Ideal A}
    (hJ : IsOpen (J : Set A)) (hK : IsOpen (K : Set A)) (hJK : J ≤ K)
    (x : (Spf A).presheaf.stalk p ⧸ J.map (toStalk p)) :
    Ideal.Quotient.factor (Ideal.map_mono hJK)
        (stalkQuotientEquivCompletedAtPrimeQuotient p hJ x) =
      stalkQuotientEquivCompletedAtPrimeQuotient p hK
        (Ideal.Quotient.factor (Ideal.map_mono hJK) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- Ring-homomorphism form of `factor_stalkQuotientEquivCompletedAtPrimeQuotient`. -/
theorem factor_comp_stalkQuotientEquivCompletedAtPrimeQuotient {J K : Ideal A}
    (hJ : IsOpen (J : Set A)) (hK : IsOpen (K : Set A)) (hJK : J ≤ K) :
    (Ideal.Quotient.factor (Ideal.map_mono hJK)).comp
        (stalkQuotientEquivCompletedAtPrimeQuotient p hJ).toRingHom =
      (stalkQuotientEquivCompletedAtPrimeQuotient p hK).toRingHom.comp
        (Ideal.Quotient.factor (Ideal.map_mono hJK)) :=
  RingHom.ext (factor_stalkQuotientEquivCompletedAtPrimeQuotient p hJ hK hJK)

omit [IsTopologicalRing A] [IsAdicRing A] in
/-- For any ideal `J` of `A` and prime ideal `Q` of `A ⧸ J` lying over `𝔭`, the quotient
`A_𝔭 ⧸ J A_𝔭` is canonically `(A ⧸ J)`-algebra isomorphic to the localisation `(A ⧸ J)_Q`. -/
noncomputable def localizationQuotientEquivQuotientLocalization {J : Ideal A}
    (Q : Ideal (A ⧸ J)) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk J) = (p : PrimeSpectrum A).asIdeal) :
    (Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
        J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) ≃ₐ[A ⧸ J]
      Localization.AtPrime Q :=
  haveI : IsLocalization.AtPrime (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      (Q.comap (Ideal.Quotient.mk J)) := by simp only [hQ]; infer_instance
  J.quotientLocalizationAtPrimeEquiv Q

omit [IsTopologicalRing A] [IsAdicRing A] in
/-- On elements of `A`, `localizationQuotientEquivQuotientLocalization` sends the image of `a` in
`A_𝔭 ⧸ J A_𝔭` to the image of `a mod J` in `(A ⧸ J)_Q`. -/
@[simp]
theorem localizationQuotientEquivQuotientLocalization_algebraMap {J : Ideal A}
    (Q : Ideal (A ⧸ J)) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk J) = (p : PrimeSpectrum A).asIdeal) (a : A) :
    localizationQuotientEquivQuotientLocalization p Q hQ
        (algebraMap A
          (Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
            J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) a) =
      algebraMap (A ⧸ J) (Localization.AtPrime Q) (Ideal.Quotient.mk J a) := by
  have : IsLocalization.AtPrime (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      (Q.comap (Ideal.Quotient.mk J)) := by simp only [hQ]; infer_instance
  exact J.quotientLocalizationAtPrimeEquiv_algebraMap Q a

/-- For every open ideal `J` of `A` and prime ideal `Q` of `A ⧸ J` lying over `𝔭`, the quotient
`𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}` is canonically isomorphic to `(A ⧸ J)_Q`. -/
noncomputable def stalkQuotientEquivQuotientLocalization {J : Ideal A} (hJ : IsOpen (J : Set A))
    (Q : Ideal (A ⧸ J)) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk J) = (p : PrimeSpectrum A).asIdeal) :
    ((Spf A).presheaf.stalk p ⧸ J.map (toStalk p)) ≃+* Localization.AtPrime Q :=
  (localizationQuotientEquivStalkQuotient p hJ).symm.trans
    (localizationQuotientEquivQuotientLocalization p Q hQ).toRingEquiv

/-- On elements of `A`, `stalkQuotientEquivQuotientLocalization` sends the image of `toStalk p a`
to the image of `a mod J` in `(A ⧸ J)_Q`. -/
@[simp]
theorem stalkQuotientEquivQuotientLocalization_mk_toStalk {J : Ideal A} (hJ : IsOpen (J : Set A))
    (Q : Ideal (A ⧸ J)) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk J) = (p : PrimeSpectrum A).asIdeal) (a : A) :
    stalkQuotientEquivQuotientLocalization p hJ Q hQ (Ideal.Quotient.mk _ (toStalk p a)) =
      algebraMap (A ⧸ J) (Localization.AtPrime Q) (Ideal.Quotient.mk J a) := by
  have hsymm : (localizationQuotientEquivStalkQuotient p hJ).symm
      (Ideal.Quotient.mk _ (toStalk p a)) =
      algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal ⧸
        J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))) a := by
    rw [RingEquiv.symm_apply_eq, ← Ideal.Quotient.mk_algebraMap,
      localizationQuotientEquivStalkQuotient_mk, localizationToStalk_algebraMap_eq_toStalk]
  rw [stalkQuotientEquivQuotientLocalization, RingEquiv.trans_apply, hsymm]
  exact localizationQuotientEquivQuotientLocalization_algebraMap p Q hQ a

private theorem toRingHom_ofId_stalkAlgebra :
    (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p)).toRingHom =
      stalkToCompletedAtPrime p :=
  RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra]

private theorem ideal_map_toStalk_le_comap_ofId (I : Ideal A) :
    I.map (toStalk p) ≤
      (I.map (algebraMap A (CompletedAtPrime p))).comap
        (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p)) := by
  refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
  rw [Ideal.mem_comap, Ideal.mem_comap, Algebra.ofId_apply, RingHom.algebraMap_toAlgebra]
  exact (map_stalkToCompletedAtPrime_map p I) ▸
    Ideal.mem_map_of_mem (stalkToCompletedAtPrime p) (Ideal.mem_map_of_mem (toStalk p) hx)

/-- For every ideal of definition `I` of `A`, the map `𝒪_{Spf A, p} → Â_𝔭` identifies `Â_𝔭` with
the `I`-adic completion of `𝒪_{Spf A, p}` (EGA I, Ch. 0, 7.6.17). -/
noncomputable def stalkAdicCompletionEquivCompletedAtPrime {I : Ideal A} (hI : IsAdic I) :
    AdicCompletion (I.map (toStalk p)) ((Spf A).presheaf.stalk p) ≃+* CompletedAtPrime p :=
  haveI := isAdicComplete_completedAtPrime p hI
  have hbij := AdicCompletion.mapₐ_bijective
      (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p))
      (ideal_map_toStalk_le_comap_ofId p I) fun n ↦ by
    have hq := quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen p ((isAdic_iff.mp hI).1 n)
      (H := map_stalkToCompletedAtPrime_map p (I ^ n) ▸ Ideal.le_comap_map)
    exact RingHom.quotientMap_bijective_congr (stalkToCompletedAtPrime p) (Ideal.map_pow _ _ _)
      (Ideal.map_pow _ _ _) hq
  (AlgEquiv.ofBijective _ hbij).toRingEquiv.trans
    (RingEquiv.ofBijective
      (algebraMap (CompletedAtPrime p)
        (AdicCompletion (I.map (algebraMap A (CompletedAtPrime p))) (CompletedAtPrime p)))
      (AdicCompletion.of_bijective _ _)).symm

/-- On elements of `𝒪_{Spf A, p}`, `stalkAdicCompletionEquivCompletedAtPrime` applies
`stalkToCompletedAtPrime p`. -/
@[simp]
theorem stalkAdicCompletionEquivCompletedAtPrime_of {I : Ideal A} (hI : IsAdic I)
    (s : (Spf A).presheaf.stalk p) :
    stalkAdicCompletionEquivCompletedAtPrime p hI
        (AdicCompletion.of (I.map (toStalk p)) ((Spf A).presheaf.stalk p) s) =
      stalkToCompletedAtPrime p s := by
  rw [stalkAdicCompletionEquivCompletedAtPrime, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
  exact AdicCompletion.mapₐ_of
    (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p)) _ s

/-- Modulo `(I Â_𝔭) ^ n`, `stalkAdicCompletionEquivCompletedAtPrime` reduces to the quotient map
induced by `stalkToCompletedAtPrime p` on `AdicCompletion.evalₐ (I 𝒪_{Spf A, p}) n`. -/
@[simp]
theorem mk_stalkAdicCompletionEquivCompletedAtPrime {I : Ideal A} (hI : IsAdic I) (n : ℕ)
    (x : AdicCompletion (I.map (toStalk p)) ((Spf A).presheaf.stalk p)) :
    Ideal.Quotient.mk (I.map (algebraMap A (CompletedAtPrime p)) ^ n)
        (stalkAdicCompletionEquivCompletedAtPrime p hI x) =
      Ideal.quotientMap (I.map (algebraMap A (CompletedAtPrime p)) ^ n)
        (stalkToCompletedAtPrime p)
        ((Ideal.pow_right_mono
          (map_stalkToCompletedAtPrime_map p I ▸ Ideal.le_comap_map) n).trans
          (Ideal.le_comap_pow _ n))
        (AdicCompletion.evalₐ (I.map (toStalk p)) n x) := by
  have := isAdicComplete_completedAtPrime p hI
  rw [← AdicCompletion.evalₐ_of (I.map (algebraMap A (CompletedAtPrime p))) n]
  have hof : AdicCompletion.of (I.map (algebraMap A (CompletedAtPrime p))) (CompletedAtPrime p)
      (stalkAdicCompletionEquivCompletedAtPrime p hI x) =
      AdicCompletion.mapₐ (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p))
        (ideal_map_toStalk_le_comap_ofId p I) x := by
    rw [stalkAdicCompletionEquivCompletedAtPrime, RingEquiv.trans_apply]
    exact (RingEquiv.ofBijective
      (algebraMap (CompletedAtPrime p)
        (AdicCompletion (I.map (algebraMap A (CompletedAtPrime p))) (CompletedAtPrime p)))
      (AdicCompletion.of_bijective _ _)).apply_symm_apply _
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (I.map (toStalk p)) n x)
  rw [hof, AdicCompletion.evalₐ_mapₐ, ← hs, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun (toRingHom_ofId_stalkAlgebra p) s)

end Quotients

end TauCeti.FormalScheme.Spf
