/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk

import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.AdicCompletion.Pow
import TauCeti.RingTheory.AdicCompletion.Topology
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Localization.AtPrime.Quotient

/-!
# Completed localisations and stalks of `Spf A` modulo open ideals

Let `A` be a complete separated adic ring of finite ideal type, and let `p` be an open prime of
`A`, a point of the formal spectrum `Spf A` with underlying prime ideal `𝔭`. Building on the
canonical maps `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` constructed in
`TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk`, this module proves without any noetherian
hypothesis on `A`:

* `Â_𝔭` is a local ring whose maximal ideal is the extension of `𝔪_{A_𝔭}`;
* for every open ideal `J` of `A` (in particular every power `I ^ n` of an ideal of definition
  `I`), both maps induce ring isomorphisms
  `A_𝔭 ⧸ J A_𝔭 ≃+* 𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} ≃+* Â_𝔭 ⧸ J Â_𝔭`, and for any prime `Q` of
  `A ⧸ J` lying over `𝔭` (in particular `(homeomorphSpecQuotient hJ p).asIdeal` when `J` is an
  ideal of definition), both `A_𝔭 ⧸ J A_𝔭` and `𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}` are canonically
  isomorphic to `(A ⧸ J)_Q`;
* for every ideal of definition `I` of `A`, `stalkToLocalCompletion p` identifies `Â_𝔭` with the
  `I`-adic completion of `𝒪_{Spf A, p}`.

For maximal-ideal-adic completion comparisons, discrete and complete local special cases, and
noetherian flatness and invariant transfers, see
`TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Comparison`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
-/

public section

open CategoryTheory Limits IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-! ### Local structure of `Â_𝔭` -/

section LocalStructure

omit [IsTopologicalRing A] [IsAdicRing A] in
/-- The extension of any ideal of definition `I` to `A_𝔭` lies in the maximal ideal of `A_𝔭`. -/
theorem ideal_map_le_maximalIdeal_localization {I : Ideal A} (hI : IsAdic I) :
    I.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (p : PrimeSpectrum A).asIdeal]
  exact Ideal.map_mono ((mem_carrier_iff_le hI).mp p.property)

/-- The completed localisation `Â_𝔭` is a local ring. -/
instance isLocalRing_localCompletion : IsLocalRing (LocalCompletion p) :=
  TauCeti.AdicCompletion.isLocalRing_of_le_maximalIdeal
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)

/-- The maximal ideal of `Â_𝔭` is the extension of the maximal ideal of `A_𝔭`. -/
theorem maximalIdeal_localCompletion :
    maximalIdeal (LocalCompletion p) =
      (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)).map
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) :=
  TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le_maximalIdeal
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    ((IsAdicRing.ideal_spec A).1.map _)

/-- The canonical completion map `A_𝔭 → Â_𝔭` is a local homomorphism. -/
instance isLocalHom_algebraMap_localCompletion :
    IsLocalHom
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) :=
  TauCeti.AdicCompletion.isLocalHom_algebraMap_of_le_maximalIdeal
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)

end LocalStructure

/-! ### Isomorphisms modulo open ideals and powers of ideals of definition -/

section Quotients

private noncomputable def awayToAtPrime (f : BasicNeighbourhood p) :
    Localization.Away f.elem →+* Localization.AtPrime (p : PrimeSpectrum A).asIdeal :=
  IsLocalization.map (T := (p : PrimeSpectrum A).asIdeal.primeCompl) _ (RingHom.id A)
    (Submonoid.powers_le.mpr f.notMem)

private theorem localizationToStalk_away (f : BasicNeighbourhood p)
    (y : Localization.Away f.elem) :
    localizationToStalk p (awayToAtPrime p f y) =
      (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).hom
        (colimit.ι (completedNeighbourhoodDiagram p) f
          (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) y)) := by
  let lhs : Localization.Away f.elem →+* (Spf A).presheaf.stalk p :=
    (localizationToStalk p).comp (awayToAtPrime p f)
  let rhs : Localization.Away f.elem →+* (Spf A).presheaf.stalk p :=
    ((completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1).hom.hom.comp
      (colimit.ι (completedNeighbourhoodDiagram p) f).hom).comp
      (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem))
  refine RingHom.congr_fun
    (IsLocalization.ringHom_ext (Submonoid.powers f.elem) (j := lhs) (k := rhs)
      (RingHom.ext fun a ↦ ?_)) y
  have hl : lhs (algebraMap A _ a) = toStalk p a := by
    simp only [lhs, RingHom.comp_apply, awayToAtPrime, IsLocalization.map_eq, RingHom.id_apply,
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

/-- Pushing an ideal of `A` to `𝒪_{Spf A, p}` and then along `stalkToLocalCompletion p` agrees
with pushing it directly to `Â_𝔭`. -/
@[simp]
theorem map_stalkToLocalCompletion_map (J : Ideal A) :
    (J.map (toStalk p)).map (stalkToLocalCompletion p) =
      J.map (algebraMap A (LocalCompletion p)) := by
  rw [Ideal.map_map, stalkToLocalCompletion_comp_toStalk]

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
  refine ⟨Ideal.Quotient.mk _ (awayToAtPrime p f y), ?_⟩
  rw [Ideal.quotientMap_mk]
  have hcomp : φ.comp (algebraMap A (CompletedAway A f.elem)) = toStalk p :=
    RingHom.ext fun a ↦ (toStalk_eq_completedNeighbourhoodColimitIso p f a).symm
  have hmem := Ideal.mem_map_of_mem φ hy'
  rw [Ideal.map_map, hcomp] at hmem
  have hsub : localizationToStalk p (awayToAtPrime p f y) - φ x =
      -φ (x - algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) y) := by
    rw [map_sub, neg_sub]
    exact congrArg (· - φ x) (localizationToStalk_away p f y)
  exact Ideal.Quotient.eq.mpr (hsub.symm ▸ neg_mem hmem)

private theorem quotientMap_ideal_pow_bijective (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((IsAdicRing.ideal A ^ n).map (toStalk p))
      (localizationToStalk p)
      (map_localizationToStalk_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)) ∧
    Function.Bijective (Ideal.quotientMap
      ((IsAdicRing.ideal A ^ n).map (algebraMap A (LocalCompletion p)))
      (stalkToLocalCompletion p)
      (map_stalkToLocalCompletion_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)) := by
  let q₁ := Ideal.quotientMap ((IsAdicRing.ideal A ^ n).map (toStalk p)) (localizationToStalk p)
    (map_localizationToStalk_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)
  let q₂ := Ideal.quotientMap ((IsAdicRing.ideal A ^ n).map (algebraMap A (LocalCompletion p)))
    (stalkToLocalCompletion p)
    (map_stalkToLocalCompletion_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map)
  have hcomp_bij : Function.Bijective (q₂ ∘ q₁) := by
    have hbij' := Ideal.quotientMap_bijective_congr
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p))
      (Ideal.map_pow _ _ _).symm
      (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, ← Ideal.map_pow])
      (AdicCompletion.quotientMap_algebraMap_bijective ((IsAdicRing.ideal_spec A).1.map _) n
        (H := (Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))
      (H₂ := Ideal.map_le_iff_le_comap.mpr fun _ ha ↦ by
        rw [Ideal.mem_comap, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
        exact Ideal.mem_map_of_mem _ ha)
    convert hbij' using 1
    ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [q₁, q₂, stalkToLocalCompletion_localizationToStalk]
  have hq₁_bij : Function.Bijective q₁ :=
    ⟨Function.Injective.of_comp hcomp_bij.1,
      quotientMap_localizationToStalk_surjective_ideal_pow p n⟩
  exact ⟨hq₁_bij, (Function.Bijective.of_comp_iff q₂ hq₁_bij).mp hcomp_bij⟩

/-- For every open ideal `J` of `A`, `A_𝔭 → 𝒪_{Spf A, p}` induces a bijection
`A_𝔭 ⧸ J A_𝔭 → 𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}`. -/
theorem quotientMap_localizationToStalk_bijective_of_isOpen {J : Ideal A} (hJ : IsOpen (J : Set A))
    {H : J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      (J.map (toStalk p)).comap (localizationToStalk p)} :
    Function.Bijective (Ideal.quotientMap (J.map (toStalk p)) (localizationToStalk p) H) := by
  obtain ⟨n, hn⟩ :=
    (isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).2 (J : Set A) (hJ.mem_nhds J.zero_mem)
  exact Ideal.quotientMap_bijective_congr (localizationToStalk p) rfl
    (map_localizationToStalk_map p J)
    (Ideal.quotientMap_bijective_of_le (localizationToStalk p) (Ideal.map_mono hn)
      (Ideal.quotientMap_bijective_congr (localizationToStalk p) rfl
        (map_localizationToStalk_map p (IsAdicRing.ideal A ^ n)).symm
        (quotientMap_ideal_pow_bijective p n).1 (H₂ := Ideal.le_comap_map))
      (HJ := Ideal.le_comap_map))

/-- For every open ideal `J` of `A`, `𝒪_{Spf A, p} → Â_𝔭` induces a bijection
`𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} → Â_𝔭 ⧸ J Â_𝔭`. -/
theorem quotientMap_stalkToLocalCompletion_bijective_of_isOpen {J : Ideal A}
    (hJ : IsOpen (J : Set A))
    {H : J.map (toStalk p) ≤
      (J.map (algebraMap A (LocalCompletion p))).comap (stalkToLocalCompletion p)} :
    Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap A (LocalCompletion p)))
        (stalkToLocalCompletion p) H) := by
  obtain ⟨n, hn⟩ :=
    (isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).2 (J : Set A) (hJ.mem_nhds J.zero_mem)
  exact Ideal.quotientMap_bijective_congr (stalkToLocalCompletion p) rfl
    (map_stalkToLocalCompletion_map p J)
    (Ideal.quotientMap_bijective_of_le (stalkToLocalCompletion p) (Ideal.map_mono hn)
      (Ideal.quotientMap_bijective_congr (stalkToLocalCompletion p) rfl
        (map_stalkToLocalCompletion_map p (IsAdicRing.ideal A ^ n)).symm
        (quotientMap_ideal_pow_bijective p n).2 (H₂ := Ideal.le_comap_map))
      (HJ := Ideal.le_comap_map))

/-- For every open ideal `J` of `A`, `A_𝔭 → Â_𝔭` induces a bijection
`A_𝔭 ⧸ J A_𝔭 → Â_𝔭 ⧸ J Â_𝔭`. -/
theorem quotientMap_algebraMap_localCompletion_bijective_of_isOpen {J : Ideal A}
    (hJ : IsOpen (J : Set A))
    {H : J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      (J.map (algebraMap A (LocalCompletion p))).comap
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p))} :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap A (LocalCompletion p)))
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) H) := by
  convert (quotientMap_stalkToLocalCompletion_bijective_of_isOpen p hJ
    (H := map_stalkToLocalCompletion_map p J ▸ Ideal.le_comap_map)).comp
    (quotientMap_localizationToStalk_bijective_of_isOpen p hJ
      (H := map_localizationToStalk_map p J ▸ Ideal.le_comap_map))
  ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [stalkToLocalCompletion_localizationToStalk]

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

/-- For every open ideal `J` of `A`, the canonical ring isomorphism
`𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} ≃+* Â_𝔭 ⧸ J Â_𝔭`. In particular this applies to `J = I ^ n` for
every ideal of definition `I` of `A` and every `n : ℕ`. -/
noncomputable def stalkQuotientEquivLocalCompletionQuotient {J : Ideal A}
    (hJ : IsOpen (J : Set A)) :
    ((Spf A).presheaf.stalk p ⧸ J.map (toStalk p)) ≃+*
      (LocalCompletion p ⧸ J.map (algebraMap A (LocalCompletion p))) :=
  RingEquiv.ofBijective _ (quotientMap_stalkToLocalCompletion_bijective_of_isOpen p hJ
    (H := map_stalkToLocalCompletion_map p J ▸ Ideal.le_comap_map))

/-- `stalkQuotientEquivLocalCompletionQuotient` acts by `stalkToLocalCompletion p` on cosets. -/
@[simp]
theorem stalkQuotientEquivLocalCompletionQuotient_mk {J : Ideal A} (hJ : IsOpen (J : Set A))
    (x : (Spf A).presheaf.stalk p) :
    stalkQuotientEquivLocalCompletionQuotient p hJ (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (stalkToLocalCompletion p x) := by
  rfl

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
  TauCeti.IsLocalization.AtPrime.quotientEquiv J Q

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
  exact TauCeti.IsLocalization.AtPrime.quotientEquiv_algebraMap J Q a

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

/-- For every ideal of definition `I` of `A`, `Â_𝔭` is `I Â_𝔭`-adically complete. -/
theorem isAdicComplete_localCompletion {I : Ideal A} (hI : IsAdic I) :
    IsAdicComplete (I.map (algebraMap A (LocalCompletion p))) (LocalCompletion p) :=
  (IsAdicComplete.map_algebraMap_iff I (LocalCompletion p)).mpr <|
    ((IsAdicRing.ideal_spec A).2.1.isAdicComplete_iff_of_isAdic hI).mp <|
      (IsAdicComplete.map_algebraMap_iff (IsAdicRing.ideal A) (LocalCompletion p)).mp
        (AdicCompletion.isAdicComplete ((IsAdicRing.ideal_spec A).1.map _))

/-- For every ideal of definition `I` of `A`, the map `𝒪_{Spf A, p} → Â_𝔭` identifies `Â_𝔭` with
the `I`-adic completion of `𝒪_{Spf A, p}` (EGA I, Ch. 0, 7.6.17). -/
noncomputable def stalkAdicCompletionEquivLocalCompletion {I : Ideal A} (hI : IsAdic I) :
    AdicCompletion (I.map (toStalk p)) ((Spf A).presheaf.stalk p) ≃+* LocalCompletion p :=
  haveI := isAdicComplete_localCompletion p hI
  letI : Algebra ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    (stalkToLocalCompletion p).toAlgebra
  have hle : I.map (toStalk p) ≤
      (I.map (algebraMap A (LocalCompletion p))).comap
        (Algebra.ofId ((Spf A).presheaf.stalk p) (LocalCompletion p)) := by
    change I.map (toStalk p) ≤
      (I.map (algebraMap A (LocalCompletion p))).comap (stalkToLocalCompletion p)
    exact Ideal.map_le_iff_le_comap.mp (map_stalkToLocalCompletion_map p I).le
  have hbij := AdicCompletion.mapₐ_bijective
      (Algebra.ofId ((Spf A).presheaf.stalk p) (LocalCompletion p)) hle fun n ↦ by
    have hq := quotientMap_stalkToLocalCompletion_bijective_of_isOpen p ((isAdic_iff.mp hI).1 n)
      (H := map_stalkToLocalCompletion_map p (I ^ n) ▸ Ideal.le_comap_map)
    exact Ideal.quotientMap_bijective_congr (stalkToLocalCompletion p) (Ideal.map_pow _ _ _)
      (Ideal.map_pow _ _ _) hq
  (AlgEquiv.ofBijective _ hbij).toRingEquiv.trans
    (RingEquiv.ofBijective
      (algebraMap (LocalCompletion p)
        (AdicCompletion (I.map (algebraMap A (LocalCompletion p))) (LocalCompletion p)))
      (AdicCompletion.of_bijective _ _)).symm

/-- On elements of `𝒪_{Spf A, p}`, `stalkAdicCompletionEquivLocalCompletion` applies
`stalkToLocalCompletion p`. -/
@[simp]
theorem stalkAdicCompletionEquivLocalCompletion_of {I : Ideal A} (hI : IsAdic I)
    (s : (Spf A).presheaf.stalk p) :
    stalkAdicCompletionEquivLocalCompletion p hI
        (AdicCompletion.of (I.map (toStalk p)) ((Spf A).presheaf.stalk p) s) =
      stalkToLocalCompletion p s := by
  let : Algebra ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    (stalkToLocalCompletion p).toAlgebra
  rw [stalkAdicCompletionEquivLocalCompletion, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
  exact AdicCompletion.mapₐ_of
    (Algebra.ofId ((Spf A).presheaf.stalk p) (LocalCompletion p)) _ s

/-- Modulo `(I Â_𝔭) ^ n`, `stalkAdicCompletionEquivLocalCompletion` reduces to the quotient map
induced by `stalkToLocalCompletion p` on `AdicCompletion.evalₐ (I 𝒪_{Spf A, p}) n`. -/
@[simp]
theorem mk_stalkAdicCompletionEquivLocalCompletion {I : Ideal A} (hI : IsAdic I) (n : ℕ)
    (x : AdicCompletion (I.map (toStalk p)) ((Spf A).presheaf.stalk p)) :
    Ideal.Quotient.mk (I.map (algebraMap A (LocalCompletion p)) ^ n)
        (stalkAdicCompletionEquivLocalCompletion p hI x) =
      Ideal.quotientMap (I.map (algebraMap A (LocalCompletion p)) ^ n)
        (stalkToLocalCompletion p)
        ((Ideal.pow_right_mono
          (map_stalkToLocalCompletion_map p I ▸ Ideal.le_comap_map) n).trans
          (Ideal.le_comap_pow _ n))
        (AdicCompletion.evalₐ (I.map (toStalk p)) n x) := by
  have := isAdicComplete_localCompletion p hI
  let : Algebra ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    (stalkToLocalCompletion p).toAlgebra
  rw [← AdicCompletion.evalₐ_of (I.map (algebraMap A (LocalCompletion p))) n]
  have hof : AdicCompletion.of (I.map (algebraMap A (LocalCompletion p))) (LocalCompletion p)
      (stalkAdicCompletionEquivLocalCompletion p hI x) =
      AdicCompletion.mapₐ (Algebra.ofId ((Spf A).presheaf.stalk p) (LocalCompletion p))
        (by
          change I.map (toStalk p) ≤
            (I.map (algebraMap A (LocalCompletion p))).comap (stalkToLocalCompletion p)
          exact Ideal.map_le_iff_le_comap.mp (map_stalkToLocalCompletion_map p I).le) x := by
    rw [stalkAdicCompletionEquivLocalCompletion, RingEquiv.trans_apply]
    exact (RingEquiv.ofBijective
      (algebraMap (LocalCompletion p)
        (AdicCompletion (I.map (algebraMap A (LocalCompletion p))) (LocalCompletion p)))
      (AdicCompletion.of_bijective _ _)).apply_symm_apply _
  rw [hof, AdicCompletion.evalₐ_mapₐ]
  rfl

end Quotients

end TauCeti.FormalScheme.Spf
