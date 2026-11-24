/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedAtPrime.Stalk
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Basic

import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.AdicCompletion.Pow
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Localization.AtPrime.Basic
import TauCeti.RingTheory.Localization.AtPrime.Quotient

/-!
# Completed localisations and stalks of `Spf A` modulo open ideals

Let `A` be a complete separated adic ring of finite ideal type, and let `p` be an open prime of
`A`, a point of the formal spectrum `Spf A` with underlying prime ideal `𝔭`. Building on the
canonical maps `A_𝔭 → 𝒪_{Spf A, p}` (`TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Basic`) and
`𝒪_{Spf A, p} → Â_𝔭` (`TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedAtPrime.Stalk`), this
module proves without any noetherian hypothesis on `A`:

* `stalkToCompletedAtPrime p` is compatible with `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭`;
* for every open ideal `J` of `A` (in particular every power `I ^ n` of an ideal of definition
  `I`), both maps induce ring isomorphisms
  `A_𝔭 ⧸ J A_𝔭 ≃+* 𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} ≃+* Â_𝔭 ⧸ J Â_𝔭`, compatible with reduction
  between open ideals `J ≤ K`, and for any prime `Q` of `A ⧸ J` lying over `𝔭` (in particular
  `(homeomorphSpecQuotient hJ p).asIdeal` when `J` is an ideal of definition), both
  `A_𝔭 ⧸ J A_𝔭` and `𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}` are canonically isomorphic to `(A ⧸ J)_Q`;
* for every ideal of definition `I` of `A`, `stalkToCompletedAtPrime p` identifies `Â_𝔭` with the
  `I`-adic completion of `𝒪_{Spf A, p}`.

For maximal-ideal-adic completion comparisons and discrete and complete local special cases, see
`TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Comparison`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
-/

public section

universe u

open CategoryTheory Limits IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

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

private theorem localizationToStalk_away (f : BasicNeighbourhood p)
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

/-- For every open ideal `J` of `A`, `A_𝔭 → 𝒪_{Spf A, p}` induces a bijection
`A_𝔭 ⧸ J A_𝔭 → 𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p}`. -/
theorem quotientMap_localizationToStalk_bijective_of_isOpen {J : Ideal A} (hJ : IsOpen (J : Set A))
    {H : J.map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ≤
      (J.map (toStalk p)).comap (localizationToStalk p)} :
    Function.Bijective (Ideal.quotientMap (J.map (toStalk p)) (localizationToStalk p) H) := by
  obtain ⟨n, hn⟩ :=
    (isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).2 (J : Set A) (hJ.mem_nhds J.zero_mem)
  exact RingHom.quotientMap_bijective_congr (localizationToStalk p) rfl
    (map_localizationToStalk_map p J)
    (RingHom.quotientMap_bijective_of_le (localizationToStalk p) (Ideal.map_mono hn)
      (RingHom.quotientMap_bijective_congr (localizationToStalk p) rfl
        (map_localizationToStalk_map p (IsAdicRing.ideal A ^ n)).symm
        (quotientMap_ideal_pow_bijective p n).1 (H₂ := Ideal.le_comap_map))
      (HJ := Ideal.le_comap_map))

/-- For every open ideal `J` of `A`, `𝒪_{Spf A, p} → Â_𝔭` induces a bijection
`𝒪_{Spf A, p} ⧸ J 𝒪_{Spf A, p} → Â_𝔭 ⧸ J Â_𝔭`. -/
theorem quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen {J : Ideal A}
    (hJ : IsOpen (J : Set A))
    {H : J.map (toStalk p) ≤
      (J.map (algebraMap A (CompletedAtPrime p))).comap (stalkToCompletedAtPrime p)} :
    Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap A (CompletedAtPrime p)))
        (stalkToCompletedAtPrime p) H) := by
  obtain ⟨n, hn⟩ :=
    (isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).2 (J : Set A) (hJ.mem_nhds J.zero_mem)
  exact RingHom.quotientMap_bijective_congr (stalkToCompletedAtPrime p) rfl
    (map_stalkToCompletedAtPrime_map p J)
    (RingHom.quotientMap_bijective_of_le (stalkToCompletedAtPrime p) (Ideal.map_mono hn)
      (RingHom.quotientMap_bijective_congr (stalkToCompletedAtPrime p) rfl
        (map_stalkToCompletedAtPrime_map p (IsAdicRing.ideal A ^ n)).symm
        (quotientMap_ideal_pow_bijective p n).2 (H₂ := Ideal.le_comap_map))
      (HJ := Ideal.le_comap_map))

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

/-- For every ideal of definition `I` of `A`, the map `𝒪_{Spf A, p} → Â_𝔭` identifies `Â_𝔭` with
the `I`-adic completion of `𝒪_{Spf A, p}` (EGA I, Ch. 0, 7.6.17). -/
noncomputable def stalkAdicCompletionEquivCompletedAtPrime {I : Ideal A} (hI : IsAdic I) :
    AdicCompletion (I.map (toStalk p)) ((Spf A).presheaf.stalk p) ≃+* CompletedAtPrime p :=
  haveI := isAdicComplete_completedAtPrime p hI
  letI : Algebra ((Spf A).presheaf.stalk p) (CompletedAtPrime p) :=
    (stalkToCompletedAtPrime p).toAlgebra
  have hle : I.map (toStalk p) ≤
      (I.map (algebraMap A (CompletedAtPrime p))).comap
        (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p)) := by
    change I.map (toStalk p) ≤
      (I.map (algebraMap A (CompletedAtPrime p))).comap (stalkToCompletedAtPrime p)
    exact Ideal.map_le_iff_le_comap.mp (map_stalkToCompletedAtPrime_map p I).le
  have hbij := AdicCompletion.mapₐ_bijective
      (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p)) hle fun n ↦ by
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
  let : Algebra ((Spf A).presheaf.stalk p) (CompletedAtPrime p) :=
    (stalkToCompletedAtPrime p).toAlgebra
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
  let : Algebra ((Spf A).presheaf.stalk p) (CompletedAtPrime p) :=
    (stalkToCompletedAtPrime p).toAlgebra
  rw [← AdicCompletion.evalₐ_of (I.map (algebraMap A (CompletedAtPrime p))) n]
  have hof : AdicCompletion.of (I.map (algebraMap A (CompletedAtPrime p))) (CompletedAtPrime p)
      (stalkAdicCompletionEquivCompletedAtPrime p hI x) =
      AdicCompletion.mapₐ (Algebra.ofId ((Spf A).presheaf.stalk p) (CompletedAtPrime p))
        (by
          change I.map (toStalk p) ≤
            (I.map (algebraMap A (CompletedAtPrime p))).comap (stalkToCompletedAtPrime p)
          exact Ideal.map_le_iff_le_comap.mp (map_stalkToCompletedAtPrime_map p I).le) x := by
    rw [stalkAdicCompletionEquivCompletedAtPrime, RingEquiv.trans_apply]
    exact (RingEquiv.ofBijective
      (algebraMap (CompletedAtPrime p)
        (AdicCompletion (I.map (algebraMap A (CompletedAtPrime p))) (CompletedAtPrime p)))
      (AdicCompletion.of_bijective _ _)).apply_symm_apply _
  rw [hof, AdicCompletion.evalₐ_mapₐ]
  rfl

end Quotients

end TauCeti.FormalScheme.Spf
