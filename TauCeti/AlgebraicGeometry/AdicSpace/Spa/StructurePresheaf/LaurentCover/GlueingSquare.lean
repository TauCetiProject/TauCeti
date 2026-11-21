/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing
public import TauCeti.RingTheory.Huber.GlueingSquare
public import TauCeti.RingTheory.Huber.LocalizationTopology.RationalCompletion
import Mathlib.CategoryTheory.Sites.Whiskering
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Proper
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.IsSheafFor
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Support

/-!
# Simple Laurent covers of sheafy Tate rings form glueing squares

Let `R` be a complete Hausdorff Tate ring and `S = (R, R⁺)` a Huber pair whose presentation-limit
structure presheaf is a sheaf (`IsSheafyForEveryPresentation S.plus`). For any `f : R` and models
`R₁`, `R₂`, `R₁₂` of `R⟨{f, 1}/1⟩ = R⟨f⟩`, `R⟨{1}/f⟩ = R⟨1/f⟩`, and `R⟨{f², 1}/f⟩ = R⟨f, 1/f⟩`
with continuous `R`-algebra transition maps `R₁ → R₁₂` and `R₂ → R₁₂`, the square
`R → R₁, R₂ → R₁₂` is a `TauCeti.Huber.GlueingSquare`.

This bridges sheafiness and Kedlaya–Liu Lemma 2.4.22 to Definition 2.7.3:
* *Exactness (`0 → R → R₁ × R₂ → R₁₂`)* comes from the sheaf condition on the two-piece cover
  `R({f, 1}/1)`, `R({1}/f)` with overlap `R({f², 1}/f)`.
* *Surjectivity of `(r₁, r₂) ↦ r₁ - r₂`* comes from
  `IsRationalCompletion.surjective_algebraMap_sub_laurent`.
* *Topological strictness* follows automatically from `GlueingSquare.of_exact` via Henkel's open
  mapping theorem and transport along `GlueingSquare.congr`.
* *Dense range of `R₂ → R₁₂`* follows from the shared denominator `f`, and *maximal-ideal prime
  contraction* follows from Wedhorn's Proposition 7.51 (`exists_mem_spa_supp_eq_of_isMaximal`).

## Main results

* `TauCeti.ValuationSpectrum.spaBasicOpen_laurentOverlap_eq_inf`:
  `R({f², 1}/f) = R({f, 1}/1) ⊓ R({1}/f)`.
* `TauCeti.Huber.laurent_injective_and_exact_of_isSheafyForEveryPresentation`: algebraic left
  exactness of `0 → R → R₁ × R₂ → R₁₂`.
* `TauCeti.Huber.GlueingSquare.of_simpleLaurent` and
  `TauCeti.Huber.GlueingSquare.of_simpleLaurent_of_isSheafyRing`: simple Laurent covers of sheafy
  complete Hausdorff Tate rings form glueing squares.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23; §2.7, Definition 2.7.3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.51 and §8.1.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.ValuationSpectrum

namespace TauCeti.ValuationSpectrum

open scoped Pointwise in
/-- The basic open `R({f², 1}/f)` equals the intersection `R({f, 1}/1) ⊓ R({1}/f)` of the two
pieces of the simple Laurent cover of `Spa(A, A⁺)`: intersecting `{f, 1}/1` and `{1}/f` gives
`{f², f, 1}/(1 · f)`, and the denominator `f` may be dropped from `{f², f, 1}` by
`rationalSubset_insert_self`. -/
theorem spaBasicOpen_laurentOverlap_eq_inf {A : Type*} [CommRing A] [TopologicalSpace A]
    [DecidableEq A] (Aplus : Subring A) (f : A) :
    spaBasicOpen Aplus {f * f, 1} f =
      spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f := by
  have hrat : rationalSubset Aplus {f * f, 1} f =
      rationalSubset Aplus {f, 1} 1 ∩ rationalSubset Aplus {1} f := by
    rw [rationalSubset_inter, one_mul, ← rationalSubset_insert_self Aplus {f * f, 1} f]
    congr 1; ext x; simp [Finset.mem_mul, eq_comm]; tauto
  ext v
  simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_spaBasicOpen]
  rw [← Set.mem_inter_iff, ← hrat]

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber

section Helpers

universe v

private def isoToRingEquiv {U V : _root_.TopCommRingCat.{v}} (I : U ≅ V) : U ≃+* V :=
  RingEquiv.ofRingHom I.hom.val I.inv.val
    (RingHom.ext fun x ↦ I.inv_hom_id_apply x) (RingHom.ext fun y ↦ I.hom_inv_id_apply y)

variable {R : Type v} [CommRing R] [UniformSpace R] [IsTopologicalRing R]

section RationalSection

variable (P : PairOfDefinition R) {Aplus : Subring R}
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset R) (s : R)
  (hT : IsOpen (Ideal.span (T : Set R) : Set R))

private noncomputable def rationalSectionTopIso :
    (TopCommRingCat.isCompleteSeparated.ι.obj
      (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s))) ≅
      _root_.TopCommRingCat.of
        (ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT)) :=
  let p : Presentation P := ⟨T, s, P.hasDenominatorPower_of_isOpen_span T s _ hT⟩
  (TopCommRingCat.isCompleteSeparated.ι.mapIso (presentationLimitRationalIso Aplus hAplus p hT))
    ≪≫ eqToIso (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)

variable {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
  (hB : IsRationalCompletion P T s hT B)

/-- Bicontinuous ring isomorphism `presentationLimit Aplus (spaBasicOpen Aplus T s) ≃+* B` for any
model `B` of `R⟨T/s⟩`. -/
private noncomputable def rationalSectionRingEquiv :
    presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃+* B :=
  (isoToRingEquiv (rationalSectionTopIso P hAplus T s hT)).trans
    ((isRationalCompletion_iff_ratLoc P T s hT B).mp hB).choose.toRingEquiv

private theorem rationalSectionRingEquiv_apply
    (z : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) :
    let p : Presentation P := ⟨T, s, P.hasDenominatorPower_of_isOpen_span T s _ hT⟩
    rationalSectionRingEquiv P hAplus T s hT hB z =
      ((isRationalCompletion_iff_ratLoc P T s hT B).mp hB).choose
        ((eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).val
          ((presentationLimitRationalIso Aplus hAplus p hT).hom.hom.val z)) := by
  simp only [rationalSectionRingEquiv, rationalSectionTopIso, isoToRingEquiv,
    RingEquiv.trans_apply, RingEquiv.ofRingHom_apply, AlgEquiv.coe_toRingEquiv,
    Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  -- Morphism composition `(f ≫ g).val z` in `TopCommRingCat` is definitionally `g.val (f.val z)`.
  rfl

private theorem continuous_rationalSectionRingEquiv :
    Continuous (rationalSectionRingEquiv P hAplus T s hT hB) :=
  ((isRationalCompletion_iff_ratLoc P T s hT B).mp hB).choose_spec.1.comp
    (rationalSectionTopIso P hAplus T s hT).hom.property

private theorem continuous_rationalSectionRingEquiv_symm :
    Continuous (rationalSectionRingEquiv P hAplus T s hT hB).symm :=
  (rationalSectionTopIso P hAplus T s hT).inv.property.comp
    ((isRationalCompletion_iff_ratLoc P T s hT B).mp hB).choose_spec.2

end RationalSection

section Complete

variable [IsUniformAddGroup R] [CompleteSpace R] [T0Space R]

/-- Bicontinuous ring isomorphism `presentationLimit Aplus ⊤ ≃+* R` identifying global sections
with `R`. -/
private noncomputable def topSectionRingEquiv (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    presentationLimit (P := P) Aplus ⊤ ≃+* R :=
  isoToRingEquiv <|
    (TopCommRingCat.isCompleteSeparated.ι.mapIso (presentationLimitTopIso (P := P) Aplus hAplus))
      ≪≫ eqToIso (CompleteSeparatedTopCommRingCat.of_obj R)

private theorem topSectionRingEquiv_symm_eq (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (r : R) :
    (topSectionRingEquiv P hAplus).symm r =
      (toPresentationLimit (P := P) Aplus ⊤).hom.val
        ((eqToHom (CompleteSeparatedTopCommRingCat.of_obj R).symm).val r) := by
  simp only [topSectionRingEquiv, isoToRingEquiv, RingEquiv.ofRingHom_symm,
    RingEquiv.ofRingHom_apply, Iso.trans_inv, eqToIso.inv, Functor.mapIso_inv,
    presentationLimitTopIso_inv]
  -- Morphism composition `(f ≫ g).val r` in `TopCommRingCat` is definitionally `g.val (f.val r)`.
  rfl

/-- Under `topSectionRingEquiv` and `rationalSectionRingEquiv`, restricting a global section to
`R(T/s)` is `algebraMap R B`. -/
private theorem rationalSectionRingEquiv_map_top (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset R) (s : R)
    (hT : IsOpen (Ideal.span (T : Set R) : Set R))
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    (hB : IsRationalCompletion P T s hT B) (x : presentationLimit (P := P) Aplus ⊤) :
    rationalSectionRingEquiv P hAplus T s hT hB
        ((presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus T s ≤ ⊤)).hom.val x) =
      algebraMap R B (topSectionRingEquiv P hAplus x) := by
  let p : Presentation P := ⟨T, s, P.hasDenominatorPower_of_isOpen_span T s _ hT⟩
  set r := topSectionRingEquiv P hAplus x
  have hx : x = (topSectionRingEquiv P hAplus).symm r := by simp [r]
  have hof : (eqToHom (CompleteSeparatedTopCommRingCat.of_obj R)).val
      ((eqToHom (CompleteSeparatedTopCommRingCat.of_obj R).symm).val r) = r :=
    (eqToIso (CompleteSeparatedTopCommRingCat.of_obj R).symm).hom_inv_id_apply r
  rw [hx, topSectionRingEquiv_symm_eq, rationalSectionRingEquiv_apply,
    presentationLimitRationalIso_map_top_apply Aplus hAplus p hT, hof, ← algebraMap_ratLoc,
    ((isRationalCompletion_iff_ratLoc P T s hT B).mp hB).choose.commutes]

/-- Under `rationalSectionRingEquiv`, restriction along an inclusion of rational opens agrees with
any continuous `R`-algebra homomorphism `B → B'`. -/
private theorem rationalSectionRingEquiv_map_le (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {T T' : Finset R} {s s' : R}
    (hT : IsOpen (Ideal.span (T : Set R) : Set R))
    (hT' : IsOpen (Ideal.span (T' : Set R) : Set R))
    (hle : spaBasicOpen Aplus T' s' ≤ spaBasicOpen Aplus T s)
    {B B' : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    [CommRing B'] [TopologicalSpace B'] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    (hB : IsRationalCompletion P T s hT B) (hB' : IsRationalCompletion P T' s' hT' B')
    (hc : Continuous (algebraMap B B'))
    (z : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) :
    rationalSectionRingEquiv P hAplus T' s' hT' hB'
        ((presentationLimitMap (P := P) hle).hom.val z) =
      algebraMap B B' (rationalSectionRingEquiv P hAplus T s hT hB z) := by
  have : T2Space B' := hB'.t2Space
  set φB := rationalSectionRingEquiv P hAplus T s hT hB
  set φB' := rationalSectionRingEquiv P hAplus T' s' hT' hB'
  let g : B →+* B' :=
    φB'.toRingHom.comp <| (presentationLimitMap (P := P) hle).hom.val.comp φB.symm.toRingHom
  have hg_cont : Continuous g :=
    (continuous_rationalSectionRingEquiv P hAplus T' s' hT' hB').comp <|
      (presentationLimitMap (P := P) hle).hom.property.comp
        (continuous_rationalSectionRingEquiv_symm P hAplus T s hT hB)
  have hg_eq : g = algebraMap B B' :=
    hB.ringHom_ext_of_continuous hg_cont hc <| RingHom.ext fun r ↦ by
    let x₀ := (topSectionRingEquiv P hAplus).symm r
    have hrB : algebraMap R B r =
        φB ((presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus T s ≤ ⊤)).hom.val x₀) := by
      rw [rationalSectionRingEquiv_map_top, RingEquiv.apply_symm_apply]
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R B B', hrB]
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply, presentationLimitMap_apply_presentationLimitMap_apply]
    dsimp only [φB']
    rw [rationalSectionRingEquiv_map_top, RingEquiv.apply_symm_apply]
  rw [← congrArg (· (φB z)) hg_eq]
  simp [g]

end Complete

/-- Sheafiness of `presentationLimitPresheaf P Aplus` implies the sheaf condition for the two-piece
Laurent cover on `presentationLimit`. -/
private theorem existsUnique_presentationLimit_laurent [IsHuberRing R] [DecidableEq R]
    (P : PairOfDefinition R) {Aplus : Subring R} (hs : IsSheafyForEveryPresentation Aplus) (f : R)
    (x₁ : presentationLimit (P := P) Aplus (spaBasicOpen Aplus {f, 1} 1))
    (x₂ : presentationLimit (P := P) Aplus (spaBasicOpen Aplus {1} f))
    (hx : (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val x₁ =
      (presentationLimitMap (P := P)
        (inf_le_right : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val x₂) :
    ∃! a : presentationLimit (P := P) Aplus ⊤,
      (presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus {f, 1} 1 ≤ ⊤)).hom.val a = x₁ ∧
      (presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus {1} f ≤ ⊤)).hom.val a = x₂ := by
  have hsheaf := ((isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P).mp hs).2
  have hsheafG : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _root_.TopCommRingCat)
      (Presheaf.isSheaf_comp_of_isSheaf _ (presentationLimitPresheaf P Aplus)
        TopCommRingCat.isCompleteSeparated.ι hsheaf)
  let U : Bool → Opens ↥(spa Aplus) :=
    fun b ↦ b.rec (spaBasicOpen Aplus {1} f) (spaBasicOpen Aplus {f, 1} 1)
  have hcov : Sieve.ofArrows U (fun _ ↦ homOfLE le_top) ∈
      Opens.grothendieckTopology ↥(spa Aplus) ⊤ := fun v _ ↦ by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (spa_subset_iUnion_laurentCover Aplus f v.property)
    refine ⟨U b, homOfLE le_top, Sieve.ofArrows_mk _ _ b, ?_⟩
    cases b <;> simpa [U, mem_spaBasicOpen, mem_rationalSubset_iff] using hb
  have hfor := (Presieve.isSheafFor_iff_generate _).mpr (hsheafG.isSheafFor _ hcov)
  obtain ⟨a, ha, hu⟩ := (isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P
    (fun (b : Bool) ↦ (le_top : U b ≤ ⊤))).mp hfor (fun b ↦ b.rec x₂ x₁) fun i j ↦ by
    cases i <;> cases j
    · rfl
    · have h := congrArg (presentationLimitMap (P := P)
          (le_inf inf_le_right inf_le_left : U false ⊓ U true ≤ U true ⊓ U false)).hom.val hx.symm
      rwa [presentationLimitMap_apply_presentationLimitMap_apply,
        presentationLimitMap_apply_presentationLimitMap_apply] at h
    · exact hx
    · rfl
  exact ⟨a, ⟨ha true, ha false⟩, fun a' ⟨ha'₁, ha'₂⟩ ↦ hu a' fun b ↦ by cases b <;> assumption⟩

/-- If a point `v ∈ R(T/s)` has maximal support `m = v.supp`, then `m` contracts from a prime ideal
of any model `B` of `R⟨T/s⟩`. -/
private theorem exists_prime_comap_eq_of_mem_rationalSubset [IsHuberRing R]
    {P P₀ : PairOfDefinition R} {S : Pair R} (hP₀ : P₀.ringOfDefinition ≤ S.plus)
    {T : Finset R} {s : R} {hT : IsOpen (Ideal.span (T : Set R) : Set R)}
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    (hB : IsRationalCompletion P T s hT B) {v : Spv R}
    (hvb : v ∈ rationalSubset S.plus T s) (hm : v.supp.IsMaximal) :
    ∃ q : Ideal B, q.IsPrime ∧ q.comap (algebraMap R B) = v.supp := by
  obtain ⟨e, -, -⟩ := (isRationalCompletion_iff_ratLoc P₀ T s hT B).mp
    (hB.congr_pairOfDefinition P₀)
  let hden := P₀.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  have hcomp : e.toRingHom.comp (P₀.toCompletionLoc T s _ hden) = algebraMap R B :=
    RingHom.ext fun a ↦ by simpa [algebraMap_ratLoc] using e.commutes a
  set J := Ideal.map (P₀.toCompletionLoc T s _ hden) v.supp
  have hne : Ideal.map (algebraMap R B) v.supp ≠ ⊤ := by
    rw [← hcomp, ← Ideal.map_map]
    intro htop
    have hcomp_id : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ :=
      RingHom.ext e.symm_apply_apply
    have hJtop : J = ⊤ := by
      have h := congrArg (Ideal.map e.symm.toRingHom) htop
      rwa [Ideal.map_map, hcomp_id, Ideal.map_id, Ideal.map_top] at h
    exact map_supp_toCompletionLoc_ne_top P₀ S.plus hP₀ T s _ hden hvb hJtop
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨M, hMmax.isPrime,
    (hm.eq_of_le (hMmax.isPrime.comap _).ne_top (Ideal.map_le_iff_le_comap.mp hle)).symm⟩

/-- Maximal-ideal prime contraction for a simple Laurent cover: every maximal ideal of `R` is the
contraction of a prime ideal of `R₁ × R₂` via a point of `Spa(R, R⁺)`. -/
private theorem exists_prime_comap_eq_of_simpleLaurent [IsUniformAddGroup R] [CompleteSpace R]
    [T0Space R] [IsHuberRing R] [DecidableEq R]
    (P : PairOfDefinition R) (S : Pair R) (hs : IsSheafyForEveryPresentation S.plus) (f : R)
    {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [TopologicalSpace R₁] [TopologicalSpace R₂]
    [Algebra R R₁] [Algebra R R₂]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (m : Ideal R) (hm : m.IsMaximal) :
    ∃ p : Ideal (R₁ × R₂), p.IsPrime ∧
      p.comap ((algebraMap R R₁).prod (algebraMap R R₂)) = m := by
  have := hm
  obtain ⟨P₀, hP₀, -⟩ := hs.exists_compatible_isSheaf
  obtain ⟨v, hv, rfl⟩ := exists_mem_spa_supp_eq_of_isMaximal S.plus S.isRingOfIntegralElements m
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (spa_subset_iUnion_laurentCover S.plus f hv)
  cases b with
  | true =>
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₁
      (by simpa [mem_rationalSubset_iff] using hb) hm
    exact ⟨q.comap (RingHom.fst R₁ R₂), hq.comap _, by rw [Ideal.comap_comap]; exact hqm⟩
  | false =>
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₂
      (by simpa [mem_rationalSubset_iff] using hb) hm
    exact ⟨q.comap (RingHom.snd R₁ R₂), hq.comap _, by rw [Ideal.comap_comap]; exact hqm⟩

end Helpers

section Main

variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [CompleteSpace R] [T0Space R]
  [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [DecidableEq R]
  {P : PairOfDefinition R} {f : R}
  {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
  {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
  {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}

private theorem presentationLimitMap_laurentInf_eq {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁) (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂))
    {y₁ : R₁} {y₂ : R₂} (hy : algebraMap R₁ R₁₂ y₁ = algebraMap R₂ R₁₂ y₂) :
    (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val
      ((rationalSectionRingEquiv P hAplus {f, 1} 1 hT₁ h₁).symm y₁) =
    (presentationLimitMap (P := P)
        (inf_le_right : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.val
      ((rationalSectionRingEquiv P hAplus {1} f hT₂ h₂).symm y₂) := by
  have hEq := spaBasicOpen_laurentOverlap_eq_inf Aplus f
  set e₁ := rationalSectionRingEquiv P hAplus {f, 1} 1 hT₁ h₁
  set e₂ := rationalSectionRingEquiv P hAplus {1} f hT₂ h₂
  set e₁₂ := rationalSectionRingEquiv P hAplus {f * f, 1} f hT₁₂ h₁₂
  have hInv : Function.LeftInverse (presentationLimitMap (P := P) hEq.ge).hom.val
      (presentationLimitMap (P := P) hEq.le).hom.val := fun z ↦ by
    rw [presentationLimitMap_apply_presentationLimitMap_apply, presentationLimitMap_refl]
    exact ConcreteCategory.id_apply z
  refine hInv.injective (e₁₂.injective ?_)
  rw [presentationLimitMap_apply_presentationLimitMap_apply,
    presentationLimitMap_apply_presentationLimitMap_apply,
    rationalSectionRingEquiv_map_le P hAplus hT₁ hT₁₂ (hEq.le.trans inf_le_left) h₁ h₁₂ hc₁,
    rationalSectionRingEquiv_map_le P hAplus hT₂ hT₁₂ (hEq.le.trans inf_le_right) h₂ h₁₂ hc₂,
    e₁.apply_symm_apply, e₂.apply_symm_apply, hy]

/-- Over a complete Hausdorff Huber ring `R` equipped with a Huber pair `S` satisfying
`IsSheafyForEveryPresentation S.plus`, the simple Laurent sequence `0 → R → R₁ × R₂ → R₁₂` is
injective on `R` and exact in the middle. -/
theorem laurent_injective_and_exact_of_isSheafyForEveryPresentation [IsHuberRing R] (S : Pair R)
    (hs : IsSheafyForEveryPresentation S.plus) (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂) (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    (Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r)) ∧
      Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
        fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2 := by
  have hSplus : ∀ ⦃a⦄, a ∈ S.plus → IsPowerBounded a :=
    fun _ ha ↦ mem_powerBoundedSubring.mp (S.isRingOfIntegralElements.le_powerBoundedSubring ha)
  set e₀ := topSectionRingEquiv P hSplus
  set e₁ := rationalSectionRingEquiv P hSplus {f, 1} 1 hT₁ h₁
  set e₂ := rationalSectionRingEquiv P hSplus {1} f hT₂ h₂
  refine ⟨fun r₁ r₂ hr ↦ ?_, fun ⟨x₁, x₂⟩ ↦ ⟨fun hsub ↦ ?_, ?_⟩⟩
  · have hglue := existsUnique_presentationLimit_laurent P hs f
      (e₁.symm (algebraMap R R₁ r₁)) (e₂.symm (algebraMap R R₂ r₁))
      (presentationLimitMap_laurentInf_eq hSplus h₁ h₂ h₁₂ hc₁ hc₂ (by
        rw [← IsScalarTower.algebraMap_apply R R₁ R₁₂,
          ← IsScalarTower.algebraMap_apply R R₂ R₁₂]))
    have htop₁ (r : R) : e₁ ((presentationLimitMap (P := P) le_top).hom.val (e₀.symm r)) =
        algebraMap R R₁ r := by rw [rationalSectionRingEquiv_map_top, e₀.apply_symm_apply]
    have htop₂ (r : R) : e₂ ((presentationLimitMap (P := P) le_top).hom.val (e₀.symm r)) =
        algebraMap R R₂ r := by rw [rationalSectionRingEquiv_map_top, e₀.apply_symm_apply]
    exact e₀.symm.injective (hglue.unique
      ⟨e₁.injective (by rw [e₁.apply_symm_apply, htop₁]),
       e₂.injective (by rw [e₂.apply_symm_apply, htop₂])⟩
      ⟨e₁.injective (by rw [e₁.apply_symm_apply, htop₁]; exact (congrArg Prod.fst hr).symm),
       e₂.injective (by rw [e₂.apply_symm_apply, htop₂]; exact (congrArg Prod.snd hr).symm)⟩)
  · obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := existsUnique_presentationLimit_laurent P hs f
      (e₁.symm x₁) (e₂.symm x₂)
      (presentationLimitMap_laurentInf_eq hSplus h₁ h₂ h₁₂ hc₁ hc₂ (sub_eq_zero.mp hsub))
    refine ⟨e₀ a, Prod.ext ?_ ?_⟩
    · have h := congrArg e₁ ha₁; rwa [e₁.apply_symm_apply, rationalSectionRingEquiv_map_top] at h
    · have h := congrArg e₂ ha₂; rwa [e₂.apply_symm_apply, rationalSectionRingEquiv_map_top] at h
  · rintro ⟨r, hr⟩
    rcases Prod.mk.inj hr with ⟨rfl, rfl⟩
    simp [← IsScalarTower.algebraMap_apply R R₁ R₁₂, ← IsScalarTower.algebraMap_apply R R₂ R₁₂]

/-- A simple Laurent cover `{|f| ≤ 1}`, `{|f| ≥ 1}` of a complete Hausdorff Tate ring `R` equipped
with a Huber pair `S` satisfying `IsSheafyForEveryPresentation S.plus` forms a `GlueingSquare`
(Kedlaya–Liu, §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23). -/
theorem GlueingSquare.of_simpleLaurent [IsTateRing R] (S : Pair R)
    (hs : IsSheafyForEveryPresentation S.plus) (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂) (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ := by
  obtain ⟨e₁, he₁, he₁'⟩ := (isRationalCompletion_iff_ratLoc P {f, 1} 1 hT₁ R₁).mp h₁
  obtain ⟨e₂, he₂, he₂'⟩ := (isRationalCompletion_iff_ratLoc P {1} f hT₂ R₂).mp h₂
  obtain ⟨e₁₂, he₁₂, he₁₂'⟩ := (isRationalCompletion_iff_ratLoc P {f * f, 1} f hT₁₂ R₁₂).mp h₁₂
  let L₁ := ratLoc P {f, 1} 1 (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₁)
  let L₂ := ratLoc P {1} f (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₂)
  let L₁₂ := ratLoc P {f * f, 1} f (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₁₂)
  let φ₁ : L₁ →+* L₁₂ := e₁₂.symm.toRingHom.comp ((algebraMap R₁ R₁₂).comp e₁.toRingHom)
  let φ₂ : L₂ →+* L₁₂ := e₁₂.symm.toRingHom.comp ((algebraMap R₂ R₁₂).comp e₂.toRingHom)
  let _ : Algebra L₁ L₁₂ := φ₁.toAlgebra
  let _ : Algebra L₂ L₁₂ := φ₂.toAlgebra
  have _ : IsScalarTower R L₁ L₁₂ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, φ₁, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
    rw [e₁.commutes, ← IsScalarTower.algebraMap_apply R R₁ R₁₂, ← e₁₂.commutes,
      AlgEquiv.symm_apply_apply]
  have _ : IsScalarTower R L₂ L₁₂ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, φ₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
    rw [e₂.commutes, ← IsScalarTower.algebraMap_apply R R₂ R₁₂, ← e₁₂.commutes,
      AlgEquiv.symm_apply_apply]
  have hL₁ := isRationalCompletion_ratLoc P {f, 1} 1 hT₁
  have hL₂ := isRationalCompletion_ratLoc P {1} f hT₂
  have hL₁₂ := isRationalCompletion_ratLoc P {f * f, 1} f hT₁₂
  have hcL₁ : Continuous (algebraMap L₁ L₁₂) := by
    rw [RingHom.algebraMap_toAlgebra]; exact he₁₂'.comp (hc₁.comp he₁)
  have hcL₂ : Continuous (algebraMap L₂ L₁₂) := by
    rw [RingHom.algebraMap_toAlgebra]; exact he₁₂'.comp (hc₂.comp he₂)
  obtain ⟨hinj, hexact⟩ :=
    laurent_injective_and_exact_of_isSheafyForEveryPresentation S hs hL₁ hL₂ hL₁₂ hcL₁ hcL₂
  have hsqL : GlueingSquare R L₁ L₂ L₁₂ :=
    GlueingSquare.of_exact hL₁.continuous_algebraMap hL₂.continuous_algebraMap hcL₁ hcL₂
      hinj hexact (hL₁.surjective_algebraMap_sub_laurent hL₂ hL₁₂ hcL₁ hcL₂)
      (hL₂.denseRange_of_comp_algebraMap_eq hL₁₂
        (RingHom.ext fun x ↦ (IsScalarTower.algebraMap_apply R L₂ L₁₂ x).symm))
      (exists_prime_comap_eq_of_simpleLaurent P S hs f hL₁ hL₂)
  exact hsqL.congr e₁ he₁ he₁' e₂ he₂ he₂' e₁₂.toRingEquiv he₁₂ he₁₂'
    (fun x ↦ by simp only [RingHom.algebraMap_toAlgebra, φ₁, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply])
    (fun x ↦ by simp only [RingHom.algebraMap_toAlgebra, φ₂, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply])

/-- Convenience form of `GlueingSquare.of_simpleLaurent` for any sheafy complete Hausdorff Tate
ring `R`, using the canonical Huber pair `(R, R°)`. -/
theorem GlueingSquare.of_simpleLaurent_of_isSheafyRing [IsTateRing R] (hs : IsSheafyRing R)
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁) (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ :=
  GlueingSquare.of_simpleLaurent (Pair.powerBounded R)
    (hs.isSheafyForEveryPresentation (Pair.powerBounded R).isRingOfIntegralElements)
    h₁ h₂ h₁₂ hc₁ hc₂

end Main

end TauCeti.Huber
