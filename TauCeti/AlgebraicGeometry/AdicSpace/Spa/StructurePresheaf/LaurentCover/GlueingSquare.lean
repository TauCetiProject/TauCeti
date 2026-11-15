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
`R₁`, `R₂`, `R₁₂` of the completed rational localisations `R⟨{f, 1}/1⟩ = R⟨f⟩`,
`R⟨{1}/f⟩ = R⟨1/f⟩`, and `R⟨{f², 1}/f⟩ = R⟨f, 1/f⟩` equipped with continuous `R`-algebra
transition maps `R₁ → R₁₂` and `R₂ → R₁₂`, the square `R → R₁, R₂ → R₁₂` is a
`TauCeti.Huber.GlueingSquare`.

This formalises the bridge from sheafiness and Lemma 2.4.22 of Kedlaya–Liu to Definition 2.7.3
(used in the proof of Theorem 2.4.23 of Kedlaya–Liu):

* *Exactness in degree `0` (`0 → R → R₁ × R₂ → R₁₂`).* The basic opens `R({f, 1}/1)` and
  `R({1}/f)` cover `Spa(R, R⁺)` with intersection `R({f², 1}/f)`
  (`TauCeti.ValuationSpectrum.spaBasicOpen_laurentOverlap_eq_inf`). The sheaf condition on
  `presentationLimitPresheaf P S.plus`, read through `presentationLimitTopIso` and
  `presentationLimitRationalIso` together with uniqueness of continuous `R`-algebra homomorphisms
  out of `R₁` and `R₂`, gives injectivity and middle exactness
  (`TauCeti.Huber.laurent_injective_and_exact_of_isSheafyForEveryPresentation`).
* *Surjectivity of `(r₁, r₂) ↦ r₁ - r₂`.* Supplied unconditionally (without sheafiness) by
  Kedlaya–Liu Lemma 2.4.22 (`TauCeti.Huber.IsRationalCompletion.surjective_algebraMap_sub_laurent`).
* *Topological strictness (`isInducing` and `isStrictMap_sub`).* Supplied automatically by Henkel's
  open mapping theorem over `R` via `TauCeti.Huber.GlueingSquare.of_exact` on complete Hausdorff
  models and transported along `TauCeti.Huber.GlueingSquare.congr`.
* *Dense range of `R₂ → R₁₂`.* Both `R₂ = R⟨{1}/f⟩` and `R₁₂ = R⟨{f², 1}/f⟩` localise away from
  the same denominator `f`, so the image of `R₂` contains the dense algebraic localisation `R[1/f]`
  (`TauCeti.Huber.IsRationalCompletion.denseRange_of_comp_algebraMap_eq`). By contrast, `R₁ → R₁₂`
  need not have dense range when `f` is not invertible in `R₁`.
* *Maximal-ideal prime contraction.* By Wedhorn's Proposition 7.51
  (`TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq_of_isMaximal`), every maximal ideal `𝔪` of `R`
  is the support of a point `v ∈ Spa(R, R⁺)`. That point lies in one of the two Laurent pieces,
  where `𝔪` generates a proper ideal in the corresponding completed localisation
  (`TauCeti.ValuationSpectrum.map_supp_toCompletionLoc_ne_top`) and therefore contracts from a
  maximal (hence prime) ideal of `R₁` or `R₂`.

## Main results

* `TauCeti.ValuationSpectrum.spaBasicOpen_laurentOverlap_eq_inf`: the basic open `R({f², 1}/f)` is
  the intersection `R({f, 1}/1) ⊓ R({1}/f)` of the two pieces of the simple Laurent cover.
* `TauCeti.Huber.laurent_injective_and_exact_of_isSheafyForEveryPresentation`: over a complete
  Hausdorff Huber pair satisfying `IsSheafyForEveryPresentation`, `0 → R → R₁ × R₂ → R₁₂` is exact.
* `TauCeti.Huber.GlueingSquare.of_simpleLaurent`: a simple Laurent cover of a complete Hausdorff
  Tate ring with a sheafy Huber pair forms a `GlueingSquare`.
* `TauCeti.Huber.GlueingSquare.of_simpleLaurent_of_isSheafyRing`: convenience corollary assuming
  `IsSheafyRing R` directly, using the canonical pair `(R, R°)`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23; §2.7, Definition 2.7.3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.51 and §8.1.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.ValuationSpectrum

namespace TauCeti.ValuationSpectrum

open scoped Classical Pointwise in
/-- The basic open `R({f², 1}/f)` equals the intersection `R({f, 1}/1) ⊓ R({1}/f)` of the two
pieces of the simple Laurent cover of `Spa(A, A⁺)`: intersecting `{f, 1}/1` and `{1}/f` gives
`{f², f, 1}/(1 · f)`, and the denominator `f` may be dropped from the numerator set `{f², f, 1}` by
`rationalSubset_insert_self`. -/
theorem spaBasicOpen_laurentOverlap_eq_inf {A : Type*} [CommRing A] [UniformSpace A]
    [DecidableEq A] (Aplus : Subring A) (f : A) :
    spaBasicOpen Aplus {f * f, 1} f =
      spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f := by
  have hrat : rationalSubset Aplus {f * f, 1} f =
      rationalSubset Aplus {f, 1} 1 ∩ rationalSubset Aplus {1} f := by
    rw [rationalSubset_inter, one_mul, ← rationalSubset_insert_self Aplus {f * f, 1} f]
    congr 1
    ext x
    simp [Finset.mem_mul, eq_comm]
    tauto
  ext v
  simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_spaBasicOpen]
  rw [← Set.mem_inter_iff, ← hrat]

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber

section Helpers

universe v

private theorem eqToHom_symm_apply_eqToHom_apply {X Y : _root_.TopCommRingCat.{v}} (e : X = Y)
    (x : X) : (eqToHom e.symm).1 ((eqToHom e).1 x) = x :=
  (eqToIso e).hom_inv_id_apply x

private def isoToRingEquiv {U V : _root_.TopCommRingCat.{v}} (I : U ≅ V) : U ≃+* V :=
  RingEquiv.ofRingHom I.hom.1 I.inv.1
    (RingHom.ext fun x ↦ I.inv_hom_id_apply x)
    (RingHom.ext fun y ↦ I.hom_inv_id_apply y)

private theorem continuous_isoToRingEquiv {U V : _root_.TopCommRingCat.{v}} (I : U ≅ V) :
    Continuous (isoToRingEquiv I) :=
  I.hom.2

private theorem continuous_isoToRingEquiv_symm {U V : _root_.TopCommRingCat.{v}} (I : U ≅ V) :
    Continuous (isoToRingEquiv I).symm :=
  I.inv.2

variable {R : Type v} [CommRing R] [UniformSpace R] [IsTopologicalRing R]

private noncomputable def rationalSectionTopIso (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset R) (s : R)
    (hT : IsOpen (Ideal.span (T : Set R) : Set R)) :
    (TopCommRingCat.isCompleteSeparated.ι.obj
      (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s))) ≅
      _root_.TopCommRingCat.of
        (letI := P.locUniformSpace T s (Localization.Away s)
          (P.hasDenominatorPower_of_isOpen_span T s _ hT)
        letI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s)
          (P.hasDenominatorPower_of_isOpen_span T s _ hT)
        letI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s)
          (P.hasDenominatorPower_of_isOpen_span T s _ hT)
        UniformSpace.Completion (Localization.Away s)) :=
  let p : Presentation P := ⟨T, s, P.hasDenominatorPower_of_isOpen_span T s _ hT⟩
  (TopCommRingCat.isCompleteSeparated.ι.mapIso (presentationLimitRationalIso Aplus hAplus p hT))
    ≪≫ eqToIso (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)

/-- Bicontinuous ring isomorphism `presentationLimit Aplus (spaBasicOpen Aplus T s) ≃+* B` for any
model `B` of `R⟨T/s⟩`. -/
private noncomputable def rationalSectionRingEquiv (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset R) (s : R)
    (hT : IsOpen (Ideal.span (T : Set R) : Set R))
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    (hB : IsRationalCompletion P T s hT B) :
    presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃+* B :=
  (isoToRingEquiv (rationalSectionTopIso P hAplus T s hT)).trans
    ((isRationalCompletion_def P T s hT B).mp hB).choose

private theorem continuous_rationalSectionRingEquiv (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset R) (s : R)
    (hT : IsOpen (Ideal.span (T : Set R) : Set R))
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    (hB : IsRationalCompletion P T s hT B) :
    Continuous (rationalSectionRingEquiv P hAplus T s hT hB) :=
  ((isRationalCompletion_def P T s hT B).mp hB).choose_spec.1.comp
    (continuous_isoToRingEquiv (rationalSectionTopIso P hAplus T s hT))

private theorem continuous_rationalSectionRingEquiv_symm (P : PairOfDefinition R)
    {Aplus : Subring R} (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset R) (s : R)
    (hT : IsOpen (Ideal.span (T : Set R) : Set R))
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    (hB : IsRationalCompletion P T s hT B) :
    Continuous (rationalSectionRingEquiv P hAplus T s hT hB).symm :=
  (continuous_isoToRingEquiv_symm (rationalSectionTopIso P hAplus T s hT)).comp
    ((isRationalCompletion_def P T s hT B).mp hB).choose_spec.2.1

section Complete

variable [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]

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
      (toPresentationLimit (P := P) Aplus ⊤).hom.1
        ((eqToHom (CompleteSeparatedTopCommRingCat.of_obj R).symm).1 r) := by
  simp only [topSectionRingEquiv, isoToRingEquiv, RingEquiv.ofRingHom_symm,
    RingEquiv.ofRingHom_apply, Iso.trans_inv, eqToIso.inv, Functor.mapIso_inv,
    presentationLimitTopIso_inv]
  rfl

/-- Under `topSectionRingEquiv` and `rationalSectionRingEquiv`, restricting a global section to
`R(T/s)` is `algebraMap R B`. -/
private theorem rationalSectionRingEquiv_map_top (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset R) (s : R)
    (hT : IsOpen (Ideal.span (T : Set R) : Set R))
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    (hB : IsRationalCompletion P T s hT B) (x : presentationLimit (P := P) Aplus ⊤) :
    rationalSectionRingEquiv P hAplus T s hT hB
        ((presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus T s ≤ ⊤)).hom.1 x) =
      algebraMap R B (topSectionRingEquiv P hAplus x) := by
  let p : Presentation P := ⟨T, s, P.hasDenominatorPower_of_isOpen_span T s _ hT⟩
  set r := topSectionRingEquiv P hAplus x
  have hx : x = (topSectionRingEquiv P hAplus).symm r := by simp [r]
  let c : CompleteSeparatedTopCommRingCat.of R :=
    (eqToHom (CompleteSeparatedTopCommRingCat.of_obj R).symm).1 r
  have hkey : toPresentationLimit (P := P) Aplus ⊤ ≫
      presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus p.num p.den ≤ ⊤) ≫
        (presentationLimitRationalIso Aplus hAplus p hT).hom = p.toCompletionLocObjHom := by
    simp
  have hc : (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).1
      ((presentationLimitRationalIso Aplus hAplus p hT).hom.hom.1
        ((presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus p.num p.den ≤ ⊤)).hom.1
          ((toPresentationLimit (P := P) Aplus ⊤).hom.1 c))) =
      P.toCompletionLoc p.num p.den _ p.hasDenominatorPower r := by
    refine (congrArg
      (fun g ↦ (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).1 (g.hom.1 c))
      hkey).trans ?_
    rw [Presentation.toCompletionLocObjHom_hom]
    exact (eqToHom_symm_apply_eqToHom_apply _ _).trans (congrArg _
      (eqToHom_symm_apply_eqToHom_apply (CompleteSeparatedTopCommRingCat.of_obj R).symm r))
  rw [hx, topSectionRingEquiv_symm_eq]
  have hdef : rationalSectionRingEquiv P hAplus T s hT hB
      ((presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus T s ≤ ⊤)).hom.1
        ((toPresentationLimit (P := P) Aplus ⊤).hom.1 c)) =
      ((isRationalCompletion_def P T s hT B).mp hB).choose
        ((eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).1
          ((presentationLimitRationalIso Aplus hAplus p hT).hom.hom.1
            ((presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus p.num p.den ≤ ⊤)).hom.1
              ((toPresentationLimit (P := P) Aplus ⊤).hom.1 c)))) := by
    simp only [rationalSectionRingEquiv, rationalSectionTopIso, isoToRingEquiv,
      RingEquiv.trans_apply, RingEquiv.ofRingHom_apply, Iso.trans_hom, eqToIso.hom,
      Functor.mapIso_hom]
    rfl
  rw [hdef, hc]
  exact congrArg (fun k : R →+* B ↦ k r)
    ((isRationalCompletion_def P T s hT B).mp hB).choose_spec.2.2

/-- Under `rationalSectionRingEquiv`, restriction along an inclusion of rational opens agrees with
any continuous `R`-algebra homomorphism `B → B'`. -/
private theorem rationalSectionRingEquiv_map_le (P : PairOfDefinition R) {Aplus : Subring R}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    {T T' : Finset R} {s s' : R}
    (hT : IsOpen (Ideal.span (T : Set R) : Set R))
    (hT' : IsOpen (Ideal.span (T' : Set R) : Set R))
    (hle : spaBasicOpen Aplus T' s' ≤ spaBasicOpen Aplus T s)
    {B B' : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    [CommRing B'] [TopologicalSpace B'] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    (hB : IsRationalCompletion P T s hT B) (hB' : IsRationalCompletion P T' s' hT' B')
    (hc : Continuous (algebraMap B B'))
    (z : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) :
    rationalSectionRingEquiv P hAplus T' s' hT' hB'
        ((presentationLimitMap (P := P) hle).hom.1 z) =
      algebraMap B B' (rationalSectionRingEquiv P hAplus T s hT hB z) := by
  have : T2Space B' := hB'.t2Space
  set φB := rationalSectionRingEquiv P hAplus T s hT hB
  set φB' := rationalSectionRingEquiv P hAplus T' s' hT' hB'
  let g : B →+* B' :=
    φB'.toRingHom.comp <| (presentationLimitMap (P := P) hle).hom.1.comp φB.symm.toRingHom
  have hg_cont : Continuous g :=
    (continuous_rationalSectionRingEquiv P hAplus T' s' hT' hB').comp <|
      (presentationLimitMap (P := P) hle).hom.2.comp
        (continuous_rationalSectionRingEquiv_symm P hAplus T s hT hB)
  have hg_eq : g = algebraMap B B' := by
    refine hB.ringHom_ext_of_continuous hg_cont hc (RingHom.ext fun r ↦ ?_)
    let x₀ := (topSectionRingEquiv P hAplus).symm r
    have hrB : algebraMap R B r =
        φB ((presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus T s ≤ ⊤)).hom.1 x₀) := by
      rw [rationalSectionRingEquiv_map_top, RingEquiv.apply_symm_apply]
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R B B', hrB]
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply, presentationLimitMap_apply_presentationLimitMap_apply]
    rw [show φB' _ = _ from rationalSectionRingEquiv_map_top P hAplus T' s' hT' hB' x₀,
      RingEquiv.apply_symm_apply]
  rw [← congrArg (fun k : B →+* B' ↦ k (φB z)) hg_eq]
  simp [g]

end Complete

/-- Sheafiness of `presentationLimitPresheaf P Aplus` implies the sheaf condition for the two-piece
Laurent cover on `presentationLimit`. -/
private theorem existsUnique_presentationLimit_laurent [IsHuberRing R] [DecidableEq R]
    (P : PairOfDefinition R) {Aplus : Subring R} (hs : IsSheafyForEveryPresentation Aplus) (f : R)
    (x₁ : presentationLimit (P := P) Aplus (spaBasicOpen Aplus {f, 1} 1))
    (x₂ : presentationLimit (P := P) Aplus (spaBasicOpen Aplus {1} f))
    (hx : (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.1 x₁ =
      (presentationLimitMap (P := P)
        (inf_le_right : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.1 x₂) :
    ∃! a : presentationLimit (P := P) Aplus ⊤,
      (presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus {f, 1} 1 ≤ ⊤)).hom.1 a = x₁ ∧
      (presentationLimitMap (P := P) (le_top : spaBasicOpen Aplus {1} f ≤ ⊤)).hom.1 a = x₂ := by
  have hsheaf := ((isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P).mp hs).2
  have hsheafG : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) :=
    Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology _)
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι)
      (forget _root_.TopCommRingCat)
      (Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology _)
        (presentationLimitPresheaf P Aplus) TopCommRingCat.isCompleteSeparated.ι hsheaf)
  let U : Bool → Opens ↥(spa Aplus) :=
    fun b ↦ b.rec (spaBasicOpen Aplus {1} f) (spaBasicOpen Aplus {f, 1} 1)
  have hcov : Sieve.ofArrows U (fun _ ↦ homOfLE le_top) ∈
      Opens.grothendieckTopology ↥(spa Aplus) ⊤ := by
    intro v _
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (spa_subset_iUnion_laurentCover Aplus f v.2)
    refine ⟨U b, homOfLE le_top, Sieve.ofArrows_mk _ _ b, ?_⟩
    cases b <;> simpa [U, mem_spaBasicOpen, mem_rationalSubset_iff] using hb
  have hfor : (Presieve.ofArrows U (fun _ ↦ homOfLE le_top)).IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsheafG.isSheafFor _ hcov)
  have hglue := (isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P
    (fun (b : Bool) ↦ (le_top : U b ≤ ⊤))).mp hfor (fun b ↦ b.rec x₂ x₁) fun i j ↦ by
    cases i <;> cases j
    · rfl
    · have h := congrArg (presentationLimitMap (P := P)
          (le_inf inf_le_right inf_le_left : U false ⊓ U true ≤ U true ⊓ U false)).hom.1 hx.symm
      rwa [presentationLimitMap_apply_presentationLimitMap_apply,
        presentationLimitMap_apply_presentationLimitMap_apply] at h
    · exact hx
    · rfl
  obtain ⟨a, ha, hu⟩ := hglue
  refine ⟨a, ⟨ha true, ha false⟩, fun a' ⟨ha'₁, ha'₂⟩ ↦ hu a' fun b ↦ ?_⟩
  cases b
  · exact ha'₂
  · exact ha'₁

/-- If a point `v ∈ R(T/s)` has maximal support `m = v.supp`, then `m` contracts from a prime ideal
of any model `B` of `R⟨T/s⟩`. -/
private theorem exists_prime_comap_eq_of_mem_rationalSubset [IsHuberRing R]
    {P P₀ : PairOfDefinition R} {S : Pair R} (hP₀ : P₀.ringOfDefinition ≤ S.plus)
    {T : Finset R} {s : R} {hT : IsOpen (Ideal.span (T : Set R) : Set R)}
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    (hB : IsRationalCompletion P T s hT B) {v : Spv R}
    (hvb : v ∈ rationalSubset S.plus T s) (hm : v.supp.IsMaximal) :
    ∃ q : Ideal B, q.IsPrime ∧ q.comap (algebraMap R B) = v.supp := by
  obtain ⟨e, -, -, hcomp⟩ := (isRationalCompletion_def P₀ T s hT B).mp
    (hB.congr_pairOfDefinition P₀)
  let hden := P₀.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  let _ := P₀.locUniformSpace T s _ hden
  have _ := P₀.isUniformAddGroup_locUniformSpace T s _ hden
  have _ := P₀.isTopologicalRing_locUniformSpace T s _ hden
  set J := Ideal.map (P₀.toCompletionLoc T s _ hden) v.supp
  have hne : Ideal.map (algebraMap R B) v.supp ≠ ⊤ := by
    rw [← hcomp, ← Ideal.map_map]
    intro htop
    have hJle : Ideal.map e.toRingHom J ≤ Ideal.comap e.symm.toRingHom J :=
      Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by
        change e.symm (e x) ∈ J
        simpa using hx
    rw [htop] at hJle
    have h1 : (1 : B) ∈ Ideal.comap e.symm.toRingHom J := hJle Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact map_supp_toCompletionLoc_ne_top P₀ S.plus hP₀ T s _ hden hvb
      ((Ideal.eq_top_iff_one J).mpr h1)
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hMprime : M.IsPrime := hMmax.isPrime
  exact ⟨M, hMprime, (hm.eq_of_le (hMprime.comap _).ne_top (Ideal.map_le_iff_le_comap.mp hle)).symm⟩

/-- Maximal-ideal prime contraction for a simple Laurent cover: every maximal ideal of `R` is the
contraction of a prime ideal of `R₁ × R₂` via a point of `Spa(R, R⁺)`. -/
private theorem exists_prime_comap_eq_of_simpleLaurent [IsUniformAddGroup R] [CompleteSpace R]
    [T2Space R] [IsHuberRing R] [DecidableEq R]
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
    have hvb : v ∈ rationalSubset S.plus {f, 1} 1 := by
      simpa [mem_rationalSubset_iff] using hb
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₁ hvb hm
    refine ⟨q.comap (RingHom.fst R₁ R₂), hq.comap _, ?_⟩
    rw [Ideal.comap_comap]
    exact hqm
  | false =>
    have hvb : v ∈ rationalSubset S.plus {1} f := by
      simpa [mem_rationalSubset_iff] using hb
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₂ hvb hm
    refine ⟨q.comap (RingHom.snd R₁ R₂), hq.comap _, ?_⟩
    rw [Ideal.comap_comap]
    exact hqm

end Helpers

section Main

universe u

private theorem exists_uniform_model {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]
    (hB : IsRationalCompletion P T s hT B) :
    ∃ (L : Type u) (_ : CommRing L) (_ : UniformSpace L) (_ : IsUniformAddGroup L)
      (_ : IsTopologicalRing L) (_ : CompleteSpace L) (_ : T2Space L) (_ : IsHuberRing L)
      (_ : Algebra A L) (e : L ≃ₐ[A] B),
      IsRationalCompletion P T s hT L ∧ Continuous e ∧ Continuous e.symm := by
  have hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  obtain ⟨e, he, he'⟩ := (isRationalCompletion_iff_ratLoc P T s hT B).mp hB
  exact ⟨ratLoc P T s hden, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, e,
    isRationalCompletion_ratLoc P T s hT, he, he'⟩

variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [CompleteSpace R] [T2Space R]
  [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]

private theorem presentationLimitMap_laurentInf_eq [DecidableEq R]
    (P : PairOfDefinition R) {Aplus : Subring R} (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (f : R)
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂))
    {y₁ : R₁} {y₂ : R₂} (hy : algebraMap R₁ R₁₂ y₁ = algebraMap R₂ R₁₂ y₂) :
    (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.1
      ((rationalSectionRingEquiv P hAplus {f, 1} 1 hT₁ h₁).symm y₁) =
    (presentationLimitMap (P := P)
        (inf_le_right : spaBasicOpen Aplus {f, 1} 1 ⊓ spaBasicOpen Aplus {1} f ≤ _)).hom.1
      ((rationalSectionRingEquiv P hAplus {1} f hT₂ h₂).symm y₂) := by
  have hEq := spaBasicOpen_laurentOverlap_eq_inf Aplus f
  set e₁ := rationalSectionRingEquiv P hAplus {f, 1} 1 hT₁ h₁
  set e₂ := rationalSectionRingEquiv P hAplus {1} f hT₂ h₂
  set e₁₂ := rationalSectionRingEquiv P hAplus {f * f, 1} f hT₁₂ h₁₂
  have hInv : Function.LeftInverse (presentationLimitMap (P := P) hEq.ge).hom.1
      (presentationLimitMap (P := P) hEq.le).hom.1 := fun z ↦ by
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
theorem laurent_injective_and_exact_of_isSheafyForEveryPresentation [IsHuberRing R] [DecidableEq R]
    {P : PairOfDefinition R} (S : Pair R) (hs : IsSheafyForEveryPresentation S.plus) {f : R}
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
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
  · have hr₁ : algebraMap R R₁ r₂ = algebraMap R R₁ r₁ := (congrArg Prod.fst hr).symm
    have hr₂ : algebraMap R R₂ r₂ = algebraMap R R₂ r₁ := (congrArg Prod.snd hr).symm
    have hglue := existsUnique_presentationLimit_laurent P hs f
      (e₁.symm (algebraMap R R₁ r₁)) (e₂.symm (algebraMap R R₂ r₁))
      (presentationLimitMap_laurentInf_eq P hSplus f h₁ h₂ h₁₂ hc₁ hc₂ (by
        rw [← IsScalarTower.algebraMap_apply R R₁ R₁₂,
          ← IsScalarTower.algebraMap_apply R R₂ R₁₂]))
    refine e₀.symm.injective (hglue.unique ⟨?_, ?_⟩ ⟨?_, ?_⟩)
    · exact e₁.injective (by
        rw [e₁.apply_symm_apply, rationalSectionRingEquiv_map_top, e₀.apply_symm_apply])
    · exact e₂.injective (by
        rw [e₂.apply_symm_apply, rationalSectionRingEquiv_map_top, e₀.apply_symm_apply])
    · exact e₁.injective (by
        rw [e₁.apply_symm_apply, rationalSectionRingEquiv_map_top, e₀.apply_symm_apply, hr₁])
    · exact e₂.injective (by
        rw [e₂.apply_symm_apply, rationalSectionRingEquiv_map_top, e₀.apply_symm_apply, hr₂])
  · obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := existsUnique_presentationLimit_laurent P hs f
      (e₁.symm x₁) (e₂.symm x₂)
      (presentationLimitMap_laurentInf_eq P hSplus f h₁ h₂ h₁₂ hc₁ hc₂ (sub_eq_zero.mp hsub))
    refine ⟨e₀ a, Prod.ext ?_ ?_⟩
    · have h := congrArg e₁ ha₁
      rwa [e₁.apply_symm_apply, rationalSectionRingEquiv_map_top] at h
    · have h := congrArg e₂ ha₂
      rwa [e₂.apply_symm_apply, rationalSectionRingEquiv_map_top] at h
  · rintro ⟨r, hr⟩
    rcases Prod.mk.inj hr with ⟨rfl, rfl⟩
    simp [← IsScalarTower.algebraMap_apply R R₁ R₁₂, ← IsScalarTower.algebraMap_apply R R₂ R₁₂]

private theorem GlueingSquare.of_simpleLaurent_of_uniform
    {L₁ L₂ L₁₂ : Type*} [CommRing L₁] [CommRing L₂] [CommRing L₁₂]
    [UniformSpace L₁] [IsUniformAddGroup L₁] [IsTopologicalRing L₁]
    [CompleteSpace L₁] [T2Space L₁] [IsHuberRing L₁]
    [UniformSpace L₂] [IsUniformAddGroup L₂] [IsTopologicalRing L₂]
    [CompleteSpace L₂] [T2Space L₂] [IsHuberRing L₂]
    [UniformSpace L₁₂] [IsUniformAddGroup L₁₂] [IsTopologicalRing L₁₂]
    [CompleteSpace L₁₂] [T2Space L₁₂] [IsHuberRing L₁₂]
    [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₁₂] [Algebra L₂ L₁₂] [Algebra R L₁₂]
    [IsScalarTower R L₁ L₁₂] [IsScalarTower R L₂ L₁₂]
    [IsTateRing R] [DecidableEq R] (P : PairOfDefinition R)
    (S : Pair R) (hs : IsSheafyForEveryPresentation S.plus) (f : R)
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}
    (hL₁ : IsRationalCompletion P {f, 1} 1 hT₁ L₁)
    (hL₂ : IsRationalCompletion P {1} f hT₂ L₂)
    (hL₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ L₁₂)
    (hcL₁ : Continuous (algebraMap L₁ L₁₂)) (hcL₂ : Continuous (algebraMap L₂ L₁₂)) :
    GlueingSquare R L₁ L₂ L₁₂ := by
  obtain ⟨hinj, hexact⟩ :=
    laurent_injective_and_exact_of_isSheafyForEveryPresentation S hs hL₁ hL₂ hL₁₂ hcL₁ hcL₂
  exact GlueingSquare.of_exact hL₁.continuous_algebraMap hL₂.continuous_algebraMap hcL₁ hcL₂
    hinj hexact
    (hL₁.surjective_algebraMap_sub_laurent hL₂ hL₁₂ hcL₁ hcL₂)
    (hL₂.denseRange_of_comp_algebraMap_eq hL₁₂
      (RingHom.ext fun x ↦ (IsScalarTower.algebraMap_apply R L₂ L₁₂ x).symm))
    (exists_prime_comap_eq_of_simpleLaurent P S hs f hL₁ hL₂)

/-- A simple Laurent cover `{|f| ≤ 1}`, `{|f| ≥ 1}` of a complete Hausdorff Tate ring `R` equipped
with a Huber pair `S` satisfying `IsSheafyForEveryPresentation S.plus` forms a `GlueingSquare`
(Kedlaya–Liu, §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23). -/
theorem GlueingSquare.of_simpleLaurent [IsTateRing R] [DecidableEq R] {P : PairOfDefinition R}
    (S : Pair R) (hs : IsSheafyForEveryPresentation S.plus) {f : R}
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ := by
  obtain ⟨L₁, _, _, _, _, _, _, _, _, e₁, hL₁, he₁, he₁'⟩ := exists_uniform_model P {f, 1} 1 hT₁ h₁
  obtain ⟨L₂, _, _, _, _, _, _, _, _, e₂, hL₂, he₂, he₂'⟩ := exists_uniform_model P {1} f hT₂ h₂
  obtain ⟨L₁₂, _, _, _, _, _, _, _, _, e₁₂, hL₁₂, he₁₂, he₁₂'⟩ :=
    exists_uniform_model P {f * f, 1} f hT₁₂ h₁₂
  let _ : Algebra L₁ L₁₂ :=
    RingHom.toAlgebra (e₁₂.symm.toRingHom.comp ((algebraMap R₁ R₁₂).comp e₁.toRingHom))
  let _ : Algebra L₂ L₁₂ :=
    RingHom.toAlgebra (e₁₂.symm.toRingHom.comp ((algebraMap R₂ R₁₂).comp e₂.toRingHom))
  have _ : IsScalarTower R L₁ L₁₂ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R L₁₂ r = e₁₂.symm (algebraMap R₁ R₁₂ (e₁ (algebraMap R L₁ r)))
    rw [e₁.commutes, ← IsScalarTower.algebraMap_apply R R₁ R₁₂, ← e₁₂.commutes,
      AlgEquiv.symm_apply_apply]
  have _ : IsScalarTower R L₂ L₁₂ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R L₁₂ r = e₁₂.symm (algebraMap R₂ R₁₂ (e₂ (algebraMap R L₂ r)))
    rw [e₂.commutes, ← IsScalarTower.algebraMap_apply R R₂ R₁₂, ← e₁₂.commutes,
      AlgEquiv.symm_apply_apply]
  have hcL₁ : Continuous (algebraMap L₁ L₁₂) := he₁₂'.comp (hc₁.comp he₁)
  have hcL₂ : Continuous (algebraMap L₂ L₁₂) := he₁₂'.comp (hc₂.comp he₂)
  have hsqL : GlueingSquare R L₁ L₂ L₁₂ :=
    GlueingSquare.of_simpleLaurent_of_uniform P S hs f hL₁ hL₂ hL₁₂ hcL₁ hcL₂
  refine hsqL.congr e₁ he₁ he₁' e₂ he₂ he₂' e₁₂ he₁₂ he₁₂' (fun x ↦ ?_) (fun x ↦ ?_)
  · change e₁₂ (e₁₂.symm (algebraMap R₁ R₁₂ (e₁ x))) = algebraMap R₁ R₁₂ (e₁ x)
    exact e₁₂.apply_symm_apply _
  · change e₁₂ (e₁₂.symm (algebraMap R₂ R₁₂ (e₂ x))) = algebraMap R₂ R₁₂ (e₂ x)
    exact e₁₂.apply_symm_apply _

/-- Convenience form of `GlueingSquare.of_simpleLaurent` for any sheafy complete Hausdorff Tate
ring `R`, using the canonical Huber pair `(R, R°)`. -/
theorem GlueingSquare.of_simpleLaurent_of_isSheafyRing [IsTateRing R] (hs : IsSheafyRing R)
    [DecidableEq R] {P : PairOfDefinition R} {f : R}
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ :=
  GlueingSquare.of_simpleLaurent (Pair.powerBounded R)
    (hs.isSheafyForEveryPresentation (Pair.powerBounded R).isRingOfIntegralElements)
    h₁ h₂ h₁₂ hc₁ hc₂

end Main

end TauCeti.Huber
