/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.SheafCriterion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

import Mathlib.Topology.Metrizable.CompletelyMetrizable
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.IsSheafFor
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.KanExtension
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic
import TauCeti.CategoryTheory.Sites.IsSheafForTrans
import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.Topology.Category.TopCommRingCat.Sheaf
import TauCeti.Topology.Homeomorph.Inducing

/-!
# Topological sheafhood from set-level sheafhood over a Tate ring

Over a Tate ring `A`, the structure presheaf `presentationLimitPresheaf P Aplus` of complete
separated topological commutative rings on `Spa(A, A⁺)` is a sheaf as soon as its underlying
presheaf of sets is a sheaf — and in fact as soon as its underlying presheaf of sets satisfies the
sheaf condition for every finite rational cover of every rational open.

The mechanism is the open mapping theorem over a Tate ring
(`LinearMap.isStrictMap_of_isClosed_range_of_isTateRing`). For a countable family `(V k)` of
rational open subsets of a rational open `W = R(T₀/s₀)`, `presentationLimitRationalIso` identifies
the sections over `W` with the completed rational localization `B = A⟨T₀/s₀⟩` — which is again a
complete Hausdorff first-countable Tate ring — and the sections over each `V k` with its completed
coordinate ring `B k`, which is completely metrizable. When the set-level presheaf satisfies the
sheaf condition for `(V k)`, the product restriction map `B → ∏ k, B k` is injective and its range
is cut out by pairwise overlap equalities in the Hausdorff rings of sections over `V k ⊓ V l`,
hence is closed. Henkel's open mapping theorem then makes the product restriction map strict and
therefore a topological embedding. Since rational opens are quasi-compact, arbitrary rational
covers reduce to finite subcovers, and `TauCeti.TopCommRingCat.isSheafFor_of_isSheafFor_forget`
upgrades set-level gluing to topological-ring gluing on the basis of rational opens.

## Main results

* `TauCeti.ValuationSpectrum.isInducing_presentationLimitMap_of_isSheafFor_spaRationalOpens`:
  over a Tate ring, if the underlying presheaf of sets satisfies the sheaf condition for a
  countable family of rational open subsets of a rational open, then the product restriction map
  on presentation limits is inducing.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_of_isSheafFor_finite_rationalOpens`:
  over a Tate ring with `A⁺ ⊆ A°`, set-level gluing for finite rational covers of rational opens
  implies that `presentationLimitPresheaf P Aplus` is a sheaf of complete separated topological
  commutative rings on all opens of `Spa(A, A⁺)`.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_iff_isSheaf_forget`:
  over a Tate ring with `A⁺ ⊆ A°`, `presentationLimitPresheaf P Aplus` is a sheaf if and only if
  its underlying presheaf of sets is a sheaf.

## References

* P. Scholze and J. Weinstein, *Berkeley Lectures on `p`-adic Geometry*, Annals of Mathematics
  Studies 207, Princeton University Press (2020), Lecture 4, Proposition 4.3.4.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.20 and Theorem 6.16.
-/

public section

open CategoryTheory Opposite TopologicalSpace Topology TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  (P : PairOfDefinition A) {Aplus : Subring A}

/-- Helper packaging a rational open `U ∈ spaRationalOpens Aplus` with a concrete admissible
presentation `p : Presentation P` and the isomorphism `presentationLimit Aplus U ≅ A⟨p⟩` in
`TopCommRingCat`. -/
private noncomputable def rationalLimitRingIso (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    {U : Opens ↥(spa Aplus)} (hU : U ∈ spaRationalOpens Aplus) :
    Σ (p : Presentation P),
      letI := locUniformSpace P p.num p.den (Localization.Away p.den) p.hasDenominatorPower
      letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
      letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
      (presentationLimit (P := P) Aplus U).obj ≅
        TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) := by
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  have hex := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hU
  let T := hex.choose
  let s := hex.choose_spec.choose
  have hT : IsOpen (Ideal.span (T : Set A) : Set A) := hex.choose_spec.choose_spec.1
  have hUeq : U = spaBasicOpen Aplus T s := hex.choose_spec.choose_spec.2
  let p : Presentation P :=
    ⟨T, s, hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT⟩
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  refine ⟨p, ?_⟩
  exact TopCommRingCat.isCompleteSeparated.ι.mapIso
    (eqToIso (congrArg (presentationLimit (P := P) Aplus) hUeq) ≪≫
      presentationLimitRationalIso Aplus hAplus p hT) ≪≫
    eqToIso (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)

/-- **Strictness of restriction on a countable rational family.** Over a Tate ring `A`, if
`A⁺ ⊆ A°` and the underlying presheaf of sets satisfies the sheaf condition for a countable family
`(V k)` of rational open subsets of a rational open `W`, then the product restriction map on
presentation limits is inducing. -/
theorem isInducing_presentationLimitMap_of_isSheafFor_spaRationalOpens
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {W : Opens ↥(spa Aplus)}
    (hW : W ∈ spaRationalOpens Aplus) {κ : Type*} [Countable κ] {V : κ → Opens ↥(spa Aplus)}
    (hV : ∀ k, V k ∈ spaRationalOpens Aplus) (hVW : ∀ k, V k ≤ W)
    (hSheaf : (Presieve.ofArrows V fun k ↦ homOfLE (hVW k)).IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat)) :
    IsInducing fun (x : presentationLimit (P := P) Aplus W) (k : κ) ↦
      (presentationLimitMap (P := P) (hVW k)).hom.val x := by
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  -- Extract the coordinate ring `B ≃ presentationLimit W` and `B_k ≃ presentationLimit (V k)`.
  obtain ⟨pW, isoW⟩ := rationalLimitRingIso P hAplus hW
  let _ := locUniformSpace P pW.num pW.den _ pW.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P pW.num pW.den _ pW.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P pW.num pW.den _ pW.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology P pW.num pW.den _ pW.hasDenominatorPower
  have _ := isTateRing_completion_locTopology_of_isTateRing P pW.num pW.den _
    pW.hasDenominatorPower
  let B := UniformSpace.Completion (Localization.Away pW.den)
  have _ : (𝓝 (0 : B)).IsCountablyGenerated :=
    (completionLocalization P pW.num pW.den _ pW.hasDenominatorPower).hasBasis_nhds_zero
      |>.isCountablyGenerated
  let dataV (k : κ) := rationalLimitRingIso P hAplus (hV k)
  let pV (k : κ) : Presentation P := (dataV k).1
  let uV (k : κ) := locUniformSpace P (pV k).num (pV k).den _ (pV k).hasDenominatorPower
  have gV (k : κ) :=
    isUniformAddGroup_locUniformSpace P (pV k).num (pV k).den _ (pV k).hasDenominatorPower
  have rV (k : κ) :=
    isTopologicalRing_locUniformSpace P (pV k).num (pV k).den _ (pV k).hasDenominatorPower
  let Bk (k : κ) := UniformSpace.Completion (Localization.Away (pV k).den)
  let isoV (k : κ) := (dataV k).2
  have nhdsV (k : κ) : (𝓝 (0 : Bk k)).IsCountablyGenerated :=
    (completionLocalization P (pV k).num (pV k).den _
      (pV k).hasDenominatorPower).hasBasis_nhds_zero.isCountablyGenerated
  have uCountV (k : κ) : (uniformity (Bk k)).IsCountablyGenerated :=
    have := nhdsV k
    IsUniformAddGroup.uniformity_countably_generated
  have cMetV (k : κ) : IsCompletelyMetrizableSpace (Bk k) :=
    have := uCountV k
    IsCompletelyMetrizableSpace.of_completeSpace_metrizable
  -- Transport restriction maps to continuous ring homs `φHom k : B ⟶ Bk k`.
  let φHom (k : κ) : TopCommRingCat.of B ⟶ TopCommRingCat.of (Bk k) :=
    isoW.inv ≫ (presentationLimitMap (P := P) (hVW k)).hom ≫ (isoV k).hom
  let modV (k : κ) : Module B (Bk k) := RingHom.toModule (φHom k).val
  -- Package the product map `L : B →ₗ[B] ∀ k, Bk k`.
  let N := ∀ k : κ, Bk k
  have hsmul (k : κ) (b : B) (y : N) : (b • y) k = (φHom k).val b * y k := rfl
  have _ : ContinuousConstSMul B N :=
    { continuous_const_smul b := continuous_pi fun k ↦ by
        simp_rw [hsmul]
        exact continuous_const.mul (continuous_apply k) }
  have _ : IsCompletelyMetrizableSpace N := IsCompletelyMetrizableSpace.pi_countable
  let L : B →ₗ[B] N :=
    { toFun b k := (φHom k).val b
      map_add' b₁ b₂ := funext fun k ↦ (φHom k).val.map_add b₁ b₂
      map_smul' c b := funext fun k ↦ (φHom k).val.map_mul c b }
  have hLcont : Continuous (L : B → N) := continuous_pi fun k ↦ (φHom k).property
  -- Relate `L` to the presentation-limit restriction map `r` via homeomorphisms.
  let eW : presentationLimit (P := P) Aplus W ≃ₜ B :=
    TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso isoW)
  let eV (k : κ) : presentationLimit (P := P) Aplus (V k) ≃ₜ Bk k :=
    TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso (isoV k))
  let ePi : (∀ k : κ, presentationLimit (P := P) Aplus (V k)) ≃ₜ N :=
    Homeomorph.piCongrRight eV
  let r : presentationLimit (P := P) Aplus W → ∀ k : κ, presentationLimit (P := P) Aplus (V k) :=
    fun x k ↦ (presentationLimitMap (P := P) (hVW k)).hom.val x
  have hcomm (x : presentationLimit (P := P) Aplus W) : L (eW x) = ePi (r x) := by
    funext k
    have h1 : (isoW.hom ≫ φHom k) =
        (presentationLimitMap (P := P) (hVW k)).hom ≫ (isoV k).hom := by
      simp [φHom]
    exact ConcreteCategory.congr_hom h1 x
  -- Extract injectivity and closed range of `r` from the set-level sheaf condition.
  have hglue := (isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P hVW).mp hSheaf
  have hr_compat (x : presentationLimit (P := P) Aplus W) (k l : κ) :
      (presentationLimitMap (P := P) (inf_le_left : V k ⊓ V l ≤ V k)).hom.val (r x k) =
        (presentationLimitMap (P := P) (inf_le_right : V k ⊓ V l ≤ V l)).hom.val (r x l) :=
    (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom) (presentationLimitMap_comp (P := P)
        (Aplus := Aplus) (hVW k) (inf_le_left : V k ⊓ V l ≤ V k))) x).trans
      (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom) (presentationLimitMap_comp (P := P)
        (Aplus := Aplus) (hVW l) (inf_le_right : V k ⊓ V l ≤ V l))) x).symm
  have hr_inj : Function.Injective r := fun x₁ x₂ hx ↦ by
    obtain ⟨_, _, hu⟩ := hglue (r x₁) (hr_compat x₁)
    exact (hu x₁ fun _ ↦ rfl).trans (hu x₂ fun k ↦ congrFun hx.symm k).symm
  have hr_range : Set.range r = { y | ∀ k l : κ,
      (presentationLimitMap (P := P) (inf_le_left : V k ⊓ V l ≤ V k)).hom.val (y k) =
        (presentationLimitMap (P := P) (inf_le_right : V k ⊓ V l ≤ V l)).hom.val (y l) } :=
    Set.ext fun y ↦ ⟨by rintro ⟨x, rfl⟩; exact hr_compat x,
      fun hy ↦ by obtain ⟨a, ha, -⟩ := hglue y hy; exact ⟨a, funext ha⟩⟩
  have hr_closed : IsClosed (Set.range r) := by
    rw [hr_range]
    simp_rw [Set.ofPred_forall]
    exact isClosed_iInter fun k ↦ isClosed_iInter fun l ↦ isClosed_eq
      ((presentationLimitMap (P := P) (inf_le_left : V k ⊓ V l ≤ V k)).hom.property.comp
        (continuous_apply k))
      ((presentationLimitMap (P := P) (inf_le_right : V k ⊓ V l ≤ V l)).hom.property.comp
        (continuous_apply l))
  -- Transfer closedness and injectivity along `eW` and `ePi` to `L`, and apply Open Mapping.
  have hL_range : (L.range : Set N) = ePi '' Set.range r := by
    ext z
    simp only [Set.mem_image, Set.mem_range]
    exact ⟨by rintro ⟨b, rfl⟩
              exact ⟨r (eW.symm b), ⟨_, rfl⟩, by rw [← hcomm, eW.apply_symm_apply]⟩,
      by rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨eW x, hcomm x⟩⟩
  have hL_closed : IsClosed (L.range : Set N) := hL_range ▸ ePi.isClosedMap _ hr_closed
  have hL_inj : Function.Injective L := fun b₁ b₂ hb ↦ eW.symm.injective <| hr_inj <|
    ePi.injective <| by rw [← hcomm, ← hcomm, eW.apply_symm_apply, eW.apply_symm_apply, hb]
  have hL_emb : IsEmbedding (L : B → N) :=
    isEmbedding_iff_isStrictMap_injective.mpr
      ⟨L.isStrictMap_of_isClosed_range_of_isTateRing hLcont.continuousAt hL_closed, hL_inj⟩
  exact ePi.isInducing.of_comp_iff.mp <|
    (funext hcomm : (L : B → N) ∘ eW = ePi ∘ r) ▸ hL_emb.isInducing.comp eW.isInducing

/-- **Topological sheafhood from finite rational covers of rational opens.** Over a Tate ring `A`
with `A⁺ ⊆ A°`, if the presheaf of sets underlying `presentationLimitPresheaf P Aplus` satisfies
the sheaf condition for every finite rational cover of every rational open, then
`presentationLimitPresheaf P Aplus` is a sheaf of complete separated topological commutative rings
on all opens of `Spa(A, A⁺)`. -/
theorem isSheaf_presentationLimitPresheaf_of_isSheafFor_finite_rationalOpens
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hfin : ∀ {W : Opens ↥(spa Aplus)} {κ : Type v} [Finite κ] {V : κ → Opens ↥(spa Aplus)},
      W ∈ spaRationalOpens Aplus → (∀ k, V k ∈ spaRationalOpens Aplus) →
      ∀ hcov : ⨆ k, V k = W,
      (Presieve.ofArrows V fun k ↦ homOfLE ((le_iSup V k).trans_eq hcov)).IsSheafFor
        (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
          forget _root_.TopCommRingCat)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) := by
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  refine isSheaf_presentationLimitPresheaf_of_isSheaf_rational <|
    Presheaf.isSheaf_of_isSheaf_comp _ _ TopCommRingCat.isCompleteSeparated.ι fun E ↦ ?_
  refine isSheaf_restrictedTopology_rationalOpens_of_isSheafFor_ofArrows Aplus
    (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
      coyoneda.obj (op E)) fun {W} {ι} {U} hW hU hcov ↦ ?_
  have hSet := isSheafFor_spaRationalOpens_of_finite Aplus hfin hW hU hcov
  obtain ⟨I, hcovI⟩ := exists_finite_subcover_spaRationalOpens hW hcov
  have hIndI := (isInducing_restrictionMap_iff_isInducing_presentationLimitMap P
    (fun k : ↥I ↦ (le_iSup (fun k : ↥I ↦ U k.val) k).trans_eq hcovI)).mpr
      (isInducing_presentationLimitMap_of_isSheafFor_spaRationalOpens P hAplus hW
        (fun k : ↥I ↦ hU k.val) (fun k : ↥I ↦ (le_iSup (fun k : ↥I ↦ U k.val) k).trans_eq hcovI)
        (hfin (V := fun k : ↥I ↦ U k.val) hW (fun k ↦ hU k.val) hcovI))
  let F := presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι
  have hIndU : IsInducing fun (x : F.obj (op W)) (i : ι) ↦
      (F.map (homOfLE ((le_iSup U i).trans_eq hcov)).op).val x :=
    .of_comp (continuous_pi fun i ↦ (F.map (homOfLE ((le_iSup U i).trans_eq hcov)).op).property)
      (continuous_pi fun k : ↥I ↦ continuous_apply k.val) hIndI
  have hIndSieve := (TopCommRingCat.isInducing_restrictionMap_ofArrows_iff F U
    (fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov))).mpr hIndU
  rw [Presieve.isSheafFor_iff_generate]
  exact TopCommRingCat.isSheafFor_of_isSheafFor_forget F
    (Sieve.ofArrows U fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov)).arrows
    ((Presieve.isSheafFor_iff_generate _).mp hSet) hIndSieve E

/-- **Berkeley Lectures Proposition 4.3.4.** Over a Tate ring `A` with `A⁺ ⊆ A°`, the structure
presheaf `presentationLimitPresheaf P Aplus` of complete separated topological commutative rings on
`Spa(A, A⁺)` is a sheaf if and only if its underlying presheaf of sets is a sheaf. -/
theorem isSheaf_presentationLimitPresheaf_iff_isSheaf_forget
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) ↔
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
          forget _root_.TopCommRingCat) := by
  refine ⟨fun h ↦ Presheaf.isSheaf_comp_of_isSheaf _ _
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat) h, fun h ↦ ?_⟩
  refine isSheaf_presentationLimitPresheaf_of_isSheafFor_finite_rationalOpens P hAplus
    fun {W} {κ} _ {V} _ _ hcov ↦ ?_
  rw [Presieve.isSheafFor_iff_generate]
  exact h.isSheafFor _
    (TauCeti.TopologicalSpace.Opens.sieve_ofArrows_mem_grothendieckTopology _ hcov.ge)

end TauCeti.ValuationSpectrum

end
