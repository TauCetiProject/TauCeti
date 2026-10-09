/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Homeomorph
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.BaseChange

import TauCeti.Topology.Sheaves.Functors
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.DenseRange
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Transporting the sheaf property along isomorphisms and completion

This file compares the presentation-limit presheaves `presentationLimitPresheaf` of two
topological rings, each with a pair of definition and a subring (the plus subring `A⁺`, `B⁺`),
whose adic spectra correspond, and shows that one is a sheaf exactly when the other is. The plus
subrings need not be rings of integral elements:

* along an isomorphism of topological rings `e : A ≃+* B`, continuous in both directions, carrying
  `A⁺` onto `B⁺`. The pairs of definition of `A` and of `B` are arbitrary, and no condition is put
  on `A⁺`. At the identity of `A` this compares two pairs of definition of one ring.
* along the completion `A → Â` of a Huber ring `A` with a uniform structure, with `Â⁺` the closure
  of the image of `A⁺`, when every element of `A⁺` is power-bounded. The pairs of definition of `A`
  and of `Â` are arbitrary. The adic spectra are then identified by Wedhorn's Proposition 7.48
  (`spaCompletionHomeomorph`), and `Â⟨T/s⟩` with `A⟨T/s⟩`.

In both cases the presentation-limit presheaf of `(A, A⁺)` is isomorphic to the pushforward of the
other along the homeomorphism of adic spectra; its components are built from the base-change maps
between completed rational localisations of
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.BaseChange`.

The consequences for `TauCeti.Huber.IsSheafyForEveryPresentation` are in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafForEveryPresentation`.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPresheafIsoPushforward` : the presentation-limit
  presheaf of `(A, A⁺)` as the pushforward of that of `(B, B⁺)`, along mutually inverse continuous
  ring homomorphisms.

## Main results

* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_iff_of_ringEquiv` : invariance of
  the sheaf property under isomorphism.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_completionPlus_iff` : invariance of
  the sheaf property under completion.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51
  (the universal property of `A⟨T/s⟩`), Proposition 7.48 (the adic spectrum of the completion) and
  §8.1 (the structure presheaf).
-/

open CategoryTheory _root_.TopologicalSpace

public section

universe v

namespace TauCeti.ValuationSpectrum

open CategoryTheory.Limits TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {P : PairOfDefinition A}
  {P' : PairOfDefinition B} {Aplus : Subring A} {Bplus : Subring B}

/-! ### The comparison maps of presentation limits along an isomorphism -/

variable (φ : A →+* B) (hφ : Continuous φ)
  (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))

variable (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {U : Opens ↥(spa Aplus)} {V : Opens ↥(spa Bplus)}
  (hUV : ∀ w, spaComap φ hφ Aplus Bplus hplus w ∈ U → w ∈ V)

-- The comparison along an isomorphism is built from two mutually inverse continuous ring
-- homomorphisms `φ` and `ψ` rather than from a ring isomorphism `e`: swapping the two gives the
-- inverse comparison as the same construction, whereas `e.symm` would reintroduce `e.symm.symm`,
-- which is `e` only up to definitional unfolding that `rw` and `simp` do not perform.
variable (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)

variable (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus)
  (hVU : ∀ w, spaComap ψ hψ Bplus Aplus hplus' w ∈ V → w ∈ U)

/-- The component at `j` of the comparison map: project to the index of `U` induced by `j`
through `ψ`, then base change along `φ`. -/
private noncomputable def presentationLimitLeg (j : PresentationIndex (P := P') Bplus V) :
    presentationLimit (P := P) Aplus U ⟶ j.pres.completionLocObj :=
  presentationLimitπToPresentation Aplus U
      (j.map ψ hψ (fun _ ↦ isOpen_map_of_continuous_inverse hφ hφψ hψφ) hplus' hVU) ≫
    Presentation.mapHom φ hφ _ j.pres (by rw [PresentationIndex.map_pres_den, hφψ])
      (fun t ht ↦ by
        classical
        rw [PresentationIndex.map_pres_num] at ht
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
        rwa [hφψ])

/-- The legs form a cone over the diagram of `V`. -/
private theorem presentationLimitLeg_comp_restrictionHom
    {j₁ j₂ : PresentationIndex (P := P') Bplus V} (h : j₁ ⟶ j₂) :
    presentationLimitLeg (P := P) φ hφ ψ hψ hψφ hφψ hplus' hVU j₁ ≫
        Presentation.restrictionHom h.le =
      presentationLimitLeg φ hφ ψ hψ hψφ hφψ hplus' hVU j₂ := by
  refine (Category.assoc _ _ _).trans (presentationLimitπToPresentation_comp_eq
    (PresentationIndex.map_mono _ _ _ _ _ h.le) ?_)
  simp [Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
    Presentation.toCompletionLocTopHom_comp_restrictionHom,
    Presentation.toCompletionLocTopHom_comp_mapHom]

/-- **The comparison map** `presentationLimit Aplus U ⟶ presentationLimit Bplus V` induced by
`φ`, for `V` contained in the image of `U`: the lift of the legs. -/
private noncomputable def presentationLimitHom :
    presentationLimit (P := P) Aplus U ⟶ presentationLimit (P := P') Bplus V :=
  eqToHom (presentationIndexCone_pt Bplus V _ (presentationLimitLeg φ hφ ψ hψ hψφ hφψ hplus' hVU)
      fun f ↦ presentationLimitLeg_comp_restrictionHom φ hφ ψ hψ hψφ hφψ hplus' hVU f).symm ≫
    presentationLimitLift Bplus V (presentationIndexCone Bplus V _
      (presentationLimitLeg φ hφ ψ hψ hψφ hφψ hplus' hVU)
      fun f ↦ presentationLimitLeg_comp_restrictionHom φ hφ ψ hψ hψφ hφψ hplus' hVU f)

/-- The comparison map projects to the legs. -/
@[reassoc]
private theorem presentationLimitHom_comp_πToPresentation
    (j : PresentationIndex (P := P') Bplus V) :
    presentationLimitHom (P := P) φ hφ ψ hψ hψφ hφψ hplus' hVU ≫
        presentationLimitπToPresentation Bplus V j =
      presentationLimitLeg φ hφ ψ hψ hψφ hφψ hplus' hVU j := by
  rw [presentationLimitHom, Category.assoc]
  exact presentationIndexCone_lift_comp_πToPresentation Bplus V _ _ _ j

/-- **The comparison maps of `φ` and `ψ` are mutually inverse.** -/
private theorem presentationLimitHom_comp_presentationLimitHom :
    presentationLimitHom (P := P) (P' := P') φ hφ ψ hψ hψφ hφψ hplus' hVU ≫
        presentationLimitHom ψ hψ φ hφ hφψ hψφ hplus hUV = 𝟙 _ := by
  refine presentationLimit_hom_ext_toPresentation fun i ↦ ?_
  -- the composite projects at the index `ψ(φ(i))`, which refines `i`, and then applies a map
  -- `A⟨ψ(φ(i))⟩ → A⟨i⟩` compatible with `ψ ∘ φ = id`
  rw [Category.assoc, presentationLimitHom_comp_πToPresentation, presentationLimitLeg,
    presentationLimitHom_comp_πToPresentation_assoc, presentationLimitLeg, Category.assoc,
    Category.id_comp, ← Category.comp_id (presentationLimitπToPresentation _ _ i)]
  refine (presentationLimitπToPresentation_comp_eq ?_ ?_).symm
  · classical
    refine Presentation.le_def.mpr ⟨1, ?_, fun t ht ↦ ?_⟩
    · rw [PresentationIndex.map_pres_den, PresentationIndex.map_pres_den, hψφ, mul_one]
    · rw [PresentationIndex.map_pres_num, PresentationIndex.map_pres_num, mul_one]
      exact Finset.mem_image.mpr ⟨φ t, Finset.mem_image_of_mem φ ht, hψφ t⟩
  · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      Category.comp_id, Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
      Presentation.toCompletionLocTopHom_comp_mapHom]
    rw [← Category.assoc]
    refine (Category.id_comp _).symm.trans (eq_whisker ?_ _)
    exact (Subtype.ext (RingHom.ext hψφ)).symm

/-- **The comparison maps commute with restriction.** -/
@[reassoc]
private theorem presentationLimitMap_comp_presentationLimitHom {U₁ : Opens ↥(spa Aplus)}
    {V₁ : Opens ↥(spa Bplus)} (hU : U ≤ U₁) (hV : V ≤ V₁)
    (hVU₁ : ∀ w, spaComap ψ hψ Bplus Aplus hplus' w ∈ V₁ → w ∈ U₁) :
    presentationLimitMap (P := P) hU ≫ presentationLimitHom φ hφ ψ hψ hψφ hφψ hplus' hVU =
      presentationLimitHom (P' := P') φ hφ ψ hψ hψφ hφψ hplus' hVU₁ ≫ presentationLimitMap hV := by
  refine presentationLimit_hom_ext_toPresentation fun j ↦ ?_
  -- both sides project at indices of `U₁` with the same presentation, then map compatibly with `φ`
  simp only [Category.assoc, presentationLimitHom_comp_πToPresentation,
    presentationLimitHom_comp_πToPresentation_assoc, presentationLimitLeg,
    reassoc_of% presentationLimitMap_comp_πToPresentation,
    presentationLimitMap_comp_πToPresentation]
  refine presentationLimitπToPresentation_comp_eq
    (le_of_eq (PresentationIndex.ext (Presentation.ext ?_ ?_))) ?_
  · simp [PresentationIndex.map_pres_num]
  · simp [PresentationIndex.map_pres_den]
  · simp [Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
      Presentation.toCompletionLocTopHom_comp_mapHom]

/-! ### The isomorphism of presheaves -/

-- The presentation-limit presheaf of `(A, A⁺)` is isomorphic to the pushforward of that of
-- `(B, B⁺)` along the homeomorphism `Spa(B, B⁺) → Spa(A, A⁺)` induced by `φ`; its components are
-- assembled from the base-change maps `A⟨T/s⟩ → B⟨φ(T)/φ(s)⟩` of the universal property.

omit [IsTopologicalRing A] [IsTopologicalRing B] in
include hψφ in
/-- Pulling back along `ψ` and then along `φ` is the identity of `Spa(A, A⁺)`. -/
private theorem spaComap_spaComap (w : ↥(spa Aplus)) :
    spaComap φ hφ Aplus Bplus hplus (spaComap ψ hψ Bplus Aplus hplus' w) = w := by
  have hcomp : ψ.comp φ = RingHom.id A := RingHom.ext hψφ
  refine Subtype.ext ?_
  rw [spaComap_val, spaComap_val, ← Function.comp_apply (f := comap φ), ← comap_comp, hcomp,
    comap_id, id]

omit [IsTopologicalRing A] [IsTopologicalRing B] in
include hψφ in
/-- The preimage of `W` under the map of adic spectra induced by `φ` is contained in the image of
`W`. -/
private theorem mem_of_spaComap_mem_map (W : Opens ↥(spa Aplus)) (w : ↥(spa Aplus))
    (hw : spaComap ψ hψ Bplus Aplus hplus' w ∈ (Opens.map (spaComapTopHom φ hφ hplus)).obj W) :
    w ∈ W := by
  rw [← spaComap_spaComap φ hφ hplus ψ hψ hψφ hplus' w]
  exact Opens.mem_map.mp hw

/-- The comparison maps of `φ` and `ψ` as an isomorphism of presentation limits. -/
private noncomputable def presentationLimitIso (W : Opens ↥(spa Aplus)) :
    presentationLimit (P := P) Aplus W ≅
      presentationLimit (P := P') Bplus ((Opens.map (spaComapTopHom φ hφ hplus)).obj W) where
  hom := presentationLimitHom φ hφ ψ hψ hψφ hφψ hplus'
    (mem_of_spaComap_mem_map φ hφ hplus ψ hψ hψφ hplus' W)
  inv := presentationLimitHom ψ hψ φ hφ hφψ hψφ hplus fun _ hw ↦ Opens.mem_map.mpr hw
  hom_inv_id := presentationLimitHom_comp_presentationLimitHom _ _ _ _ _ _ _ _ _ _
  inv_hom_id := presentationLimitHom_comp_presentationLimitHom _ _ _ _ _ _ _ _ _ _

/-- **Transport of the presentation-limit presheaf along an isomorphism.** For mutually inverse
continuous ring homomorphisms `φ : A → B` and `ψ : B → A` carrying `A⁺` into `B⁺` and `B⁺` into
`A⁺`, the presentation-limit presheaf of `(A, A⁺)` for a pair of definition `P` is isomorphic to
the pushforward of that of `(B, B⁺)` for a pair of definition `P'` along the homeomorphism
`Spa(B, B⁺) → Spa(A, A⁺)` induced by `φ`. On an open `W`, the component
`𝒪_{Spa A}(W) → 𝒪_{Spa B}(φ⁻¹W)` is assembled from the base changes `A⟨T/s⟩ → B⟨φ(T)/φ(s)⟩` of
the universal property. At `A = B` and `P = P'` this is the action on the structure presheaf of an
automorphism of the pair `(A, A⁺)`. -/
noncomputable def presentationLimitPresheafIsoPushforward :
    presentationLimitPresheaf P Aplus ≅
      (TopCat.Presheaf.pushforward _ (spaComapTopHom φ hφ hplus)).obj
        (presentationLimitPresheaf P' Bplus) :=
  NatIso.ofComponents
    (fun W ↦ eqToIso (presentationLimitPresheaf_obj P Aplus W) ≪≫
      presentationLimitIso φ hφ hplus ψ hψ hψφ hφψ hplus' W.unop ≪≫
      eqToIso (presentationLimitPresheaf_obj P' Bplus _).symm)
    fun {W W'} f ↦ by
      simp only [presentationLimitPresheaf_map, TopCat.Presheaf.pushforward_obj_map, Iso.trans_hom,
        eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        presentationLimitIso]
      rw [presentationLimitMap_comp_presentationLimitHom_assoc (hU := leOfHom f.unop)
        (hV := (Opens.map _).monotone (leOfHom f.unop))
        (hVU₁ := mem_of_spaComap_mem_map φ hφ hplus ψ hψ hψφ hplus' W.unop)]

include hψφ hφψ in
/-- The maps of adic spectra induced by `φ` and `ψ`, as an isomorphism of `TopCat`. -/
private noncomputable def spaTopIso : TopCat.of ↥(spa Bplus) ≅ TopCat.of ↥(spa Aplus) where
  hom := spaComapTopHom φ hφ hplus
  inv := spaComapTopHom ψ hψ hplus'
  hom_inv_id := TopCat.ext (spaComap_spaComap ψ hψ hplus' φ hφ hφψ hplus)
  inv_hom_id := TopCat.ext (spaComap_spaComap φ hφ hplus ψ hψ hψφ hplus')

/-- **Sheafhood of the presentation limit is invariant under isomorphism.** If `e : A ≃+* B` is an
isomorphism of topological rings carrying `A⁺` onto `B⁺`, then the presentation-limit presheaf of
`Spa(A, A⁺)` for a pair of definition `P` of `A` is a sheaf exactly when that of `Spa(B, B⁺)` for a
pair of definition `P'` of `B` is. The two pairs of definition are arbitrary. -/
theorem isSheaf_presentationLimitPresheaf_iff_of_ringEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : Aplus.map (e : A →+* B) = Bplus) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus)) (presentationLimitPresheaf P Aplus) ↔
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
        (presentationLimitPresheaf P' Bplus) := by
  subst hplus
  have h₁ : ∀ a ∈ Aplus, (e : A →+* B) a ∈ Aplus.map (e : A →+* B) :=
    fun a ha ↦ ⟨a, ha, rfl⟩
  have h₂ : ∀ b ∈ Aplus.map (e : A →+* B), (e.symm : B →+* A) b ∈ Aplus :=
    fun _ hb ↦ Subring.mem_map_equiv.mp hb
  exact TopCat.Presheaf.isSheaf_iff_of_iso_pushforward (X := TopCat.of ↥(spa Aplus))
    (Y := TopCat.of ↥(spa (Aplus.map (e : A →+* B)))) (F := presentationLimitPresheaf P Aplus)
    (G := presentationLimitPresheaf P' (Aplus.map (e : A →+* B)))
    (spaTopIso _ he h₁ _ he' e.symm_apply_apply e.apply_symm_apply h₂)
    (presentationLimitPresheafIsoPushforward _ he h₁ _ he' e.symm_apply_apply e.apply_symm_apply h₂)

end TauCeti.ValuationSpectrum

/-! ### Maps between `A⟨T/s⟩` and `Â⟨T/s⟩` -/

namespace TauCeti.Huber.PairOfDefinition

open UniformSpace

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {P' : PairOfDefinition (Completion A)}

/-- The extension `Â → A⟨p⟩` of the structure map, as a morphism of `TopCommRingCat`. -/
private noncomputable def Presentation.completionExtendTopHom (p : Presentation P) :
    TopCommRingCat.of (Completion A) ⟶ p.completionLocObj.obj := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  exact (⟨Completion.extensionHom _ (continuous_toCompletionLoc P p.num p.den _ _),
      Completion.continuous_extension⟩ :
      TopCommRingCat.of (Completion A) ⟶
        TopCommRingCat.of (Completion (Localization.Away p.den))) ≫
    eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm

/-- The extension of the structure map restricts to the structure map on `A`. -/
@[reassoc]
private theorem Presentation.coeRingHom_comp_completionExtendTopHom (p : Presentation P) :
    (⟨Completion.coeRingHom, Completion.continuous_coeRingHom⟩ :
        TopCommRingCat.of A ⟶ TopCommRingCat.of (Completion A)) ≫ p.completionExtendTopHom =
      p.toCompletionLocTopHom := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  simp only [Presentation.completionExtendTopHom, Presentation.toCompletionLocTopHom_eq]
  simp only [← Category.assoc]
  apply eq_whisker
  exact Subtype.ext <| RingHom.ext <|
    Completion.extensionHom_coe _ (continuous_toCompletionLoc P p.num p.den _ _)

/-- **Descent of `Â⟨T/s⟩` to `A⟨T/s⟩`.** When the presentation `q` of `Â` is the image of the
presentation `p` of `A`, the extension to `Â` of the structure map `A → A⟨p⟩` extends uniquely to a
continuous map `Â⟨q⟩ → A⟨p⟩`. -/
private theorem existsUnique_continuous_ringHom_completion_comp_eq (p : Presentation P)
    (q : Presentation P') (hden : q.den = p.den)
    (hnum : ∀ t ∈ q.num, ∃ t₀ ∈ p.num, (t₀ : Completion A) = t) :
    letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    ∃! g : Completion (Localization.Away q.den) →+* Completion (Localization.Away p.den),
      Continuous g ∧ g.comp (toCompletionLoc P' q.num q.den _ q.hasDenominatorPower) =
        Completion.extensionHom _ (continuous_toCompletionLoc P p.num p.den _ _) := by
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology P p.num p.den _ p.hasDenominatorPower
  have hc := continuous_toCompletionLoc P p.num p.den _ p.hasDenominatorPower
  have hu := isUnit_toCompletionLoc_of_dvd P p.num p.den _ p.hasDenominatorPower (dvd_refl p.den)
  have hs : IsUnit (Completion.extensionHom _ hc q.den) := by
    rwa [hden, Completion.extensionHom_coe]
  have hunit : hs.unit = hu.unit :=
    Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, hden, Completion.extensionHom_coe])
  refine existsUnique_continuous_ringHom_completion_locTopology P' q.num q.den _
    q.hasDenominatorPower Completion.continuous_extension.continuousAt hs fun t ht ↦ ?_
  obtain ⟨t₀, ht₀, rfl⟩ := hnum t ht
  rw [hunit, Completion.extensionHom_coe]
  exact isPowerBounded_toCompletionLoc_mul_unit_inv P p.num p.den _ _ (mul_one p.den).symm hu
    ((mul_one t₀).symm ▸ ht₀)

/-- The morphism `Â⟨q⟩ ⟶ A⟨p⟩` of `existsUnique_continuous_ringHom_completion_comp_eq`. -/
private noncomputable def Presentation.completionHom (p : Presentation P) (q : Presentation P')
    (hden : q.den = p.den) (hnum : ∀ t ∈ q.num, ∃ t₀ ∈ p.num, (t₀ : Completion A) = t) :
    q.completionLocObj ⟶ p.completionLocObj := by
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have hg := existsUnique_continuous_ringHom_completion_comp_eq p q hden hnum
  exact InducedCategory.homMk (eqToHom (completionLocObj_obj P' q.num q.den _ _) ≫
    (⟨hg.choose, hg.choose_spec.1.1⟩ :
      TopCommRingCat.of (Completion (Localization.Away q.den)) ⟶
        TopCommRingCat.of (Completion (Localization.Away p.den))) ≫
      eqToHom (completionLocObj_obj P p.num p.den _ _).symm)

/-- `Presentation.completionHom` carries the structure map of `q` to the extension of that of
`p`. -/
@[reassoc]
private theorem Presentation.toCompletionLocTopHom_comp_completionHom (p : Presentation P)
    (q : Presentation P') (hden : q.den = p.den)
    (hnum : ∀ t ∈ q.num, ∃ t₀ ∈ p.num, (t₀ : Completion A) = t) :
    q.toCompletionLocTopHom ≫ (p.completionHom q hden hnum).hom = p.completionExtendTopHom := by
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  simp only [Presentation.toCompletionLocTopHom_eq, Presentation.completionHom,
    Presentation.completionExtendTopHom, InducedCategory.homMk_hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  apply eq_whisker
  exact Subtype.ext
    (existsUnique_continuous_ringHom_completion_comp_eq p q hden hnum).choose_spec.1.2

end TauCeti.Huber.PairOfDefinition

/-! ### Invariance under completion -/

namespace TauCeti.ValuationSpectrum

open CategoryTheory.Limits TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] {P : PairOfDefinition A} {P' : PairOfDefinition (Completion A)}
  {Aplus : Subring A}

variable (Aplus) in
/-- The homeomorphism `Spa(Â, Â⁺) ≃ Spa(A, A⁺)` of Wedhorn's Proposition 7.48, as a morphism of
`TopCat`. -/
private noncomputable abbrev spaCompletionTopHom :
    TopCat.of ↥(spa (completionPlus Aplus)) ⟶ TopCat.of ↥(spa Aplus) :=
  (TopCat.isoOfHomeo (spaCompletionHomeomorph Aplus)).hom

/-- Membership in the preimage of an open under `spaCompletionTopHom` is membership of the
pullback along the completion map. -/
private theorem mem_map_spaCompletionTopHom {U : Opens ↥(spa Aplus)}
    {w : ↥(spa (completionPlus Aplus))} :
    w ∈ (Opens.map (spaCompletionTopHom Aplus)).obj U ↔
      spaComap Completion.coeRingHom Completion.continuous_coeRingHom Aplus (completionPlus Aplus)
        (fun _ ha ↦ map_mem_completionPlus ha) w ∈ U := by
  rw [Opens.mem_map, ← spaCompletionHomeomorph_apply]
  rfl

variable {U : Opens ↥(spa Aplus)}

/-- An index of `U` induces, through the completion map, an index of the preimage of `U` in
`Spa(Â, Â⁺)`. -/
private noncomputable abbrev PresentationIndex.completion (i : PresentationIndex (P := P) Aplus U) :
    PresentationIndex (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U) :=
  PresentationIndex.map (P := P) (P' := P') (Bplus := completionPlus Aplus) (U := U)
    (V := (Opens.map (spaCompletionTopHom Aplus)).obj U) Completion.coeRingHom
    Completion.continuous_coeRingHom (fun _ hJ ↦ isOpen_map_coeRingHom hJ)
    (fun _ ha ↦ map_mem_completionPlus ha) (fun _ hw ↦ mem_map_spaCompletionTopHom.mpr hw) i

open scoped Classical in
/-- A containment of the rational subsets of `Spa(Â, Â⁺)` induced by two presentations of `A`
is a containment of their rational subsets of `Spa(A, A⁺)`. -/
private theorem rationalSubset_subset_of_image_subset {T T' : Finset A} {s s' : A}
    (h : rationalSubset (completionPlus Aplus) (T'.image Completion.coeRingHom)
        (Completion.coeRingHom s') ⊆
      rationalSubset (completionPlus Aplus) (T.image Completion.coeRingHom)
        (Completion.coeRingHom s)) :
    rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s := by
  rw [← spaBasicOpen_le_spaBasicOpen_iff] at h ⊢
  intro v hv
  obtain ⟨w, rfl⟩ := (spaCompletionHomeomorph Aplus).surjective v
  -- `R(ι(T)/ι(s))` is the preimage of `R(T/s)` under the homeomorphism
  have key (T : Finset A) (s : A) := Set.ext_iff.mp (spaComap_preimage_rationalSubset
    Completion.coeRingHom Completion.continuous_coeRingHom Aplus (completionPlus Aplus)
      (fun _ ha ↦ map_mem_completionPlus ha) T s) w
  rw [spaCompletionHomeomorph_apply] at hv ⊢
  exact mem_spaBasicOpen.mpr <| (key T s).mpr <| mem_spaBasicOpen.mp <|
    h <| mem_spaBasicOpen.mpr <| (key T' s').mp <| mem_spaBasicOpen.mp hv

open scoped Classical in
/-- Every index of the preimage of `U` in `Spa(Â, Â⁺)` presents the same rational subset as the
index induced by some index of `U`. -/
private theorem exists_presentationIndex_rationalSubset_eq
    (j : PresentationIndex (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U)) :
    ∃ i : PresentationIndex (P := P) Aplus U,
      rationalSubset (completionPlus Aplus) j.pres.num j.pres.den =
        rationalSubset (completionPlus Aplus) (i.pres.num.image Completion.coeRingHom)
          (Completion.coeRingHom i.pres.den) := by
  -- the rational subset of `j` is the preimage of a rational subset `R(T/s)` of `Spa(A, A⁺)`
  obtain ⟨W, hW, hWj⟩ := exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange
    Completion.continuous_coeRingHom Completion.denseRange_coe Aplus (completionPlus Aplus)
    (fun _ ha ↦ map_mem_completionPlus ha)
    (mem_spaRationalFamily_iff.mpr ⟨_, _, j.isOpen_span, rfl⟩)
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalFamily_iff.mp hW
  refine ⟨⟨⟨T, s, hasDenominatorPower_of_isOpen_span P T s _ hT⟩, hT, fun v hv ↦ ?_⟩, ?_⟩
  · obtain ⟨w, rfl⟩ := (spaCompletionHomeomorph Aplus).surjective v
    rw [spaCompletionHomeomorph_apply] at hv ⊢
    have hw : w ∈ Subtype.val ⁻¹' rationalSubset (completionPlus Aplus) j.pres.num j.pres.den := by
      rw [← hWj]
      exact mem_spaBasicOpen.mp hv
    exact mem_map_spaCompletionTopHom.mp (j.le_open (mem_spaBasicOpen.mpr hw))
  · have h := spaComap_preimage_rationalSubset Completion.coeRingHom
      Completion.continuous_coeRingHom Aplus (completionPlus Aplus)
      (fun _ ha ↦ map_mem_completionPlus ha) T s
    rw [hWj] at h
    have h' := Subtype.preimage_coe_eq_preimage_coe_iff.mp h
    rwa [Set.inter_eq_right.mpr (rationalSubset_subset_spa _ _ _),
      Set.inter_eq_right.mpr (rationalSubset_subset_spa _ _ _)] at h'

/-- An index of `U` whose induced index presents the same rational subset of `Spa(Â, Â⁺)` as `j`. -/
private noncomputable def PresentationIndex.descend
    (j : PresentationIndex (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U)) :
    PresentationIndex (P := P) Aplus U :=
  (exists_presentationIndex_rationalSubset_eq j).choose

private theorem PresentationIndex.rationalSubset_descend
    (j : PresentationIndex (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U)) :
    rationalSubset (completionPlus Aplus) j.pres.num j.pres.den =
      rationalSubset (completionPlus Aplus) ((j.descend (P := P)).completion (P' := P')).pres.num
        ((j.descend (P := P)).completion (P' := P')).pres.den := by
  rw [PresentationIndex.map_pres_num, PresentationIndex.map_pres_den]
  exact (exists_presentationIndex_rationalSubset_eq j).choose_spec

/-- The component at an index `i` of `U` of the comparison map from the completed side: project to
the induced index, then descend from `Â⟨T/s⟩` to `A⟨T/s⟩`. -/
private noncomputable def presentationLimitCompletionLeg (i : PresentationIndex (P := P) Aplus U) :
    presentationLimit (P := P') (completionPlus Aplus)
        ((Opens.map (spaCompletionTopHom Aplus)).obj U) ⟶ i.pres.completionLocObj :=
  presentationLimitπToPresentation _ _ (i.completion (P' := P')) ≫
    Presentation.completionHom i.pres (i.completion (P' := P')).pres
      (by rw [PresentationIndex.map_pres_den]; rfl) fun t ht ↦ by
      classical
      rw [PresentationIndex.map_pres_num] at ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨t₀, ht₀, rfl⟩

variable (P') in
/-- The component at an index `j` of the preimage of `U` of the comparison map to the completed
side: project to the descended index, base change along `A → Â`, then compare rational subsets. -/
private noncomputable def presentationLimitDescendLeg
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a)
    (j : PresentationIndex (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U)) :
    presentationLimit (P := P) Aplus U ⟶ j.pres.completionLocObj :=
  presentationLimitπToPresentation Aplus U (j.descend (P := P)) ≫
    Presentation.mapHom Completion.coeRingHom Completion.continuous_coeRingHom _
      ((j.descend (P := P)).completion (P' := P')).pres (by rw [PresentationIndex.map_pres_den])
      (fun t ht ↦ by
        classical
        rw [PresentationIndex.map_pres_num]
        exact Finset.mem_image_of_mem _ ht) ≫
    homOfRationalSubsetSubset (completionPlus Aplus) hAplus' (j.rationalSubset_descend).le

/-- The legs from the completed side form a cone over the diagram of `U`. -/
private theorem presentationLimitCompletionLeg_comp_restrictionHom
    {i₁ i₂ : PresentationIndex (P := P) Aplus U} (h : i₁ ⟶ i₂) :
    presentationLimitCompletionLeg (P' := P') i₁ ≫ Presentation.restrictionHom h.le =
      presentationLimitCompletionLeg i₂ := by
  refine (Category.assoc _ _ _).trans (presentationLimitπToPresentation_comp_eq
    (PresentationIndex.map_mono _ _ _ _ _ h.le) ?_)
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_completionHom_assoc,
    Presentation.toCompletionLocTopHom_comp_completionHom]
  -- two maps out of `Â` agreeing on the dense image of `A`
  refine Subtype.ext <| Completion.ringHom_ext_of_continuous
    (Subtype.property (p := fun f : _ →+* _ ↦ Continuous f) _)
    (Subtype.property (p := fun f : _ →+* _ ↦ Continuous f) _) ?_
  -- composing a ring homomorphism with `coeRingHom` is precomposing its `TopCommRingCat` morphism
  -- with the completion map, which is how the compatibility lemmas below are stated
  let ι : TopCommRingCat.of A ⟶ TopCommRingCat.of (Completion A) :=
    ⟨Completion.coeRingHom, Completion.continuous_coeRingHom⟩
  change (ι ≫ _).1 = (ι ≫ _).1
  refine congrArg Subtype.val ?_
  simp only [ι, Presentation.coeRingHom_comp_completionExtendTopHom_assoc,
    Presentation.toCompletionLocTopHom_comp_restrictionHom]
  exact (Presentation.coeRingHom_comp_completionExtendTopHom _).symm

/-- The legs to the completed side form a cone over the diagram of the preimage of `U`. -/
private theorem presentationLimitDescendLeg_comp_restrictionHom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a)
    {j₁ j₂ : PresentationIndex (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U)} (h : j₁ ⟶ j₂) :
    presentationLimitDescendLeg (P := P) P' hAplus' j₁ ≫ Presentation.restrictionHom h.le =
      presentationLimitDescendLeg P' hAplus' j₂ := by
  simp only [presentationLimitDescendLeg, Category.assoc]
  -- the descended indices present rational subsets contained in one another, as `j₁` and `j₂` do
  refine (presentationLimitπToPresentation_comp_eq_of_subset hAplus
    (rationalSubset_subset_of_image_subset ?_) ?_).symm
  · have hsub := rationalSubset_subset_rationalSubset_of_le (completionPlus Aplus) h.le
    rw [j₁.rationalSubset_descend (P := P), j₂.rationalSubset_descend (P := P)] at hsub
    simpa only [PresentationIndex.map_pres_num, PresentationIndex.map_pres_den] using hsub
  · simp only [ObjectProperty.FullSubcategory.comp_hom,
      Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
      toCompletionLocTopHom_comp_homOfRationalSubsetSubset_assoc,
      toCompletionLocTopHom_comp_homOfRationalSubsetSubset,
      Presentation.toCompletionLocTopHom_comp_restrictionHom]

/-- The comparison map from the completed side, `𝒪_{Â}(V) ⟶ 𝒪_A(U)` for `V` the preimage of
`U`: the lift of the legs `presentationLimitCompletionLeg`. -/
private noncomputable def presentationLimitCompletionHom (U : Opens ↥(spa Aplus)) :
    presentationLimit (P := P') (completionPlus Aplus)
        ((Opens.map (spaCompletionTopHom Aplus)).obj U) ⟶ presentationLimit (P := P) Aplus U :=
  eqToHom (presentationIndexCone_pt Aplus U _ presentationLimitCompletionLeg
      fun f ↦ presentationLimitCompletionLeg_comp_restrictionHom f).symm ≫
    presentationLimitLift Aplus U (presentationIndexCone Aplus U _ presentationLimitCompletionLeg
      fun f ↦ presentationLimitCompletionLeg_comp_restrictionHom f)

@[reassoc]
private theorem presentationLimitCompletionHom_comp_πToPresentation
    (i : PresentationIndex (P := P) Aplus U) :
    presentationLimitCompletionHom (P' := P') U ≫ presentationLimitπToPresentation Aplus U i =
      presentationLimitCompletionLeg i := by
  rw [presentationLimitCompletionHom, Category.assoc]
  exact presentationIndexCone_lift_comp_πToPresentation Aplus U _ _ _ i

variable (P') in
/-- The comparison map to the completed side, `𝒪_A(U) ⟶ 𝒪_{Â}(V)` for `V` the preimage of `U`:
the lift of the legs `presentationLimitDescendLeg`. -/
private noncomputable def presentationLimitDescendHom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a) (U : Opens ↥(spa Aplus)) :
    presentationLimit (P := P) Aplus U ⟶ presentationLimit (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U) :=
  eqToHom (presentationIndexCone_pt _ _ _ (presentationLimitDescendLeg P' hAplus')
      fun f ↦ presentationLimitDescendLeg_comp_restrictionHom hAplus hAplus' f).symm ≫
    presentationLimitLift _ _ (presentationIndexCone _ _ _ (presentationLimitDescendLeg P' hAplus')
      fun f ↦ presentationLimitDescendLeg_comp_restrictionHom hAplus hAplus' f)

@[reassoc]
private theorem presentationLimitDescendHom_comp_πToPresentation
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a)
    (j : PresentationIndex (P := P') (completionPlus Aplus)
      ((Opens.map (spaCompletionTopHom Aplus)).obj U)) :
    presentationLimitDescendHom (P := P) P' hAplus hAplus' U ≫
        presentationLimitπToPresentation _ _ j =
      presentationLimitDescendLeg P' hAplus' j := by
  rw [presentationLimitDescendHom, Category.assoc]
  exact presentationIndexCone_lift_comp_πToPresentation _ _ _ _ _ j

/-- **The comparison maps with the completed side are mutually inverse**, on `𝒪_A(U)`. -/
private theorem presentationLimitDescendHom_comp_presentationLimitCompletionHom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a) :
    presentationLimitDescendHom (P := P) P' hAplus hAplus' U ≫
      presentationLimitCompletionHom U = 𝟙 _ := by
  refine presentationLimit_hom_ext_toPresentation fun i ↦ ?_
  -- the composite projects at the index descended from the one `i` induces, whose rational
  -- subset is that of `i`, and then applies a map compatible with the identity of `A`
  rw [Category.assoc, presentationLimitCompletionHom_comp_πToPresentation,
    presentationLimitCompletionLeg, presentationLimitDescendHom_comp_πToPresentation_assoc,
    presentationLimitDescendLeg, Category.id_comp, Category.assoc, Category.assoc,
    ← Category.comp_id (presentationLimitπToPresentation Aplus U i)]
  refine (presentationLimitπToPresentation_comp_eq_of_subset hAplus
    (rationalSubset_subset_of_image_subset ?_) ?_).symm
  · simpa only [PresentationIndex.map_pres_num, PresentationIndex.map_pres_den] using
      ((i.completion (P' := P')).rationalSubset_descend (P := P)).le
  · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      Category.comp_id, Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
      toCompletionLocTopHom_comp_homOfRationalSubsetSubset_assoc,
      Presentation.toCompletionLocTopHom_comp_completionHom]
    exact (Presentation.coeRingHom_comp_completionExtendTopHom _).symm

/-- **The comparison maps with the completed side are mutually inverse**, on `𝒪_{Â}(V)`. -/
private theorem presentationLimitCompletionHom_comp_presentationLimitDescendHom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a) :
    presentationLimitCompletionHom U ≫ presentationLimitDescendHom (P := P) P' hAplus hAplus' U =
      𝟙 _ := by
  refine presentationLimit_hom_ext_toPresentation fun j ↦ ?_
  -- the composite projects at the index induced by the one descended from `j`, which presents the
  -- rational subset of `j`, and then applies a map out of `Â⟨T/s⟩` fixed on `A`, hence on `Â`
  rw [Category.assoc, presentationLimitDescendHom_comp_πToPresentation,
    presentationLimitDescendLeg, presentationLimitCompletionHom_comp_πToPresentation_assoc,
    presentationLimitCompletionLeg, Category.id_comp, Category.assoc,
    ← Category.comp_id (presentationLimitπToPresentation _ _ j)]
  refine (presentationLimitπToPresentation_comp_eq_of_subset hAplus'
    (j.rationalSubset_descend (P := P)).le ?_).symm
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    Category.comp_id, Presentation.toCompletionLocTopHom_comp_completionHom_assoc]
  refine Subtype.ext <| Completion.ringHom_ext_of_continuous
    (Subtype.property (p := fun f : _ →+* _ ↦ Continuous f) _)
    (Subtype.property (p := fun f : _ →+* _ ↦ Continuous f) _) ?_
  -- composing a ring homomorphism with `coeRingHom` is precomposing its `TopCommRingCat` morphism
  -- with the completion map, which is how the compatibility lemmas below are stated
  let ι : TopCommRingCat.of A ⟶ TopCommRingCat.of (Completion A) :=
    ⟨Completion.coeRingHom, Completion.continuous_coeRingHom⟩
  change (ι ≫ _).1 = (ι ≫ _).1
  refine congrArg Subtype.val ?_
  simp only [ι, Presentation.coeRingHom_comp_completionExtendTopHom_assoc,
    Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
    toCompletionLocTopHom_comp_homOfRationalSubsetSubset]

/-- **The comparison map to the completed side commutes with restriction.** -/
@[reassoc]
private theorem presentationLimitMap_comp_presentationLimitDescendHom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a) {U₁ : Opens ↥(spa Aplus)}
    (hU : U ≤ U₁) :
    presentationLimitMap (P := P) hU ≫ presentationLimitDescendHom P' hAplus hAplus' U =
      presentationLimitDescendHom P' hAplus hAplus' U₁ ≫
        presentationLimitMap (P := P') ((Opens.map (spaCompletionTopHom Aplus)).monotone hU) := by
  refine presentationLimit_hom_ext_toPresentation fun j ↦ ?_
  simp only [Category.assoc, presentationLimitDescendHom_comp_πToPresentation,
    presentationLimitDescendHom_comp_πToPresentation_assoc, presentationLimitDescendLeg,
    reassoc_of% presentationLimitMap_comp_πToPresentation,
    presentationLimitMap_comp_πToPresentation]
  -- both sides project at indices of `U₁` presenting the rational subset descended from `j`
  refine presentationLimitπToPresentation_comp_eq_of_subset hAplus
    (rationalSubset_subset_of_image_subset ?_) ?_
  · have e₁ := ((presentationIndexRestrict ((Opens.map (spaCompletionTopHom Aplus)).monotone
      hU)).obj j).rationalSubset_descend (P := P)
    simp only [presentationIndexRestrict_obj_pres] at e₁ ⊢
    simpa only [PresentationIndex.map_pres_num, PresentationIndex.map_pres_den] using
      ((j.rationalSubset_descend (P := P)).symm.trans e₁).le
  · simp [Presentation.toCompletionLocTopHom_comp_mapHom_assoc,
      toCompletionLocTopHom_comp_homOfRationalSubsetSubset_assoc,
      toCompletionLocTopHom_comp_homOfRationalSubsetSubset]

variable (P P') in
/-- The presentation-limit presheaf of `(A, A⁺)` is the pushforward of that of `(Â, Â⁺)` along the
homeomorphism `Spa(Â, Â⁺) ≃ Spa(A, A⁺)`. -/
private noncomputable def presentationLimitPresheafCompletionIso
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a) :
    presentationLimitPresheaf P Aplus ≅ (TopCat.Presheaf.pushforward _
      (spaCompletionTopHom Aplus)).obj (presentationLimitPresheaf P' (completionPlus Aplus)) :=
  NatIso.ofComponents
    (fun W ↦ eqToIso (presentationLimitPresheaf_obj P Aplus W) ≪≫
      Iso.mk (presentationLimitDescendHom P' hAplus hAplus' W.unop)
        (presentationLimitCompletionHom W.unop)
        (presentationLimitDescendHom_comp_presentationLimitCompletionHom hAplus hAplus')
        (presentationLimitCompletionHom_comp_presentationLimitDescendHom hAplus hAplus') ≪≫
      eqToIso (presentationLimitPresheaf_obj P' (completionPlus Aplus) _).symm)
    fun {W W'} f ↦ by
      simp only [presentationLimitPresheaf_map, TopCat.Presheaf.pushforward_obj_map, Iso.trans_hom,
        eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [presentationLimitMap_comp_presentationLimitDescendHom_assoc]

variable (P P') in
/-- **Sheafhood of the presentation limit is invariant under completion.** If `A⁺` consists of
power-bounded elements and `Â⁺` is the closure of its image in the completion `Â`, the
presentation-limit presheaf of `Spa(Â, Â⁺)` for a pair of definition `P'` of `Â` is a sheaf exactly
when that of `Spa(A, A⁺)` for a pair of definition `P` of `A` is. -/
theorem isSheaf_presentationLimitPresheaf_completionPlus_iff
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (completionPlus Aplus)))
        (presentationLimitPresheaf P' (completionPlus Aplus)) ↔
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) := by
  have hAplus' : ∀ ⦃a⦄, a ∈ completionPlus Aplus → IsPowerBounded a := fun a ha ↦
    mem_powerBoundedSubring.mp <| topologicalClosure_map_coeRingHom_le_powerBoundedSubring
      (fun b hb ↦ mem_powerBoundedSubring.mpr (hAplus hb)) (completionPlus_def Aplus ▸ ha)
  exact (TopCat.Presheaf.isSheaf_iff_of_iso_pushforward (X := TopCat.of ↥(spa Aplus))
    (Y := TopCat.of ↥(spa (completionPlus Aplus)))
    (F := presentationLimitPresheaf P Aplus)
    (G := presentationLimitPresheaf P' (completionPlus Aplus))
    (TopCat.isoOfHomeo (spaCompletionHomeomorph Aplus))
    (presentationLimitPresheafCompletionIso P P' hAplus hAplus')).symm

end TauCeti.ValuationSpectrum

end
