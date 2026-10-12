/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.Valuation
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedPlus

/-!
# The plus presheaf `𝒪_X⁺` of the presentation-limit presheaf

Let `X = Spa(A,A⁺)` and let `𝒪_X` be the presentation-limit structure presheaf, read as a presheaf
of commutative rings. Every point `x ∈ X` carries the stalk valuation `v_x` on `𝒪_{X,x}`, and
Wedhorn defines the *plus presheaf* by

```text
𝒪_X⁺(V) = { f ∈ 𝒪_X(V) : v_x(f_x) ≤ 1 for every x ∈ V },
```

where `f_x` is the germ of `f` at `x`. This file defines `𝒪_X⁺(V)` as a subring of `𝒪_X(V)`,
shows that the restriction maps of `𝒪_X` carry `𝒪_X⁺(V)` into `𝒪_X⁺(W)` for `W ⊆ V`, and packages
the result as a presheaf of commutative rings `𝒪_X⁺` with a monomorphism `𝒪_X⁺ ⟶ 𝒪_X`.

On a rational open `U = R(T/s)` the sections `𝒪_X(U)` are the coordinate ring `A⟨T/s⟩`, and the
main result identifies `𝒪_X⁺(U)` with its plus ring `A_U⁺ = completedPlusSubring`: this is the
second component of Wedhorn's Proposition 8.16. The identification is the sub-unit description of
`A_U⁺` from `Spa/Localization/CompletedPlus.lean` read through the stalk valuations, which restrict
to the points of `A⟨T/s⟩` determined by the points of `U`.

The hypotheses are those of the stalk valuation: `A⁺` consists of power-bounded elements and
contains the ring of definition of the chosen pair of definition.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPlusSubring`: `𝒪_X⁺(V)`, a subring of `𝒪_X(V)`.
* `TauCeti.ValuationSpectrum.presentationLimitPlusPresheaf`: `𝒪_X⁺` as a presheaf of commutative
  rings on `Spa(A,A⁺)`.
* `TauCeti.ValuationSpectrum.presentationLimitPlusPresheafι`: the inclusion `𝒪_X⁺ ⟶ 𝒪_X`, a
  monomorphism.

## Main results

* `TauCeti.ValuationSpectrum.mem_presentationLimitPlusSubring_iff`: a section lies in `𝒪_X⁺(V)`
  exactly when its germ at every point of `V` is sub-unit for the stalk valuation.
* `TauCeti.ValuationSpectrum.presentationLimitPlusSubring_le_comap`: restriction carries `𝒪_X⁺(V)`
  into `𝒪_X⁺(W)`.
* `TauCeti.ValuationSpectrum.comap_presentationLimitPlusSubring_spaBasicOpen` and
  `TauCeti.ValuationSpectrum.map_completedPlusSubring_eq_presentationLimitPlusSubring`: on a
  rational open `R(T/s)`, the subring `𝒪_X⁺(R(T/s))` corresponds to `A_U⁺ ⊆ A⟨T/s⟩` under the
  identification `𝒪_X(R(T/s)) ≅ A⟨T/s⟩`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.16.
-/

namespace TauCeti.ValuationSpectrum

open AlgebraicGeometry CategoryTheory _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-! ### The plus subring of the sections over an open -/

/-- **`𝒪_X⁺(V)`**, the plus subring of the sections of the presentation-limit presheaf over an
open `V ⊆ Spa(A,A⁺)`: the sections whose germ at every point `x ∈ V` is sub-unit for the stalk
valuation `v_x`. It is the intersection over `x ∈ V` of the preimages, under the germ maps, of the
valuation rings of the stalk valuations. -/
noncomputable def presentationLimitPlusSubring (V : Opens ↥(spa Aplus)) :
    Subring ((presentationLimitPresheafInCommRingCat P Aplus).obj (Opposite.op V)) :=
  ⨅ x : V, (presentationLimitStalkValuation hAplus hP x).valuation.integer.comap
    ((presentationLimitPresheafInCommRingCat P Aplus).germ V x x.2).hom

/-- **Membership in `𝒪_X⁺(V)`**: a section over `V` lies in the plus subring exactly when its germ
at every point `x ∈ V` is sub-unit for the stalk valuation at `x`. -/
@[simp]
theorem mem_presentationLimitPlusSubring_iff {V : Opens ↥(spa Aplus)}
    {f : (presentationLimitPresheafInCommRingCat P Aplus).obj (Opposite.op V)} :
    f ∈ presentationLimitPlusSubring hAplus hP V ↔
      ∀ (x : ↥(spa Aplus)) (hx : x ∈ V),
        (presentationLimitStalkValuation hAplus hP x).toValuativeRel.vle
          ((presentationLimitPresheafInCommRingCat P Aplus).germ V x hx f) 1 := by
  rw [presentationLimitPlusSubring, Subring.mem_iInf]
  refine Subtype.forall.trans (forall_congr' fun x ↦ forall_congr' fun hx ↦ ?_)
  rw [Subring.mem_comap, Valuation.mem_integer_iff,
    ← map_one (presentationLimitStalkValuation hAplus hP x).valuation, valuation_le_iff]

/-- **Restriction preserves the plus subrings**: the restriction map of the presentation-limit
presheaf along `i : V ⟶ W` in `(Opens X)ᵒᵖ`, that is along `W ⊆ V`, carries `𝒪_X⁺(V)` into
`𝒪_X⁺(W)`. -/
theorem presentationLimitPlusSubring_le_comap {V W : (Opens ↥(spa Aplus))ᵒᵖ} (i : V ⟶ W) :
    presentationLimitPlusSubring hAplus hP V.unop ≤
      (presentationLimitPlusSubring hAplus hP W.unop).comap
        ((presentationLimitPresheafInCommRingCat P Aplus).map i).hom := by
  intro f hf
  rw [mem_presentationLimitPlusSubring_iff] at hf
  rw [Subring.mem_comap, mem_presentationLimitPlusSubring_iff]
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply']
  exact hf x (i.unop.le hx)

/-! ### The plus presheaf -/

/-- **The plus presheaf `𝒪_X⁺`** of `X = Spa(A,A⁺)`: the presheaf of commutative rings whose
sections over `V` are the plus subring `𝒪_X⁺(V)` of the sections of the presentation-limit
presheaf, with the restriction maps of that presheaf. -/
noncomputable def presentationLimitPlusPresheaf :
    (TopCat.of ↥(spa Aplus)).Presheaf CommRingCat.{v} where
  obj V := CommRingCat.of (presentationLimitPlusSubring hAplus hP V.unop)
  map i := CommRingCat.ofHom
    (((presentationLimitPresheafInCommRingCat P Aplus).map i).hom.restrict _ _
      (presentationLimitPlusSubring_le_comap hAplus hP i))
  -- On underlying elements the restricted maps are the restriction maps of the ambient presheaf
  -- (`RingHom.coe_restrict_apply` is `rfl`), so both laws are those of that presheaf.
  map_id V := CommRingCat.hom_ext <| RingHom.ext fun f ↦ Subtype.ext <|
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      ((presentationLimitPresheafInCommRingCat P Aplus).map_id V)) (f : _)
  map_comp i j := CommRingCat.hom_ext <| RingHom.ext fun f ↦ Subtype.ext <|
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      ((presentationLimitPresheafInCommRingCat P Aplus).map_comp i j)) (f : _)

/-- The sections of `𝒪_X⁺` over `V` are the plus subring `𝒪_X⁺(V)`. -/
@[simp]
theorem presentationLimitPlusPresheaf_obj (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPlusPresheaf hAplus hP).obj V =
      CommRingCat.of (presentationLimitPlusSubring hAplus hP V.unop) := by
  rfl

/-- The restriction maps of `𝒪_X⁺` are those of the presentation-limit presheaf, restricted to
the plus subrings. The equality transports account for the sealed evaluation theorem
`presentationLimitPlusPresheaf_obj`. -/
@[simp]
theorem presentationLimitPlusPresheaf_map {V W : (Opens ↥(spa Aplus))ᵒᵖ} (i : V ⟶ W) :
    (presentationLimitPlusPresheaf hAplus hP).map i ≫
        eqToHom (presentationLimitPlusPresheaf_obj hAplus hP W) =
      eqToHom (presentationLimitPlusPresheaf_obj hAplus hP V) ≫ CommRingCat.ofHom
        (((presentationLimitPresheafInCommRingCat P Aplus).map i).hom.restrict _ _
          (presentationLimitPlusSubring_le_comap hAplus hP i)) := by
  rfl

/-- **The inclusion `𝒪_X⁺ ⟶ 𝒪_X`** of the plus presheaf into the presentation-limit presheaf. -/
noncomputable def presentationLimitPlusPresheafι :
    presentationLimitPlusPresheaf hAplus hP ⟶ presentationLimitPresheafInCommRingCat P Aplus where
  app V := CommRingCat.ofHom (presentationLimitPlusSubring hAplus hP V.unop).subtype
  naturality _ _ _ := CommRingCat.hom_ext <| RingHom.ext fun _ ↦ rfl

/-- The inclusion `𝒪_X⁺ ⟶ 𝒪_X` is, over each open `V`, the inclusion of the subring `𝒪_X⁺(V)`.
The equality transport accounts for the sealed evaluation theorem
`presentationLimitPlusPresheaf_obj`. -/
@[simp]
theorem presentationLimitPlusPresheafι_app (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPlusPresheafι hAplus hP).app V =
      eqToHom (presentationLimitPlusPresheaf_obj hAplus hP V) ≫
        CommRingCat.ofHom (presentationLimitPlusSubring hAplus hP V.unop).subtype := by
  rfl

/-- The inclusion `𝒪_X⁺ ⟶ 𝒪_X` is a monomorphism: `𝒪_X⁺` is a sub-presheaf of `𝒪_X`. -/
instance : Mono (presentationLimitPlusPresheafι hAplus hP) :=
  haveI : ∀ V, Mono ((presentationLimitPlusPresheafι hAplus hP).app V) := fun V ↦ by
    rw [presentationLimitPlusPresheafι_app]
    have := ConcreteCategory.mono_of_injective
      (CommRingCat.ofHom (presentationLimitPlusSubring hAplus hP V.unop).subtype)
      (Subring.subtype_injective _)
    exact mono_comp _ _
  NatTrans.mono_of_mono_app _

/-! ### The plus subring of a rational open is `A_U⁺` -/

/-- **`𝒪_X⁺(R(T/s)) = A_U⁺`** (Wedhorn, Proposition 8.16, second component): under the
identification `A⟨T/s⟩ ≅ 𝒪_X(R(T/s))` of the coordinate ring of an admissible presentation with the
sections of the presentation-limit presheaf over its rational open, the plus subring
`𝒪_X⁺(R(T/s))` pulls back to the plus ring `A_U⁺` of `A⟨T/s⟩`. -/
theorem comap_presentationLimitPlusSubring_spaBasicOpen (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    (presentationLimitPlusSubring hAplus hP (spaBasicOpen Aplus p.num p.den)).comap
        ((Presentation.completionLocObjCommRingCatIso p).inv ≫
          (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv).hom =
      completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  ext g
  rw [Subring.mem_comap, mem_presentationLimitPlusSubring_iff,
    mem_completedPlusSubring_iff_forall_mem_rationalSubset_vle_one P Aplus hP p.num p.den _
      p.hasDenominatorPower]
  -- at a point `x` of `R(p)`: the germ of the section corresponding to `g` is the rational germ
  -- of `g`, and the stalk valuation pulls back along the rational germ map to the point of
  -- `A⟨p⟩` determined by `x`, which is the point of `Spa (A⟨p⟩, A_p⁺)` over `x`
  have key : ∀ (x : ↥(spa Aplus)) (hx : x ∈ spaBasicOpen Aplus p.num p.den),
      (presentationLimitStalkValuation hAplus hP x).toValuativeRel.vle
        ((presentationLimitPresheafInCommRingCat P Aplus).germ (spaBasicOpen Aplus p.num p.den) x hx
          (((Presentation.completionLocObjCommRingCatIso p).inv ≫
            (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv) g)) 1 ↔
      ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _ p.hasDenominatorPower).symm
        ⟨x, mem_spaBasicOpen.mp hx⟩ : Spv _).toValuativeRel.vle g 1 := by
    intro x hx
    have hgerm : (presentationLimitPresheafInCommRingCat P Aplus).germ
          (spaBasicOpen Aplus p.num p.den) x hx
          (((Presentation.completionLocObjCommRingCatIso p).inv ≫
            (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv) g) =
        presentationLimitRationalGerm hAplus p hp x hx
          ((Presentation.completionLocObjCommRingCatIso p).inv g) := by
      rw [presentationLimitRationalGerm_def, CommRingCat.comp_apply, CommRingCat.comp_apply]
    rw [hgerm, ← map_one (presentationLimitRationalGerm hAplus p hp x hx).hom, ← comap_vle,
      comap_presentationLimitRationalGerm_presentationLimitStalkValuation,
      rationalLocalizationPoint_def, comap_vle, map_one, CommRingCat.hom_inv_apply]
  -- the two quantifiers over the points of `R(p)` differ only in how membership is phrased
  exact forall_congr' fun x ↦
    ⟨fun h hx ↦ (key x (mem_spaBasicOpen.mpr hx)).mp (h _), fun h hx ↦ (key x hx).mpr (h _)⟩

/-- **`𝒪_X⁺(R(T/s)) = A_U⁺`** (Wedhorn, Proposition 8.16, second component), as the image of
`A_U⁺` under the identification `A⟨T/s⟩ ≅ 𝒪_X(R(T/s))`. -/
theorem map_completedPlusSubring_eq_presentationLimitPlusSubring (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    (completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower).map
        ((Presentation.completionLocObjCommRingCatIso p).inv ≫
          (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv).hom =
      presentationLimitPlusSubring hAplus hP (spaBasicOpen Aplus p.num p.den) := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  rw [← comap_presentationLimitPlusSubring_spaBasicOpen hAplus hP p hp]
  exact Subring.map_comap_eq_self_of_surjective
    (((Presentation.completionLocObjCommRingCatIso p).symm ≪≫
      (presentationLimitRationalIsoInCommRingCat hAplus p hp).symm)
        |>.commRingCatIsoToRingEquiv.surjective) _

end

end TauCeti.ValuationSpectrum
