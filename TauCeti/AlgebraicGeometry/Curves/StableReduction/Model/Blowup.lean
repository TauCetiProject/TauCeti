/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Flat
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Isomorphism

/-!
# Blowing up a model in a centre of its special fibre

Let `R` be a discrete valuation ring with fraction field `K`, let `M` be a model over `R` of a
scheme `C` over `K`, and let `I` be an ideal sheaf of finite type on the total space `X` of `M`
whose support `V(I)` does not meet the generic fibre `C ⊆ X`; for instance the ideal sheaf of a
closed point of the special fibre. The blowup `Bl_I X ⟶ X` is again a model of `C`:

* it is flat over `R`, since blowups of flat schemes over a discrete valuation ring are flat
  (`AlgebraicGeometry.Scheme.IdealSheafData.flat_blowupToBase_comp`);
* it is of finite presentation over `R`, since `I` is of finite type and `R` is noetherian;
* its generic fibre is still `C`, since the blowup is an isomorphism over the open `X ∖ V(I)`,
  which contains `C`.

The blowup `Bl_I X ⟶ X` is a morphism of models, proper when `M` is. It is the terminal model
over `M` on which `V(I)` pulls back to an effective Cartier divisor. These are the blowups whose
iteration, interleaved with normalization, resolves the singularities of a model of a smooth
curve.

## Main definitions

* `TauCeti.Model.blowup M I hI hC`: the blowup of the model `M` along `I`, as a model of `C`.
* `TauCeti.Model.blowupHom M I hI hC`: the blowup morphism, as a morphism of models.
* `TauCeti.Model.blowupLift`: the morphism of models into the blowup given by the universal
  property of the blowup.

## Main results

* `TauCeti.Model.genericι_blowupToBase`: on generic fibres, the blowup morphism is the identity
  of `C`.
* `TauCeti.Model.isProper_blowup`: the blowup of a proper model is a proper model.
* `TauCeti.Model.blowupLift_blowupHom` and `TauCeti.Model.eq_blowupLift`: the universal property
  of the blowup, in the category of models.
* `TauCeti.Model.isIso_blowupHom_iff`: blowing up changes the model exactly when `V(I)` is not
  already an effective Cartier divisor.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.1
  (blowing up) and Chapter 10 (models of curves).
* [Stacks Project, Chapter 55](https://stacks.math.columbia.edu/tag/0C2P), *Semistable
  Reduction*, where regular models are produced by blowing up closed points of the special fibre.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable (M : Model R K C toK) (I : M.total.IdealSheafData)
  (hI : ∀ U : M.total.affineOpens, (I.ideal U).FG)
  (hC : Disjoint (Set.range M.genericι) (I.support : Set M.total))

/-- The generic fibre `C` of `M` lies in the open complement `X ∖ V(I)` of the centre. -/
private def genericToCompl : C ⟶ I.support.compl :=
  IsOpenImmersion.lift (Scheme.Opens.ι I.support.compl) M.genericι (by
    rw [Scheme.Opens.range_ι]
    exact hC.subset_compl_right)

@[reassoc]
private lemma genericToCompl_ι :
    genericToCompl M I hC ≫ Scheme.Opens.ι I.support.compl = M.genericι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The generic fibre `C` of `M`, lifted to the blowup through the open `X ∖ V(I)` over which the
blowup is an isomorphism. -/
private def genericLift : C ⟶ I.blowup :=
  genericToCompl M I hC ≫ inv (I.blowupToBase ∣_ I.support.compl) ≫
    (I.blowupToBase ⁻¹ᵁ I.support.compl).ι

@[reassoc]
private lemma genericLift_blowupToBase : genericLift M I hC ≫ I.blowupToBase = M.genericι := by
  simp [genericLift, ← morphismRestrict_ι, genericToCompl_ι]

/-- The generic fibre `C` of `M` is the pullback of the blowup along the inclusion `C ⟶ X`. -/
private lemma isPullback_genericLift :
    IsPullback (genericLift M I hC) (𝟙 C) I.blowupToBase M.genericι := by
  -- Over `X ∖ V(I)` the blowup is an isomorphism, and `C` lies over `X ∖ V(I)`.
  have h := (IsPullback.of_vert_isIso (fst := genericToCompl M I hC ≫
      inv (I.blowupToBase ∣_ I.support.compl)) (snd := 𝟙 C) (g := genericToCompl M I hC)
      ⟨by simp⟩).paste_horiz
    (isPullback_morphismRestrict I.blowupToBase I.support.compl).flip
  rw [genericToCompl_ι, Category.assoc] at h
  exact h

/-- The generic fibre of the blowup, over the fraction field, is `C`. -/
private lemma isPullback_genericLift_toBase :
    IsPullback (genericLift M I hC) toK (I.blowupToBase ≫ M.toBase)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  simpa using (isPullback_genericLift M I hC).paste_vert M.isPullback_genericι

/-- The identification of the generic fibre of the blowup of the total space of `M` along `I`
with `C`, when the support of `I` does not meet the generic fibre. -/
def blowupGenericFiberIso : genericFiber R K (I.blowupToBase ≫ M.toBase) ≅ Over.mk toK :=
  Over.isoMk (isPullback_genericLift_toBase M I hC).isoPullback.symm (by simp)

/-- **The blowup of a model in a centre of its special fibre.** For an ideal sheaf `I` of finite
type on the total space of `M` whose support does not meet the generic fibre, the blowup of the
total space along `I` is a model of `C`, with structure morphism through the blowup morphism. -/
abbrev blowup : Model R K C toK where
  total := I.blowup
  toBase := I.blowupToBase ≫ M.toBase
  flat := I.flat_blowupToBase_comp M.toBase
  locallyOfFinitePresentation := by
    have := I.isProper_blowupToBase hI
    infer_instance
  quasiCompact := by
    have := I.isProper_blowupToBase hI
    infer_instance
  quasiSeparated := by
    have := I.isProper_blowupToBase hI
    infer_instance
  genericFiberIso := M.blowupGenericFiberIso I hC

/-- The total space of the blowup model is the blowup of the total space. -/
@[simp]
lemma blowup_total : (M.blowup I hI hC).total = I.blowup :=
  (rfl)

/-- The structure morphism of the blowup model factors through the blowup morphism. -/
@[simp]
lemma blowup_toBase : (M.blowup I hI hC).toBase = I.blowupToBase ≫ M.toBase :=
  (rfl)

/-- The blowup of a proper model is a proper model. -/
lemma isProper_blowup [hM : M.IsProper] : (M.blowup I hI hC).IsProper := by
  have := I.isProper_blowupToBase hI
  have : AlgebraicGeometry.IsProper M.toBase := hM
  rw [Model.IsProper, blowup_toBase]
  infer_instance

/-- On generic fibres, the blowup morphism is the identity of `C`: the generic fibre of the
blowup model maps to that of `M` by the identity. -/
@[reassoc (attr := simp)]
lemma genericι_blowupToBase :
    (M.blowup I hI hC).genericι ≫ I.blowupToBase = M.genericι := by
  have h : (M.blowup I hI hC).genericι = genericLift M I hC := by
    simp only [genericι_def, blowup, blowupGenericFiberIso, Over.isoMk_inv_left, Iso.symm_inv]
    exact IsPullback.isoPullback_hom_fst _
  rw [h]
  exact genericLift_blowupToBase M I hC

/-- **The blowup morphism of models.** The blowup morphism `Bl_I X ⟶ X` is a morphism from the
blowup model to `M`. -/
def blowupHom : M.blowup I hI hC ⟶ M where
  hom := I.blowupToBase
  overBase := (rfl)
  genericFiber := by
    have : Mono M.genericι := by
      have := M.isOpenImmersion_genericι
      infer_instance
    rw [← cancel_mono M.genericι, Category.assoc, genericFiberIso_hom_left_genericι,
      baseChangeHom_genericFiberι, ← genericι_blowupToBase M I hI hC,
      genericFiberIso_hom_left_genericι_assoc]

/-- The blowup morphism of models has the blowup morphism as underlying morphism. -/
@[simp]
lemma blowupHom_hom : (M.blowupHom I hI hC).hom = I.blowupToBase :=
  (rfl)

/-- The blowup morphism of models is an isomorphism exactly when the centre `V(I)` is already an
effective Cartier divisor on the total space of `M`. -/
theorem isIso_blowupHom_iff : IsIso (M.blowupHom I hI hC) ↔ I.IsEffectiveCartier := by
  rw [isIso_iff_isIso_hom, blowupHom_hom, I.isIso_blowupToBase_iff]

variable {M I hI hC} {N : Model R K C toK}

/-- **The universal property of the blowup model: the lift.** A morphism of models `f : N ⟶ M`
along which the centre `V(I)` pulls back to an effective Cartier divisor factors through the
blowup model. -/
def blowupLift (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    N ⟶ M.blowup I hI hC where
  hom := I.blowupLift f.hom hf
  overBase := by
    rw [blowup_toBase, I.blowupLift_blowupToBase_assoc, f.overBase]
  genericFiber := by
    have : Mono (M.blowup I hI hC).genericι := by
      have := (M.blowup I hI hC).isOpenImmersion_genericι
      infer_instance
    rw [← cancel_mono (M.blowup I hI hC).genericι, Category.assoc,
      genericFiberIso_hom_left_genericι, baseChangeHom_genericFiberι]
    -- Two morphisms to the blowup agree once they agree over `X` and pull the centre back to an
    -- effective Cartier divisor; the generic fibre of `N` is open in `N`, hence flat over it.
    have := isOpenImmersion_genericFiberι R K N.toBase
    refine I.blowup_hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, Scheme.IdealSheafData.blowupLift_blowupToBase,
        genericι_blowupToBase, ← genericι_hom f, genericFiberIso_hom_left_genericι_assoc]
    · rw [Category.assoc, Scheme.IdealSheafData.blowupLift_blowupToBase,
        Scheme.IdealSheafData.comap_comp]
      exact hf.comap _

/-- The lift to the blowup model has the lift to the blowup as underlying morphism. -/
@[simp]
lemma blowupLift_hom (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    (blowupLift (hI := hI) (hC := hC) f hf).hom = I.blowupLift f.hom hf :=
  (rfl)

/-- The lift to the blowup model is a morphism over `M`. -/
@[reassoc (attr := simp)]
lemma blowupLift_blowupHom (f : N ⟶ M) (hf : (I.comap f.hom).IsEffectiveCartier) :
    blowupLift (hI := hI) (hC := hC) f hf ≫ M.blowupHom I hI hC = f :=
  Hom.ext (by simp)

/-- **The universal property of the blowup model: uniqueness.** Every morphism of models to the
blowup model lifting `f` is the lift `blowupLift`. -/
theorem eq_blowupLift {f : N ⟶ M} (hf : (I.comap f.hom).IsEffectiveCartier)
    {g : N ⟶ M.blowup I hI hC} (hg : g ≫ M.blowupHom I hI hC = f) : g = blowupLift f hf := by
  refine Hom.ext (I.eq_blowupLift hf ?_)
  rw [← hg, comp_hom, blowupHom_hom]

end Model

end TauCeti
