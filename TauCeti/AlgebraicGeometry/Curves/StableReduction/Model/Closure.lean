/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Image

/-!
# Models by scheme-theoretic closure

Let `R` be a discrete valuation ring with fraction field `K`, let `P` be a quasi-compact scheme
locally of finite type over `R`, and let `C` be a closed subscheme of the generic fibre `P_K`. The
scheme-theoretic closure of `C` in `P` is a model of `C` over `R`: it is flat over `R`, because its
local sections embed into sections over `C`, on which every nonzero element of `R` is invertible;
it is of finite presentation, because `R` is noetherian; and its generic fibre is `C` again,
because `C` is closed in the open subscheme `P_K` of `P`. When `P` is proper over `R`, for
instance a projective space `ℙᴺ_R` in which `C` is embedded, the closure is a proper model of `C`.
This is how a projective curve over `K` acquires a proper model over `R`.

## Main definitions

* `TauCeti.Model.closure`: the scheme-theoretic closure of `C` in `P`, as a model of `C`.
* `TauCeti.Model.closureι`: its closed immersion into `P`.

## Main results

* `TauCeti.Model.ker_closureι`: the closure is the scheme-theoretic image of `C → P`.
* `TauCeti.Model.genericι_closureι`: on generic fibres, the closure restricts to `C ⟶ P_K`.
* `TauCeti.Model.isProper_closure`: the closure in a proper scheme over `R` is a proper model.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002: flatness
  over Dedekind schemes in Section 4.3, and models of curves in Chapter 10.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable {P : Scheme.{u}} {toR : P ⟶ Spec (.of R)} (i : C ⟶ (genericFiber R K toR).left)

private lemma comp_genericFiberι_comp (hi : i ≫ (genericFiber R K toR).hom = toK) :
    (i ≫ genericFiberι R K toR) ≫ toR = toK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [Category.assoc, genericFiberι_toBase, ← Category.assoc, hi]

/-- The comparison map from `C` to the generic fibre of the scheme-theoretic closure of `C`
in `P`. -/
private def toGenericFiber (hi : i ≫ (genericFiber R K toR).hom = toK) :
    C ⟶ (genericFiber R K ((i ≫ genericFiberι R K toR).imageι ≫ toR)).left :=
  pullback.lift (i ≫ genericFiberι R K toR).toImage toK (by
    simpa using comp_genericFiberι_comp i hi)

variable (hi : i ≫ (genericFiber R K toR).hom = toK)

@[reassoc]
private lemma toGenericFiber_genericFiberι :
    toGenericFiber i hi ≫ genericFiberι R K ((i ≫ genericFiberι R K toR).imageι ≫ toR) =
      (i ≫ genericFiberι R K toR).toImage :=
  pullback.lift_fst _ _ _

@[reassoc]
private lemma toGenericFiber_hom :
    toGenericFiber i hi ≫ (genericFiber R K ((i ≫ genericFiberι R K toR).imageι ≫ toR)).hom =
      toK :=
  pullback.lift_snd _ _ _

/-- The generic fibre of the closure maps to the generic fibre of `P`, by base change of the
closed immersion of the closure into `P`. -/
private def genericFiberToGenericFiber :
    (genericFiber R K ((i ≫ genericFiberι R K toR).imageι ≫ toR)).left ⟶
      (genericFiber R K toR).left :=
  (pullbackRightPullbackFstIso toR _ (i ≫ genericFiberι R K toR).imageι).inv ≫
    pullback.snd _ _

private instance : IsClosedImmersion (genericFiberToGenericFiber i) := by
  rw [genericFiberToGenericFiber]
  infer_instance

private lemma toGenericFiber_genericFiberToGenericFiber :
    toGenericFiber i hi ≫ genericFiberToGenericFiber i = i := by
  apply pullback.hom_ext
  · simp only [genericFiberToGenericFiber, Over.mk_left, Over.mk_hom, Over.pullback_obj_left,
      Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]
    rw [← Category.assoc, toGenericFiber_genericFiberι i hi, Scheme.Hom.toImage_imageι]
  · simp only [genericFiberToGenericFiber, Over.mk_left, Over.mk_hom, Over.pullback_obj_left,
      Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    exact (toGenericFiber_hom i hi).trans hi.symm

private lemma isIso_toGenericFiber [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    [IsClosedImmersion i] : IsIso (toGenericFiber i hi) := by
  have := isOpenImmersion_genericFiberι R K toR
  have := isOpenImmersion_genericFiberι R K ((i ≫ genericFiberι R K toR).imageι ≫ toR)
  have : IsOpenImmersion (toGenericFiber i hi ≫
      genericFiberι R K ((i ≫ genericFiberι R K toR).imageι ≫ toR)) := by
    rw [toGenericFiber_genericFiberι]
    infer_instance
  have : IsOpenImmersion (toGenericFiber i hi) := .of_comp _
    (genericFiberι R K ((i ≫ genericFiberι R K toR).imageι ≫ toR))
  have : IsClosedImmersion (toGenericFiber i hi ≫ genericFiberToGenericFiber i) := by
    rw [toGenericFiber_genericFiberToGenericFiber]
    infer_instance
  have : IsClosedImmersion (toGenericFiber i hi) :=
    .of_comp_isClosedImmersion _ (genericFiberToGenericFiber i)
  -- The range is closed, and dense because the closure is the image of `C`.
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
  have hdense : Dense (Set.range (toGenericFiber i hi)) := by
    refine ((i ≫ genericFiberι R K toR).toImage.denseRange.preimage
      (genericFiberι R K _).isOpenEmbedding.isOpenMap).mono ?_
    rintro x ⟨c, hc⟩
    refine ⟨c, (genericFiberι R K _).isOpenEmbedding.injective ?_⟩
    rw [← hc, ← Scheme.Hom.comp_apply, toGenericFiber_genericFiberι]
  simpa using (toGenericFiber i hi).isClosedEmbedding.isClosed_range.closure_eq.symm.trans
    hdense.closure_eq

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsClosedImmersion i]

section

variable [LocallyOfFiniteType toR] [QuasiCompact toR]

/-- The scheme-theoretic closure in `P` of a closed subscheme `C` of the generic fibre of
`P → Spec R`, as a model of `C`: its total space is the scheme-theoretic image of `C → P`, and its
generic fibre is identified with `C`. -/
def closure : Model R K C toK where
  total := (i ≫ genericFiberι R K toR).image
  toBase := (i ≫ genericFiberι R K toR).imageι ≫ toR
  flat := Scheme.Hom.flat_imageι_comp _ toR toK (comp_genericFiberι_comp i hi)
  locallyOfFinitePresentation := inferInstance
  quasiCompact := inferInstance
  quasiSeparated := by
    have := LocallyOfFiniteType.isLocallyNoetherian ((i ≫ genericFiberι R K toR).imageι ≫ toR)
    infer_instance
  genericFiberIso :=
    have := isIso_toGenericFiber i hi
    Over.isoMk (asIso (toGenericFiber i hi)).symm (by
      simp only [Iso.symm_hom, asIso_inv, Over.mk_hom, IsIso.inv_comp_eq, toGenericFiber_hom])

/-- The chosen identification of the closure model's generic fibre with `C` is, in the direction
`C ⟶ (closure)_K`, the comparison map `toGenericFiber`: `closure` builds it as the inverse of
`asIso (toGenericFiber i hi)`. -/
private lemma closure_genericFiberIso_inv_left :
    (closure i hi).genericFiberIso.inv.left = toGenericFiber i hi := by
  simp only [closure, Over.isoMk_inv_left, Iso.symm_inv, asIso_hom]

/-- The closed immersion of the closure model into `P`. -/
def closureι : (closure i hi).total ⟶ P :=
  (i ≫ genericFiberι R K toR).imageι

instance : IsClosedImmersion (closureι i hi) :=
  inferInstanceAs (IsClosedImmersion (i ≫ genericFiberι R K toR).imageι)

/-- The structure morphism of the closure model is the restriction of that of `P`. -/
@[reassoc (attr := simp)]
lemma closureι_toBase : closureι i hi ≫ toR = (closure i hi).toBase :=
  (rfl)

/-- The closure model is the scheme-theoretic image of `C` in `P`: its ideal sheaf in `P` is the
kernel of `C → P`. -/
@[simp]
lemma ker_closureι : (closureι i hi).ker = (i ≫ genericFiberι R K toR).ker :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- On generic fibres, the inclusion of the closure model into `P` restricts to the inclusion of
`C` into the generic fibre of `P`. -/
@[reassoc (attr := simp)]
lemma genericι_closureι : (closure i hi).genericι ≫ closureι i hi = i ≫ genericFiberι R K toR := by
  rw [← Over.inv_left_hom_left_assoc (closure i hi).genericFiberIso
    ((closure i hi).genericι ≫ closureι i hi), genericFiberIso_hom_left_genericι_assoc,
    closure_genericFiberIso_inv_left]
  exact (toGenericFiber_genericFiberι_assoc i hi _).trans (Scheme.Hom.toImage_imageι _)

end

/-- The closure of `C` in a proper scheme over `R` is a proper model of `C`. -/
lemma isProper_closure [AlgebraicGeometry.IsProper toR] : (closure i hi).IsProper := by
  rw [Model.IsProper, ← closureι_toBase]
  infer_instance

end Model

end TauCeti
