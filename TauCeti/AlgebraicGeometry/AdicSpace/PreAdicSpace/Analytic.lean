/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.PresentationLimit
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Restrict
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Analytic

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Cofinality
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic

/-!
# Analytic points of a pre-adic space

A point `x` of a pre-adic space `X` is *analytic* if some open neighbourhood `U` of `x` has a
pseudouniformiser, a topologically nilpotent unit, in `𝒪_X(U)`. This is the intrinsic form of
Huber's analytic points, which on an affinoid `Spa(A, A⁺)` are the points whose support is not
open. The analytic points form an open subset by definition, and they are compatible with
restriction to open subspaces.

On the adic spectrum `Spa(A, A⁺)` with its presentation-limit structure presheaf the two notions
agree. A section of a neighbourhood of `x` which is a pseudouniformiser restricts to one of a
completed rational localisation `A⟨T/s⟩` with `x ∈ R(T/s)`, and `A → A⟨T/s⟩` is adic, so `x` is
analytic in Huber's sense
(`TauCeti.ValuationSpectrum.rationalSubset_subset_spaAnalytic_of_isTateRing`).
Conversely an analytic point lies in a chart `R(G/g)` of the standard rational cover of the
analytic locus, `g` running over generators of an ideal of definition, and the image of `g` is a
pseudouniformiser of the sections `A⟨G/g⟩` over that chart.

The open set of analytic points underlies the analytic locus `X_a` of an adic space `X`
(Wedhorn, Remark 8.37).

## Main definitions

* `TauCeti.PreAdicSpace.analyticPoints`: the analytic points of a pre-adic space.

## Main results

* `TauCeti.PreAdicSpace.isOpen_analyticPoints`: the analytic points form an open subset.
* `TauCeti.PreAdicSpace.analyticPoints_restrict`: the analytic points of the restriction of `X`
  along an open embedding `f` are the preimage under `f` of those of `X`.
* `TauCeti.ValuationSpectrum.analyticPoints_presentationLimitPreAdicSpace`: the analytic points of
  `Spa(A, A⁺)` are the points of its analytic locus `Spa(A, A⁺)ᵃ`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.39,
  Proposition 7.49 and Proposition and Definition 8.36.
* [R. Huber, *A generalization of formal schemes and rigid analytic varieties*], §3.
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology

namespace TauCeti

open Huber

universe u

namespace PreAdicSpace

variable (X : PreAdicSpace.{u})

/-- **Analytic points of a pre-adic space** (Wedhorn, Proposition and Definition 8.36): the points
`x` having an open neighbourhood `U` such that `𝒪_X(U)` contains a pseudouniformiser, that is, a
topologically nilpotent unit. On `Spa(A, A⁺)` these are the points whose support is not open
(`TauCeti.ValuationSpectrum.analyticPoints_presentationLimitPreAdicSpace`). -/
def analyticPoints : Set X :=
  {x | ∃ U : Opens X, x ∈ U ∧
    ∃ f : X.toPresheafedSpace.presheaf.obj (op U), IsPseudoUniformizer f}

variable {X}

/-- Unfolding lemma for `TauCeti.PreAdicSpace.analyticPoints`. -/
theorem mem_analyticPoints_iff {x : X} : x ∈ X.analyticPoints ↔ ∃ U : Opens X, x ∈ U ∧
    ∃ f : X.toPresheafedSpace.presheaf.obj (op U), IsPseudoUniformizer f :=
  Iff.rfl

/-- **The analytic points form an open subset** of a pre-adic space. -/
theorem isOpen_analyticPoints : IsOpen X.analyticPoints :=
  isOpen_iff_forall_mem_open.mpr fun _ ⟨U, hxU, f, hf⟩ ↦
    ⟨U, fun _ hy ↦ ⟨U, hy, f, hf⟩, U.isOpen, hxU⟩

/-- **Analytic points of an open subspace** (Wedhorn, Remark 8.37(2)): the analytic points of the
restriction of `X` along an open embedding `f` are the points that `f` sends to analytic points of
`X`. -/
@[simp]
theorem analyticPoints_restrict {U : TopCat.{u}} {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) :
    (X.restrict h).analyticPoints = f ⁻¹' X.analyticPoints := by
  ext x
  refine ⟨fun ⟨V, hxV, g, hg⟩ ↦ ⟨h.isOpenMap.functor.obj V, ⟨x, hxV, rfl⟩, g, hg⟩, fun hx ↦ ?_⟩
  obtain ⟨W, hxW, g, hg⟩ := hx
  -- the preimage of `W` is a neighbourhood of `x` whose image lies in `W`
  have hle : h.isOpenMap.functor.obj ((Opens.map f).obj W) ≤ W :=
    Set.image_preimage_subset f W
  exact ⟨(Opens.map f).obj W, hxW, _,
    hg.map (X.toPresheafedSpace.presheaf.map (homOfLE hle).op).hom.2⟩

end PreAdicSpace

namespace ValuationSpectrum

open PairOfDefinition

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

/-- **The analytic points of `Spa(A, A⁺)` are its analytic locus** (Wedhorn, Proposition and
Definition 8.36): a point of the adic spectrum has a neighbourhood whose sections contain a
pseudouniformiser exactly when its support is not open. The ring `A` need not be complete. -/
@[simp]
theorem analyticPoints_presentationLimitPreAdicSpace :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints =
      (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) := by
  ext x
  constructor
  · rintro ⟨U, hxU, f, hf⟩
    -- restrict `f` to a rational neighbourhood `R(T/s) ⊆ U` of `x`, whose sections are `A⟨T/s⟩`
    obtain ⟨i, hi⟩ := exists_presentationIndex_mem (P := P) hxU
    let _ := locUniformSpace P i.pres.num i.pres.den _ i.pres.hasDenominatorPower
    have _ := isUniformAddGroup_locUniformSpace P i.pres.num i.pres.den _ i.pres.hasDenominatorPower
    have _ := isTopologicalRing_locUniformSpace P i.pres.num i.pres.den _
      i.pres.hasDenominatorPower
    have _ := isHuberRing_completion_locTopology P i.pres.num i.pres.den _
      i.pres.hasDenominatorPower
    let φ := (eqToHom (presentationLimitPresheaf_obj P Aplus (op U))).hom ≫
      (presentationLimitπToPresentation Aplus U i).hom ≫
      eqToHom (completionLocObj_obj P i.pres.num i.pres.den _ i.pres.hasDenominatorPower)
    -- the image of `f` is a pseudouniformiser of `A⟨T/s⟩`, which is therefore a Tate ring
    exact rationalSubset_subset_spaAnalytic_of_isTateRing P hP i.pres.num i.pres.den _
      i.pres.hasDenominatorPower i.isOpen_span ⟨⟨_, hf.map φ.2⟩⟩ (mem_spaBasicOpen.mp hi)
  · intro hx
    -- `x` lies in a chart `R(G/g)` of the standard rational cover of the analytic locus
    classical
    obtain ⟨G, hG⟩ := P.fg_idealOfDefinition
    replace hx : x.1 ∈ spaAnalytic Aplus := hx
    rw [spaAnalytic_eq_biUnion_rationalSubset P Aplus G hG] at hx
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp hx
    set T := G.image ((↑) : P.ringOfDefinition → A)
    have hT : IsOpen (Ideal.span (T : Set A) : Set A) :=
      P.span_image_eq_extendedIdealOfDefinition G hG ▸ P.isOpen_extendedIdealOfDefinition
    let p : Presentation P := ⟨T, g, P.hasDenominatorPower_of_isOpen_span _ _ _ hT⟩
    let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    -- the image of `g` in `A⟨G/g⟩`, the sections over `R(G/g)`, is a pseudouniformiser
    let ψ := eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm ≫
      (presentationLimitRationalIso Aplus hAplus p hT).inv.hom ≫
      (eqToHom (presentationLimitPresheaf_obj P Aplus (op (spaBasicOpen Aplus T g))).symm).hom
    exact ⟨spaBasicOpen Aplus T g, mem_spaBasicOpen.mpr hxg, _,
      (isPseudoUniformizer_toCompletionLoc P _ _ _ p.hasDenominatorPower
        (P.isTopologicallyNilpotent_of_mem_idealOfDefinition
          (hG ▸ Ideal.subset_span (Finset.mem_coe.mpr hg)))).map ψ.2⟩

end ValuationSpectrum

end TauCeti
