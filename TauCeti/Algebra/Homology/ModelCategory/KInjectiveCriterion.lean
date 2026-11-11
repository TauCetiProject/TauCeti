/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import TauCeti.Algebra.Homology.CochainComplex.AcyclicSubcomplex
public import TauCeti.CategoryTheory.MorphismProperty.Cokernel

import Mathlib.Algebra.Homology.ShortComplex.Pullback
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.Order.TransfiniteIteration
import TauCeti.Algebra.Homology.HomologySequenceLemmas
import TauCeti.Algebra.Homology.ModelCategory.Injective
import TauCeti.Algebra.Homology.ShortComplex.Colimit
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.Algebra.Homology.Subobject

/-!
# Testing K-injectivity on small acyclic complexes

Let `C` be a Grothendieck abelian category. A cochain complex `I` of injective objects of `C` is
K-injective as soon as every `1`-cocycle from a complex in a suitable family of acyclic complexes
to `I` is a coboundary, that is, every map from such a complex to `I[1]` is null-homotopic, rather
than requiring this for every acyclic complex. Given a separator of `C`, the family can be chosen
essentially small (`CategoryTheory.IsSeparator.exists_isKInjective_iff`). This reduces the
construction of K-injective replacements of unbounded complexes to a transfinite construction
which only has to kill a set of maps.

The family is described by a property `S` of complexes such that every nonzero acyclic complex
contains a nonzero acyclic subcomplex satisfying `S`. If `G` is a separator of `C`, the bounded
above acyclic complexes whose terms are quotients of a fixed sequence of objects form such a
family (`CategoryTheory.IsSeparator.exists_bounded_nonzero_acyclic_subcomplex`).

## Main results

* `CochainComplex.exists_transfiniteCompositionOfShape_of_quasiIso`: every monomorphism of
  cochain complexes which is a quasi-isomorphism is a transfinite composition of monomorphisms
  whose cokernels satisfy `S` (the morphism property `S.monoWithCokernel`).
* `CochainComplex.isKInjective_of_forall_eq_δ`: if `I` has injective terms and every `1`-cocycle
  from a complex satisfying `S` to `I` is a coboundary, then `I` is K-injective.
* `CategoryTheory.IsSeparator.exists_isKInjective_iff`: given a separator of `C`, there is a
  sequence of objects `B j` such that a complex `I` of injective objects is K-injective if and
  only if every map to `I[1]` from a bounded above acyclic complex whose terms are quotients of
  objects `B j` is null-homotopic, that is, every such `1`-cocycle is a coboundary.

## Implementation notes

For a complex `I` of injective objects, a morphism `I ⟶ 0` has the right lifting property with
respect to a monomorphism `i` whose cokernel has only coboundaries as `1`-cocycles to `I`: the
degreewise extensions of a map along `i` differ from a chain map by such a cocycle
(`CochainComplex.hasLiftingProperty_of_forall_eq_δ`, built on Joël Riou's obstruction cocycle
`CochainComplex.Lifting.cocycle₁`). The class of morphisms with the left lifting property with
respect to `I ⟶ 0` is stable under transfinite composition, so it suffices to write a
monomorphic quasi-isomorphism `A ⟶ X` as a transfinite composition of monomorphisms with
cokernels satisfying `S`. Adapting Joël Riou's proof in Mathlib that Grothendieck abelian
categories have enough injectives
(`CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_rlp`), this is done by a
transfinite iteration in the lattice of subobjects of `X`: a subobject `A'` whose inclusion is
a quasi-isomorphism and which is not `⊤` is enlarged by the preimage of a nonzero subcomplex
satisfying `S` of the acyclic quotient `X / A'`. At limit stages, the inclusion of the union is
again a quasi-isomorphism because homology commutes with filtered colimits. Finally, a complex of
injective objects whose map to `0` lifts against all monomorphic quasi-isomorphisms is
K-injective (`CochainComplex.rlp_monomorphisms_inf_quasiIso_iff_of_isZero`).

## References

* [Stacks: Lemma 079L](https://stacks.math.columbia.edu/tag/079L)
* J. Lurie, *Higher Algebra*, Proposition 1.3.5.3.
-/

public section

universe w v u

namespace CochainComplex

open CategoryTheory Limits MorphismProperty HomComplex ZeroObject

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {S : ObjectProperty (CochainComplex C ℤ)} [S.IsClosedUnderIsomorphisms]

namespace KInjectiveCriterion

variable (hS : ∀ M : CochainComplex C ℤ, M.Acyclic → ¬ IsZero M →
  ∃ (N : CochainComplex C ℤ) (i : N ⟶ M), Mono i ∧ ¬ IsZero N ∧ N.Acyclic ∧ S N)

include hS

/-- A proper subobject `A` of `X` whose inclusion is a quasi-isomorphism is contained in a strictly
larger subobject `A'` whose inclusion is a quasi-isomorphism, such that the cokernel of the
inclusion `A ⟶ A'` satisfies `S`. -/
private lemma exists_larger_subobject {X : CochainComplex C ℤ} (A : Subobject X) (hA : A ≠ ⊤)
    (hA' : QuasiIso A.arrow) :
    ∃ (A' : Subobject X) (h : A < A'), QuasiIso A'.arrow ∧
      S.monoWithCokernel (Subobject.ofLE A A' h.le) := by
  induction A using Subobject.ind with | _ f
  have hf : QuasiIso f := (Subobject.quasiIso_mk_arrow_iff f).1 hA'
  have hQ : (cokernel f).Acyclic := (TauCeti.cokernelSequence_shortExact f).quasiIso_f_iff.1 hf
  have hQ' : ¬ IsZero (cokernel f) := fun h ↦ hA (by
    have := Preadditive.epi_of_isZero_cokernel f h
    have := isIso_of_mono_of_epi f
    exact (Subobject.isIso_iff_mk_eq_top f).1 this)
  obtain ⟨N, j, _, hN, hN', hSN⟩ := hS _ hQ hQ'
  have hE := (TauCeti.cokernelSequence_shortExact f).pull j
  let u : _ ⟶ pullback j (cokernel.π f) := pullback.lift 0 f (by simp)
  have : Mono u := hE.mono_f
  have : Epi (pullback.fst j (cokernel.π f)) := hE.epi_g
  have hu : u ≫ pullback.snd j (cokernel.π f) = f := pullback.lift_snd _ _ _
  have : QuasiIso u := hE.quasiIso_f_iff.2 hN'
  have : QuasiIso (pullback.snd j (cokernel.π f)) := by
    have : QuasiIso (u ≫ pullback.snd _ _) := by rwa [hu]
    exact quasiIso_of_comp_left u _
  have hu' : ¬ IsIso u := fun _ ↦ hN (by
    have : pullback.fst j (cokernel.π f) = 0 := by simp [← cancel_epi u, u]
    exact IsZero.of_epi_eq_zero _ this)
  refine ⟨Subobject.mk (pullback.snd j (cokernel.π f)), Subobject.mk_lt_mk_of_comm u hu hu', ?_, ?_⟩
  · exact (Subobject.quasiIso_mk_arrow_iff _).2 inferInstance
  · refine (S.monoWithCokernel.arrow_mk_iso_iff ?_).1 ((ObjectProperty.mem_monoWithCokernel_iff u).2
      ⟨inferInstance, S.prop_of_iso
        (hE.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)) hSN⟩)
    refine Arrow.isoMk (Subobject.underlyingIso f).symm
      (Subobject.underlyingIso (pullback.snd _ _)).symm ?_
    simp [← cancel_mono (Subobject.mk (pullback.snd j (cokernel.π f))).arrow, hu]

variable {X : CochainComplex C ℤ}

open scoped Classical in
/-- The enlargement step of the transfinite construction: a proper subobject whose inclusion is a
quasi-isomorphism is sent to the subobject given by `exists_larger_subobject`, and every other
subobject is sent to `⊤`. -/
private noncomputable def largerSubobject (A : Subobject X) : Subobject X :=
  if h : A ≠ ⊤ ∧ QuasiIso A.arrow then (exists_larger_subobject hS A h.1 h.2).choose else ⊤

private lemma largerSubobject_top : largerSubobject hS (⊤ : Subobject X) = ⊤ := by
  simp [largerSubobject]

private lemma lt_largerSubobject (A : Subobject X) (hA : A ≠ ⊤) : A < largerSubobject hS A := by
  by_cases hA' : QuasiIso A.arrow
  · rw [largerSubobject, dite_eq_left ⟨hA, hA'⟩]
    exact (exists_larger_subobject hS A hA hA').choose_spec.choose
  · rw [largerSubobject, dite_eq_right (by tauto)]
    exact lt_top_iff_ne_top.2 hA

private lemma le_largerSubobject (A : Subobject X) : A ≤ largerSubobject hS A := by
  by_cases hA : A = ⊤
  · subst hA
    rw [largerSubobject_top]
  · exact (lt_largerSubobject hS A hA).le

private lemma quasiIso_largerSubobject_arrow (A : Subobject X) (hA : QuasiIso A.arrow) :
    QuasiIso (largerSubobject hS A).arrow := by
  by_cases hA' : A = ⊤
  · subst hA'
    rw [largerSubobject_top]
    infer_instance
  · rw [largerSubobject, dite_eq_left ⟨hA', hA⟩]
    exact (exists_larger_subobject hS A hA' hA).choose_spec.choose_spec.1

private lemma prop_ofLE_largerSubobject (A : Subobject X) (hA : A ≠ ⊤) (hA' : QuasiIso A.arrow) :
    S.monoWithCokernel
      (Subobject.ofLE A (largerSubobject hS A) (le_largerSubobject hS A)) := by
  have h := (exists_larger_subobject hS A hA hA').choose_spec.choose_spec.2
  refine (S.monoWithCokernel.arrow_mk_iso_iff (Arrow.isoMk (Iso.refl _) (Subobject.isoOfEq _ _
    (by rw [largerSubobject, dite_eq_left ⟨hA, hA'⟩])) ?_ :
      Arrow.mk (Subobject.ofLE A _ (exists_larger_subobject hS A hA hA').choose_spec.choose.le) ≅
        Arrow.mk (Subobject.ofLE A (largerSubobject hS A) (le_largerSubobject hS A)))).1 h
  simp

end KInjectiveCriterion

section Grothendieck

variable [IsGrothendieckAbelian.{w} C]
  (hS : ∀ M : CochainComplex C ℤ, M.Acyclic → ¬ IsZero M →
    ∃ (N : CochainComplex C ℤ) (i : N ⟶ M), Mono i ∧ ¬ IsZero N ∧ N.Acyclic ∧ S N)

namespace KInjectiveCriterion

include hS

variable {X : CochainComplex C ℤ} (A₀ : Subobject X) (J : Type w) [LinearOrder J] [OrderBot J]
  [SuccOrder J] [WellFoundedLT J]

private lemma transfiniteIterate_mono {j j' : J} (h : j ≤ j') :
    transfiniteIterate (largerSubobject hS) j A₀ ≤ transfiniteIterate (largerSubobject hS) j' A₀ :=
  monotone_transfiniteIterate _ _ (le_largerSubobject hS) h

/-- The transfinite iteration of `largerSubobject`, as a functor to `MonoOver X`. -/
private noncomputable def functorToMonoOver : J ⥤ MonoOver X where
  obj j := MonoOver.mk (transfiniteIterate (largerSubobject hS) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (transfiniteIterate_mono hS A₀ J (leOfHom f)))

/-- The transfinite iteration of `largerSubobject`, as a functor to complexes. -/
private noncomputable abbrev functor : J ⥤ CochainComplex C ℤ :=
  functorToMonoOver hS A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

private lemma functor_map {j j' : J} (f : j ⟶ j') :
    (functor hS A₀ J).map f = Subobject.ofLE (transfiniteIterate (largerSubobject hS) j A₀)
      (transfiniteIterate (largerSubobject hS) j' A₀)
        (transfiniteIterate_mono hS A₀ J (leOfHom f)) :=
  rfl

private lemma isWellOrderContinuous_functor : (functor hS A₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver hS A₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver hS A₀ J) c
    dsimp [c, functorToMonoOver]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hS) A₀ m hm⟩

/-- Every subobject in the transfinite iteration starting from a subobject whose inclusion is a
quasi-isomorphism has an inclusion which is a quasi-isomorphism. -/
private lemma quasiIso_transfiniteIterate_arrow (hA₀ : QuasiIso A₀.arrow) (j : J) :
    QuasiIso (transfiniteIterate (largerSubobject hS) j A₀).arrow := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    rwa [transfiniteIterate_bot]
  | succ j hj hj' =>
    rw [transfiniteIterate_succ _ _ _ hj]
    exact quasiIso_largerSubobject_arrow hS _ hj'
  | isSuccLimit m hm ih =>
    have := hm.nonempty_Iio.to_subtype
    obtain ⟨hc⟩ := (isWellOrderContinuous_functor hS A₀ J).nonempty_isColimit m hm
    rw [quasiIso_iff]
    intro n
    let i₀ : Set.Iio m := ⟨⊥, hm.bot_lt⟩
    let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
    have hF : ((Set.principalSegIio m).monotone.functor ⋙ functor hS A₀ J ⋙ H)
        |>.IsEventuallyConstantFrom i₀ := fun k φ ↦ by
      have : QuasiIso ((functor hS A₀ J).map ((Set.principalSegIio m).monotone.functor.map φ)) :=
        Subobject.quasiIso_ofLE _ (ih _ i₀.2) (ih _ k.2)
      rw [Functor.comp_map, Functor.comp_map, HomologicalComplex.homologyFunctor_map]
      exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 ((quasiIso_iff _).1 this n)
    have hι := hF.isIso_ι_of_isColimit (isColimitOfPreserves H hc)
    rw [Functor.mapCocone_ι_app, PrincipalSeg.cocone_ι_app, HomologicalComplex.homologyFunctor_map,
      functor_map] at hι
    have := ih _ i₀.2
    have : QuasiIsoAt (Subobject.ofLE _ _ (transfiniteIterate_mono hS A₀ J i₀.2.le)) n :=
      (quasiIsoAt_iff_isIso_homologyMap _ n).2 hι
    rw [← quasiIsoAt_iff_comp_left (Subobject.ofLE _ _ (transfiniteIterate_mono hS A₀ J i₀.2.le)),
      Subobject.ofLE_arrow]
    infer_instance

variable {J} in
/-- The transfinite iteration up to `j`, as a transfinite composition, provided it does not reach
`⊤` before `j`. -/
private noncomputable def transfiniteCompositionOfShapeMapFromBot (hA₀ : QuasiIso A₀.arrow)
    (j : J) (hj : ∀ k < j, transfiniteIterate (largerSubobject hS) k A₀ ≠ ⊤) :
    S.monoWithCokernel.TransfiniteCompositionOfShape (Set.Iic j)
      ((functor hS A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ functor hS A₀ J
  isoBot := Iso.refl _
  isWellOrderContinuous := by
    have := isWellOrderContinuous_functor hS A₀ J
    infer_instance
  incl :=
    { app k := (functor hS A₀ J).map (homOfLE k.2)
      naturality k k' h := by
        simp only [Functor.comp_map, Functor.const_obj_map]
        exact (Subobject.ofLE_comp_ofLE _ _ _ _ _).trans (Category.comp_id _).symm }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    have hk' : k.1 < j := lt_of_le_of_ne k.2 fun h ↦ hk fun l _ ↦ by
      rw [← Subtype.coe_le_coe, h]
      exact l.2
    have heq : transfiniteIterate (largerSubobject hS) (Order.succ k).1 A₀ =
        largerSubobject hS (transfiniteIterate (largerSubobject hS) k.1 A₀) := by
      rw [Set.Iic.succ_eq_of_not_isMax hk,
        transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]
    refine (S.monoWithCokernel.arrow_mk_iso_iff
      (Arrow.isoMk (Iso.refl _) (Subobject.isoOfEq _ _ heq.symm) ?_ :
        Arrow.mk (Subobject.ofLE _ _ (le_largerSubobject hS _)) ≅
          Arrow.mk (((Set.initialSegIic j).monotone.functor ⋙ functor hS A₀ J).map
            (homOfLE (Order.le_succ k))))).1
      (prop_ofLE_largerSubobject hS _ (hj _ hk')
        (quasiIso_transfiniteIterate_arrow hS A₀ J hA₀ k.1))
    exact (Category.id_comp _).trans (Subobject.ofLE_comp_ofLE _ _ _ _ _).symm

/-- The transfinite iteration of `largerSubobject` reaches `⊤`. -/
private lemma exists_ordinal :
    ∃ (o : Ordinal.{w}) (j : o.ToType), transfiniteIterate (largerSubobject hS) j A₀ = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have hJ : HasCardinalLT (Subobject X) (Cardinal.mk κ.ord.ToType) :=
    lt_of_lt_of_le (Order.lt_succ _) (by simp [κ])
  exact ⟨κ.ord, top_mem_range_transfiniteIterate (largerSubobject hS) A₀
    (lt_largerSubobject hS) (largerSubobject_top hS)
    (fun h ↦ by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)⟩

end KInjectiveCriterion

include hS

open KInjectiveCriterion in
/-- Let `S` be a property of cochain complexes in a Grothendieck abelian category such that every
nonzero acyclic complex contains a nonzero acyclic subcomplex satisfying `S`. Then every
monomorphism of cochain complexes which is a quasi-isomorphism is a transfinite composition of
monomorphisms whose cokernels satisfy `S`. -/
theorem exists_transfiniteCompositionOfShape_of_quasiIso {A X : CochainComplex C ℤ} (f : A ⟶ X)
    [Mono f] [QuasiIso f] :
    ∃ (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J),
      Nonempty (S.monoWithCokernel.TransfiniteCompositionOfShape J f) := by
  have hA₀ : QuasiIso (Subobject.mk f).arrow := (Subobject.quasiIso_mk_arrow_iff f).2 inferInstance
  obtain ⟨o, j, hj⟩ := exists_ordinal hS (Subobject.mk f)
  have : Nonempty o.ToType := ⟨j⟩
  have := WellFoundedLT.toOrderBot o.ToType
  -- the first index at which the iteration reaches `⊤`
  obtain ⟨j₀, hj₀, hj₀'⟩ : ∃ j₀ : o.ToType,
      transfiniteIterate (largerSubobject hS) j₀ (Subobject.mk f) = ⊤ ∧
        ∀ k < j₀, transfiniteIterate (largerSubobject hS) k (Subobject.mk f) ≠ ⊤ :=
    let T := {k : o.ToType | transfiniteIterate (largerSubobject hS) k (Subobject.mk f) = ⊤}
    ⟨wellFounded_lt.min T ⟨j, hj⟩, wellFounded_lt.min_mem T ⟨j, hj⟩,
      fun k hk hk' ↦ wellFounded_lt.not_lt_min T hk' hk⟩
  have h := transfiniteCompositionOfShapeMapFromBot hS (Subobject.mk f) hA₀ j₀ hj₀'
  have := (Subobject.isIso_arrow_iff_eq_top _).2 hj₀
  have hw : (Subobject.isoOfEq _ _ (transfiniteIterate_bot (largerSubobject hS) _) ≪≫
      Subobject.underlyingIso f).hom ≫ f =
        Subobject.ofLE _ _
          (transfiniteIterate_mono hS (Subobject.mk f) o.ToType (bot_le (a := j₀))) ≫
          (transfiniteIterate (largerSubobject hS) j₀ (Subobject.mk f)).arrow := by
    rw [Subobject.ofLE_arrow]
    simp
  let e₀ := asIso (transfiniteIterate (largerSubobject hS) j₀ (Subobject.mk f)).arrow
  let e : Arrow.mk ((functor hS (Subobject.mk f) o.ToType).map (homOfLE bot_le : ⊥ ⟶ j₀)) ≅
      Arrow.mk f :=
    Arrow.isoMk _ e₀ hw
  exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, ⟨h.ofArrowIso e⟩⟩

/-- **Testing K-injectivity on a family of acyclic complexes.** Let `S` be a property of cochain
complexes in a Grothendieck abelian category such that every nonzero acyclic complex contains a
nonzero acyclic subcomplex satisfying `S`. If `I` is a complex of injective objects such that every
`1`-cocycle from a complex satisfying `S` to `I` is a coboundary, then `I` is K-injective. -/
theorem isKInjective_of_forall_eq_δ (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]
    (hI : ∀ N, S N → ∀ z : Cocycle N I 1, ∃ α : Cochain N I 0, δ 0 1 α = z.1) :
    IsKInjective I := by
  refine ((rlp_monomorphisms_inf_quasiIso_iff_of_isZero (0 : I ⟶ 0) (isZero_zero _)).1
    fun A X f ⟨_, (_ : QuasiIso f)⟩ ↦ ?_).2
  obtain ⟨J, _, _, _, _, ⟨h⟩⟩ := exists_transfiniteCompositionOfShape_of_quasiIso hS f
  have hp : degreewiseEpiWithInjectiveKernel (0 : I ⟶ 0) := fun n ↦
    (Abelian.epiWithInjectiveKernel_iff_of_isZero _
      ((HomologicalComplex.eval C _ n).map_isZero (isZero_zero _))).2 inferInstance
  exact transfiniteCompositionsOfShape_le_llp_rlp _ _ _ h.mem _ fun _ _ g hg ↦ by
    obtain ⟨_, hg⟩ := (ObjectProperty.mem_monoWithCokernel_iff g).1 hg
    exact hasLiftingProperty_of_forall_eq_δ g _ hp (KernelFork.IsLimit.ofId _ rfl) (hI _ hg)

end Grothendieck

end Abelian

end CochainComplex

namespace CategoryTheory.IsSeparator

open CochainComplex HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- **K-injectivity is tested on a set of small acyclic complexes.** Let `G` be a separator of a
Grothendieck abelian category `C`. There is a sequence of objects `B j` of `C` such that a complex
`I` of injective objects is K-injective if and only if every `1`-cocycle to `I` from a bounded
above acyclic complex whose terms are quotients of objects `B j` is a coboundary, that is, every
morphism from such a complex to `I[1]` is null-homotopic. -/
@[stacks 079L]
theorem exists_isKInjective_iff {G : C} (hG : IsSeparator G) :
    ∃ B : ℕ → C, ∀ (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)],
      IsKInjective I ↔ ∀ N : CochainComplex C ℤ, N.Acyclic → (∃ n : ℤ, N.IsStrictlyLE n) →
        (∀ m, ∃ (j : ℕ) (p : B j ⟶ N.X m), Epi p) →
          ∀ z : Cocycle N I 1, ∃ α : Cochain N I 0, δ 0 1 α = z.1 := by
  obtain ⟨B, hB⟩ := hG.exists_bounded_nonzero_acyclic_subcomplex
  let S : ObjectProperty (CochainComplex C ℤ) := fun N ↦
    N.Acyclic ∧ (∃ n : ℤ, N.IsStrictlyLE n) ∧ ∀ m, ∃ (j : ℕ) (p : B j ⟶ N.X m), Epi p
  have : S.IsClosedUnderIsomorphisms := ⟨fun {N N'} e ⟨hN, ⟨n, _⟩, hN'⟩ ↦
    ⟨fun i ↦ (exactAt_iff_of_quasiIsoAt e.hom i).1 (hN i),
      ⟨n, isStrictlyLE_of_iso e n⟩, fun m ↦
        have ⟨j, p, _⟩ := hN' m
        ⟨j, p ≫ e.hom.f m, epi_comp _ _⟩⟩⟩
  refine ⟨B, fun I _ ↦ ⟨fun _ N hN _ _ z ↦ IsKInjective.eq_δ_of_cocycle z hN 0 (by simp),
    fun h ↦ isKInjective_of_forall_eq_δ (S := S) (fun M hM hM' ↦ ?_) I
      fun N hN ↦ h N hN.1 hN.2.1 hN.2.2⟩⟩
  obtain ⟨N, i, _, n, hN, hN', _, hN''⟩ := hB M hM hM'
  exact ⟨N, i, inferInstance, hN, hN',
    (⟨hN', ⟨n, inferInstance⟩, hN''⟩ : N.Acyclic ∧ (∃ n : ℤ, N.IsStrictlyLE n) ∧ _)⟩

end CategoryTheory.IsSeparator
