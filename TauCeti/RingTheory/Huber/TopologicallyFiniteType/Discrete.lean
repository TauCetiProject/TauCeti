/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import TauCeti.RingTheory.Huber.LocalizationTopology.BaseChange
public import TauCeti.RingTheory.Huber.NoetherianType.HuberStandard
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.PlusWeak

import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.FiniteType
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.Topology.UniformSpace.DiscreteUniformity

/-!
# Topological finite type over a discrete ring

Over a ring `A` carrying the discrete topology, every family of sets is a weight family, every
weighted restricted power-series ring `A⟨X₁, …, Xₖ⟩_T` is the polynomial ring `A[X₁, …, Xₖ]` with
the discrete topology (`TauCeti.Huber.weightedPolynomialEquivOfDiscrete`), and its separated
completion is isomorphic to `A[X₁, …, Xₖ]` as well
(`TauCeti.Huber.weightedPolynomialCompletionEquivOfDiscrete`).

This collapses topological finite type over a discrete base to ordinary algebraic finite generation:

* **Ring level:** for `φ : A →+* B` with `A` discrete, `IsTopologicallyFiniteType φ` holds if and
  only if `B` is discrete and `φ.FiniteType`
  (`isTopologicallyFiniteType_iff_discreteTopology_and_finiteType`).
  When `B` is discrete, both `IsTopologicallyFiniteType φ` and `IsStrictlyTopologicallyFiniteType φ`
  coincide with `φ.FiniteType`.
* **Pair level:** for a morphism of Huber pairs `f : (A, A⁺) → (B, B⁺)` with `A` discrete,
  `f.IsTopologicallyFiniteType` coincides with `f.IsPlusWeaklyFiniteType`
  (`Pair.Hom.isTopologicallyFiniteType_iff_isPlusWeaklyFiniteType_of_discreteTopology`). Indeed, in
  the discrete topology empty weight sets `Tᵢ = ∅` are admissible, so algebra generators of `B` over
  `A` may be adjoined with empty weights — contributing nothing to the source plus ring — while a
  finite plus-generating set `E ⊆ B⁺` is adjoined with trivial weights `{1}`.
* **Trivial plus rings (`Pair.discrete`):** when `A⁺ = A` and `B⁺ = B`, a finite generating set of
  `B` as an `A`-algebra already generates `B⁺` over `f(A⁺)`, so `f.IsTopologicallyFiniteType` holds
  if and only if `B` is discrete and `f.toRingHom.FiniteType`
  (`Pair.Hom.isTopologicallyFiniteType_iff_discreteTopology_and_finiteType_of_plus_eq_top`,
  `Pair.Hom.isTopologicallyFiniteType_iff_finiteType_discrete`).

## Main definitions

* `TauCeti.Huber.weightedPolynomialCompletionEquivOfDiscrete`: the ring isomorphism
  `MvPolynomial (Fin k) A ≃+* Completion (weightedRestrictedSubring T hT)` over a discrete ring `A`.
* `TauCeti.Huber.Pair.Hom.ofDiscrete`: a ring homomorphism between discrete rings packaged as a
  morphism `Pair.discrete A → Pair.discrete B`.

## Main results

* `TauCeti.Huber.isWeightFamily_of_discreteTopology`: over a discrete ring every family of sets is a
  weight family.
* `TauCeti.Huber.isTopologicallyFiniteType_iff_discreteTopology_and_finiteType`,
  `TauCeti.Huber.isTopologicallyFiniteType_iff_finiteType`,
  `TauCeti.Huber.isStrictlyTopologicallyFiniteType_iff_finiteType`: ring-level characterization of
  topological finite type over a discrete base.
* `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_isPlusWeaklyFiniteType_of_discreteTopology`:
  over a discrete base, topological finite type and +weak finite type of morphisms of Huber pairs
  coincide.
* `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top` and
  `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_finiteType_discrete`: when both plus rings
  are `⊤`, topological finite type over a discrete base reduces to `RingHom.FiniteType`.
* `TauCeti.Huber.IsHuberStandard.discreteTopology_or_isNoetherianRing_of_isTopologicallyFiniteType`,
  `TauCeti.Huber.PairOfDefinition.finitePresentation_completionLocMap_of_discreteTopology`:
  standing-class dichotomy and preservation of conditional discrete finite presentation under
  completed rational localization.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48,
  Proposition and Definition 6.29, Definition 8.42, and Remark 8.43.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Definition 1.2.1.
-/

public section

open UniformSpace

namespace TauCeti.Huber

section WeightFamily

variable {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- **Over a discrete ring every family of sets is a weight family**, including families containing
empty weight sets: every additive subgroup of `A` contains `0` and is therefore open. -/
theorem isWeightFamily_of_discreteTopology {k : ℕ} (T : Fin k → Set A) : IsWeightFamily T :=
  isWeightFamily_iff.mpr fun _ _ _ _ ↦ (isOpen_discrete _).mem_nhds (zero_mem _)

end WeightFamily

section PolynomialEquiv

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [DiscreteTopology A]
  {k : ℕ}

/-- **Over a discrete ring, the completed weighted restricted power-series ring `Â⟨X₁, …, Xₖ⟩_T` is
the polynomial ring `A[X₁, …, Xₖ]`.** Both `A⟨X⟩_T` and its uniformity are discrete, so the
polynomial comparison `weightedPolynomialEquivOfDiscrete` composes with the completion equivalence
`Completion.completeRingEquivSelf`. -/
noncomputable def weightedPolynomialCompletionEquivOfDiscrete
    (T : Fin k → Set A) (hT : IsWeightFamily T) :
    MvPolynomial (Fin k) A ≃+* Completion (weightedRestrictedSubring T hT) :=
  have : DiscreteUniformity (weightedRestrictedSubring T hT) :=
    IsRightUniformAddGroup.discreteUniformity
  (weightedPolynomialEquivOfDiscrete T hT).trans
    (Completion.completeRingEquivSelf (weightedRestrictedSubring T hT)).symm

@[simp]
theorem weightedPolynomialCompletionEquivOfDiscrete_apply
    {T : Fin k → Set A} {hT : IsWeightFamily T} (p : MvPolynomial (Fin k) A) :
    weightedPolynomialCompletionEquivOfDiscrete T hT p =
      (weightedPolynomialHom T hT p : Completion (weightedRestrictedSubring T hT)) := by
  have : DiscreteUniformity (weightedRestrictedSubring T hT) :=
    IsRightUniformAddGroup.discreteUniformity
  simp [weightedPolynomialCompletionEquivOfDiscrete]

theorem weightedPolynomialCompletionEquivOfDiscrete_C
    {T : Fin k → Set A} {hT : IsWeightFamily T} (a : A) :
    weightedPolynomialCompletionEquivOfDiscrete T hT (MvPolynomial.C a) =
      algebraMap A (Completion (weightedRestrictedSubring T hT)) a := by
  rw [weightedPolynomialCompletionEquivOfDiscrete_apply, weightedPolynomialHom_C,
    algebraMap_completion_weightedRestrictedSubring_apply]

theorem weightedPolynomialCompletionEquivOfDiscrete_X
    {T : Fin k → Set A} {hT : IsWeightFamily T} (i : Fin k) :
    weightedPolynomialCompletionEquivOfDiscrete T hT (MvPolynomial.X i) =
      (weightedX T hT i : Completion (weightedRestrictedSubring T hT)) := by
  rw [weightedPolynomialCompletionEquivOfDiscrete_apply, weightedPolynomialHom_X]

@[simp]
theorem weightedPolynomialCompletionEquivOfDiscrete_symm_coe
    {T : Fin k → Set A} {hT : IsWeightFamily T} (p : MvPolynomial (Fin k) A) :
    (weightedPolynomialCompletionEquivOfDiscrete T hT).symm
        (weightedPolynomialHom T hT p : Completion (weightedRestrictedSubring T hT)) = p := by
  rw [← weightedPolynomialCompletionEquivOfDiscrete_apply, RingEquiv.symm_apply_apply]

end PolynomialEquiv

section Ring

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [DiscreteTopology A]
  {B : Type*} [CommRing B] [TopologicalSpace B] {φ : A →+* B}

/-- **A homomorphism topologically of finite type out of a discrete ring is algebraically of finite
type**: its presenting algebra `Â⟨X₁, …, Xₖ⟩_T` is isomorphic to `A[X₁, …, Xₖ]`. -/
theorem IsTopologicallyFiniteType.finiteType (hφ : IsTopologicallyFiniteType φ) :
    φ.FiniteType := by
  obtain ⟨k, T, _, hT, π, hπ, rfl⟩ := isTopologicallyFiniteType_iff.mp hφ
  let e := weightedPolynomialCompletionEquivOfDiscrete T hT
  have hcomp : (π.comp e.toRingHom).comp (algebraMap A (MvPolynomial (Fin k) A)) =
      π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) := by
    ext a
    simp [e, MvPolynomial.algebraMap_eq]
  rw [← hcomp]
  exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp_surjective
    (hπ.surjective.comp e.surjective)

/-- **Between discrete rings, every ring homomorphism of finite type is strictly topologically of
finite type**: a polynomial surjection `A[X₁, …, Xₖ] ↠ B` transports across
`A[X₁, …, Xₖ] ≃+* A⟨X₁, …, Xₖ⟩`, and any surjection between discrete spaces is an open quotient
map. -/
theorem IsStrictlyTopologicallyFiniteType.of_finiteType [DiscreteTopology B] (hφ : φ.FiniteType) :
    IsStrictlyTopologicallyFiniteType φ := by
  let _ : Algebra A B := φ.toAlgebra
  have hft : Algebra.FiniteType A B := hφ
  obtain ⟨k, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let e := weightedPolynomialCompletionEquivOfDiscrete
    (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  have : DiscreteUniformity (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
    IsRightUniformAddGroup.discreteUniformity
  refine isStrictlyTopologicallyFiniteType_iff.mpr
    ⟨k, ψ.toRingHom.comp e.symm.toRingHom,
      ⟨hψ.comp e.symm.surjective, continuous_of_discreteTopology, fun _ _ ↦ isOpen_discrete _⟩,
      RingHom.ext fun a ↦ ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply, ← weightedPolynomialCompletionEquivOfDiscrete_C]
  change ψ (e.symm (e (MvPolynomial.C a))) = φ a
  rw [RingEquiv.symm_apply_apply, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rfl

/-- **Between discrete rings, every ring homomorphism of finite type is topologically of finite
type.** -/
theorem IsTopologicallyFiniteType.of_finiteType [DiscreteTopology B] (hφ : φ.FiniteType) :
    IsTopologicallyFiniteType φ :=
  (IsStrictlyTopologicallyFiniteType.of_finiteType hφ).isTopologicallyFiniteType

/-- **Over a discrete base, `IsTopologicallyFiniteType φ` holds if and only if `B` is discrete and
`φ` is algebraically of finite type.** -/
theorem isTopologicallyFiniteType_iff_discreteTopology_and_finiteType :
    IsTopologicallyFiniteType φ ↔ DiscreteTopology B ∧ φ.FiniteType :=
  ⟨fun h ↦ ⟨h.discreteTopology, h.finiteType⟩, fun ⟨_, h⟩ ↦ .of_finiteType h⟩

/-- **Between discrete rings, `IsTopologicallyFiniteType` and `RingHom.FiniteType` coincide.** -/
theorem isTopologicallyFiniteType_iff_finiteType [DiscreteTopology B] :
    IsTopologicallyFiniteType φ ↔ φ.FiniteType :=
  ⟨IsTopologicallyFiniteType.finiteType, IsTopologicallyFiniteType.of_finiteType⟩

/-- **Between discrete rings, `IsStrictlyTopologicallyFiniteType` and `RingHom.FiniteType`
coincide.** -/
theorem isStrictlyTopologicallyFiniteType_iff_finiteType [DiscreteTopology B] :
    IsStrictlyTopologicallyFiniteType φ ↔ φ.FiniteType :=
  ⟨fun h ↦ h.isTopologicallyFiniteType.finiteType, IsStrictlyTopologicallyFiniteType.of_finiteType⟩

end Ring

namespace Pair.Hom

section PlusWeak

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {U : Pair B}

/-- **Over a discrete base, topological finite type and +weak finite type of morphisms of Huber
pairs coincide.** Algebra generators of `B` over `A` may be adjoined with empty weight sets `∅`
(admissible because `A` is discrete), contributing no weighted variables to the plus ring, while a
finite set `E` generating `B⁺` over `f(A⁺)` is adjoined with trivial weights `{1}`. -/
theorem isTopologicallyFiniteType_iff_isPlusWeaklyFiniteType_of_discreteTopology {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔ f.IsPlusWeaklyFiniteType := by
  refine ⟨IsTopologicallyFiniteType.isPlusWeaklyFiniteType, fun hf ↦ ?_⟩
  classical
  obtain ⟨hft, E, hE⟩ := isPlusWeaklyFiniteType_iff.mp hf
  have : DiscreteTopology B := hft.discreteTopology
  let _ : Algebra A B := f.toRingHom.toAlgebra
  have hf_alg : Algebra.FiniteType A B := hft.finiteType
  obtain ⟨k, ψ₀, hψ₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf_alg
  let eE := E.equivFin.symm
  let m := E.card
  let T : Fin (k + m) → Set A :=
    Fin.append (fun _ : Fin k ↦ (∅ : Set A)) (fun _ : Fin m ↦ ({1} : Set A))
  have hTfin : ∀ i, (T i).Finite :=
    Fin.addCases (fun _ ↦ by simp [T]) (fun _ ↦ by simp [T])
  have hT : IsWeightFamily T := isWeightFamily_of_discreteTopology T
  let ev : MvPolynomial (Fin (k + m)) A →ₐ[A] B :=
    MvPolynomial.aeval (Fin.append (fun i ↦ ψ₀ (MvPolynomial.X i)) (fun j ↦ (eE j : B)))
  have hev_surj : Function.Surjective ev := fun b ↦ by
    obtain ⟨p, rfl⟩ := hψ₀ b
    refine ⟨MvPolynomial.rename (Fin.castAdd m) p, ?_⟩
    have hcomp : ev.comp (MvPolynomial.rename (Fin.castAdd m)) = ψ₀ := by
      ext i
      simp [ev]
    exact AlgHom.congr_fun hcomp p
  let e := weightedPolynomialCompletionEquivOfDiscrete T hT
  let π : Completion (weightedRestrictedSubring T hT) →+* B := ev.toRingHom.comp e.symm.toRingHom
  have : DiscreteUniformity (weightedRestrictedSubring T hT) :=
    IsRightUniformAddGroup.discreteUniformity
  have hπ : IsOpenQuotientMap π :=
    ⟨hev_surj.comp e.symm.surjective, continuous_of_discreteTopology, fun _ _ ↦ isOpen_discrete _⟩
  have hπC (a : A) :
      π (algebraMap A (Completion (weightedRestrictedSubring T hT)) a) = f.toRingHom a := by
    rw [← weightedPolynomialCompletionEquivOfDiscrete_C (T := T) (hT := hT)]
    change ev (e.symm (e (MvPolynomial.C a))) = f.toRingHom a
    rw [RingEquiv.symm_apply_apply, MvPolynomial.aeval_C]
    rfl
  have hπX_right (j : Fin m) :
      π (weightedX T hT (Fin.natAdd k j) : Completion (weightedRestrictedSubring T hT)) =
        (eE j : B) := by
    rw [← weightedPolynomialCompletionEquivOfDiscrete_X (T := T) (hT := hT)]
    change ev (e.symm (e (MvPolynomial.X (Fin.natAdd k j)))) = (eE j : B)
    rw [RingEquiv.symm_apply_apply]
    simp [ev]
  have hEU : (E : Set B) ⊆ U.plus := hE ▸ fun _ hb ↦ subset_plusClosure _ (Or.inr hb)
  refine isTopologicallyFiniteType_iff_exists_isOpenQuotientMap.mpr
    ⟨k + m, T, hTfin, hT, π, hπ, RingHom.ext hπC, le_antisymm ?_ ?_⟩
  · rw [hE]
    refine plusClosure_le (isOpen_discrete _) (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      refine (integralClosure ((S.weighted hT).completion.plus.map π) B).algebraMap_mem
        ⟨f.toRingHom a, Subring.mem_map.mpr
          ⟨(weightedC T hT a : Completion (weightedRestrictedSubring T hT)),
            S.weightedC_mem_weighted_completion_plus hT ha, ?_⟩⟩
      rw [← algebraMap_completion_weightedRestrictedSubring_apply, hπC]
    · intro b hb
      let j : Fin m := eE.symm ⟨b, hb⟩
      have hj : (eE j : B) = b := congrArg Subtype.val (eE.apply_symm_apply ⟨b, hb⟩)
      have ht : (1 : A) ∈ T (Fin.natAdd k j) := by simp [T]
      refine (integralClosure ((S.weighted hT).completion.plus.map π) B).algebraMap_mem
        ⟨b, Subring.mem_map.mpr
          ⟨((weightedC T hT 1 * weightedX T hT (Fin.natAdd k j) :
              weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT)),
            S.weightedC_mul_weightedX_mem_weighted_completion_plus hT ht, ?_⟩⟩
      rw [Completion.coe_mul, map_mul, ← algebraMap_completion_weightedRestrictedSubring_apply,
        hπC, map_one, one_mul, hπX_right, hj]
  · have := U.isRingOfIntegralElements.isIntegrallyClosedIn
    rw [Subring.integralClosure_subring_le_iff]
    refine Subring.map_le_iff_le_comap.mpr <|
      S.weighted_completion_plus_le_comap hT U hπ.continuous
        (fun a ha ↦ ?_) (Fin.addCases (fun i t ht ↦ ?_) (fun j t ht ↦ ?_))
    · rw [← algebraMap_completion_weightedRestrictedSubring_apply, hπC]
      exact f.map_mem_plus a ha
    · simp only [T, Fin.append_left, Set.mem_empty_iff_false] at ht
    · simp only [T, Fin.append_right, Set.mem_singleton_iff] at ht
      subst ht
      rw [Completion.coe_mul, map_mul,
        ← algebraMap_completion_weightedRestrictedSubring_apply, hπC, map_one, one_mul,
        hπX_right]
      exact hEU (eE j).2

/-- **When `S.plus = ⊤` and `U.plus = ⊤` over a discrete base `A`, a morphism of Huber pairs `f` is
topologically of finite type if and only if `B` is discrete and `f.toRingHom.FiniteType`.** Any
finite algebra-generating set of `B` over `A` then generates `B` as a subring over `f(A)`. -/
theorem isTopologicallyFiniteType_iff_discreteTopology_and_finiteType_of_plus_eq_top
    (hS : S.plus = ⊤) (hU : U.plus = ⊤) {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔ DiscreteTopology B ∧ f.toRingHom.FiniteType := by
  refine ⟨fun hf ↦ ⟨hf.isTopologicallyFiniteType_toRingHom.discreteTopology,
    hf.isTopologicallyFiniteType_toRingHom.finiteType⟩, fun ⟨hdisc, hft⟩ ↦ ?_⟩
  classical
  rw [isTopologicallyFiniteType_iff_isPlusWeaklyFiniteType_of_discreteTopology]
  let _ : Algebra A B := f.toRingHom.toAlgebra
  obtain ⟨E, hE⟩ := hft.out
  refine isPlusWeaklyFiniteType_of_plus_le (.of_finiteType hft) E
    (fun _ _ ↦ hU ▸ Subring.mem_top _) ?_
  let P : Subalgebra A B :=
    { (plusClosure (f.toRingHom '' S.plus ∪ E)).toSubsemiring with
      algebraMap_mem' := fun a ↦
        subset_plusClosure _ (Or.inl ⟨a, hS ▸ Subring.mem_top a, rfl⟩) }
  have htop : (⊤ : Subalgebra A B) ≤ P :=
    hE ▸ Algebra.adjoin_le fun _ hx ↦ subset_plusClosure _ (Or.inr hx)
  exact fun b _ ↦ htop Algebra.mem_top

/-- **Between discrete Huber pairs with trivial plus rings (`S.plus = ⊤`, `U.plus = ⊤`),
`Pair.Hom.IsTopologicallyFiniteType` coincides with `RingHom.FiniteType`.** -/
theorem isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top [DiscreteTopology B]
    (hS : S.plus = ⊤) (hU : U.plus = ⊤) {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔ f.toRingHom.FiniteType := by
  rw [isTopologicallyFiniteType_iff_discreteTopology_and_finiteType_of_plus_eq_top hS hU]
  exact and_iff_right inferInstance

end PlusWeak

section DiscretePair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]

/-- Package a ring homomorphism between discrete rings as a morphism `Pair.discrete A →
Pair.discrete B` of discrete Huber pairs. -/
def ofDiscrete (φ : A →+* B) : Hom (Pair.discrete A) (Pair.discrete B) where
  toRingHom := φ
  continuous_toRingHom := continuous_of_discreteTopology
  map_mem_plus _ _ := by simp

@[simp]
theorem toRingHom_ofDiscrete (φ : A →+* B) : (ofDiscrete φ).toRingHom = φ := by
  rfl

/-- **For morphisms between discrete Huber pairs `(A, A) → (B, B)`, topological finite type
coincides with `RingHom.FiniteType`.** -/
theorem isTopologicallyFiniteType_iff_finiteType_discrete
    {f : Hom (Pair.discrete A) (Pair.discrete B)} :
    f.IsTopologicallyFiniteType ↔ f.toRingHom.FiniteType :=
  isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top Pair.discrete_plus Pair.discrete_plus

end DiscretePair

end Pair.Hom

section HuberStandard

/-- **Dichotomy for homomorphisms topologically of finite type out of Huber's standing class**: if
`A` belongs to Huber's standing class (`IsHuberStandard A`) and `γ : A →+* C` is topologically of
finite type, then either `A` is discrete or `C` is a noetherian ring. -/
theorem IsHuberStandard.discreteTopology_or_isNoetherianRing_of_isTopologicallyFiniteType
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [hA : IsHuberStandard A] {C : Type*} [CommRing C] [TopologicalSpace C]
    {γ : A →+* C} (hγ : IsTopologicallyFiniteType γ) :
    DiscreteTopology A ∨ IsNoetherianRing C := by
  refine hA.elim (fun Q _ _ ↦ Or.inr ?_) (fun _ _ ↦ Or.inr hγ.isNoetherianRing) Or.inl
  obtain ⟨Q', _, _⟩ := hγ.exists_pairOfDefinition_isNoetherianRing_and_finiteType Q
  exact Algebra.FiniteType.isNoetherianRing Q'.ringOfDefinition C

/-- **Base change along a rational localization preserves conditional discrete finite presentation
over Huber's standing class**: if `A` belongs to Huber's standing class, `f : A →+* B` is
topologically of finite type with `DiscreteTopology A → f.FinitePresentation`, and `A⟨T/s⟩` is
discrete, then `completionLocMap : A⟨T/s⟩ →+* B⟨T'/f(s)⟩` is algebraically of finite presentation
(`RingHom.FinitePresentation`). -/
theorem PairOfDefinition.finitePresentation_completionLocMap_of_discreteTopology
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [IsHuberStandard A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hT_open : IsOpen (Ideal.span (insert s (T : Set A)) : Set A))
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : P.HasDenominatorPower (T : Set A) s S)
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    (P' : PairOfDefinition B) {f : A →+* B} (hf : IsTopologicallyFiniteType f)
    (hfp : DiscreteTopology A → f.FinitePresentation)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : P'.HasDenominatorPower (T' : Set B) s' S')
    (hs : f s = s') (hT : ∀ t ∈ T, f t ∈ T')
    (hspan : IsOpen (Ideal.span (insert s' (T' : Set B)) : Set B))
    {hf_cont : ContinuousAt f 0} :
    letI := P.locUniformSpace (T : Set A) s S hden
    letI := P.isUniformAddGroup_locUniformSpace (T : Set A) s S hden
    letI := P.isTopologicalRing_locUniformSpace (T : Set A) s S hden
    letI := P'.locUniformSpace (T' : Set B) s' S' hden'
    letI := P'.isUniformAddGroup_locUniformSpace (T' : Set B) s' S' hden'
    letI := P'.isTopologicalRing_locUniformSpace (T' : Set B) s' S' hden'
    DiscreteTopology (Completion S) →
      (P.completionLocMap T s S hden P' f hf_cont T' s' S' hden' hs hT).FinitePresentation := by
  let _ := P.locUniformSpace (T : Set A) s S hden
  have _ := P.isUniformAddGroup_locUniformSpace (T : Set A) s S hden
  have _ := P.isTopologicalRing_locUniformSpace (T : Set A) s S hden
  have _ := P.isHuberRing_completion_locTopology (T : Set A) s S hden
  let _ := P'.locUniformSpace (T' : Set B) s' S' hden'
  have _ := P'.isUniformAddGroup_locUniformSpace (T' : Set B) s' S' hden'
  have _ := P'.isTopologicalRing_locUniformSpace (T' : Set B) s' S' hden'
  have _ := P'.isHuberRing_completion_locTopology (T' : Set B) s' S' hden'
  intro hDiscS
  rcases IsHuberStandard.discreteTopology_or_isNoetherianRing_of_isTopologicallyFiniteType
      (P.isTopologicallyFiniteType_toCompletionLoc T s S hden hT_open) with hDiscA | hNoethS
  · have : DiscreteTopology B := hf.discreteTopology
    have hlocA := P.finitePresentation_toCompletionLoc_of_discreteTopology (T : Set A) s S hden
    have hlocB := P'.finitePresentation_toCompletionLoc_of_discreteTopology (T' : Set B) s' S' hden'
    refine RingHom.FinitePresentation.of_comp_finiteType
      (P.toCompletionLoc (T : Set A) s S hden) ?_
      (RingHom.FiniteType.of_finitePresentation hlocA)
    rw [P.completionLocMap_comp_toCompletionLoc T s S hden P' f hf_cont T' s' S' hden' hs hT]
    exact hlocB.comp (hfp hDiscA)
  · have hft := P.isTopologicallyFiniteType_completionLocMap T s S hden P' hf T' s' S' hden'
      hs hT hspan
    have : DiscreteTopology (Completion S') := hft.discreteTopology
    exact RingHom.FinitePresentation.of_finiteType.mp hft.finiteType

end HuberStandard

end TauCeti.Huber
