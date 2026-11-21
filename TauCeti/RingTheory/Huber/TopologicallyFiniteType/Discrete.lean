/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.PlusWeak

import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.Topology.Maps.OpenQuotient
import TauCeti.Topology.UniformSpace.DiscreteUniformity

/-!
# Topological finite type over a discrete ring

Over a discrete nonarchimedean ring `A`, `Â⟨X₁, …, Xₖ⟩_T ≃+* A[X₁, …, Xₖ]`, so topological
finiteness conditions collapse to algebraic finite type together with target discreteness:

* On underlying rings, `IsTopologicallyFiniteType φ ↔ DiscreteTopology B ∧ φ.FiniteType`, and
  finite-type homomorphisms between discrete rings are strictly topologically of finite type.
* On Huber pairs over a discrete base, `f.IsTopologicallyFiniteType ↔ f.IsPlusWeaklyFiniteType`,
  and when `S.plus = ⊤` and `U.plus = ⊤` (e.g. `Pair.discrete`), this reduces to
  `DiscreteTopology B ∧ f.toRingHom.FiniteType`.

## Main results

* `TauCeti.Huber.IsTopologicallyFiniteType.discreteTopology`,
  `TauCeti.Huber.IsTopologicallyFiniteType.finiteType`,
  `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.of_finiteType`,
  `TauCeti.Huber.IsTopologicallyFiniteType.of_finiteType`,
  `TauCeti.Huber.isTopologicallyFiniteType_iff_discreteTopology_and_finiteType`: ring-level
  equivalences.
* `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_isPlusWeaklyFiniteType_of_discreteTopology`,
  `Pair.Hom.isTopologicallyFiniteType_iff_discreteTopology_and_finiteType_of_plus_eq_top`,
  `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top`,
  `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_finiteType_discrete`: pair-level
  equivalences.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48,
  Proposition and Definition 6.29, Example 6.32(1), and Definition 8.42.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces* (1996), §1.2.
-/

public section

open UniformSpace

namespace TauCeti.Huber

/-- **Discrete topology ascends along homomorphisms topologically of finite type**: over a discrete
ring `A`, every weighted restricted power-series ring `A⟨X⟩_T` and its completion are discrete, so
any open quotient `B` is discrete as well. -/
theorem IsTopologicallyFiniteType.discreteTopology {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] {B : Type*} [CommRing B] [TopologicalSpace B] {φ : A →+* B}
    [DiscreteTopology A] (hφ : IsTopologicallyFiniteType φ) : DiscreteTopology B := by
  obtain ⟨k, T, _, hT, π, hπ, -⟩ := isTopologicallyFiniteType_iff.mp hφ
  have : DiscreteUniformity (weightedRestrictedSubring T hT) :=
    IsRightUniformAddGroup.discreteUniformity
  exact hπ.discreteTopology

section Helpers

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [DiscreteTopology A]
  {B : Type*} [CommRing B]

/-- Transport an `A`-algebra homomorphism `ψ : A[X₁, …, Xₖ] →ₐ[A] B` (with `Algebra A B :=
φ.toAlgebra`) along `(weightedPolynomialCompletionEquivOfDiscrete T hT).symm` to a ring
homomorphism `Â⟨X₁, …, Xₖ⟩_T →+* B`. -/
private noncomputable def weightedCompletionQuotientHom {k : ℕ} (T : Fin k → Set A)
    (hT : IsWeightFamily T) {φ : A →+* B}
    (ψ : letI : Algebra A B := φ.toAlgebra; MvPolynomial (Fin k) A →ₐ[A] B) :
    Completion (weightedRestrictedSubring T hT) →+* B :=
  letI : Algebra A B := φ.toAlgebra
  ψ.toRingHom.comp (weightedPolynomialCompletionEquivOfDiscrete T hT).symm.toRingHom

/-- Between discrete rings, transporting a surjective `A`-algebra homomorphism
`A[X₁, …, Xₖ] →ₐ[A] B` across `weightedPolynomialCompletionEquivOfDiscrete.symm` yields an open
quotient map. -/
private theorem isOpenQuotientMap_weightedCompletionQuotientHom [TopologicalSpace B]
    [DiscreteTopology B] {k : ℕ} (T : Fin k → Set A) (hT : IsWeightFamily T) {φ : A →+* B}
    (ψ : letI : Algebra A B := φ.toAlgebra; MvPolynomial (Fin k) A →ₐ[A] B)
    (hψ : Function.Surjective ψ) :
    IsOpenQuotientMap (weightedCompletionQuotientHom T hT ψ) := by
  let _ : Algebra A B := φ.toAlgebra
  have : DiscreteUniformity (weightedRestrictedSubring T hT) :=
    IsRightUniformAddGroup.discreteUniformity
  exact ⟨hψ.comp (weightedPolynomialCompletionEquivOfDiscrete T hT).symm.surjective,
    continuous_of_discreteTopology, fun _ _ ↦ isOpen_discrete _⟩

/-- The transported quotient homomorphism agrees with `φ` on the structure map `A → Â⟨X⟩_T`. -/
private theorem weightedCompletionQuotientHom_algebraMap {k : ℕ} (T : Fin k → Set A)
    (hT : IsWeightFamily T) {φ : A →+* B}
    (ψ : letI : Algebra A B := φ.toAlgebra; MvPolynomial (Fin k) A →ₐ[A] B) (a : A) :
    weightedCompletionQuotientHom T hT ψ
      (algebraMap A (Completion (weightedRestrictedSubring T hT)) a) = φ a := by
  let _ : Algebra A B := φ.toAlgebra
  simp only [weightedCompletionQuotientHom,
    ← weightedPolynomialCompletionEquivOfDiscrete_C (T := T) (hT := hT),
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
    RingHom.algebraMap_toAlgebra]

/-- The transported quotient homomorphism sends the completed weighted variable `weightedX T hT i`
to `ψ (X i)`. -/
private theorem weightedCompletionQuotientHom_weightedX {k : ℕ} (T : Fin k → Set A)
    (hT : IsWeightFamily T) {φ : A →+* B}
    (ψ : letI : Algebra A B := φ.toAlgebra; MvPolynomial (Fin k) A →ₐ[A] B) (i : Fin k) :
    weightedCompletionQuotientHom T hT ψ
      (weightedX T hT i : Completion (weightedRestrictedSubring T hT)) =
      ψ (MvPolynomial.X i) := by
  let _ : Algebra A B := φ.toAlgebra
  simp only [weightedCompletionQuotientHom,
    ← weightedPolynomialCompletionEquivOfDiscrete_X (T := T) (hT := hT),
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]

/-- The transported quotient homomorphism sends `(weightedC T hT 1 * weightedX T hT i : A⟨X⟩_T)`
in the completion to `ψ (X i)`. -/
private theorem weightedCompletionQuotientHom_weightedC_one_mul_weightedX {k : ℕ}
    (T : Fin k → Set A) (hT : IsWeightFamily T) {φ : A →+* B}
    (ψ : letI : Algebra A B := φ.toAlgebra; MvPolynomial (Fin k) A →ₐ[A] B) (i : Fin k) :
    weightedCompletionQuotientHom T hT ψ
      ((weightedC T hT 1 * weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) =
      ψ (MvPolynomial.X i) := by
  let _ : Algebra A B := φ.toAlgebra
  rw [Completion.coe_mul, map_mul, ← algebraMap_completion_weightedRestrictedSubring_apply,
    weightedCompletionQuotientHom_algebraMap, map_one, one_mul,
    weightedCompletionQuotientHom_weightedX]

end Helpers

section Ring

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [DiscreteTopology A]
  {B : Type*} [CommRing B] [TopologicalSpace B] {φ : A →+* B}

/-- Over a discrete nonarchimedean ring `A`, every ring homomorphism `φ : A →+* B` topologically of
finite type is algebraically of finite type (`RingHom.FiniteType`), because `B` is a quotient of
`Â⟨X₁, …, Xₖ⟩_T ≃+* A[X₁, …, Xₖ]`. -/
theorem IsTopologicallyFiniteType.finiteType (hφ : IsTopologicallyFiniteType φ) :
    φ.FiniteType := by
  obtain ⟨k, T, _, hT, π, hπ, rfl⟩ := isTopologicallyFiniteType_iff.mp hφ
  let e := weightedPolynomialCompletionEquivOfDiscrete T hT
  have hcomp : (π.comp e.toRingHom).comp (algebraMap A (MvPolynomial (Fin k) A)) =
      π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) := by
    ext a; simp [e, MvPolynomial.algebraMap_eq]
  rw [← hcomp]
  exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp_surjective
    (hπ.surjective.comp e.surjective)

/-- Between discrete rings (`A` nonarchimedean), an algebraically finite-type homomorphism
`φ : A →+* B` is strictly topologically of finite type: any polynomial presentation
`A[X₁, …, Xₖ] ↠ B` transports along `A[X₁, …, Xₖ] ≃+* Â⟨X₁, …, Xₖ⟩` to an open quotient map. -/
theorem IsStrictlyTopologicallyFiniteType.of_finiteType [DiscreteTopology B] (hφ : φ.FiniteType) :
    IsStrictlyTopologicallyFiniteType φ := by
  let _ : Algebra A B := φ.toAlgebra
  obtain ⟨k, ψ, hψ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (hφ : Algebra.FiniteType A B)
  exact isStrictlyTopologicallyFiniteType_iff.mpr
    ⟨k, weightedCompletionQuotientHom _ isWeightFamily_one_weight ψ,
      isOpenQuotientMap_weightedCompletionQuotientHom _ isWeightFamily_one_weight ψ hψ,
      RingHom.ext (weightedCompletionQuotientHom_algebraMap _ isWeightFamily_one_weight ψ)⟩

/-- Between discrete rings (`A` nonarchimedean), an algebraically finite-type homomorphism
`φ : A →+* B` is topologically of finite type. -/
theorem IsTopologicallyFiniteType.of_finiteType [DiscreteTopology B] (hφ : φ.FiniteType) :
    IsTopologicallyFiniteType φ :=
  (IsStrictlyTopologicallyFiniteType.of_finiteType hφ).isTopologicallyFiniteType

/-- **Characterization of topological finite type over a discrete base**: for a discrete
nonarchimedean ring `A` and an arbitrary topological ring `B`, a ring homomorphism `φ : A →+* B`
is topologically of finite type if and only if `B` is discrete and `φ` is algebraically of finite
type. -/
theorem isTopologicallyFiniteType_iff_discreteTopology_and_finiteType :
    IsTopologicallyFiniteType φ ↔ DiscreteTopology B ∧ φ.FiniteType :=
  ⟨fun h ↦ ⟨h.discreteTopology, h.finiteType⟩, fun ⟨_, h⟩ ↦ .of_finiteType h⟩

end Ring

namespace Pair.Hom

section PlusWeak

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {U : Pair B}

/-- Given a continuous ring homomorphism `π : Â⟨X⟩_T →+* B` sending constants to `f(a)` and the
designated `1 * X_{k + j}` variables to the generators `E`, the integral closure of `π(Â⟨X⟩_T⁺)`
coincides with `U.plus` when `U.plus` is the plus-closure of `f(S.plus) ∪ E`. -/
private theorem integralClosure_map_weighted_plus_eq [DiscreteTopology B]
    {k : ℕ} {E : Finset B} (eE : Fin E.card ≃ E) {f : Hom S U}
    (hE : U.plus = plusClosure (f.toRingHom '' S.plus ∪ (E : Set B)))
    {T : Fin (k + E.card) → Set A} (hT : IsWeightFamily T)
    (hT_left : ∀ i : Fin k, T (Fin.castAdd E.card i) = ∅)
    (hT_right : ∀ j : Fin E.card, T (Fin.natAdd k j) = {1})
    {π : Completion (weightedRestrictedSubring T hT) →+* B} (hπc : Continuous π)
    (hπC : ∀ a : A, π (algebraMap A _ a) = f.toRingHom a)
    (hπ_right : ∀ j : Fin E.card, π ((weightedC T hT 1 * weightedX T hT (Fin.natAdd k j) :
        weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT)) =
      (eE j : B)) :
    U.plus = (integralClosure ((S.weighted hT).completion.plus.map π) B).toSubring := by
  have hEU : (E : Set B) ⊆ U.plus := hE ▸ fun _ hb ↦ subset_plusClosure _ (Or.inr hb)
  let I := integralClosure ((S.weighted hT).completion.plus.map π) B
  refine le_antisymm ?_ ?_
  · rw [hE]
    refine plusClosure_le (isOpen_discrete _) (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      refine I.algebraMap_mem ⟨f.toRingHom a, Subring.mem_map.mpr
        ⟨(weightedC T hT a : _), S.weightedC_mem_weighted_completion_plus hT ha, ?_⟩⟩
      rw [← algebraMap_completion_weightedRestrictedSubring_apply, hπC]
    · intro b hb
      let j : Fin E.card := eE.symm ⟨b, hb⟩
      have ht : (1 : A) ∈ T (Fin.natAdd k j) := hT_right j ▸ Set.mem_singleton _
      refine I.algebraMap_mem ⟨b, Subring.mem_map.mpr
        ⟨((weightedC T hT 1 * weightedX T hT (Fin.natAdd k j) : weightedRestrictedSubring T hT) :
            Completion (weightedRestrictedSubring T hT)),
          S.weightedC_mul_weightedX_mem_weighted_completion_plus hT ht,
          (hπ_right j).trans (congrArg Subtype.val (eE.apply_symm_apply ⟨b, hb⟩))⟩⟩
  · have := U.isRingOfIntegralElements.isIntegrallyClosedIn
    rw [Subring.integralClosure_subring_le_iff]
    refine Subring.map_le_iff_le_comap.mpr <| S.weighted_completion_plus_le_comap hT U hπc
      (fun a ha ↦ ?_) (Fin.addCases (fun i _ ht ↦ ?_) (fun j _ ht ↦ ?_))
    · rw [← algebraMap_completion_weightedRestrictedSubring_apply, hπC]; exact f.map_mem_plus a ha
    · exact (Set.notMem_empty _ (hT_left i ▸ ht)).elim
    · rw [hT_right, Set.mem_singleton_iff] at ht; subst ht; rw [hπ_right]
      exact hEU (eE j).property

/-- **Over a discrete base, pair-level topological finite type coincides with `+`-weakly finite
type**: given a finite set `E ⊆ U.plus` such that `U.plus` is the plus-closure of `f(S.plus) ∪ E`,
a finite polynomial generating set for `B` over `A` can be adjoined with weight `∅` while `E` is
adjoined with weight `{1}`, yielding a weighted quotient presentation of `f`. -/
theorem isTopologicallyFiniteType_iff_isPlusWeaklyFiniteType_of_discreteTopology {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔ f.IsPlusWeaklyFiniteType := by
  refine ⟨IsTopologicallyFiniteType.isPlusWeaklyFiniteType, fun hf ↦ ?_⟩
  classical
  obtain ⟨hft, E, hE⟩ := isPlusWeaklyFiniteType_iff.mp hf
  have : DiscreteTopology B := hft.discreteTopology
  let _ : Algebra A B := f.toRingHom.toAlgebra
  obtain ⟨k, ψ₀, hψ₀⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (hft.finiteType : Algebra.FiniteType A B)
  let eE := E.equivFin.symm
  let T : Fin (k + E.card) → Set A :=
    Fin.append (fun _ : Fin k ↦ (∅ : Set A)) (fun _ : Fin E.card ↦ ({1} : Set A))
  have hTfin : ∀ i, (T i).Finite := Fin.addCases (fun _ ↦ by simp [T]) (fun _ ↦ by simp [T])
  have hT : IsWeightFamily T := isWeightFamily_of_discreteTopology T
  let ev : MvPolynomial (Fin (k + E.card)) A →ₐ[A] B :=
    MvPolynomial.aeval (Fin.append (fun i ↦ ψ₀ (MvPolynomial.X i)) (fun j ↦ (eE j : B)))
  have hev_surj : Function.Surjective ev := fun b ↦ by
    obtain ⟨p, rfl⟩ := hψ₀ b
    refine ⟨MvPolynomial.rename (Fin.castAdd E.card) p, ?_⟩
    have hcomp : ev.comp (MvPolynomial.rename (Fin.castAdd E.card)) = ψ₀ := by ext i; simp [ev]
    exact AlgHom.congr_fun hcomp p
  let π := weightedCompletionQuotientHom T hT ev
  have hπ : IsOpenQuotientMap π := isOpenQuotientMap_weightedCompletionQuotientHom T hT ev hev_surj
  have hπC (a : A) : π (algebraMap A _ a) = f.toRingHom a :=
    weightedCompletionQuotientHom_algebraMap T hT ev a
  have hπ_right (j : Fin E.card) :
      π ((weightedC T hT 1 * weightedX T hT (Fin.natAdd k j) : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = (eE j : B) := by
    rw [weightedCompletionQuotientHom_weightedC_one_mul_weightedX]; simp [ev]
  exact isTopologicallyFiniteType_iff_exists_isOpenQuotientMap.mpr
    ⟨k + E.card, T, hTfin, hT, π, hπ, RingHom.ext hπC,
      integralClosure_map_weighted_plus_eq eE hE hT (fun _ ↦ by simp [T]) (fun _ ↦ by simp [T])
        hπ.continuous hπC hπ_right⟩

/-- Over a discrete base `A`, a morphism `f : S → U` of Huber pairs whose plus rings are both the
entire ring (`S.plus = ⊤`, `U.plus = ⊤`) is topologically of finite type if and only if `B` is
discrete and `f.toRingHom` is algebraically of finite type. -/
theorem isTopologicallyFiniteType_iff_discreteTopology_and_finiteType_of_plus_eq_top
    (hS : S.plus = ⊤) (hU : U.plus = ⊤) {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔ DiscreteTopology B ∧ f.toRingHom.FiniteType := by
  refine ⟨fun hf ↦ ⟨hf.isTopologicallyFiniteType_toRingHom.discreteTopology,
    hf.isTopologicallyFiniteType_toRingHom.finiteType⟩, fun ⟨_, hft⟩ ↦ ?_⟩
  classical
  rw [isTopologicallyFiniteType_iff_isPlusWeaklyFiniteType_of_discreteTopology]
  let _ : Algebra A B := f.toRingHom.toAlgebra
  obtain ⟨E, hE⟩ := hft.out
  refine isPlusWeaklyFiniteType_of_plus_le (.of_finiteType hft) E
    (fun _ _ ↦ hU ▸ Subring.mem_top _) ?_
  let P : Subalgebra A B :=
    { (plusClosure (f.toRingHom '' S.plus ∪ E)).toSubsemiring with
      algebraMap_mem' := fun a ↦ subset_plusClosure _ (Or.inl ⟨a, hS ▸ Subring.mem_top a, rfl⟩) }
  have htop : (⊤ : Subalgebra A B) ≤ P :=
    hE ▸ Algebra.adjoin_le fun _ hx ↦ subset_plusClosure _ (Or.inr hx)
  exact fun _ _ ↦ htop Algebra.mem_top

/-- Between discrete Huber rings `A` and `B`, a morphism `f : S → U` of Huber pairs with
`S.plus = ⊤` and `U.plus = ⊤` is topologically of finite type if and only if `f.toRingHom` is
algebraically of finite type. -/
theorem isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top [DiscreteTopology B]
    (hS : S.plus = ⊤) (hU : U.plus = ⊤) {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔ f.toRingHom.FiniteType := by
  rw [isTopologicallyFiniteType_iff_discreteTopology_and_finiteType_of_plus_eq_top hS hU]
  exact and_iff_right inferInstance

/-- A morphism `f : Pair.discrete A → Pair.discrete B` between discrete Huber pairs is topologically
of finite type if and only if its underlying ring homomorphism is algebraically of finite type. -/
theorem isTopologicallyFiniteType_iff_finiteType_discrete [DiscreteTopology B]
    {f : Hom (Pair.discrete A) (Pair.discrete B)} :
    f.IsTopologicallyFiniteType ↔ f.toRingHom.FiniteType :=
  isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top Pair.discrete_plus Pair.discrete_plus

end PlusWeak

end Pair.Hom

end TauCeti.Huber
