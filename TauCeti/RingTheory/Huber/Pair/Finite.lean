/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp
import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.RingTheory.Huber.WeightedEval.Completion
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Finite morphisms of Huber pairs

A morphism `φ : (A, A⁺) → (B, B⁺)` of Huber pairs is *finite* (Huber 1996, (1.4.2)) if it is
topologically of finite type as a morphism of Huber pairs, that is, it factors through a quotient
mapping out of a completed weighted restricted power-series pair
(`Pair.Hom.IsTopologicallyFiniteType`), and the ring maps `A → B` and `A⁺ → B⁺` are integral.
Huber states this for complete pairs; completeness is not imposed here, and a consumer that needs
it assumes it alongside, as the results below on quotient mappings do for the source. Integrality
of `A⁺ → B⁺` is stated as integrality of every element of `B⁺` over the image of `A⁺`, which
implies it (`Pair.Hom.IsFinite.isIntegral_restrict`) and pins down the plus ring:
`B⁺` is the integral closure of the image of `A⁺` (`Pair.Hom.IsFinite.plus_eq`). This is the
affinoid notion from which finite morphisms of adic spaces are built. The plus-ring condition is
not implied by the others: the identity of `K` is a finite ring map, but `(K, K⁺) → (K, K°)` is not
finite when `K⁺ ⊊ K°` (`Pair.Hom.IsFinite.plus_eq_of_toRingHom_eq_id`).

Every quotient mapping out of a complete Hausdorff pair is finite, in particular the identity and
the canonical maps to quotient pairs, and finite morphisms compose over a Tate base.

Over a Tate ring, for a target that is complete and Hausdorff, the topological finite type clause
follows once the ring map is module-finite and `B⁺` is integral over the image of `A⁺`
(`Pair.Hom.isFinite_of_finite_of_isIntegral_plus`). Generators `b₁, …, bₙ` of `B` as an `A`-module
can be taken in `B⁺`, because `B⁺` is open and scaling by a power of a pseudouniformiser is
invertible. Evaluation at them gives a continuous surjection `A⟨X₁, …, Xₙ⟩ → B`, which the open
mapping theorem makes open as soon as `B` is complete and Hausdorff. It carries the plus ring of
`A⟨X⟩` into `B⁺`, which is integral over the image of `A⁺`. Consequently a finite étale morphism of
Huber pairs over a complete Hausdorff Tate ring is finite (`Pair.Hom.IsFiniteEtale.isFinite`): its
target is a finite projective module, hence complete and Hausdorff for its natural topology.

## Main definitions

* `TauCeti.Huber.Pair.Hom.IsFinite`: finite morphisms of Huber pairs.

## Main results

* `TauCeti.Huber.Pair.Hom.IsFinite.plus_eq`: the plus ring of the target is the integral closure
  of the image of the plus ring of the source.
* `TauCeti.Huber.Pair.Hom.IsFinite.isIntegral_restrict`: the plus-ring map `A⁺ → B⁺` of a finite
  morphism is integral.
* `TauCeti.Huber.Pair.Hom.IsFinite.plus_eq_of_toRingHom_eq_id`: a finite morphism whose ring map
  is the identity does not enlarge the plus ring.
* `TauCeti.Huber.Pair.Hom.IsQuotientMapping.isFinite`, `TauCeti.Huber.Pair.Hom.isFinite_id` and
  `TauCeti.Huber.Pair.Hom.isFinite_quotientHom`: quotient mappings out of a complete Hausdorff pair,
  in particular the identity and quotient maps, are finite.
* `TauCeti.Huber.Pair.Hom.IsFinite.comp`: finite morphisms compose over a Tate base.
* `TauCeti.Huber.Pair.Hom.isFinite_of_finite_of_isIntegral_plus`: over a Tate ring, a
  module-finite morphism into a complete Hausdorff pair whose target plus ring is integral over the
  image of the source plus ring is finite.
* `TauCeti.Huber.Pair.Hom.IsFiniteEtale.isFinite`: over a complete Hausdorff Tate ring, a finite
  étale morphism of Huber pairs is finite.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.4, (1.4.2), and Example 1.6.6(ii).
* B. Zavyalov, *Quotients of admissible formal schemes and adic spaces by finite groups*,
  Appendix B.2, Definition B.2.6 and Lemmas B.2.8–B.2.9.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 8.42.
-/

public section

open Filter Topology UniformSpace Uniformity

namespace TauCeti.Huber.Pair

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {U : Pair B} {V : Pair C}

namespace Hom

/-- A morphism `φ : (A, A⁺) → (B, B⁺)` of Huber pairs is *finite* (Huber 1996, (1.4.2)) if it is
topologically of finite type as a morphism of Huber pairs and the ring maps `A → B` and
`A⁺ → B⁺` are integral, the latter in the form that every element of `B⁺` is integral over the
image of `A⁺`. -/
structure IsFinite (φ : Hom S U) : Prop where
  /-- `φ` is topologically of finite type as a morphism of Huber pairs. -/
  isTopologicallyFiniteType : φ.IsTopologicallyFiniteType
  /-- The ring map `A → B` is integral. -/
  isIntegral : φ.toRingHom.IsIntegral
  /-- Every element of `B⁺` is integral over the image of `A⁺`. -/
  isIntegral_plus : ∀ b ∈ U.plus, IsIntegral (S.plus.map φ.toRingHom) b

/-- **Membership in the target plus ring of a finite morphism is integrality over the image of
the source plus ring.** -/
theorem IsFinite.mem_plus_iff {φ : Hom S U} (hφ : φ.IsFinite) {b : B} :
    b ∈ U.plus ↔ IsIntegral (S.plus.map φ.toRingHom) b :=
  ⟨hφ.isIntegral_plus b, φ.mem_plus_of_isIntegral⟩

/-- **The plus ring of the target of a finite morphism is the integral closure of the image of
the plus ring of the source.** -/
theorem IsFinite.plus_eq {φ : Hom S U} (hφ : φ.IsFinite) :
    U.plus = (integralClosure (S.plus.map φ.toRingHom) B).toSubring := by
  ext b
  rw [hφ.mem_plus_iff, Subalgebra.mem_toSubring, mem_integralClosure_iff]

/-- **The plus-ring map `A⁺ → B⁺` of a finite morphism is integral**: a monic polynomial over the
image of `A⁺` lifts to a monic polynomial over `A⁺`. -/
theorem IsFinite.isIntegral_restrict {φ : Hom S U} (hφ : φ.IsFinite) :
    (φ.toRingHom.restrict S.plus U.plus φ.map_mem_plus).IsIntegral := by
  rintro ⟨b, hb⟩
  obtain ⟨p, hpm, hp⟩ := hφ.isIntegral_plus b hb
  let ρ : S.plus →+* S.plus.map φ.toRingHom :=
    φ.toRingHom.restrict _ _ fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨q, rfl, -, hqm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.mem_lifts_of_surjective hρ p) hpm
  refine ⟨q, hqm, Subtype.ext ?_⟩
  rw [Polynomial.eval₂_map] at hp
  rw [← Subring.coe_subtype, Polynomial.hom_eval₂]
  exact hp

/-- **A finite morphism whose ring map is the identity does not enlarge the plus ring.** Thus
`(K, K⁺) → (K, K°)` is not finite when `K⁺ ⊊ K°`, although its ring map is. -/
theorem IsFinite.plus_eq_of_toRingHom_eq_id {S' : Pair A} {φ : Hom S S'} (hφ : φ.IsFinite)
    (h : φ.toRingHom = RingHom.id A) : S'.plus = S.plus := by
  refine le_antisymm (fun a ha ↦ ?_) fun a ha ↦ by simpa [h] using φ.map_mem_plus a ha
  have hint := hφ.isIntegral_plus a ha
  rw [h, Subring.map_id] at hint
  exact Subring.isIntegrallyClosedIn_iff.mp S.isRingOfIntegralElements.isIntegrallyClosedIn hint

end Hom

/-! ### Quotient mappings -/

section Complete

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A] {S : Pair A} {U : Pair B}

/-- **A quotient mapping out of a complete Hausdorff Huber pair is finite**: it is topologically
of finite type, presented with no variables, and surjective. -/
theorem Hom.IsQuotientMapping.isFinite {f : Hom S U} (hf : f.IsQuotientMapping) : f.IsFinite where
  isTopologicallyFiniteType := hf.isTopologicallyFiniteType
  isIntegral := RingHom.isIntegral_of_surjective _ hf.isOpenQuotientMap.surjective
  isIntegral_plus _ := hf.mem_plus_iff.mp

variable (S) in
/-- **The identity of a complete Hausdorff Huber pair is finite.** -/
@[simp]
theorem Hom.isFinite_id : (Hom.id S).IsFinite :=
  (Hom.isQuotientMapping_id S).isFinite

variable (S) in
/-- **The canonical morphism from a complete Hausdorff Huber pair to a quotient pair is finite**,
for every ideal. -/
@[simp]
theorem Hom.isFinite_quotientHom (J : Ideal A) : (S.quotientHom J).IsFinite :=
  (Hom.isQuotientMapping_quotientHom S J).isFinite

end Complete

/-! ### Composition -/

section Comp

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {S : Pair A} {U : Pair B}

/-- **Finite morphisms compose over a Tate base.** -/
theorem Hom.IsFinite.comp {f : Hom S U} {g : Hom U V} (hg : g.IsFinite)
    (hf : f.IsFinite) : (g.comp f).IsFinite where
  isTopologicallyFiniteType := hg.isTopologicallyFiniteType.comp hf.isTopologicallyFiniteType
  isIntegral := by rw [toRingHom_comp]; exact hf.isIntegral.trans _ _ hg.isIntegral
  isIntegral_plus c hc := isIntegral_plus_map_comp hf.isIntegral_plus (hg.isIntegral_plus c hc)

end Comp

/-! ### Module-finite morphisms over a Tate ring -/

section Tate

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsHuberRing B] [CompleteSpace B] [T0Space B] {S : Pair A} {U : Pair B}

/-- Evaluation `A⟨X₁, …, Xₙ⟩ → B` at a weight-bounded family spanning `B` over `A` is an open
quotient map: it is surjective because the family spans, and open by the open mapping theorem
over the Tate ring `A`. -/
private theorem isOpenQuotientMap_weightedEvalHomCompletion [Algebra A B]
    (hcont : Continuous (algebraMap A B)) {n : ℕ} {T : Fin n → Set A} (hT : IsWeightFamily T)
    {b : Fin n → B} (hb : IsWeightBounded (algebraMap A B) T b)
    (hspan : Submodule.span A (Set.range b) = ⊤) :
    IsOpenQuotientMap (weightedEvalHomCompletion hT hcont.continuousAt hb) := by
  set ψ := weightedEvalHomCompletion hT hcont.continuousAt hb
  have hψc : Continuous ψ := continuous_weightedEvalHomCompletion ..
  have hψC (a : A) : ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) = algebraMap A B a := by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]
  have hψX (j : Fin n) : ψ ((weightedX T hT j : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) = b j := by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp
      (hspan ▸ Submodule.mem_top : y ∈ Submodule.span A (Set.range b))
    refine ⟨∑ j, ((weightedC T hT (a j) * weightedX T hT j : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)), ?_⟩
    simp only [map_sum, Completion.coe_mul, map_mul, hψC, hψX, Algebra.smul_def]
  let π : Completion (weightedRestrictedSubring T hT) →ₐ[A] B :=
    { ψ with
      commutes' := fun a ↦ by
        have := hψC a
        rwa [← algebraMap_completion_weightedRestrictedSubring_apply] at this }
  have : ContinuousSMul A B := continuousSMul_of_algebraMap A B hcont
  have : (𝓤 (Completion (weightedRestrictedSubring T hT))).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have : (𝓤 B).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact ⟨hsurj, hψc, π.toLinearMap.isOpenMap_of_isTateRing hsurj hψc.continuousAt⟩

/-- Evaluation at elements `b₁, …, bₙ` of `B⁺` spanning `B` over `A` presents `φ` as a quotient
mapping out of `(A⟨X₁, …, Xₙ⟩, A⟨X⟩⁺)`, provided `B⁺` is integral over the image of `A⁺`. -/
private theorem Hom.isTopologicallyFiniteType_of_span_eq_top [Algebra A B] {φ : Hom S U}
    (hφA : algebraMap A B = φ.toRingHom) {n : ℕ} {b : Fin n → B} (hbU : ∀ j, b j ∈ U.plus)
    (hspan : Submodule.span A (Set.range b) = ⊤)
    (hplus : ∀ b ∈ U.plus, IsIntegral (S.plus.map φ.toRingHom) b) :
    φ.IsTopologicallyFiniteType := by
  -- evaluation at `b`, which is power-bounded since it lies in `B⁺`
  set T : Fin n → Set A := fun _ ↦ {1}
  have hT : IsWeightFamily T := isWeightFamily_one_weight
  have hcont : Continuous (algebraMap A B) := hφA ▸ φ.continuous_toRingHom
  have hb : IsWeightBounded (algebraMap A B) T b :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
      U.isRingOfIntegralElements.isPowerBounded_of_mem (hbU j)
  let ψ := weightedEvalHomCompletion hT hcont.continuousAt hb
  have hψ : IsOpenQuotientMap ψ := isOpenQuotientMap_weightedEvalHomCompletion hcont hT hb hspan
  have hψC (a : A) : ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) = φ.toRingHom a := by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedC, hφA]
  -- `ψ` carries the plus ring of `A⟨X⟩` into `B⁺`: the constants and variables go into `B⁺`
  let ψ' : Hom (S.weighted hT).completion U :=
    { toRingHom := ψ
      continuous_toRingHom := hψ.continuous
      map_mem_plus := S.weighted_completion_plus_le_comap hT U hψ.continuous
        (fun a ha ↦ by rw [hψC]; exact φ.map_mem_plus a ha)
        (fun j t ht ↦ by
          rw [Set.mem_singleton_iff.mp ht, Completion.coe_mul, map_mul, hψC, map_one, one_mul,
            weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
          exact hbU j) }
  -- the image of `A⁺` lies in the image of the plus ring of `A⟨X⟩`
  have hle : S.plus.map φ.toRingHom ≤ (S.weighted hT).completion.plus.map ψ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, S.weightedC_mem_weighted_completion_plus hT ha, hψC a⟩
  have hquot : ψ'.IsQuotientMapping :=
    (isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral ψ').mpr
      ⟨hψ, fun c hc ↦
        (hplus c hc).map_of_comp_eq (Subring.inclusion hle) (RingHom.id B) (by ext; rfl)⟩
  refine isTopologicallyFiniteType_iff.mpr ⟨n, T, fun _ ↦ Set.finite_singleton 1, hT, ψ', hquot,
    Hom.ext ?_⟩
  ext a
  rw [toRingHom_comp, toRingHom_weightedCompletionHom, RingHom.comp_apply,
    algebraMap_completion_weightedRestrictedSubring_apply]
  exact hψC a

/-- **Over a Tate ring, a module-finite morphism of Huber pairs into a complete Hausdorff pair is
finite as soon as the target plus ring is integral over the image of the source plus ring**: the
topological finite type clause is automatic (Zavyalov, Appendix B.2, Lemmas B.2.8–B.2.9). The
source need not be complete. -/
theorem Hom.isFinite_of_finite_of_isIntegral_plus {φ : Hom S U} (hfin : φ.toRingHom.Finite)
    (hplus : ∀ b ∈ U.plus, IsIntegral (S.plus.map φ.toRingHom) b) : φ.IsFinite := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have hφA : algebraMap A B = φ.toRingHom := RingHom.algebraMap_toAlgebra _
  have : Module.Finite A B := hfin
  have : ContinuousSMul A B := continuousSMul_of_algebraMap A B (hφA ▸ φ.continuous_toRingHom)
  obtain ⟨n, b, hbU, hspan⟩ := exists_span_range_eq_top_of_mem_nhds_zero (A := A)
    (U.isRingOfIntegralElements.isOpen.mem_nhds U.plus.zero_mem)
  exact ⟨isTopologicallyFiniteType_of_span_eq_top hφA hbU hspan hplus, hfin.to_isIntegral, hplus⟩

end Tate

/-! ### Finite étale morphisms -/

section FiniteEtale

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [CompleteSpace A] [T2Space A] {S : Pair A} {U : Pair B}

/-- **A finite étale morphism of Huber pairs over a complete Hausdorff Tate ring is finite**
(compare Huber 1996, Example 1.6.6(ii), stated for noetherian complete f-adic rings). -/
theorem Hom.IsFiniteEtale.isFinite {φ : Hom S U} (hφ : φ.IsFiniteEtale) : φ.IsFinite := by
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hφ.finite
  have : Algebra.Etale A B := hφ.etale
  have : IsModuleTopology A B := hφ.isModuleTopology
  have : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := A) (M := B))
  refine isFinite_of_finite_of_isIntegral_plus hφ.finite fun b hb ↦ ?_
  rw [hφ.plus_eq] at hb
  exact (mem_integralClosure_iff _ _).mp hb

end FiniteEtale

end TauCeti.Huber.Pair
