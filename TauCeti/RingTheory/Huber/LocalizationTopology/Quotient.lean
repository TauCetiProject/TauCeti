/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

import TauCeti.RingTheory.Huber.WeightedEval.Quotient
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded
import TauCeti.RingTheory.Ideal.Operations

/-!
# A rational localisation as a quotient of `A⟨X₁, …, Xₖ⟩`

Wedhorn's Example 6.38 presents the coordinate ring of a rational subset as a quotient of a
restricted power series ring. For a presentation `(T, s)` whose numerators other than `s` are
listed by `t : Fin k → A`, this file constructs the identification

```text
A⟨X₁, …, Xₖ⟩ ⧸ (t₁ - s X₁, …, tₖ - s Xₖ)  ≃  A⟨T/s⟩,      Xᵢ ↦ tᵢ/s,
```

as an isomorphism of topological rings compatible with the structure maps from `A`. It asks `A`
to be a complete Huber ring, the relation ideal to be closed, every `tᵢ` to lie in `T`, every
element of `T` to be `s` or some `tᵢ`, and `T` together with `s` to generate the unit ideal.

The denominator need not be listed even when it is a numerator: `({f, 1}, 1)` with `t = (f)`,
`({1}, f)` with `t = (1)`, and `({f², f, 1}, f)` with `t = (f², 1)` all satisfy the hypotheses.

## Main definitions

* `TauCeti.Huber.rationalRelationIdeal`: the ideal `(t₁ - s X₁, …, tₖ - s Xₖ)` of
  `A⟨X₁, …, Xₖ⟩`.
* `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv`: the identification of the quotient
  with `A⟨T/s⟩`.

## Main results

* `TauCeti.Huber.rationalRelationIdeal_quotientMk_weightedC_mul_weightedX`: in the quotient the
  classes of `s` and `Xᵢ` multiply to the class of `tᵢ`.
* `TauCeti.Huber.isUnit_rationalRelationIdeal_quotientMk_weightedC`: the class of `s` is a unit
  when `s` and the `tᵢ` generate the unit ideal.
* `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv_quotientMk_weightedC`,
  `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv_quotientMk_weightedX`,
  `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv_symm_toCompletionLoc` and
  `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv_symm_coe_divBy`: the identification and
  its inverse on constants and on the variables.
* `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv_algebraMap`: the identification is
  compatible with the structure maps from `A`.
* `TauCeti.Huber.PairOfDefinition.continuous_rationalQuotientRingEquiv` and its `symm` form: the
  identification is one of topological rings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.38.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, branch `dev/adic-spaces`, commit `37bbdaeb9`, Apache-2.0),
`projects/AdicSpaces/Adic spaces/Example638.lean`, proves the two one-variable cases as
`example638Plus_equiv`, `B⟨X⟩ ⧸ (b - X) ≃+* presheafValue (trivialPlusDatum P b)`, and
`example638Minus_equiv`, `B⟨X⟩ ⧸ (1 - b X) ≃+* presheafValue (trivialMinusDatum P b)`, over its own
`TateAlgebra` and `presheafValue`. This file states the identification for `k` variables and an
arbitrary presentation, against this repository's `weightedRestrictedSubring` and
`toCompletionLoc`; no AINTLIB code is copied.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

section RelationIdeal

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] {k : ℕ}

/-- **The relation ideal `(t₁ - s X₁, …, tₖ - s Xₖ)`** of `A⟨X₁, …, Xₖ⟩`, the ring of restricted
power series in `k` variables (the weighted restricted series with weight `{1}`). In the quotient
the class of `s` times the class of `Xᵢ` is the class of `tᵢ`
(`rationalRelationIdeal_quotientMk_weightedC_mul_weightedX`).
`PairOfDefinition.rationalQuotientRingEquiv` identifies the quotient with `A⟨T/s⟩`.

Compare `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal`, the ideal `(t/s - X)` of
`A⟨T/s⟩⟨X⟩`: its quotient adjoins one more fraction to `A⟨T/s⟩`, whereas the quotient by this
ideal builds `A⟨T/s⟩` from `A`. -/
noncomputable def rationalRelationIdeal (t : Fin k → A) (s : A) : Ideal (weightedRestrictedSubring
    (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
  Ideal.span (Set.range fun i ↦ weightedC _ isWeightFamily_one_weight (t i) -
    weightedC _ isWeightFamily_one_weight s * weightedX _ isWeightFamily_one_weight i)

/-- `rationalRelationIdeal t s` is the span of the `tᵢ - s Xᵢ`. The definition's body is not
exposed across module boundaries, so rewrite with this lemma to reach the generators; for computing
in the quotient, `rationalRelationIdeal_quotientMk_weightedC_mul_weightedX` is usually more
direct. -/
theorem rationalRelationIdeal_def (t : Fin k → A) (s : A) : rationalRelationIdeal t s = Ideal.span
    (Set.range fun i ↦ weightedC _ isWeightFamily_one_weight (t i) -
      weightedC _ isWeightFamily_one_weight s * weightedX _ isWeightFamily_one_weight i) := (rfl)

/-- **The relations the ideal imposes**: in `A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ - s Xᵢ)` the class of the constant
`s` times the class of the variable `Xᵢ` is the class of the constant `tᵢ`. `simp` rewrites this
product only with the class of `s` on the left; for the other order, rewrite with `mul_comm` first.
When the class of `s` is a unit (`isUnit_rationalRelationIdeal_quotientMk_weightedC`), this
identifies the class of `Xᵢ` with the class of `tᵢ` times the inverse of the class of `s`. -/
@[simp]
theorem rationalRelationIdeal_quotientMk_weightedC_mul_weightedX (t : Fin k → A) (s : A)
    (i : Fin k) :
    Ideal.Quotient.mk (rationalRelationIdeal t s) (weightedC _ isWeightFamily_one_weight s) *
        Ideal.Quotient.mk (rationalRelationIdeal t s) (weightedX _ isWeightFamily_one_weight i) =
      Ideal.Quotient.mk (rationalRelationIdeal t s) (weightedC _ isWeightFamily_one_weight (t i)) :=
  -- `tᵢ - s Xᵢ` is a generator of the ideal
  Eq.symm <| Ideal.Quotient.eq.2 <| Ideal.subset_span ⟨i, rfl⟩

/-- **`s` becomes a unit in `A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ - s Xᵢ)`** when `s` and the numerators `tᵢ` generate
the unit ideal of `A`. -/
theorem isUnit_rationalRelationIdeal_quotientMk_weightedC {t : Fin k → A} {s : A}
    (hspan : Ideal.span (insert s (Set.range t)) = ⊤) : IsUnit (Ideal.Quotient.mk
      (rationalRelationIdeal t s) (weightedC _ isWeightFamily_one_weight s)) := by
  -- the pullback of `([s])` to `A` contains `s` and each `tᵢ`, as `[tᵢ] = [s] [Xᵢ]`, so it is `⊤`
  rw [← Ideal.span_singleton_eq_top, ← Ideal.comap_eq_top_iff (f := (Ideal.Quotient.mk _).comp
    (weightedC _ isWeightFamily_one_weight)), ← top_le_iff, ← hspan, Ideal.span_le,
    Set.insert_subset_iff, Set.range_subset_iff]
  exact ⟨Ideal.mem_span_singleton_self _, fun i ↦ Ideal.mem_span_singleton.2 <| Dvd.intro _ <|
    rationalRelationIdeal_quotientMk_weightedC_mul_weightedX t s i⟩

-- In the quotient, `u/s` for `u = s` or `u = tᵢ` is `1` or the class of a variable, so it is
-- power-bounded.
private theorem isPowerBounded_quotientMk_weightedC_mul_unit_inv {t : Fin k → A} {s : A}
    (hunit : IsUnit ((Ideal.Quotient.mk (rationalRelationIdeal t s)).comp
      (weightedC _ isWeightFamily_one_weight) s)) {u : A} (hu : u = s ∨ u ∈ Set.range t) :
    IsPowerBounded ((Ideal.Quotient.mk (rationalRelationIdeal t s)).comp
      (weightedC _ isWeightFamily_one_weight) u * ↑hunit.unit⁻¹) := by
  rcases hu with rfl | ⟨i, rfl⟩
  · simp
  -- `tᵢ/s` is the class of `Xᵢ`
  · convert (isPowerBounded_weightedX_one_weight i).map_of_isOpenMap continuous_quot_mk.continuousAt
      (QuotientRing.isOpenMap_coe (rationalRelationIdeal t s)) using 1
    exact (Units.mul_inv_eq_iff_eq_mul _).2 <|
      (rationalRelationIdeal_quotientMk_weightedC_mul_weightedX t s i).symm.trans (mul_comm _ _)

end RelationIdeal

namespace PairOfDefinition

section ToCompletion

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) {k : ℕ} (t : Fin k → A)
  (ht : ∀ i, t i ∈ T)

include ht

-- The map out of the quotient: constants go through the structure map, and `Xᵢ` goes to `tᵢ/s`.
private theorem existsUnique_continuous_ringHom_rationalQuotient_toCompletion :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃! ψ : (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
        rationalRelationIdeal t s) →+* UniformSpace.Completion S, Continuous ψ ∧
      (∀ a, ψ (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
        toCompletionLoc P T s S hden a) ∧
      ∀ i, ψ (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
        ((divBy (t i) s : S) : UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  -- each `Xᵢ` goes to the fraction `tᵢ/s`, which is power-bounded because `tᵢ ∈ T`
  refine existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring
    isWeightFamily_one_weight (continuous_toCompletionLoc P T s S hden).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).2 fun i ↦
      isPowerBounded_completion_coe_of_isPowerBounded
        (isPowerBounded_divBy_locUniformSpace P T s S hden (ht i))) ?_
  -- the evaluation kills each `tᵢ - s Xᵢ`, so the relation ideal lies in its kernel
  simp [rationalRelationIdeal_def, Ideal.span_le, Set.range_subset_iff, -coe_weightedEvalHom,
    weightedEvalHom_weightedC, weightedEvalHom_weightedX, ← UniformSpace.Completion.coe_mul]

-- The map `A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ - s Xᵢ) → A⟨T/s⟩` out of the quotient.
private noncomputable def rationalQuotientToCompletion :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      rationalRelationIdeal t s) →+* UniformSpace.Completion S :=
  (existsUnique_continuous_ringHom_rationalQuotient_toCompletion P T s S hden t ht).choose

private theorem continuous_rationalQuotientToCompletion :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (rationalQuotientToCompletion P T s S hden t ht) :=
  (existsUnique_continuous_ringHom_rationalQuotient_toCompletion P T s S hden t ht).choose_spec.1.1

private theorem rationalQuotientToCompletion_quotientMk_weightedC (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalQuotientToCompletion P T s S hden t ht
        (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
      toCompletionLoc P T s S hden a :=
  (existsUnique_continuous_ringHom_rationalQuotient_toCompletion P T s S hden t
    ht).choose_spec.1.2.1 a

private theorem rationalQuotientToCompletion_quotientMk_weightedX (i : Fin k) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalQuotientToCompletion P T s S hden t ht
        (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
      ((divBy (t i) s : S) : UniformSpace.Completion S) :=
  (existsUnique_continuous_ringHom_rationalQuotient_toCompletion P T s S hden t
    ht).choose_spec.1.2.2 i

end ToCompletion

section Identification

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*)
  [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T) (hsplit : ∀ u ∈ T, u = s ∨ u ∈ Set.range t)
  (hspan : Ideal.span (insert s (T : Set A)) = ⊤)
  (hcl : IsClosed (rationalRelationIdeal t s : Set (weightedRestrictedSubring
    (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)))

include hsplit hspan hcl

-- The map into the quotient, from the universal property of `A⟨T/s⟩`: in the quotient `s` is a
-- unit and each `u/s` for `u ∈ T` is power-bounded.
private theorem existsUnique_continuous_ringHom_completion_rationalQuotient :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight ⧸ rationalRelationIdeal t s), Continuous g ∧
      g.comp (toCompletionLoc P T s S hden) = (Ideal.Quotient.mk (rationalRelationIdeal t s)).comp
        (weightedC _ isWeightFamily_one_weight) := by
  -- the quotient is complete, and separated because the ideal is closed, as the universal
  -- property asks of its target
  let _ : UniformSpace (_ ⧸ rationalRelationIdeal t s) := IsTopologicalAddGroup.rightUniformSpace _
  have _ : IsUniformAddGroup (_ ⧸ rationalRelationIdeal t s) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (_ ⧸ rationalRelationIdeal t s) := QuotientAddGroup.completeSpace_right _ _
  exact existsUnique_continuous_ringHom_completion_locTopology P T s S hden
    (continuous_quot_mk.comp (continuous_weightedC isWeightFamily_one_weight)).continuousAt
    (isUnit_rationalRelationIdeal_quotientMk_weightedC <| Ideal.span_insert_eq_top_of_subset
      (fun u hu ↦ Set.mem_insert_iff.mpr (hsplit u hu)) hspan)
    fun u hu ↦ isPowerBounded_quotientMk_weightedC_mul_unit_inv _ (hsplit u hu)

-- The map `A⟨T/s⟩ → A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ - s Xᵢ)` into the quotient.
private noncomputable def completionToRationalQuotient :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    UniformSpace.Completion S →+* (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ⧸ rationalRelationIdeal t s) :=
  (existsUnique_continuous_ringHom_completion_rationalQuotient P T s S hden t hsplit hspan
    hcl).choose

private theorem continuous_completionToRationalQuotient :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (completionToRationalQuotient P T s S hden t hsplit hspan hcl) :=
  (existsUnique_continuous_ringHom_completion_rationalQuotient P T s S hden t hsplit hspan
    hcl).choose_spec.1.1

private theorem completionToRationalQuotient_toCompletionLoc (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    completionToRationalQuotient P T s S hden t hsplit hspan hcl (toCompletionLoc P T s S hden a) =
      Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a) :=
  DFunLike.congr_fun (existsUnique_continuous_ringHom_completion_rationalQuotient P T s S hden t
    hsplit hspan hcl).choose_spec.1.2 a

include ht

-- Into the quotient and back out again is the identity of `A⟨T/s⟩`.
private theorem rationalQuotientToCompletion_comp_completionToRationalQuotient :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (rationalQuotientToCompletion P T s S hden t ht).comp
      (completionToRationalQuotient P T s S hden t hsplit hspan hcl) = RingHom.id _ := by
  -- a continuous map out of `A⟨T/s⟩` is determined on `A`
  refine eq_id_of_comp_toCompletionLoc_eq_self P T s S hden _
    ((continuous_rationalQuotientToCompletion P T s S hden t ht).comp
      (continuous_completionToRationalQuotient P T s S hden t hsplit hspan hcl)) <|
    RingHom.ext fun a ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, completionToRationalQuotient_toCompletionLoc,
    rationalQuotientToCompletion_quotientMk_weightedC]

-- Out of the quotient and back in again is the identity of the quotient.
private theorem completionToRationalQuotient_comp_rationalQuotientToCompletion :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completionToRationalQuotient P T s S hden t hsplit hspan hcl).comp
      (rationalQuotientToCompletion P T s S hden t ht) = RingHom.id _ := by
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have hC := completionToRationalQuotient_toCompletionLoc P T s S hden t hsplit hspan hcl
  -- a continuous map out of the quotient is determined on constants and on the variables; on `Xᵢ`
  -- it is the image of `tᵢ/s`, and it and the class of `Xᵢ` solve `[s] x = [tᵢ]` with `[s]` a unit
  refine Ideal.Quotient.ringHom_ext <| weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight (((continuous_completionToRationalQuotient P T s S hden t hsplit
      hspan hcl).comp (continuous_rationalQuotientToCompletion P T s S hden t ht)).comp
      continuous_quot_mk) continuous_quot_mk (fun a ↦ ?_) fun i ↦ ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, rationalQuotientToCompletion_quotientMk_weightedC,
      hC, RingHom.id_comp]
  · refine (isUnit_rationalRelationIdeal_quotientMk_weightedC
      (Ideal.span_insert_eq_top_of_subset
        (fun u hu ↦ Set.mem_insert_iff.mpr (hsplit u hu)) hspan)).mul_left_cancel ?_
    rw [RingHom.id_comp, rationalRelationIdeal_quotientMk_weightedC_mul_weightedX, ← hC, ← hC]
    simp [rationalQuotientToCompletion_quotientMk_weightedX, ← map_mul,
      ← UniformSpace.Completion.coe_mul]

/-- **Wedhorn's Example 6.38**: over a complete Huber ring `A`, for a presentation `(T, s)` and a
listing `t : Fin k → A` of numerators, the ring isomorphism

```text
A⟨X₁, …, Xₖ⟩ ⧸ (t₁ - s X₁, …, tₖ - s Xₖ)  ≃  A⟨T/s⟩
```

that is the structure map from `A` on constants and sends `Xᵢ` to `tᵢ/s`. The hypotheses: every
`tᵢ` lies in `T` (`ht`), every element of `T` is `s` or some `tᵢ` (`hsplit`), `T` and `s`
generate the unit ideal (`hspan`), and the relation ideal is closed (`hcl`). For instance, `hcl`
holds when `A` is a separated strongly noetherian Tate ring, by
`TauCeti.Huber.isClosed_of_isNoetherian`. -/
noncomputable def rationalQuotientRingEquiv :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      rationalRelationIdeal t s) ≃+* UniformSpace.Completion S :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  -- the two maps are mutually inverse, so they assemble into the identification
  RingEquiv.ofRingHom (rationalQuotientToCompletion P T s S hden t ht)
    (completionToRationalQuotient P T s S hden t hsplit hspan hcl)
    (rationalQuotientToCompletion_comp_completionToRationalQuotient P T s S hden t ht hsplit hspan
      hcl)
    (completionToRationalQuotient_comp_rationalQuotientToCompletion P T s S hden t ht hsplit hspan
      hcl)

/-- **On constants the identification is the structure map** `A → A⟨T/s⟩`. The values on the
variables are given by `rationalQuotientRingEquiv_quotientMk_weightedX`, and
`rationalQuotientRingEquiv_symm_toCompletionLoc` is the same fact read through the inverse. -/
@[simp]
theorem rationalQuotientRingEquiv_quotientMk_weightedC (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl
        (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
      toCompletionLoc P T s S hden a :=
  rationalQuotientToCompletion_quotientMk_weightedC P T s S hden t ht a

/-- **The identification is compatible with the structure maps from `A`**: it sends the image of
`a` under `algebraMap A (A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ - s Xᵢ))` to the image of `a` in `A⟨T/s⟩`. This is
`rationalQuotientRingEquiv_quotientMk_weightedC` stated through the `A`-algebra structure of the
quotient, which is the form that composes with `algebraMap`, for instance under `RingHom.ext`. -/
@[simp]
theorem rationalQuotientRingEquiv_algebraMap (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl (algebraMap A _ a) =
      toCompletionLoc P T s S hden a :=
  rationalQuotientRingEquiv_quotientMk_weightedC P T s S hden t ht hsplit hspan hcl a

/-- **The identification sends `Xᵢ` to `tᵢ/s`**: the class of the variable goes to the image in
`A⟨T/s⟩` of the fraction `divBy (t i) s`. The inverse form is
`rationalQuotientRingEquiv_symm_coe_divBy`. -/
@[simp]
theorem rationalQuotientRingEquiv_quotientMk_weightedX (i : Fin k) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl
        (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
      ((divBy (t i) s : S) : UniformSpace.Completion S) :=
  rationalQuotientToCompletion_quotientMk_weightedX P T s S hden t ht i

/-- **The inverse identification on `A`**: it sends the image of `a` in `A⟨T/s⟩` to the class of
the constant `a`. Use it with `rw`: `simp` first rewrites `toCompletionLoc` by
`toCompletionLoc_apply`, so the left-hand side is not in simp normal form. -/
theorem rationalQuotientRingEquiv_symm_toCompletionLoc (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl).symm
        (toCompletionLoc P T s S hden a) =
      Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a) :=
  completionToRationalQuotient_toCompletionLoc P T s S hden t hsplit hspan hcl a

/-- **The inverse identification sends `tᵢ/s` to `Xᵢ`**: the image in `A⟨T/s⟩` of the fraction
`divBy (t i) s` goes to the class of the variable. `simp` and `rw` find it only while the numerator
is still of the form `t i`; for a concrete listing such as `![f, g]`, whose entries `simp` evaluates
first, `simp [RingEquiv.symm_apply_eq]` reaches the class of the variable through
`rationalQuotientRingEquiv_quotientMk_weightedX` instead. -/
@[simp]
theorem rationalQuotientRingEquiv_symm_coe_divBy (i : Fin k) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl).symm
        ((divBy (t i) s : S) : UniformSpace.Completion S) =
      Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i) := by
  simp [RingEquiv.symm_apply_eq]

/-- The identification `A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ - s Xᵢ) ≃+* A⟨T/s⟩` is continuous. With
`continuous_rationalQuotientRingEquiv_symm` this makes it an isomorphism of topological rings. -/
theorem continuous_rationalQuotientRingEquiv :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl) :=
  continuous_rationalQuotientToCompletion P T s S hden t ht

/-- The inverse of the identification `A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ - s Xᵢ) ≃+* A⟨T/s⟩` is continuous. With
`continuous_rationalQuotientRingEquiv` this makes it an isomorphism of topological rings. -/
theorem continuous_rationalQuotientRingEquiv_symm :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl).symm :=
  continuous_completionToRationalQuotient P T s S hden t hsplit hspan hcl

end Identification

end PairOfDefinition

end TauCeti.Huber

end
