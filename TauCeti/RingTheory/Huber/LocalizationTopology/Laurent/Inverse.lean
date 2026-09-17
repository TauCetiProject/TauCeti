/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

import TauCeti.RingTheory.Huber.WeightedEval.Quotient
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# The Laurent quotient `A⟨X⟩ ⧸ (1 - f X)` is `A⟨{1}/f⟩`

For `f` in a Huber ring `A`, the rational subset `{|f| ≥ 1}` of `Spa A` has the single numerator `1`
over the denominator `f`, and Wedhorn's Example 6.38 presents its coordinate ring as a quotient of
the restricted power series ring,

```text
A⟨X⟩ ⧸ (1 - f X)  ≃  A⟨{1}/f⟩,
```

the variable going to `1/f`. This file constructs that identification, as an isomorphism of
topological rings compatible with the structure maps from `A`, for a complete `A` whose ideal
`(1 - f X)` is closed. Over a complete separated strongly noetherian Tate ring every ideal of
`A⟨X⟩` is closed.

In the quotient, `f` becomes a unit whose inverse is the class of `X`, which is power-bounded; that
is what the universal property of `A⟨{1}/f⟩` asks, and it gives the map into the quotient. The map
out of the quotient sends `X` to `1/f`.

`{|f| ≥ 1}` is the other half of the Laurent pair whose first half `{|f| ≤ 1}` is the Laurent
quotient of `TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Identification`. That one adjoins
a numerator at a fixed denominator; this one changes the denominator, which makes it the first step
of Wedhorn's chain of rational subsets (Remark 7.55) and the way flatness reaches the structure map
`A → A⟨T/s⟩`.

## Main definitions

* `TauCeti.Huber.laurentInvRelationIdeal`: the ideal `(1 - f X)` of `A⟨X⟩`.
* `TauCeti.Huber.PairOfDefinition.laurentInvQuotientRingEquiv`: the identification
  `A⟨X⟩ ⧸ (1 - f X) ≃+* A⟨{1}/f⟩`.

## Main results

* `TauCeti.Huber.laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX`: in the quotient, the
  classes of `f` and `X` are mutually inverse.
* `TauCeti.Huber.PairOfDefinition.laurentInvQuotientRingEquiv_quotientMk_weightedC`,
  `TauCeti.Huber.PairOfDefinition.laurentInvQuotientRingEquiv_quotientMk_weightedX` and
  `TauCeti.Huber.PairOfDefinition.laurentInvQuotientRingEquiv_symm_toCompletionLoc`: the
  identification on constants and on `X`, and its inverse on `A`.
* `TauCeti.Huber.PairOfDefinition.laurentInvQuotientRingEquiv_algebraMap`: the identification is
  compatible with the structure maps from `A`.
* `TauCeti.Huber.PairOfDefinition.continuous_laurentInvQuotientRingEquiv` and its `symm` form: the
  identification is one of topological rings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.38, Remark 7.55 and
  the proof of Proposition 8.30.
* [AINTLIB](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`, at commit `37bbdaeb9`,
  `projects/AdicSpaces/Adic spaces/Example638.lean`, `example638Minus_equiv`.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB` @ `37bbdaeb9`, Apache-2.0) proves this identification as
`example638Minus_equiv`, `B⟨X⟩ ⧸ (1 - b X) ≃+* presheafValue (trivialMinusDatum P b)`, over its own
`TateAlgebra` and `presheafValue`. The plan here is the same: the map out of the quotient evaluates
`X` at `1/f`, the map into it comes from the universal property of the localisation, and the two
composites are checked on generators. It is written against this repository's
`weightedRestrictedSubring` and `toCompletionLoc`, following
`TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Presentation`; no AINTLIB code is copied.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

section RelationIdeal

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The relation ideal `(1 - f X)`** of `A⟨X⟩`, the ring of restricted power series in one
variable (the weighted restricted series with weight `{1}`). In the quotient the class of `X` is an
inverse of the class of `f` (`laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX`). When `A`
is a complete Huber ring and this ideal is closed, `PairOfDefinition.laurentInvQuotientRingEquiv`
identifies the quotient with `A⟨{1}/f⟩`.

Compare `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal`, the ideal `(t/s - X)`: its quotient
adjoins a numerator at a fixed denominator, while the quotient by this one inverts `f`. -/
noncomputable def laurentInvRelationIdeal (f : A) : Ideal (weightedRestrictedSubring
    (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
  Ideal.span {1 - weightedC _ isWeightFamily_one_weight f * weightedX _ isWeightFamily_one_weight 0}

/-- `laurentInvRelationIdeal f` is the span of `1 - f X`. The definition's body is not exposed
across module boundaries, so rewrite with this lemma to reach the generator; for computing in the
quotient, `laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX` is usually more direct. -/
theorem laurentInvRelationIdeal_def (f : A) : laurentInvRelationIdeal f = Ideal.span
    {1 - weightedC _ isWeightFamily_one_weight f * weightedX _ isWeightFamily_one_weight 0} := (rfl)

/-- **The relation the ideal imposes**: in `A⟨X⟩ ⧸ (1 - f X)` the class of the constant `f` times
the class of the variable `X` is `1`, so the class of `f` is a unit with inverse the class of `X`
(`IsUnit.of_mul_eq_one`, `Units.inv_eq_of_mul_eq_one_right`). -/
@[simp]
theorem laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX (f : A) :
    Ideal.Quotient.mk (laurentInvRelationIdeal f) (weightedC _ isWeightFamily_one_weight f) *
        Ideal.Quotient.mk (laurentInvRelationIdeal f) (weightedX _ isWeightFamily_one_weight 0) =
      1 := by
  rw [← map_mul, Ideal.Quotient.mk_eq_one_iff_sub_mem, laurentInvRelationIdeal_def]
  exact sub_mem_comm_iff.1 <| Ideal.mem_span_singleton_self _

end RelationIdeal

namespace PairOfDefinition

section ToCompletion

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (P : PairOfDefinition A) (f : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away f S] (h1 : HasDenominatorPower P {1} f S)

-- The map out of the quotient: constants go through the structure map, and `X` goes to `1/f`.
private theorem existsUnique_continuous_ringHom_laurentInvQuotient_toCompletion :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    ∃! ψ : (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
        laurentInvRelationIdeal f) →+* UniformSpace.Completion S, Continuous ψ ∧
      (∀ a, ψ (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
        toCompletionLoc P {1} f S h1 a) ∧
      ∀ i, ψ (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
        ((divBy 1 f : S) : UniformSpace.Completion S) := by
  let _ := locUniformSpace P {1} f S h1
  have _ := isUniformAddGroup_locUniformSpace P {1} f S h1
  have _ := isTopologicalRing_locUniformSpace P {1} f S h1
  have _ := isHuberRing_locUniformSpace P {1} f S h1
  -- `X` goes to the distinguished fraction `1/f`, which is power-bounded
  refine existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring
    isWeightFamily_one_weight (continuous_toCompletionLoc P {1} f S h1).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).2 fun _ ↦
      isPowerBounded_completion_coe_of_isPowerBounded
        (isPowerBounded_divBy_locUniformSpace P {1} f S h1 (Finset.mem_singleton_self 1))) ?_
  -- the evaluation kills `1 - f X`, so the relation ideal lies in its kernel
  rw [laurentInvRelationIdeal_def, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub,
    map_one, map_mul, weightedEvalHom_weightedC, weightedEvalHom_weightedX]
  simp [← UniformSpace.Completion.coe_mul, UniformSpace.Completion.coe_one]

end ToCompletion

section Identification

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] (P : PairOfDefinition A) (f : A) (S : Type*) [CommRing S]
  [Algebra A S] [IsLocalization.Away f S] (h1 : HasDenominatorPower P {1} f S)
  (hcl : IsClosed (laurentInvRelationIdeal f : Set (weightedRestrictedSubring
    (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight)))

include hcl

-- The map into the quotient, from the universal property of `A⟨{1}/f⟩`: in the quotient `f` is a
-- unit whose inverse, the class of `X`, is power-bounded.
private theorem existsUnique_continuous_ringHom_completion_laurentInvQuotient :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    ∃! g : UniformSpace.Completion S →+* (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
        isWeightFamily_one_weight ⧸ laurentInvRelationIdeal f), Continuous g ∧
      g.comp (toCompletionLoc P {1} f S h1) = (Ideal.Quotient.mk (laurentInvRelationIdeal f)).comp
        (weightedC _ isWeightFamily_one_weight) := by
  let _ := locUniformSpace P {1} f S h1
  have _ := isUniformAddGroup_locUniformSpace P {1} f S h1
  have _ := isTopologicalRing_locUniformSpace P {1} f S h1
  -- the quotient is a complete separated Huber ring, which is what the universal property asks
  let _ : UniformSpace (_ ⧸ laurentInvRelationIdeal f) := IsTopologicalAddGroup.rightUniformSpace _
  have _ : IsUniformAddGroup (_ ⧸ laurentInvRelationIdeal f) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (_ ⧸ laurentInvRelationIdeal f) :=
    QuotientAddGroup.completeSpace_right _ (laurentInvRelationIdeal f).toAddSubgroup
  have hrel := laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX f
  have hunit := IsUnit.of_mul_eq_one _ hrel
  have hq := QuotientRing.isOpenQuotientMap_mk (laurentInvRelationIdeal f)
  refine existsUnique_continuous_ringHom_completion_locTopology P {1} f S h1
    (hq.continuous.comp (continuous_weightedC isWeightFamily_one_weight)).continuousAt
    hunit fun t ht ↦ ?_
  -- the inverse of `f` is the class of `X`, a left inverse being a right inverse
  rw [Finset.mem_singleton.mp ht, map_one, one_mul, left_inv_eq_right_inv hunit.val_inv_mul hrel]
  exact (isPowerBounded_weightedX_one_weight 0).map_of_isOpenMap hq.continuous.continuousAt
    hq.isOpenMap

-- The two maps are mutually inverse, so they assemble into the identification.
private theorem exists_ringEquiv_laurentInvQuotient :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    ∃ e : (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
        laurentInvRelationIdeal f) ≃+* UniformSpace.Completion S,
      (∀ a, e (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
        toCompletionLoc P {1} f S h1 a) ∧
      (∀ i, e (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
        ((divBy 1 f : S) : UniformSpace.Completion S)) ∧
      (∀ a, e.symm (toCompletionLoc P {1} f S h1 a) =
        Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) ∧
      Continuous e ∧ Continuous e.symm := by
  have _ := isUniformAddGroup_locUniformSpace P {1} f S h1
  have _ := isTopologicalRing_locUniformSpace P {1} f S h1
  obtain ⟨ψ, ⟨hψc, hψC, hψX⟩, -⟩ :=
    existsUnique_continuous_ringHom_laurentInvQuotient_toCompletion P f S h1
  obtain ⟨g, ⟨hgc, hge⟩, -⟩ :=
    existsUnique_continuous_ringHom_completion_laurentInvQuotient P f S h1 hcl
  refine ⟨RingEquiv.ofRingHom ψ g ?_ ?_, hψC, hψX, DFunLike.congr_fun hge, hψc, hgc⟩
  -- a continuous map out of `A⟨{1}/f⟩` is determined on `A`
  · exact eq_id_of_comp_toCompletionLoc_eq_self P {1} f S h1 _ (hψc.comp hgc) <|
      RingHom.ext fun a ↦ (congrArg ψ (DFunLike.congr_fun hge a)).trans (hψC a)
  -- a continuous map out of the quotient is determined on constants and on `X`; on `X` it is
  -- `g (1/f)`, a left inverse of the class of `f`, whose right inverse is the class of `X`
  · refine Ideal.Quotient.ringHom_ext <| weightedRestrictedSubring_ringHom_ext_of_continuous
      isWeightFamily_one_weight ((hgc.comp hψc).comp continuous_quot_mk) continuous_quot_mk
      (fun a ↦ (congrArg g (hψC a)).trans (DFunLike.congr_fun hge a)) <| Fin.forall_fin_one.2 <|
        (congrArg g (hψX 0)).trans <| left_inv_eq_right_inv ?_
          (laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX f)
    rw [← RingHom.comp_apply (Ideal.Quotient.mk _), ← hge]
    simp [← map_mul, ← UniformSpace.Completion.coe_mul, UniformSpace.Completion.coe_one]

/-- **Wedhorn's Example 6.38 at `{|f| ≥ 1}`**: over a complete Huber ring `A`, when the ideal
`(1 - f X)` of `A⟨X⟩` is closed, the ring isomorphism

```text
A⟨X⟩ ⧸ (1 - f X)  ≃  A⟨{1}/f⟩
```

that is the structure map from `A` on constants and sends `X` to `1/f`. For instance, `hcl` holds
when `A` is a separated strongly noetherian Tate ring, by `TauCeti.Huber.isClosed_of_isNoetherian`.

Compute with it through `laurentInvQuotientRingEquiv_quotientMk_weightedC`,
`laurentInvQuotientRingEquiv_quotientMk_weightedX` and
`laurentInvQuotientRingEquiv_symm_toCompletionLoc`, or through
`laurentInvQuotientRingEquiv_algebraMap` for the `A`-algebra structure of the quotient;
`continuous_laurentInvQuotientRingEquiv` and `continuous_laurentInvQuotientRingEquiv_symm` make it
an isomorphism of topological rings.

Compare `TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv`, the identification of the
quotient by `(t/s - X)`, which adjoins a numerator at a fixed denominator; this one inverts `f`. -/
noncomputable def laurentInvQuotientRingEquiv :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      laurentInvRelationIdeal f) ≃+* UniformSpace.Completion S :=
  (exists_ringEquiv_laurentInvQuotient P f S h1 hcl).choose

/-- **On constants the identification is the structure map** `A → A⟨{1}/f⟩`. The value on `X` is
given by `laurentInvQuotientRingEquiv_quotientMk_weightedX`, and
`laurentInvQuotientRingEquiv_symm_toCompletionLoc` is the same fact read through the inverse. -/
@[simp]
theorem laurentInvQuotientRingEquiv_quotientMk_weightedC (a : A) :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    laurentInvQuotientRingEquiv P f S h1 hcl
        (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
      toCompletionLoc P {1} f S h1 a :=
  (exists_ringEquiv_laurentInvQuotient P f S h1 hcl).choose_spec.1 a

/-- **The identification is compatible with the structure maps from `A`**: it sends the image of
`a` under `algebraMap A (A⟨X⟩ ⧸ (1 - f X))` to the image of `a` in `A⟨{1}/f⟩`. This is
`laurentInvQuotientRingEquiv_quotientMk_weightedC` stated through the `A`-algebra structure of the
quotient, which is the form that composes with `algebraMap`, for instance under `RingHom.ext`. -/
@[simp]
theorem laurentInvQuotientRingEquiv_algebraMap (a : A) :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    laurentInvQuotientRingEquiv P f S h1 hcl (algebraMap A _ a) = toCompletionLoc P {1} f S h1 a :=
  laurentInvQuotientRingEquiv_quotientMk_weightedC P f S h1 hcl a

/-- **The identification sends `X` to `1/f`**: the class of the variable (its index `i : Fin 1` is
necessarily `0`) goes to the image in `A⟨{1}/f⟩` of `IsLocalization.Away.invSelf f`, which is the
fraction `divBy 1 f` by `TauCeti.Localization.divBy_one`. The companion on constants is
`laurentInvQuotientRingEquiv_quotientMk_weightedC`. -/
@[simp]
theorem laurentInvQuotientRingEquiv_quotientMk_weightedX (i : Fin 1) :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    laurentInvQuotientRingEquiv P f S h1 hcl
        (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
      ((IsLocalization.Away.invSelf f : S) : UniformSpace.Completion S) :=
  ((exists_ringEquiv_laurentInvQuotient P f S h1 hcl).choose_spec.2.1 i).trans
    (congrArg _ (divBy_one f))

/-- **The inverse identification on `A`**: it sends the image of `a` in `A⟨{1}/f⟩` to the class of
the constant `a`. Use it with `rw`: `simp` first rewrites `toCompletionLoc` by
`toCompletionLoc_apply`, so the left-hand side is not in simp normal form. -/
theorem laurentInvQuotientRingEquiv_symm_toCompletionLoc (a : A) :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    (laurentInvQuotientRingEquiv P f S h1 hcl).symm (toCompletionLoc P {1} f S h1 a) =
      Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a) :=
  (exists_ringEquiv_laurentInvQuotient P f S h1 hcl).choose_spec.2.2.1 a

/-- The identification `A⟨X⟩ ⧸ (1 - f X) ≃+* A⟨{1}/f⟩` is continuous. With
`continuous_laurentInvQuotientRingEquiv_symm` this makes it an isomorphism of topological rings. -/
theorem continuous_laurentInvQuotientRingEquiv :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    Continuous (laurentInvQuotientRingEquiv P f S h1 hcl) :=
  (exists_ringEquiv_laurentInvQuotient P f S h1 hcl).choose_spec.2.2.2.1

/-- The inverse of the identification `A⟨X⟩ ⧸ (1 - f X) ≃+* A⟨{1}/f⟩` is continuous. With
`continuous_laurentInvQuotientRingEquiv` this makes it an isomorphism of topological rings. -/
theorem continuous_laurentInvQuotientRingEquiv_symm :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    Continuous (laurentInvQuotientRingEquiv P f S h1 hcl).symm :=
  (exists_ringEquiv_laurentInvQuotient P f S h1 hcl).choose_spec.2.2.2.2

end Identification

end PairOfDefinition

end TauCeti.Huber

end
