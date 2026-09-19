/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

import TauCeti.RingTheory.Huber.LocalizationTopology.Quotient

/-!
# The Laurent quotient `A⟨X⟩ ⧸ (1 - f X)` is `A⟨{1}/f⟩`

For `f` in a Huber ring `A`, the rational subset `{|f| ≥ 1}` of `Spa A` has the single numerator `1`
over the denominator `f`, and Wedhorn's Example 6.38 presents its coordinate ring as a quotient of
the restricted power series ring,

```text
A⟨X⟩ ⧸ (1 - f X)  ≃  A⟨{1}/f⟩,
```

the variable going to `1/f`. This file is the one-variable case `k = 1` of
`TauCeti.RingTheory.Huber.LocalizationTopology.Quotient`, at the presentation `({1}, f)` with its
single numerator `1`. It names the relation ideal `(1 - f X)` and records the identification, as an
isomorphism of topological rings compatible with the structure maps from `A`, for a complete `A`
whose ideal `(1 - f X)` is closed; the other hypotheses of
`TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv` always hold for this presentation.

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

## Implementation notes

The numerator is listed by the constant family `fun _ : Fin 1 ↦ 1` rather than by `![1]`: its
value at an arbitrary index is `1` by beta reduction, where `![1] i` needs a rewrite. The two
families are equal but not definitionally equal, so `TauCeti.Huber.rationalRelationIdeal ![1] f`
agrees with `laurentInvRelationIdeal f` only after rewriting along that equality.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.38, Remark 7.55 and
  the proof of Proposition 8.30.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB` @ `37bbdaeb9`, Apache-2.0) proves this identification as
`example638Minus_equiv`, `B⟨X⟩ ⧸ (1 - b X) ≃+* presheafValue (trivialMinusDatum P b)`, over its own
`TateAlgebra` and `presheafValue`. Here it is specialised from the `k`-variable identification of
`TauCeti.RingTheory.Huber.LocalizationTopology.Quotient`, which credits that source; no AINTLIB
code is copied.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

section RelationIdeal

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The relation ideal `(1 - f X)`** of `A⟨X⟩`, the ring of restricted power series in one
variable (the weighted restricted series with weight `{1}`): the ideal
`TauCeti.Huber.rationalRelationIdeal` at the single numerator `1` over the denominator `f`. In the
quotient the class of `X` is an inverse of the class of `f`
(`laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX`).
`PairOfDefinition.laurentInvQuotientRingEquiv` identifies the quotient with `A⟨{1}/f⟩`. -/
noncomputable def laurentInvRelationIdeal (f : A) : Ideal (weightedRestrictedSubring
    (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
  rationalRelationIdeal (fun _ ↦ 1) f

/-- `laurentInvRelationIdeal f` is the span of `1 - f X`. The definition's body is not exposed
across module boundaries, so rewrite with this lemma to reach the generator; for computing in the
quotient, `laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX` is usually more direct. -/
theorem laurentInvRelationIdeal_def (f : A) : laurentInvRelationIdeal f = Ideal.span
    {1 - weightedC _ isWeightFamily_one_weight f * weightedX _ isWeightFamily_one_weight 0} := by
  simp [laurentInvRelationIdeal, rationalRelationIdeal_def, Set.range_unique]

/-- **The relation the ideal imposes**: in `A⟨X⟩ ⧸ (1 - f X)` the class of the constant `f` times
the class of the variable `X` is `1`, so the class of `f` is a unit with inverse the class of `X`
(`IsUnit.of_mul_eq_one`, `Units.inv_eq_of_mul_eq_one_right`). `simp` rewrites this product only
with the class of `f` on the left; for the other order, rewrite with `mul_comm` first. -/
@[simp]
theorem laurentInvRelationIdeal_quotientMk_weightedC_mul_weightedX (f : A) :
    Ideal.Quotient.mk (laurentInvRelationIdeal f) (weightedC _ isWeightFamily_one_weight f) *
        Ideal.Quotient.mk (laurentInvRelationIdeal f) (weightedX _ isWeightFamily_one_weight 0) =
      1 := by
  rw [laurentInvRelationIdeal, rationalRelationIdeal_quotientMk_weightedC_mul_weightedX, map_one,
    map_one]

end RelationIdeal

namespace PairOfDefinition

section Hypotheses

variable {A : Type*} [CommRing A] (f : A)

-- The hypotheses of `rationalQuotientRingEquiv` for the single numerator `1` of `{1}` over `f`:
-- `1` lies in `{1}` and is its only element, and `f` and `1` generate the unit ideal.
private theorem one_mem_singleton_one : ∀ _ : Fin 1, (1 : A) ∈ ({1} : Finset A) :=
  fun _ ↦ Finset.mem_singleton_self 1

private theorem eq_or_mem_range_one :
    ∀ u ∈ ({1} : Finset A), u = f ∨ u ∈ Set.range fun _ : Fin 1 ↦ (1 : A) := by
  simp

private theorem span_insert_singleton_one :
    Ideal.span (insert f (({1} : Finset A) : Set A)) = ⊤ := by
  simp [Ideal.span_insert]

end Hypotheses

section Identification

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] (P : PairOfDefinition A) (f : A) (S : Type*) [CommRing S]
  [Algebra A S] [IsLocalization.Away f S] (h1 : HasDenominatorPower P {1} f S)
  (hcl : IsClosed (laurentInvRelationIdeal f : Set (weightedRestrictedSubring
    (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight)))

/-- **Wedhorn's Example 6.38 at `{|f| ≥ 1}`**: over a complete Huber ring `A`, when the ideal
`(1 - f X)` of `A⟨X⟩` is closed, the ring isomorphism

```text
A⟨X⟩ ⧸ (1 - f X)  ≃  A⟨{1}/f⟩
```

that is the structure map from `A` on constants and sends `X` to `1/f`. It is
`TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv` at `T = {1}` with the single numerator
`1`, for which only the closedness hypothesis `hcl` remains. For instance, `hcl` holds when `A` is
a separated strongly noetherian Tate ring, by `TauCeti.Huber.isClosed_of_isNoetherian`. -/
noncomputable def laurentInvQuotientRingEquiv :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      laurentInvRelationIdeal f) ≃+* UniformSpace.Completion S :=
  rationalQuotientRingEquiv P {1} f S h1 (fun _ ↦ 1) one_mem_singleton_one (eq_or_mem_range_one f)
    (span_insert_singleton_one f) hcl

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
  rationalQuotientRingEquiv_quotientMk_weightedC P {1} f S h1 (fun _ ↦ 1) one_mem_singleton_one
    (eq_or_mem_range_one f) (span_insert_singleton_one f) hcl a

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
  divBy_one (S := S) f ▸ rationalQuotientRingEquiv_quotientMk_weightedX P {1} f S h1 (fun _ ↦ 1)
    one_mem_singleton_one (eq_or_mem_range_one f) (span_insert_singleton_one f) hcl i

/-- **The inverse identification on `A`**: it sends the image of `a` in `A⟨{1}/f⟩` to the class of
the constant `a`. Use it with `rw`: `simp` first rewrites `toCompletionLoc` by
`toCompletionLoc_apply`, so the left-hand side is not in simp normal form. -/
theorem laurentInvQuotientRingEquiv_symm_toCompletionLoc (a : A) :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    (laurentInvQuotientRingEquiv P f S h1 hcl).symm (toCompletionLoc P {1} f S h1 a) =
      Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a) :=
  rationalQuotientRingEquiv_symm_toCompletionLoc P {1} f S h1 (fun _ ↦ 1) one_mem_singleton_one
    (eq_or_mem_range_one f) (span_insert_singleton_one f) hcl a

/-- The identification `A⟨X⟩ ⧸ (1 - f X) ≃+* A⟨{1}/f⟩` is continuous. With
`continuous_laurentInvQuotientRingEquiv_symm` this makes it an isomorphism of topological rings. -/
theorem continuous_laurentInvQuotientRingEquiv :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    Continuous (laurentInvQuotientRingEquiv P f S h1 hcl) :=
  continuous_rationalQuotientRingEquiv P {1} f S h1 (fun _ ↦ 1) one_mem_singleton_one
    (eq_or_mem_range_one f) (span_insert_singleton_one f) hcl

/-- The inverse of the identification `A⟨X⟩ ⧸ (1 - f X) ≃+* A⟨{1}/f⟩` is continuous. With
`continuous_laurentInvQuotientRingEquiv` this makes it an isomorphism of topological rings. -/
theorem continuous_laurentInvQuotientRingEquiv_symm :
    letI := locUniformSpace P {1} f S h1
    letI := isUniformAddGroup_locUniformSpace P {1} f S h1
    letI := isTopologicalRing_locUniformSpace P {1} f S h1
    Continuous (laurentInvQuotientRingEquiv P f S h1 hcl).symm :=
  continuous_rationalQuotientRingEquiv_symm P {1} f S h1 (fun _ ↦ 1) one_mem_singleton_one
    (eq_or_mem_range_one f) (span_insert_singleton_one f) hcl

end Identification

end PairOfDefinition

end TauCeti.Huber

end
