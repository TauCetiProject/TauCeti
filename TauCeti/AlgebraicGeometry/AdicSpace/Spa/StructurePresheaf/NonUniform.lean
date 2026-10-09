/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable

/-!
# A sheafy Tate ring that is not uniform

Let `A` be a nonzero complete Hausdorff strongly noetherian Tate ring, for instance a complete
nonarchimedean field `K`, and let `A⟨X₁, …, Xₖ⟩` be the ring of restricted power series over it.
For each variable `Xᵢ` the quotient

```text
A⟨X₁, …, Xₖ⟩ ⧸ (Xᵢ²)
```

is strongly noetherian and sheafy, but it is not uniform. Over a field and with two variables
`X, Q` this is the ring `K⟨X, Q⟩ ⧸ (Q²)`.

Strong noetherianness and sheafiness hold because the ideal `(Xᵢ²)` is closed, as is every ideal
of `A⟨X₁, …, Xₖ⟩`, so the quotient is again a complete Hausdorff strongly noetherian Tate ring and
Wedhorn's Theorem 8.28(b) applies to it. Uniformity fails because the class of `Xᵢ` is
nilpotent, while in a uniform Tate ring every nilpotent lies in the closure of zero
(`TauCeti.Huber.IsUniform.nilradical_le_closure_bot`): every rescaling `ϖ⁻ⁿ Xᵢ` is nilpotent,
hence power-bounded. But the coefficient of the monomial `Xᵢ` is continuous and vanishes on
`(Xᵢ²)`, so `Xᵢ` is not in the closure of `(Xᵢ²)`. This part needs only that `A` is a nonzero
Hausdorff Tate ring.

The example shows that the uniformity hypothesis of the Buzzard–Verberkmoes criterion is
sufficient but not necessary for sheafiness.

## Main results

* `TauCeti.Huber.isStronglyNoetherian_quotient_span_weightedX_sq`: `A⟨X⟩ ⧸ (Xᵢ²)` is strongly
  noetherian.
* `TauCeti.Huber.isSheafyRing_quotient_span_weightedX_sq`: `A⟨X⟩ ⧸ (Xᵢ²)` is sheafy.
* `TauCeti.Huber.not_isUniform_quotient_span_weightedX_sq`: `A⟨X⟩ ⧸ (Xᵢ²)` is not uniform for
  every nonzero Hausdorff Tate ring `A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 8.28(b).
* D. Hansen, K. S. Kedlaya, *Sheafiness criteria for Huber rings*, Definition 2.3.
* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018).
-/

public section

namespace TauCeti.Huber

section Sheafy

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [IsStronglyNoetherian A] [CompleteSpace A] [T0Space A] {k : ℕ}

/-- **`A⟨X₁, …, Xₖ⟩ ⧸ (Xᵢ²)` is strongly noetherian** over a complete Hausdorff strongly
noetherian Tate ring `A`, since every ideal of `A⟨X₁, …, Xₖ⟩` is closed. -/
theorem isStronglyNoetherian_quotient_span_weightedX_sq (i : Fin k) :
    IsStronglyNoetherian (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2}) :=
  IsStronglyNoetherian.quotient _ (Ideal.isClosed_weightedRestrictedSubring_one_weight _)

/-- **`A⟨X₁, …, Xₖ⟩ ⧸ (Xᵢ²)` is sheafy** over a complete Hausdorff strongly noetherian Tate ring
`A`, with the quotient topology and the uniformity of that additive topological group. -/
theorem isSheafyRing_quotient_span_weightedX_sq (i : Fin k) :
    letI := IsTopologicalAddGroup.rightUniformSpace (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2})
    haveI : IsUniformAddGroup (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2}) :=
      isUniformAddGroup_of_addCommGroup
    IsSheafyRing (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2}) :=
  isSheafyRing_quotient_of_isStronglyNoetherian _
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _)

end Sheafy

section NonUniform

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [T0Space A] {k : ℕ}

/-- Every element of `closure (Xᵢ²)` in `A⟨X₁, …, Xₖ⟩` has zero coefficient at the monomial
`Xᵢ`: every multiple of `Xᵢ²` does, and that coefficient is continuous with closed zero set. -/
private theorem coeff_single_eq_zero_of_mem_closure_span_weightedX_sq (i : Fin k)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hf : f ∈ closure (Ideal.span
      {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2} : Set _)) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f : MvPowerSeries (Fin k) A) = 0 := by
  refine closure_minimal (fun g hg ↦ ?_) (isClosed_singleton.preimage
    (continuous_coeff_one_weight (Finsupp.single i 1))) hf
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hg
  simp [coe_weightedX, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial]

/-- **`A⟨X₁, …, Xₖ⟩ ⧸ (Xᵢ²)` is not uniform** over a nonzero Hausdorff Tate ring `A`. The class
of `Xᵢ` is nilpotent, so in a uniform Tate ring it would lie in the closure of zero; but every
element of the closure of `(Xᵢ²)` has zero coefficient at `Xᵢ`. -/
theorem not_isUniform_quotient_span_weightedX_sq [Nontrivial A] (i : Fin k) :
    ¬ IsUniform (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ⧸
        Ideal.span
          {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2}) := by
  intro h
  set J := Ideal.span {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2}
  have hX : Ideal.Quotient.mk J (weightedX _ isWeightFamily_one_weight i) ∈
      (⊥ : Ideal _).closure := h.nilradical_le_closure_bot (mem_nilradical.mpr ⟨2, by
    rw [← map_pow (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl⟩)
  rw [← SetLike.mem_coe, Ideal.coe_closure, Submodule.bot_coe, ← Set.mem_preimage,
    (QuotientRing.isOpenQuotientMap_mk J).isOpenMap.preimage_closure_eq_closure_preimage
      continuous_quot_mk] at hX
  have := coeff_single_eq_zero_of_mem_closure_span_weightedX_sq i
    (closure_mono (fun _ ↦ Ideal.Quotient.eq_zero_iff_mem.mp) hX)
  simp [coe_weightedX, MvPowerSeries.coeff_X] at this

end NonUniform

/-! ### The ring `K⟨X, Q⟩ ⧸ (Q²)`

Over a complete nontrivially normed field `K` with an ultrametric norm, a complete rank-one
nonarchimedean field, every hypothesis above is supplied by instances. With two variables
`X = X₀` and `Q = X₁` this is the ring `K⟨X, Q⟩ ⧸ (Q²)`. -/

example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    IsStronglyNoetherian (weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set K))
      isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin 2 ↦ ({1} : Set K)) isWeightFamily_one_weight 1 ^ 2}) :=
  isStronglyNoetherian_quotient_span_weightedX_sq 1

example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    letI := IsTopologicalAddGroup.rightUniformSpace (weightedRestrictedSubring
      (fun _ : Fin 2 ↦ ({1} : Set K)) isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin 2 ↦ ({1} : Set K)) isWeightFamily_one_weight 1 ^ 2})
    haveI : IsUniformAddGroup (weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set K))
      isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin 2 ↦ ({1} : Set K)) isWeightFamily_one_weight 1 ^ 2}) :=
      isUniformAddGroup_of_addCommGroup
    IsSheafyRing (weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set K))
      isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin 2 ↦ ({1} : Set K)) isWeightFamily_one_weight 1 ^ 2}) :=
  isSheafyRing_quotient_span_weightedX_sq 1

example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    ¬ IsUniform (weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set K))
      isWeightFamily_one_weight ⧸
        Ideal.span {weightedX (fun _ : Fin 2 ↦ ({1} : Set K)) isWeightFamily_one_weight 1 ^ 2}) :=
  not_isUniform_quotient_span_weightedX_sq 1

end TauCeti.Huber
