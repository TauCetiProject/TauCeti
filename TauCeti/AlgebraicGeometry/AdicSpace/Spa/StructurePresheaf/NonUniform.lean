/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.NonUniform

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
Wedhorn's Theorem 8.28(b) applies to it. Uniformity fails because the class of `Xᵢ` is a
nonzero nilpotent that does not lie in the closure of zero; this is
`TauCeti.Huber.not_isUniform_quotient_span_weightedX_sq`, which needs only that `A` is a nonzero
Hausdorff Tate ring.

The example shows that the uniformity hypothesis of the Buzzard–Verberkmoes criterion is
sufficient but not necessary for sheafiness.

## Main results

* `TauCeti.Huber.isSheafyRing_quotient_span_weightedX_sq`: `A⟨X⟩ ⧸ (Xᵢ²)` is sheafy.

Strong noetherianness is `TauCeti.Huber.isStronglyNoetherian_quotient_span_weightedX_sq` in
`TauCeti.RingTheory.Huber.StronglyNoetherian`, and non-uniformity is
`TauCeti.Huber.not_isUniform_quotient_span_weightedX_sq` in
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.NonUniform`; the examples at the end of this
file combine all three for `K⟨X, Q⟩ ⧸ (Q²)`.

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
