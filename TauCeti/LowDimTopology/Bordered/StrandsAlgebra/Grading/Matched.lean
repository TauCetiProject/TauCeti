/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched

/-!
# The grading of the algebra of a matching

The strands algebra `A(n)` is graded by the group `G'(n)`
(`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Basic`). Lipshitz, Ozsváth and Thurston
grade the algebra `A(Z)` of a pointed matched circle by restricting this grading: the generator
`a(ρ, h)`, the sum of the diagrams obtained from a diagram `ρ` without horizontal strands by adding
a horizontal strand at one point of each pair in `h`, has the grading `gr(ρ)` of `ρ`. This file
proves that this is well defined, and that the matched subalgebra is the sum of its homogeneous
parts.

The key fact is that **horizontal strands do not change the grading**: adding a horizontal strand
at a free point, or moving one, keeps the grading
(`TauCeti.StrandDiagram.grading_addHorizontal`, `TauCeti.StrandDiagram.grading_swapHorizontal`).
Hence every diagram has the grading of its strands that are not horizontal
(`TauCeti.StrandDiagram.grading_eraseHorizontal`), and diagrams differing in the positions of
their horizontal strands within matched classes have the same grading.

So the summands of a generator `a(ρ, h)` and of a matched completion sum all have the same
grading (`TauCeti.StrandsAlgebra.horizontalCompletion_mem_gradedPart`,
`TauCeti.StrandsAlgebra.matchedSum_mem_gradedPart`), the idempotents `I(s)` and the unit have
grading `1`, and since these sums span the matched subalgebra, it is the sum of its intersections
with the graded parts of the strands algebra, which are independent
(`TauCeti.StrandsAlgebra.iSup_matchedSubalgebra_inf_gradedPart`,
`TauCeti.StrandsAlgebra.iSupIndep_matchedSubalgebra_inf_gradedPart`). These intersections
multiply according to the group law and the differential has degree `λ⁻¹`, by the corresponding
properties of the graded parts of the strands algebra.

## Main results

* `TauCeti.StrandDiagram.grading_eraseHorizontal`: removing the horizontal strands does not
  change the grading.
* `TauCeti.StrandDiagram.grading_eq_of_matchedSetoid`: diagrams differing in the positions of their
  horizontal strands within matched classes have the same grading.
* `TauCeti.StrandsAlgebra.horizontalCompletion_mem_gradedPart`: `a(ρ, h)` has grading `gr(ρ)`.
* `TauCeti.StrandsAlgebra.matchedSum_mem_gradedPart`: a matched completion sum is homogeneous.
* `TauCeti.StrandsAlgebra.matchedIdem_mem_gradedPart`,
  `TauCeti.StrandsAlgebra.matchedOne_mem_gradedPart`: the idempotents `I(s)` and the unit
  `∑ₛ I(s)` have grading `1`.
* `TauCeti.StrandsAlgebra.iSup_matchedSubalgebra_inf_gradedPart`,
  `TauCeti.StrandsAlgebra.iSupIndep_matchedSubalgebra_inf_gradedPart`: the matched subalgebra is
  the sum of its homogeneous parts, which are independent.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.3.1 (the
  grading of `A(Z)` by `G'(4k)`).
-/

public section

open Finset

namespace TauCeti

namespace StrandDiagram

open StrandGradingGroup

variable {α : Type*} [LinearOrder α] [Fintype α] {φ : StrandDiagram α}

/-- **A diagram has the grading of its strands that are not horizontal.** -/
@[simp]
theorem grading_eraseHorizontal (φ : StrandDiagram α) :
    φ.eraseHorizontal.grading = φ.grading := by
  conv_rhs => rw [← φ.addHorizontal_eraseHorizontal_horizontals]
  rw [grading_addHorizontal (by simpa using sdiff_disjoint) (by simpa using sdiff_disjoint)]

/-- Diagrams differing only in the positions of their horizontal strands within matched classes
have the same grading. -/
theorem grading_eq_of_matchedSetoid {β : Type*} {M : α → β} {ψ : StrandDiagram α}
    (h : matchedSetoid M φ ψ) : φ.grading = ψ.grading :=
  apply_eq_of_matchedSetoid (fun φ a b _ ↦ grading_swapHorizontal φ a b) h

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram StrandGradingGroup

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] {M : α → β}

/-- **A matched completion sum is homogeneous**, of the grading of the diagram it completes. -/
theorem matchedSum_mem_gradedPart (φ : StrandDiagram α) :
    matchedSum R M φ ∈ gradedPart R φ.grading := by
  classical
  refine mem_gradedPart.2 fun ψ hψ ↦ ?_
  rw [Finsupp.mem_support_iff, repr_matchedSum_apply, ne_eq, ite_eq_right_iff, not_imp] at hψ
  exact (grading_eq_of_matchedSetoid hψ.1).symm

/-- **The grading of the matched subalgebra.** The matched subalgebra is the sum of its homogeneous
parts, its intersections with the graded parts of the strands algebra. -/
theorem iSup_matchedSubalgebra_inf_gradedPart :
    ⨆ g : StrandGradingGroup α, (matchedSubalgebra R M).toSubmodule ⊓ gradedPart R g =
      (matchedSubalgebra R M).toSubmodule := by
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun x hx ↦ ?_
  rw [← span_matchedSum] at hx
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨φ, ⟨hS, hT⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem φ.grading
    ⟨matchedSum_mem_matchedSubalgebra hS hT, matchedSum_mem_gradedPart φ⟩

/-- The homogeneous parts of the matched subalgebra of different gradings are independent. -/
theorem iSupIndep_matchedSubalgebra_inf_gradedPart :
    iSupIndep fun g : StrandGradingGroup α ↦
      (matchedSubalgebra R M).toSubmodule ⊓ gradedPart R g :=
  iSupIndep_gradedPart.mono fun _ ↦ inf_le_right

variable [DecidableEq β]

/-- **The generator `a(ρ, h)` has the grading of `ρ`**, when the pairs of `h` avoid those of the
starting and end points of `ρ`: each of its summands is `ρ` with horizontal strands added. -/
theorem horizontalCompletion_mem_gradedPart {ρ : StrandDiagram α} {h : Finset β}
    (hs : Disjoint (ρ.source.image M) h) (ht : Disjoint (ρ.target.image M) h) :
    (horizontalCompletion M ρ h : StrandsAlgebra R α) ∈ gradedPart R ρ.grading := by
  rw [horizontalCompletion_def]
  refine Submodule.sum_mem _ fun U hU ↦ ?_
  have hUh := (mem_matchedChoices.1 hU).1.le
  rw [← grading_addHorizontal (disjoint_of_subset_right hUh hs).of_image_finset
    (disjoint_of_subset_right hUh ht).of_image_finset]
  exact of_mem_gradedPart _

/-- The idempotents `I(s)` have grading `1`. -/
theorem matchedIdem_mem_gradedPart (s : Finset β) :
    matchedIdem R M s ∈ gradedPart R 1 := by
  rw [matchedIdem_def]
  exact Submodule.sum_mem _ fun S _ ↦ idem_mem_gradedPart S

/-- The unit `∑ₛ I(s)` of the matched subalgebra has grading `1`. -/
theorem matchedOne_mem_gradedPart : matchedOne R M ∈ gradedPart R 1 := by
  rw [matchedOne_def]
  exact Submodule.sum_mem _ fun s _ ↦ matchedIdem_mem_gradedPart s

end StrandsAlgebra

end TauCeti
