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

The key fact is that **horizontal strands do not change the grading**
(`TauCeti.StrandDiagram.grading_addHorizontal`). The classes of `φ : S → T` and of `φ` with a
horizontal strand added at a point `p` have the same boundary `T - S`. A horizontal strand at `p`
crosses exactly the strands passing over `p`, so it adds to the number of crossings the number of
these strands. This number is the multiplicity at `p` of the class of `φ`
(`TauCeti.StrandDiagram.pointMultiplicity_boundary_eq_crossingCount`), which is what the new
starting point `p` adds to the correction term `m([φ], S)`. Hence every diagram has the grading of
its strands that are not horizontal (`TauCeti.StrandDiagram.grading_eraseHorizontal`), and moving
a horizontal strand keeps the grading (`TauCeti.StrandDiagram.grading_swapHorizontal`).

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

* `TauCeti.StrandDiagram.pointMultiplicity_boundary_eq_crossingCount`: at a point where no strand
  other than a horizontal one starts or ends, the multiplicity of the class of a diagram is the
  number of strands passing over the point.
* `TauCeti.StrandDiagram.grading_addHorizontal`, `TauCeti.StrandDiagram.grading_eraseHorizontal`,
  `TauCeti.StrandDiagram.grading_swapHorizontal`: adding, removing or moving horizontal strands
  does not change the grading.
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

variable {α : Type*} [LinearOrder α] [Fintype α] {φ : StrandDiagram α} {p : α}

/-- At a point `p` where every strand starting or ending is horizontal, the multiplicity of the
class of `φ` is the number of strands of `φ` crossing a horizontal strand at `p`: the strands
passing just below `p` and just above `p` are both the strands passing over `p`. -/
theorem pointMultiplicity_boundary_eq_crossingCount (hs : ∀ y ∈ φ p, y = p)
    (ht : ∀ x, p ∈ φ x → x = p) :
    pointMultiplicity p φ.boundary = φ.crossingCount p := by
  have h₁ : ({s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} : Finset α) =
      {x ∈ φ.source | x < p ∧ p < φ.endpoint x} := by
    refine filter_congr fun x hx ↦ and_congr_right fun hxp ↦ ?_
    rw [← endpoint_def]
    refine ⟨fun h ↦ h.lt_of_ne fun hpe ↦ hxp.ne (ht x ?_), le_of_lt⟩
    rw [hpe]
    exact endpoint_mem hx
  have h₂ : ({s ∈ φ.source | s ≤ p ∧ p < (φ s).getD s} : Finset α) =
      {x ∈ φ.source | x < p ∧ p < φ.endpoint x} := by
    refine filter_congr fun x hx ↦ ?_
    rw [← endpoint_def]
    refine ⟨fun h ↦ ⟨h.1.lt_of_ne fun hxp ↦ ?_, h.2⟩, fun h ↦ ⟨h.1.le, h.2⟩⟩
    subst hxp
    exact h.2.ne' (hs _ (endpoint_mem hx))
  rw [pointMultiplicity_boundary, h₁, h₂, crossingCount_def]
  ring

/-- Adding a horizontal strand at a point at which no strand starts or ends adds one crossing for
each strand passing over the point. -/
private theorem inversionCount_addHorizontal_singleton (hs : p ∉ φ.source) (ht : p ∉ φ.target) :
    (φ.addHorizontal {p}).inversionCount = φ.inversionCount + φ.crossingCount p := by
  have hT : Disjoint φ.target {p} := disjoint_singleton_right.2 ht
  have hsrc : (φ.addHorizontal {p}).source = insert p φ.source := by
    rw [source_addHorizontal hT, union_comm, insert_eq]
  have he (x : α) (hx : x ∈ φ.source) : (φ.addHorizontal {p}).endpoint x = φ.endpoint x := by
    rw [endpoint_def, endpoint_def, addHorizontal_apply_of_notMem hT]
    rintro hxp
    exact hs (mem_singleton.1 hxp ▸ hx)
  have hp : (φ.addHorizontal {p}).endpoint p = p := by
    rw [endpoint_def, addHorizontal_apply_of_mem φ (mem_singleton_self p), Option.getD_some]
  -- No strand starting above `p` ends below it.
  have h₀ : #{x ∈ φ.source | p < x ∧ (φ.addHorizontal {p}).endpoint x <
      (φ.addHorizontal {p}).endpoint p} = 0 := by
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun x hx ⟨hpx, hxp⟩ ↦ ?_)
    rw [he x hx, hp] at hxp
    exact (hpx.trans_le (φ.le_of_mem (endpoint_mem hx))).not_gt hxp
  rw [inversionCount_def, inversionCount_def, inversions_def, inversions_def, hsrc,
    card_inversions_insert _ hs, h₀, add_zero, inversions_congr he, crossingCount_def, hp]
  congr 2
  exact filter_congr fun x hx ↦ by rw [he x hx]

/-- Adding a horizontal strand at a point at which no strand starts or ends does not change the
grading. -/
private theorem grading_addHorizontal_singleton (hs : p ∉ φ.source) (ht : p ∉ φ.target) :
    (φ.addHorizontal {p}).grading = φ.grading := by
  have hsrc : (φ.addHorizontal {p}).source = insert p φ.source := by
    rw [source_addHorizontal (disjoint_singleton_right.2 ht), union_comm, insert_eq]
  have htgt : (φ.addHorizontal {p}).target = insert p φ.target := by
    rw [target_addHorizontal (disjoint_singleton_right.2 hs), union_comm, insert_eq]
  have hb : (φ.addHorizontal {p}).boundary = φ.boundary := by
    ext x
    rcases eq_or_ne x p with rfl | hxp
    · simp [boundary_apply, hsrc, htgt, hs, ht]
    · simp [boundary_apply, hsrc, htgt, hxp]
  have hm : pointMultiplicity p φ.boundary = φ.crossingCount p :=
    pointMultiplicity_boundary_eq_crossingCount
      (fun y hy ↦ absurd (mem_source.2 ⟨y, hy⟩) hs) fun x hx ↦ absurd (mem_target.2 ⟨x, hx⟩) ht
  ext
  · rw [grading_maslov, grading_maslov, inversionCount_addHorizontal_singleton hs ht, hsrc, hb,
      sum_insert hs, hm]
    push_cast
    ring
  · rw [grading_boundary, grading_boundary, hb]

/-- **Horizontal strands do not change the grading.** Adding horizontal strands to `ρ` at points
of `U` at which no strand of `ρ` starts or ends gives a diagram with the grading of `ρ`. -/
theorem grading_addHorizontal {ρ : StrandDiagram α} {U : Finset α} (hs : Disjoint ρ.source U)
    (ht : Disjoint ρ.target U) : (ρ.addHorizontal U).grading = ρ.grading := by
  induction U using Finset.induction_on with
  | empty => rw [addHorizontal_empty]
  | insert a U haU ih =>
    rw [disjoint_insert_right] at hs ht
    rw [insert_eq, union_comm, ← addHorizontal_addHorizontal,
      grading_addHorizontal_singleton (by simp [source_addHorizontal ht.2, hs.1, haU])
        (by simp [target_addHorizontal hs.2, ht.1, haU]), ih hs.2 ht.2]

/-- **A diagram has the grading of its strands that are not horizontal.** -/
@[simp]
theorem grading_eraseHorizontal (φ : StrandDiagram α) :
    φ.eraseHorizontal.grading = φ.grading := by
  conv_rhs => rw [← φ.addHorizontal_eraseHorizontal_horizontals]
  rw [grading_addHorizontal (by simpa using sdiff_disjoint) (by simpa using sdiff_disjoint)]

/-- **Moving a horizontal strand does not change the grading.** -/
@[simp]
theorem grading_swapHorizontal (φ : StrandDiagram α) (a b : α) :
    (φ.swapHorizontal a b).grading = φ.grading := by
  rw [← grading_eraseHorizontal, eraseHorizontal_swapHorizontal, grading_eraseHorizontal]

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
