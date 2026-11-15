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
Hence diagrams differing in the positions of their horizontal strands within matched classes have
the same grading.

The decomposition of the matched subalgebra holds for the parts `gradedPartBy R d` of any function
`d` on strand diagrams that is unchanged by moving a horizontal strand within a matched pair
(`TauCeti.StrandsAlgebra.matchedSum_mem_gradedPartBy`,
`TauCeti.StrandsAlgebra.iSup_matchedSubalgebra_inf_gradedPartBy`,
`TauCeti.StrandsAlgebra.iSupIndep_matchedSubalgebra_inf_gradedPartBy`), such as the grading and
the refined gradings of `TauCeti.MatchedGradingRefinement`; the results for `gradedPart` are its
instance for the grading.

So the summands of a generator `a(ρ, h)` and of a matched completion sum all have the same
grading (`TauCeti.StrandsAlgebra.horizontalCompletion_mem_gradedPart`,
`TauCeti.StrandsAlgebra.matchedSum_mem_gradedPart`), the idempotents `I(s)` and the unit have
grading `1`, and since these sums span the matched subalgebra, it is the sum of its intersections
with the graded parts of the strands algebra, which are independent
(`TauCeti.StrandsAlgebra.iSup_matchedSubalgebra_inf_gradedPart`,
`TauCeti.StrandsAlgebra.iSupIndep_matchedSubalgebra_inf_gradedPart`).

As parts of the unital differential algebra `matchedSubalgebra R M` itself, these intersections
are the graded parts `TauCeti.StrandsAlgebra.matchedGradedPart R M g` (and
`TauCeti.StrandsAlgebra.matchedGradedPartBy R M d g` for a function `d`). They multiply according
to the group law, the unit has grading `1` and the differential has degree `λ⁻¹`, by the
corresponding properties of the graded parts of the strands algebra, and over a ring the matched
subalgebra is their internal direct sum.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedGradedPartBy R M d g`: the elements of the matched subalgebra of
  degree `g` for a function `d` on strand diagrams.
* `TauCeti.StrandsAlgebra.matchedGradedPart R M g`: the elements of the matched subalgebra of
  grading `g`.

## Main results

* `TauCeti.StrandDiagram.grading_eq_of_matchedSetoid`: diagrams differing in the positions of their
  horizontal strands within matched classes have the same grading.
* `TauCeti.StrandsAlgebra.horizontalCompletion_mem_gradedPart`: `a(ρ, h)` has grading `gr(ρ)`.
* `TauCeti.StrandsAlgebra.matchedSum_mem_gradedPart`,
  `TauCeti.StrandsAlgebra.matchedSum_mem_gradedPart_iff`: a matched completion sum is homogeneous,
  of the grading of the diagram it completes.
* `TauCeti.StrandsAlgebra.matchedIdem_mem_gradedPart`,
  `TauCeti.StrandsAlgebra.matchedOne_mem_gradedPart`: the idempotents `I(s)` and the unit
  `∑ₛ I(s)` have grading `1`.
* `TauCeti.StrandsAlgebra.iSup_matchedSubalgebra_inf_gradedPart`,
  `TauCeti.StrandsAlgebra.iSupIndep_matchedSubalgebra_inf_gradedPart`: the matched subalgebra is
  the sum of its homogeneous parts, which are independent.
* `TauCeti.StrandsAlgebra.matchedSum_mem_gradedPartBy`,
  `TauCeti.StrandsAlgebra.matchedSum_mem_gradedPartBy_iff`,
  `TauCeti.StrandsAlgebra.iSup_matchedSubalgebra_inf_gradedPartBy`,
  `TauCeti.StrandsAlgebra.iSupIndep_matchedSubalgebra_inf_gradedPartBy`: the same for any function
  on strand diagrams unchanged by moving a horizontal strand within a matched pair.
* `TauCeti.StrandsAlgebra.one_mem_matchedGradedPart`,
  `TauCeti.StrandsAlgebra.mul_mem_matchedGradedPart`,
  `TauCeti.StrandsAlgebra.matchedDifferential_mem_matchedGradedPart`: the matched subalgebra is a
  graded differential algebra, with differential of degree `λ⁻¹`.
* `TauCeti.StrandsAlgebra.isInternal_matchedGradedPart`,
  `TauCeti.StrandsAlgebra.isInternal_matchedGradedPartBy`: over a ring, the matched subalgebra is
  the internal direct sum of its graded parts.

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

/-- Diagrams differing only in the positions of their horizontal strands within matched classes
have the same grading. -/
theorem grading_eq_of_matchedSetoid {β : Type*} {M : α → β} {ψ : StrandDiagram α}
    (h : matchedSetoid M φ ψ) : φ.grading = ψ.grading :=
  apply_eq_of_matchedSetoid (fun φ a b _ ↦ grading_swapHorizontal φ a b) h

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram StrandGradingGroup

variable {R α β G : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] {M : α → β}
  {d : StrandDiagram α → G}

/-- **A matched completion sum is homogeneous** for any function `d` on strand diagrams unchanged
by moving a horizontal strand within a matched pair, of the degree of the diagram it completes. -/
theorem matchedSum_mem_gradedPartBy
    (hd : ∀ φ a b, M a = M b → d (φ.swapHorizontal a b) = d φ) (φ : StrandDiagram α) :
    matchedSum R M φ ∈ gradedPartBy R d (d φ) := by
  classical
  refine mem_gradedPartBy.2 fun ψ hψ ↦ ?_
  rw [Finsupp.mem_support_iff, repr_matchedSum_apply, ne_eq, ite_eq_right_iff, not_imp] at hψ
  exact (apply_eq_of_matchedSetoid hd hψ.1).symm

/-- A matched completion sum lies in the part of degree `g` for a function `d` on strand diagrams
unchanged by moving a horizontal strand within a matched pair exactly when the diagram it completes
has degree `g`. -/
theorem matchedSum_mem_gradedPartBy_iff [Nontrivial R]
    (hd : ∀ φ a b, M a = M b → d (φ.swapHorizontal a b) = d φ) {φ : StrandDiagram α} {g : G} :
    matchedSum R M φ ∈ gradedPartBy R d g ↔ d φ = g := by
  classical
  refine ⟨fun h ↦ mem_gradedPartBy.1 h φ ?_, fun h ↦ h ▸ matchedSum_mem_gradedPartBy hd φ⟩
  rw [Finsupp.mem_support_iff, repr_matchedSum_apply, ite_eq_left ((matchedSetoid M).refl' φ)]
  exact one_ne_zero

/-- The matched subalgebra is the sum of its intersections with the parts `gradedPartBy R d g`, for
any function `d` on strand diagrams unchanged by moving a horizontal strand within a matched
pair. -/
theorem iSup_matchedSubalgebra_inf_gradedPartBy
    (hd : ∀ φ a b, M a = M b → d (φ.swapHorizontal a b) = d φ) :
    ⨆ g : G, (matchedSubalgebra R M).toSubmodule ⊓ gradedPartBy R d g =
      (matchedSubalgebra R M).toSubmodule := by
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun x hx ↦ ?_
  rw [← span_matchedSum] at hx
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨φ, ⟨hS, hT⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem (d φ)
    ⟨matchedSum_mem_matchedSubalgebra hS hT, matchedSum_mem_gradedPartBy hd φ⟩

/-- The intersections of the matched subalgebra with the parts `gradedPartBy R d g` of different
degrees are independent. -/
theorem iSupIndep_matchedSubalgebra_inf_gradedPartBy (d : StrandDiagram α → G) :
    iSupIndep fun g : G ↦ (matchedSubalgebra R M).toSubmodule ⊓ gradedPartBy R d g :=
  (iSupIndep_gradedPartBy d).mono fun _ ↦ inf_le_right

/-- **A matched completion sum is homogeneous**, of the grading of the diagram it completes. -/
theorem matchedSum_mem_gradedPart (φ : StrandDiagram α) :
    matchedSum R M φ ∈ gradedPart R φ.grading := by
  rw [gradedPart_eq_gradedPartBy]
  exact matchedSum_mem_gradedPartBy (fun φ a b _ ↦ grading_swapHorizontal φ a b) φ

/-- A matched completion sum has grading `g` exactly when the diagram it completes does. -/
@[simp]
theorem matchedSum_mem_gradedPart_iff [Nontrivial R] {φ : StrandDiagram α}
    {g : StrandGradingGroup α} : matchedSum R M φ ∈ gradedPart R g ↔ φ.grading = g := by
  rw [gradedPart_eq_gradedPartBy]
  exact matchedSum_mem_gradedPartBy_iff fun φ a b _ ↦ grading_swapHorizontal φ a b

/-- **The grading of the matched subalgebra.** The matched subalgebra is the sum of its homogeneous
parts, its intersections with the graded parts of the strands algebra. -/
theorem iSup_matchedSubalgebra_inf_gradedPart :
    ⨆ g : StrandGradingGroup α, (matchedSubalgebra R M).toSubmodule ⊓ gradedPart R g =
      (matchedSubalgebra R M).toSubmodule := by
  simp_rw [gradedPart_eq_gradedPartBy]
  exact iSup_matchedSubalgebra_inf_gradedPartBy fun φ a b _ ↦ grading_swapHorizontal φ a b

/-- The homogeneous parts of the matched subalgebra of different gradings are independent. -/
theorem iSupIndep_matchedSubalgebra_inf_gradedPart :
    iSupIndep fun g : StrandGradingGroup α ↦
      (matchedSubalgebra R M).toSubmodule ⊓ gradedPart R g := by
  simp_rw [gradedPart_eq_gradedPartBy]
  exact iSupIndep_matchedSubalgebra_inf_gradedPartBy grading

/-! ### The graded parts of the matched subalgebra -/

section MatchedGradedPart

variable (R M) in
/-- The part of the matched subalgebra of degree `g` for a function `d` on strand diagrams: its
elements lying in the part `gradedPartBy R d g` of the strands algebra. -/
noncomputable def matchedGradedPartBy (d : StrandDiagram α → G) (g : G) :
    Submodule R (matchedSubalgebra R M) :=
  (gradedPartBy R d g).comap (matchedSubalgebra R M).toSubmodule.subtype

@[simp]
theorem mem_matchedGradedPartBy {g : G} {x : matchedSubalgebra R M} :
    x ∈ matchedGradedPartBy R M d g ↔ (x : StrandsAlgebra R α) ∈ gradedPartBy R d g :=
  Iff.rfl

/-- If `d` is multiplicative on composable strand diagrams, the product of elements of the matched
subalgebra of degrees `g` and `h` for `d` has degree `g * h`. -/
theorem mul_mem_matchedGradedPartBy [Mul G]
    (hd : ∀ {φ ψ : StrandDiagram α}, φ.Composable ψ → d (φ.trans ψ) = d φ * d ψ)
    {g h : G} {x y : matchedSubalgebra R M}
    (hx : x ∈ matchedGradedPartBy R M d g) (hy : y ∈ matchedGradedPartBy R M d h) :
    x * y ∈ matchedGradedPartBy R M d (g * h) :=
  mul_mem_gradedPartBy hd hx hy

/-- If resolving any crossing of a strand diagram changes its degree for `d` by `f`, then the
differential of the matched subalgebra maps its part of degree `g` for `d` to its part of
degree `f g`. -/
theorem matchedDifferential_mem_matchedGradedPartBy {f : G → G}
    (hd : ∀ {φ : StrandDiagram α} {p : α × α}, p ∈ φ.resolvableInversions →
      d (φ.resolve p) = f (d φ))
    {g : G} {x : matchedSubalgebra R M} (hx : x ∈ matchedGradedPartBy R M d g) :
    matchedDifferential R M x ∈ matchedGradedPartBy R M d (f g) := by
  rw [mem_matchedGradedPartBy, coe_matchedDifferential]
  exact differential_mem_gradedPartBy hd hx

/-- The matched subalgebra is the sum of its parts of degree `g` for any function `d` on strand
diagrams unchanged by moving a horizontal strand within a matched pair. -/
theorem iSup_matchedGradedPartBy
    (hd : ∀ φ a b, M a = M b → d (φ.swapHorizontal a b) = d φ) :
    ⨆ g : G, matchedGradedPartBy R M d g = ⊤ := by
  refine Submodule.map_injective_of_injective
    (matchedSubalgebra R M).toSubmodule.injective_subtype ?_
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
  exact (iSup_congr fun g ↦ Submodule.map_comap_subtype _ (gradedPartBy R d g)).trans
    (iSup_matchedSubalgebra_inf_gradedPartBy hd)

/-- The parts of the matched subalgebra of different degrees for `d` are independent. -/
theorem iSupIndep_matchedGradedPartBy (d : StrandDiagram α → G) :
    iSupIndep (matchedGradedPartBy R M d) := by
  refine fun g ↦ Submodule.disjoint_def.2 fun x hx hx' ↦
    Subtype.ext (Submodule.disjoint_def.1 (iSupIndep_gradedPartBy d g) _ hx ?_)
  exact Submodule.mem_comap.1 (iSup₂_le (fun h hh ↦ Submodule.comap_mono
    (le_iSup₂ (f := fun h (_ : h ≠ g) ↦ gradedPartBy R d h) h hh)) hx')

/-- Over a ring, the matched subalgebra is the internal direct sum of its parts of degree `g` for
any function `d` on strand diagrams unchanged by moving a horizontal strand within a matched
pair. -/
theorem isInternal_matchedGradedPartBy {R : Type*} [CommRing R] [DecidableEq G]
    (hd : ∀ φ a b, M a = M b → d (φ.swapHorizontal a b) = d φ) :
    DirectSum.IsInternal (matchedGradedPartBy R M d) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_matchedGradedPartBy d)
    (iSup_matchedGradedPartBy hd)

variable (R M) in
/-- The part of the matched subalgebra of grading `g`: its elements lying in the part
`gradedPart R g` of the strands algebra. -/
noncomputable def matchedGradedPart (g : StrandGradingGroup α) :
    Submodule R (matchedSubalgebra R M) :=
  matchedGradedPartBy R M grading g

/-- The part of grading `g` of the matched subalgebra is its part of degree `g` for the function
`grading`. -/
theorem matchedGradedPart_eq_matchedGradedPartBy (g : StrandGradingGroup α) :
    matchedGradedPart R M g = matchedGradedPartBy R M grading g := by
  rw [matchedGradedPart]

@[simp]
theorem mem_matchedGradedPart {g : StrandGradingGroup α} {x : matchedSubalgebra R M} :
    x ∈ matchedGradedPart R M g ↔ (x : StrandsAlgebra R α) ∈ gradedPart R g := by
  rw [matchedGradedPart_eq_matchedGradedPartBy, gradedPart_eq_gradedPartBy,
    mem_matchedGradedPartBy]

/-- **The matched subalgebra is graded by the grading group**: the product of elements of
gradings `g` and `h` has grading `g * h`. -/
theorem mul_mem_matchedGradedPart {g h : StrandGradingGroup α} {x y : matchedSubalgebra R M}
    (hx : x ∈ matchedGradedPart R M g) (hy : y ∈ matchedGradedPart R M h) :
    x * y ∈ matchedGradedPart R M (g * h) :=
  mul_mem_matchedGradedPartBy grading_trans hx hy

/-- **The differential of the matched subalgebra has degree `λ⁻¹`**: it maps the part of grading
`g` to the part of grading `λ⁻¹ g`. -/
theorem matchedDifferential_mem_matchedGradedPart {g : StrandGradingGroup α}
    {x : matchedSubalgebra R M} (hx : x ∈ matchedGradedPart R M g) :
    matchedDifferential R M x ∈ matchedGradedPart R M (lambda⁻¹ * g) :=
  matchedDifferential_mem_matchedGradedPartBy (f := (lambda⁻¹ * ·)) grading_resolve hx

/-- **The grading of the matched subalgebra**: it is the sum of its homogeneous parts. -/
theorem iSup_matchedGradedPart : ⨆ g : StrandGradingGroup α, matchedGradedPart R M g = ⊤ :=
  iSup_matchedGradedPartBy fun φ a b _ ↦ grading_swapHorizontal φ a b

/-- The parts of the matched subalgebra of different gradings are independent. -/
theorem iSupIndep_matchedGradedPart : iSupIndep (matchedGradedPart R M) :=
  iSupIndep_matchedGradedPartBy grading

/-- Over a ring, the matched subalgebra is the internal direct sum of its homogeneous parts. -/
theorem isInternal_matchedGradedPart {R : Type*} [CommRing R]
    [DecidableEq (StrandGradingGroup α)] : DirectSum.IsInternal (matchedGradedPart R M) :=
  isInternal_matchedGradedPartBy fun φ a b _ ↦ grading_swapHorizontal φ a b

end MatchedGradedPart

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

/-- The unit of the matched subalgebra has grading `1`. -/
theorem one_mem_matchedGradedPart :
    (1 : matchedSubalgebra R M) ∈ matchedGradedPart R M 1 :=
  mem_matchedGradedPart.2 matchedOne_mem_gradedPart

end StrandsAlgebra

end TauCeti
