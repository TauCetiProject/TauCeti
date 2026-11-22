/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteSublattice
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
import Mathlib.Algebra.Order.Star.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The projection lattice and central support in von Neumann algebras

An orthogonal projection `U.starProjection` onto a closed subspace `U ≤ H` belongs to a concrete von
Neumann algebra `M` if and only if `U` is invariant under `M.commutant`
(`VonNeumannAlgebra.IsStarProjection.mem_iff`). Since `M.commutant` is closed under adjoints, its
invariant subspaces are closed under orthogonal complements, arbitrary intersections, and closed
linear spans (`VonNeumannAlgebra.starProjection_iInf_mem`,
`VonNeumannAlgebra.starProjection_topologicalClosure_iSup_mem`). Consequently, the closed subspaces
whose orthogonal projections lie in `M` form a complete sublattice
`VonNeumannAlgebra.Projection.closedProjectionSublattice M` of `ClosedSubmodule ℂ H`, and the
bundled star projections `M.Projection` inherit a complete ortholattice structure ordered by the
Loewner order — equivalently by inclusion of ranges:

* the meet `p ⊓ q` (and `⨅ i, p i`) is the orthogonal projection onto the intersection of ranges;
* the join `p ⊔ q` (and `⨆ i, p i`) is the orthogonal projection onto the closed linear span of
  ranges;
* the orthocomplement `pᶜ` is `1 - p`, projecting onto `(range p)ᗮ`, satisfying De Morgan's laws via
  the order isomorphism `VonNeumannAlgebra.Projection.complOrderIso`;
* inclusions `M ≤ N` induce order embeddings `VonNeumannAlgebra.Projection.inclusion hMN` preserving
  complements and all lattice operations;
* unitaries `u ∈ M` act as order automorphisms `VonNeumannAlgebra.Projection.unitaryConjOrderIso`
  preserving complements and central supports;
* monotone nets of projections converge strongly (pointwise on `H`, and in `H →Lₚₜ[ℂ] H`) to their
  supremum, and antitone nets converge strongly to their infimum
  (`VonNeumannAlgebra.Projection.tendsto_iSup_of_monotone`,
  `VonNeumannAlgebra.Projection.tendsto_toPointwiseConvergenceCLM_iSup_of_monotone`,
  `VonNeumannAlgebra.Projection.tendsto_iInf_of_antitone`,
  `VonNeumannAlgebra.Projection.tendsto_toPointwiseConvergenceCLM_iInf_of_antitone`).

In the center `M ⊓ M.commutant`, the **central support** `M.centralSupport a` of an operator
`a : H →L[ℂ] H` is the smallest central projection `z` satisfying `z * a = a`. For `a ∈ M`, we
identify `M.centralSupport a` geometrically as the orthogonal projection onto the closed span of
`{x (a ξ) | x ∈ M, ξ ∈ H}` (`VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`) and
deduce the **central-support kernel theorem**
(`VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`): for every
`y ∈ M.commutant`, `y * a = 0 ↔ y * M.centralSupport a = 0`.

## Main declarations

* `VonNeumannAlgebra.starProjection_iInf_mem`,
  `VonNeumannAlgebra.starProjection_topologicalClosure_iSup_mem`: lattice closure of orthogonal
  projections in `M`.
* `VonNeumannAlgebra.Projection`, `VonNeumannAlgebra.Projection.closedProjectionSublattice`,
  `VonNeumannAlgebra.Projection.closedRangeEquiv`,
  `VonNeumannAlgebra.Projection.closedRangeOrderIso`: bundled star projections in `M` and the
  complete-sublattice equivalence with invariant closed subspaces.
* `VonNeumannAlgebra.Projection.complOrderIso`: orthocomplementation as an order isomorphism
  `M.Projection ≃o M.Projectionᵒᵈ`, yielding binary, indexed, and set-indexed De Morgan laws.
* `VonNeumannAlgebra.Projection.inclusion`: order embedding `M.Projection ↪o N.Projection` for
  `M ≤ N`.
* `VonNeumannAlgebra.Projection.unitaryConjOrderIso`: unitary conjugation order automorphism on
  `M.Projection`.
* `VonNeumannAlgebra.Projection.tendsto_iSup_of_monotone`,
  `VonNeumannAlgebra.Projection.tendsto_toPointwiseConvergenceCLM_iSup_of_monotone`,
  `VonNeumannAlgebra.Projection.tendsto_iInf_of_antitone`,
  `VonNeumannAlgebra.Projection.tendsto_toPointwiseConvergenceCLM_iInf_of_antitone`: strong
  operator convergence of monotone and antitone families.
* `VonNeumannAlgebra.centralSupportProjection`, `VonNeumannAlgebra.centralSupport`: central support
  of an operator in `M`, unitary-conjugation invariance
  `VonNeumannAlgebra.centralSupport_unitary_conj`, its geometric span formula
  `VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`, and the kernel theorem
  `VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  §2.5, §5.5, and Proposition 5.5.2.
* M. Takesaki, *Theory of Operator Algebras I*, Proposition II.3.6 and Proposition V.1.6.
-/

public section

open Filter
open scoped Topology InnerProduct

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem toSubmodule_closure (s : Submodule ℂ H) :
    s.closure.toSubmodule = s.topologicalClosure :=
  SetLike.coe_injective <| by
    rw [ClosedSubmodule.coe_toSubmodule, Submodule.coe_closure, Submodule.topologicalClosure_coe]

/-! ### Invariant closed subspaces and orthogonal projections in `M` -/

section SubspaceProjections

/-- If a subspace `U` is invariant under `M.commutant`, then so is its orthogonal complement `Uᗮ`.
-/
theorem orthogonal_mem_invtSubmodule_commutant {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    (hU : ∀ y ∈ M.commutant, U ∈ Module.End.invtSubmodule y) :
    ∀ y ∈ M.commutant, Uᗮ ∈ Module.End.invtSubmodule y := by
  intro y hy
  have hstar : U ∈ Module.End.invtSubmodule (y†).toLinearMap := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hU (star y) (star_mem hy)
  exact y.orthogonal_mem_invtSubmodule hstar

/-- If `U.starProjection ∈ M`, then `Uᗮ.starProjection ∈ M`. -/
theorem starProjection_orthogonal_mem {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] (hU : U.starProjection ∈ M) :
    Uᗮ.starProjection ∈ M := by
  rw [U.starProjection_orthogonal']
  exact sub_mem (one_mem M) hU

/-- `Uᗮ.starProjection ∈ M` if and only if `U.starProjection ∈ M`. -/
@[simp]
theorem starProjection_orthogonal_mem_iff {M : VonNeumannAlgebra H} {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] :
    Uᗮ.starProjection ∈ M ↔ U.starProjection ∈ M :=
  ⟨fun h => by simpa only [Submodule.orthogonal_orthogonal] using starProjection_orthogonal_mem h,
    starProjection_orthogonal_mem⟩

/-- The orthogonal projection onto an intersection of closed subspaces whose projections lie in `M`
again lies in `M`. -/
theorem starProjection_iInf_mem {ι : Sort*} {M : VonNeumannAlgebra H} (U : ι → ClosedSubmodule ℂ H)
    (hU : ∀ i, (U i).toSubmodule.starProjection ∈ M) :
    (⨅ i, U i : ClosedSubmodule ℂ H).toSubmodule.starProjection ∈ M := by
  rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection,
    ClosedSubmodule.toSubmodule_iInf]
  intro y hy
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro ξ hξ
  rw [Submodule.mem_iInf] at hξ ⊢
  intro i
  have hi := (IsStarProjection.mem_iff isStarProjection_starProjection M).1 (hU i) y hy
  rw [Submodule.range_starProjection] at hi
  exact hi (hξ i)

/-- The orthogonal projection onto the closed span of a family of closed subspaces whose projections
lie in `M` again lies in `M`. -/
theorem starProjection_topologicalClosure_iSup_mem {ι : Sort*} {M : VonNeumannAlgebra H}
    (U : ι → ClosedSubmodule ℂ H) (hU : ∀ i, (U i).toSubmodule.starProjection ∈ M) :
    (⨆ i, U i : ClosedSubmodule ℂ H).toSubmodule.starProjection ∈ M := by
  rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection,
    ClosedSubmodule.toSubmodule_iSup, toSubmodule_closure]
  refine fun y hy => Submodule.topologicalClosure_mem_invtSubmodule ?_
  rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_iSup]
  refine iSup_le fun i => ?_
  have hi := (IsStarProjection.mem_iff isStarProjection_starProjection M).1 (hU i) y hy
  rw [Submodule.range_starProjection, Module.End.mem_invtSubmodule_iff_map_le] at hi
  exact hi.trans (le_iSup (fun j => (U j).toSubmodule) i)

end SubspaceProjections

/-! ### The complete ortholattice `VonNeumannAlgebra.Projection M` -/

/-- Bundled star projections belonging to a concrete von Neumann algebra `M`. -/
@[ext]
structure Projection (M : VonNeumannAlgebra H) where
  /-- The underlying bounded operator on `H`. -/
  val : H →L[ℂ] H
  /-- The operator is a star projection (`p * p = p` and `star p = p`). -/
  isStarProjection' : IsStarProjection val
  /-- The operator belongs to `M`. -/
  mem' : val ∈ M

attribute [coe] Projection.val

namespace Projection

variable {M : VonNeumannAlgebra H}

instance : CoeOut M.Projection (H →L[ℂ] H) := ⟨Projection.val⟩

@[simp]
theorem coe_mk (p : H →L[ℂ] H) (hp : IsStarProjection p) (hm : p ∈ M) :
    ((⟨p, hp, hm⟩ : M.Projection) : H →L[ℂ] H) = p :=
  (rfl)

@[simp, norm_cast]
theorem coe_inj {p q : M.Projection} : (p : H →L[ℂ] H) = q ↔ p = q :=
  ⟨Projection.ext, congrArg _⟩

theorem coe_injective : Function.Injective ((↑) : M.Projection → H →L[ℂ] H) :=
  fun _ _ => Projection.ext

@[simp]
theorem isStarProjection (p : M.Projection) : IsStarProjection (p : H →L[ℂ] H) :=
  p.isStarProjection'

@[simp]
theorem coe_mem (p : M.Projection) : (p : H →L[ℂ] H) ∈ M :=
  p.mem'

@[simp]
theorem mul_self (p : M.Projection) : (p : H →L[ℂ] H) * p = p :=
  p.isStarProjection.isIdempotentElem.eq

@[simp]
theorem star_coe (p : M.Projection) : star (p : H →L[ℂ] H) = p :=
  p.isStarProjection.isSelfAdjoint.star_eq

instance hasOrthogonalProjection_range (p : M.Projection) :
    (p : H →L[ℂ] H).range.HasOrthogonalProjection :=
  ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    p.isStarProjection.isIdempotentElem

/-- Every bundled projection in `M` is the orthogonal projection onto its range. -/
@[simp]
theorem starProjection_range (p : M.Projection) :
    (p : H →L[ℂ] H).range.starProjection = (p : H →L[ℂ] H) :=
  (isStarProjection_iff_eq_starProjection_range.1 p.isStarProjection).2.symm

/-- The range of `p : M.Projection` bundled as a `ClosedSubmodule ℂ H`. -/
def closedRange (p : M.Projection) : ClosedSubmodule ℂ H where
  toSubmodule := (p : H →L[ℂ] H).range
  isClosed' :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range p.isStarProjection.isIdempotentElem

@[simp]
theorem toSubmodule_closedRange (p : M.Projection) :
    p.closedRange.toSubmodule = (p : H →L[ℂ] H).range :=
  (rfl)

theorem starProjection_closedRange_mem (p : M.Projection) :
    p.closedRange.toSubmodule.starProjection ∈ M := by
  have h : p.closedRange.toSubmodule.starProjection = (p : H →L[ℂ] H) := by
    rw [← p.starProjection_range]
    exact Submodule.starProjection_inj.2 rfl
  rw [h]
  exact p.coe_mem

theorem closedRange_injective :
    Function.Injective (closedRange : M.Projection → ClosedSubmodule ℂ H) :=
  fun p q h => Projection.ext <| by
    rw [← p.starProjection_range, ← q.starProjection_range]
    exact Submodule.starProjection_inj.2 (congrArg ClosedSubmodule.toSubmodule h)

/-- Build a bundled projection in `M` from a closed subspace whose orthogonal projection lies in
`M`. -/
noncomputable def ofClosedSubmodule (U : ClosedSubmodule ℂ H)
    (hU : U.toSubmodule.starProjection ∈ M) : M.Projection where
  val := U.toSubmodule.starProjection
  isStarProjection' := isStarProjection_starProjection
  mem' := hU

@[simp]
theorem coe_ofClosedSubmodule (U : ClosedSubmodule ℂ H)
    (hU : U.toSubmodule.starProjection ∈ M) :
    (ofClosedSubmodule U hU : H →L[ℂ] H) = U.toSubmodule.starProjection :=
  (rfl)

@[simp]
theorem closedRange_ofClosedSubmodule (U : ClosedSubmodule ℂ H)
    (hU : U.toSubmodule.starProjection ∈ M) :
    (ofClosedSubmodule U hU).closedRange = U :=
  ClosedSubmodule.toSubmodule_injective (Submodule.range_starProjection U.toSubmodule)

/-- The complete sublattice of closed subspaces of `H` whose orthogonal projections belong to
`M`. -/
noncomputable def closedProjectionSublattice (M : VonNeumannAlgebra H) :
    CompleteSublattice (ClosedSubmodule ℂ H) :=
  CompleteSublattice.mk' {U : ClosedSubmodule ℂ H | U.toSubmodule.starProjection ∈ M}
    (fun S hS => by
      rw [Set.mem_ofPred_eq, sSup_eq_iSup']
      exact starProjection_topologicalClosure_iSup_mem _ fun U => hS U.property)
    (fun S hS => by
      rw [Set.mem_ofPred_eq, sInf_eq_iInf']
      exact starProjection_iInf_mem _ fun U => hS U.property)

@[simp]
theorem mem_closedProjectionSublattice {U : ClosedSubmodule ℂ H} :
    U ∈ closedProjectionSublattice M ↔ U.toSubmodule.starProjection ∈ M :=
  Iff.rfl

/-- Equivalence between `M.Projection` and `closedProjectionSublattice M`. -/
noncomputable def closedRangeEquiv (M : VonNeumannAlgebra H) :
    M.Projection ≃ closedProjectionSublattice M where
  toFun p := ⟨p.closedRange, mem_closedProjectionSublattice.2 p.starProjection_closedRange_mem⟩
  invFun U := ofClosedSubmodule U.val (mem_closedProjectionSublattice.1 U.property)
  left_inv p := Projection.ext <| by
    rw [coe_ofClosedSubmodule]
    exact (Submodule.starProjection_inj.2 rfl).trans p.starProjection_range
  right_inv U := Subtype.ext <| ClosedSubmodule.toSubmodule_injective <|
    Submodule.range_starProjection U.val.toSubmodule

noncomputable instance : CompleteLattice M.Projection :=
  (closedRangeEquiv M).completeLattice

/-- Order isomorphism between `M.Projection` and `closedProjectionSublattice M`. -/
noncomputable def closedRangeOrderIso (M : VonNeumannAlgebra H) :
    M.Projection ≃o closedProjectionSublattice M where
  toEquiv := closedRangeEquiv M
  map_rel_iff' := Iff.rfl

@[simp]
theorem closedRangeOrderIso_apply (p : M.Projection) :
    (closedRangeOrderIso M p : ClosedSubmodule ℂ H) = p.closedRange :=
  (rfl)

theorem le_iff_closedRange_le {p q : M.Projection} :
    p ≤ q ↔ p.closedRange ≤ q.closedRange :=
  Iff.rfl

theorem le_iff_range_le {p q : M.Projection} :
    p ≤ q ↔ (p : H →L[ℂ] H).range ≤ (q : H →L[ℂ] H).range :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe {p q : M.Projection} : (p : H →L[ℂ] H) ≤ q ↔ p ≤ q := by
  rw [le_iff_range_le, ← Submodule.starProjection_le_starProjection_iff, p.starProjection_range,
    q.starProjection_range]

theorem le_iff_mul_eq_right {p q : M.Projection} :
    p ≤ q ↔ (q : H →L[ℂ] H) * p = p := by
  rw [← coe_le_coe]
  exact p.isStarProjection.le_iff_mul_eq_right q.isStarProjection

theorem le_iff_mul_eq_left {p q : M.Projection} :
    p ≤ q ↔ (p : H →L[ℂ] H) * q = p := by
  rw [← coe_le_coe]
  exact p.isStarProjection.le_iff_mul_eq_left q.isStarProjection

@[simp]
theorem closedRange_bot : (⊥ : M.Projection).closedRange = ⊥ :=
  (congrArg Subtype.val (closedRangeOrderIso M).map_bot).trans CompleteSublattice.coe_bot

@[simp]
theorem closedRange_top : (⊤ : M.Projection).closedRange = ⊤ :=
  (congrArg Subtype.val (closedRangeOrderIso M).map_top).trans CompleteSublattice.coe_top

@[simp]
theorem closedRange_sup (p q : M.Projection) :
    (p ⊔ q).closedRange = p.closedRange ⊔ q.closedRange :=
  congrArg Subtype.val ((closedRangeOrderIso M).map_sup p q)

@[simp]
theorem closedRange_inf (p q : M.Projection) :
    (p ⊓ q).closedRange = p.closedRange ⊓ q.closedRange :=
  congrArg Subtype.val ((closedRangeOrderIso M).map_inf p q)

@[simp]
theorem closedRange_iSup {ι : Sort*} (p : ι → M.Projection) :
    (⨆ i, p i).closedRange = ⨆ i, (p i).closedRange :=
  (congrArg Subtype.val ((closedRangeOrderIso M).map_iSup p)).trans
    (CompleteSublattice.coe_iSup _)

@[simp]
theorem closedRange_iInf {ι : Sort*} (p : ι → M.Projection) :
    (⨅ i, p i).closedRange = ⨅ i, (p i).closedRange :=
  (congrArg Subtype.val ((closedRangeOrderIso M).map_iInf p)).trans
    (CompleteSublattice.coe_iInf _)

@[simp]
theorem closedRange_sSup (S : Set M.Projection) :
    (sSup S).closedRange = sSup (closedRange '' S) := by
  have h := congrArg Subtype.val ((closedRangeOrderIso M).map_sSup S)
  simpa only [sSup_image, closedRangeOrderIso_apply, CompleteSublattice.coe_iSup] using h

@[simp]
theorem closedRange_sInf (S : Set M.Projection) :
    (sInf S).closedRange = sInf (closedRange '' S) := by
  have h := congrArg Subtype.val ((closedRangeOrderIso M).map_sInf S)
  simpa only [sInf_image, closedRangeOrderIso_apply, CompleteSublattice.coe_iInf] using h

@[simp, norm_cast]
theorem coe_bot : ((⊥ : M.Projection) : H →L[ℂ] H) = 0 := by
  rw [← (⊥ : M.Projection).starProjection_range]
  exact (Submodule.starProjection_inj.2 (by
    rw [← toSubmodule_closedRange, closedRange_bot, ClosedSubmodule.toSubmodule_bot])).trans
    Submodule.starProjection_bot

@[simp, norm_cast]
theorem coe_top : ((⊤ : M.Projection) : H →L[ℂ] H) = 1 := by
  rw [← (⊤ : M.Projection).starProjection_range]
  exact (Submodule.starProjection_inj.2 (by
    rw [← toSubmodule_closedRange, closedRange_top, ClosedSubmodule.toSubmodule_top])).trans
    Submodule.starProjection_top'

/-- The meet of two projections in `M` is the orthogonal projection onto the intersection of their
closed ranges. -/
theorem coe_inf (p q : M.Projection) :
    ((p ⊓ q : M.Projection) : H →L[ℂ] H) =
      (p.closedRange ⊓ q.closedRange).toSubmodule.starProjection := by
  rw [← (p ⊓ q).starProjection_range]
  exact Submodule.starProjection_inj.2 (by rw [← toSubmodule_closedRange, closedRange_inf])

/-- The join of two projections in `M` is the orthogonal projection onto the closed span of their
ranges. -/
theorem coe_sup (p q : M.Projection) :
    ((p ⊔ q : M.Projection) : H →L[ℂ] H) =
      ((p : H →L[ℂ] H).range ⊔ (q : H →L[ℂ] H).range).topologicalClosure.starProjection := by
  rw [← (p ⊔ q).starProjection_range]
  refine Submodule.starProjection_inj.2 ?_
  rw [← toSubmodule_closedRange, closedRange_sup, ClosedSubmodule.toSubmodule_sup,
    toSubmodule_closure, toSubmodule_closedRange, toSubmodule_closedRange]

/-- The meet of an indexed family of projections in `M` is the orthogonal projection onto the
intersection of their closed ranges. -/
theorem coe_iInf {ι : Sort*} (p : ι → M.Projection) :
    ((⨅ i, p i : M.Projection) : H →L[ℂ] H) =
      (⨅ i, (p i).closedRange).toSubmodule.starProjection := by
  rw [← (⨅ i, p i).starProjection_range]
  exact Submodule.starProjection_inj.2 (by rw [← toSubmodule_closedRange, closedRange_iInf])

/-- The join of an indexed family of projections in `M` is the orthogonal projection onto the closed
span of their ranges. -/
theorem coe_iSup {ι : Sort*} (p : ι → M.Projection) :
    ((⨆ i, p i : M.Projection) : H →L[ℂ] H) =
      (⨆ i, (p i : H →L[ℂ] H).range).topologicalClosure.starProjection := by
  rw [← (⨆ i, p i).starProjection_range]
  refine Submodule.starProjection_inj.2 ?_
  simp only [← toSubmodule_closedRange, closedRange_iSup, ClosedSubmodule.toSubmodule_iSup,
    toSubmodule_closure]

/-! #### Orthocomplement and De Morgan's laws -/

instance : Compl M.Projection where
  compl p := ⟨1 - p, p.isStarProjection.one_sub, sub_mem (one_mem M) p.coe_mem⟩

@[simp, norm_cast]
theorem coe_compl (p : M.Projection) : ((pᶜ : M.Projection) : H →L[ℂ] H) = 1 - p :=
  (rfl)

@[simp]
theorem compl_compl (p : M.Projection) : pᶜᶜ = p :=
  Projection.ext (sub_sub_cancel 1 _)

theorem compl_injective : Function.Injective (Compl.compl : M.Projection → M.Projection) :=
  fun p q h => by rw [← compl_compl p, ← compl_compl q, h]

@[simp]
theorem closedRange_compl (p : M.Projection) : pᶜ.closedRange = p.closedRangeᗮ := by
  apply ClosedSubmodule.toSubmodule_injective
  have h : ((pᶜ : M.Projection) : H →L[ℂ] H) = (p : H →L[ℂ] H).rangeᗮ.starProjection := by
    rw [coe_compl, Submodule.starProjection_orthogonal', starProjection_range]
  rw [toSubmodule_closedRange, h, Submodule.range_starProjection]
  rfl

@[simp]
theorem compl_le_compl_iff {p q : M.Projection} : pᶜ ≤ qᶜ ↔ q ≤ p := by
  simp only [le_iff_closedRange_le, closedRange_compl]
  exact Submodule.orthogonal_le_orthogonal_iff

/-- Orthocomplementation as an order isomorphism `M.Projection ≃o M.Projectionᵒᵈ`. -/
noncomputable def complOrderIso (M : VonNeumannAlgebra H) :
    M.Projection ≃o M.Projectionᵒᵈ where
  toFun p := OrderDual.toDual pᶜ
  invFun p := (OrderDual.ofDual p)ᶜ
  left_inv := compl_compl
  right_inv p := by simp
  map_rel_iff' := compl_le_compl_iff

@[simp]
theorem complOrderIso_apply (M : VonNeumannAlgebra H) (p : M.Projection) :
    complOrderIso M p = OrderDual.toDual pᶜ :=
  (rfl)

/-- A projection `p` lies below `qᶜ` if and only if `p` and `q` have orthogonal ranges
(`p * q = 0`). -/
theorem le_compl_iff_mul_eq_zero {p q : M.Projection} :
    p ≤ qᶜ ↔ (p : H →L[ℂ] H) * q = 0 := by
  rw [le_iff_mul_eq_left, coe_compl, mul_sub, mul_one, sub_eq_self]

@[simp]
theorem compl_bot : (⊥ : M.Projection)ᶜ = ⊤ :=
  congrArg OrderDual.ofDual (complOrderIso M).map_bot

@[simp]
theorem compl_top : (⊤ : M.Projection)ᶜ = ⊥ :=
  congrArg OrderDual.ofDual (complOrderIso M).map_top

@[simp]
theorem compl_sup (p q : M.Projection) : (p ⊔ q)ᶜ = pᶜ ⊓ qᶜ :=
  congrArg OrderDual.ofDual ((complOrderIso M).map_sup p q)

@[simp]
theorem compl_inf (p q : M.Projection) : (p ⊓ q)ᶜ = pᶜ ⊔ qᶜ :=
  congrArg OrderDual.ofDual ((complOrderIso M).map_inf p q)

@[simp]
theorem compl_sSup (S : Set M.Projection) : (sSup S)ᶜ = sInf (Compl.compl '' S) := by
  simpa only [complOrderIso_apply, ofDual_iSup, OrderDual.ofDual_toDual, sInf_image] using
    congrArg OrderDual.ofDual ((complOrderIso M).map_sSup S)

@[simp]
theorem compl_sInf (S : Set M.Projection) : (sInf S)ᶜ = sSup (Compl.compl '' S) := by
  simpa only [complOrderIso_apply, ofDual_iInf, OrderDual.ofDual_toDual, sSup_image] using
    congrArg OrderDual.ofDual ((complOrderIso M).map_sInf S)

@[simp]
theorem compl_iSup {ι : Sort*} (p : ι → M.Projection) : (⨆ i, p i)ᶜ = ⨅ i, (p i)ᶜ := by
  simpa only [complOrderIso_apply, ofDual_iSup, OrderDual.ofDual_toDual] using
    congrArg OrderDual.ofDual ((complOrderIso M).map_iSup p)

@[simp]
theorem compl_iInf {ι : Sort*} (p : ι → M.Projection) : (⨅ i, p i)ᶜ = ⨆ i, (p i)ᶜ := by
  simpa only [complOrderIso_apply, ofDual_iInf, OrderDual.ofDual_toDual] using
    congrArg OrderDual.ofDual ((complOrderIso M).map_iInf p)

@[simp]
theorem inf_compl_eq_bot (p : M.Projection) : p ⊓ pᶜ = ⊥ :=
  closedRange_injective <| ClosedSubmodule.toSubmodule_injective <| by
    simp only [closedRange_inf, closedRange_compl, closedRange_bot, ClosedSubmodule.toSubmodule_inf,
      ClosedSubmodule.toSubmodule_bot]
    exact Submodule.inf_orthogonal_eq_bot _

@[simp]
theorem sup_compl_eq_top (p : M.Projection) : p ⊔ pᶜ = ⊤ := by
  apply compl_injective
  rw [compl_sup, compl_compl, compl_top, inf_comm, inf_compl_eq_bot]

/-! #### Inclusion along `M ≤ N` and unitary conjugation -/

/-- Transport of projections along an inclusion `M ≤ N` of von Neumann algebras, as an order
embedding. -/
def inclusion {M N : VonNeumannAlgebra H} (hMN : M ≤ N) : M.Projection ↪o N.Projection where
  toFun p := ⟨p, p.isStarProjection, hMN p.coe_mem⟩
  inj' _ _ h := Projection.ext (congrArg (fun q : N.Projection => (q : H →L[ℂ] H)) h)
  map_rel_iff' := by
    intro p q
    rw [← coe_le_coe, ← coe_le_coe]
    rfl

@[simp, norm_cast]
theorem coe_inclusion {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p : M.Projection) :
    (inclusion hMN p : H →L[ℂ] H) = p :=
  (rfl)

@[simp]
theorem closedRange_inclusion {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p : M.Projection) :
    (inclusion hMN p).closedRange = p.closedRange :=
  (rfl)

@[simp]
theorem inclusion_compl {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p : M.Projection) :
    inclusion hMN pᶜ = (inclusion hMN p)ᶜ :=
  (rfl)

@[simp]
theorem inclusion_bot {M N : VonNeumannAlgebra H} (hMN : M ≤ N) :
    inclusion hMN ⊥ = ⊥ :=
  closedRange_injective <| by simp

@[simp]
theorem inclusion_top {M N : VonNeumannAlgebra H} (hMN : M ≤ N) :
    inclusion hMN ⊤ = ⊤ :=
  closedRange_injective <| by simp

@[simp]
theorem inclusion_sup {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p q : M.Projection) :
    inclusion hMN (p ⊔ q) = inclusion hMN p ⊔ inclusion hMN q :=
  closedRange_injective <| by simp

@[simp]
theorem inclusion_inf {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p q : M.Projection) :
    inclusion hMN (p ⊓ q) = inclusion hMN p ⊓ inclusion hMN q :=
  closedRange_injective <| by simp

@[simp]
theorem inclusion_iSup {M N : VonNeumannAlgebra H} (hMN : M ≤ N) {ι : Sort*}
    (p : ι → M.Projection) :
    inclusion hMN (⨆ i, p i) = ⨆ i, inclusion hMN (p i) :=
  closedRange_injective <| by simp

@[simp]
theorem inclusion_iInf {M N : VonNeumannAlgebra H} (hMN : M ≤ N) {ι : Sort*}
    (p : ι → M.Projection) :
    inclusion hMN (⨅ i, p i) = ⨅ i, inclusion hMN (p i) :=
  closedRange_injective <| by simp

@[simp]
theorem inclusion_sSup {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (S : Set M.Projection) :
    inclusion hMN (sSup S) = sSup (inclusion hMN '' S) :=
  closedRange_injective <| by
    simp only [closedRange_inclusion, closedRange_sSup, Set.image_image]

@[simp]
theorem inclusion_sInf {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (S : Set M.Projection) :
    inclusion hMN (sInf S) = sInf (inclusion hMN '' S) :=
  closedRange_injective <| by
    simp only [closedRange_inclusion, closedRange_sInf, Set.image_image]

/-- Conjugation by a unitary operator `u ∈ M` as an order automorphism of `M.Projection`. -/
noncomputable def unitaryConjOrderIso {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) : M.Projection ≃o M.Projection where
  toFun p :=
    ⟨u * p * star u,
      p.isStarProjection.map (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) ⟨u, hu⟩),
      mul_mem (mul_mem huM p.coe_mem) (star_mem huM)⟩
  invFun p :=
    ⟨star u * p * u,
      p.isStarProjection.map (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) ⟨u, hu⟩).symm,
      mul_mem (mul_mem (star_mem huM) p.coe_mem) huM⟩
  left_inv p := Projection.ext <| by
    dsimp only
    rw [mul_assoc, mul_assoc, hu.1, mul_one, ← mul_assoc, hu.1, one_mul]
  right_inv p := Projection.ext <| by
    dsimp only
    rw [mul_assoc, mul_assoc, hu.2, mul_one, ← mul_assoc, hu.2, one_mul]
  map_rel_iff' {p q} := by
    let Φ := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) ⟨u, hu⟩
    rw [le_iff_mul_eq_left, le_iff_mul_eq_left]
    change (Φ p : H →L[ℂ] H) * Φ q = Φ p ↔ (p : H →L[ℂ] H) * q = p
    rw [← map_mul Φ]
    exact Φ.injective.eq_iff

@[simp]
theorem coe_unitaryConjOrderIso {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) (p : M.Projection) :
    (unitaryConjOrderIso huM hu p : H →L[ℂ] H) = u * p * star u :=
  (rfl)

@[simp]
theorem coe_unitaryConjOrderIso_symm {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) (p : M.Projection) :
    ((unitaryConjOrderIso huM hu).symm p : H →L[ℂ] H) = star u * p * u :=
  (rfl)

@[simp]
theorem unitaryConjOrderIso_compl {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) (p : M.Projection) :
    unitaryConjOrderIso huM hu pᶜ = (unitaryConjOrderIso huM hu p)ᶜ :=
  Projection.ext <| by
    simp only [coe_unitaryConjOrderIso, coe_compl, mul_sub, sub_mul, mul_one, hu.2]

/-! #### Strong operator convergence of monotone and antitone families -/

/-- **Monotone strong convergence of projections.** A monotone family of projections in `M`
converges strongly (pointwise on `H`) along `atTop` to its lattice supremum. -/
theorem tendsto_iSup_of_monotone {ι : Type*} [Preorder ι] {p : ι → M.Projection}
    (hp : Monotone p) (ξ : H) :
    Tendsto (fun i => (p i : H →L[ℂ] H) ξ) atTop
      (𝓝 (((⨆ i, p i : M.Projection) : H →L[ℂ] H) ξ)) := by
  have hU : Monotone (fun i => (p i : H →L[ℂ] H).range) :=
    fun _ _ hij => le_iff_range_le.1 (hp hij)
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun i => (p i : H →L[ℂ] H).range) hU ξ
  simpa only [starProjection_range, coe_iSup] using ht

/-- **Monotone strong-operator convergence of projections.** A monotone family of projections in
`M` converges in `H →Lₚₜ[ℂ] H` along `atTop` to its lattice supremum. -/
theorem tendsto_toPointwiseConvergenceCLM_iSup_of_monotone {ι : Type*} [Preorder ι]
    {p : ι → M.Projection} (hp : Monotone p) :
    Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (p i))
      atTop
      (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        ((⨆ i, p i : M.Projection) : H →L[ℂ] H))) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 (tendsto_iSup_of_monotone hp)

/-- **Antitone strong convergence of projections.** An antitone family of projections in `M`
converges strongly (pointwise on `H`) along `atTop` to its lattice infimum. -/
theorem tendsto_iInf_of_antitone {ι : Type*} [Preorder ι] {p : ι → M.Projection}
    (hp : Antitone p) (ξ : H) :
    Tendsto (fun i => (p i : H →L[ℂ] H) ξ) atTop
      (𝓝 (((⨅ i, p i : M.Projection) : H →L[ℂ] H) ξ)) := by
  have hpc : Monotone (fun i => (p i)ᶜ) := fun _ _ hij => compl_le_compl_iff.2 (hp hij)
  have ht := tendsto_const_nhds (x := ξ).sub (tendsto_iSup_of_monotone hpc ξ)
  rw [← compl_iInf] at ht
  have hsub : ∀ q : M.Projection, ξ - ((qᶜ : M.Projection) : H →L[ℂ] H) ξ = (q : H →L[ℂ] H) ξ :=
    fun q => by
      simp [coe_compl]
  simpa only [hsub] using ht

/-- **Antitone strong-operator convergence of projections.** An antitone family of projections in
`M` converges in `H →Lₚₜ[ℂ] H` along `atTop` to its lattice infimum. -/
theorem tendsto_toPointwiseConvergenceCLM_iInf_of_antitone {ι : Type*} [Preorder ι]
    {p : ι → M.Projection} (hp : Antitone p) :
    Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (p i))
      atTop
      (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        ((⨅ i, p i : M.Projection) : H →L[ℂ] H))) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 (tendsto_iInf_of_antitone hp)

end Projection

/-! ### Central support and the central-support kernel theorem -/

section CentralSupport

omit [CompleteSpace H] in
private theorem isIdempotentElem_mul_eq_right_iff {p a : H →L[ℂ] H}
    (hp : IsIdempotentElem p) : p * a = a ↔ a.range ≤ p.range := by
  rw [← ContinuousLinearMap.coe_inj, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.toLinearMap_comp]
  exact LinearMap.IsIdempotentElem.comp_eq_right_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp) a.toLinearMap

/-- The **central support** of `a : H →L[ℂ] H` relative to `M`, bundled as a projection in the
center `M ⊓ M.commutant`: the smallest central projection `z` satisfying `z * a = a`. -/
noncomputable def centralSupportProjection (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    (M ⊓ M.commutant).Projection :=
  sInf {z : (M ⊓ M.commutant).Projection | (z : H →L[ℂ] H) * a = a}

/-- The **central support** (or central carrier) `M.centralSupport a` of `a : H →L[ℂ] H` in `M`:
the smallest star projection in the center `M ⊓ M.commutant` fixing `a` on the left. -/
noncomputable def centralSupport (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  M.centralSupportProjection a

@[simp]
theorem coe_centralSupportProjection (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    (M.centralSupportProjection a : H →L[ℂ] H) = M.centralSupport a :=
  (rfl)

theorem isStarProjection_centralSupport (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    IsStarProjection (M.centralSupport a) :=
  (M.centralSupportProjection a).isStarProjection

theorem centralSupport_mem (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a ∈ M :=
  (mem_inf.1 (M.centralSupportProjection a).coe_mem).1

theorem centralSupport_mem_commutant (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a ∈ M.commutant :=
  (mem_inf.1 (M.centralSupportProjection a).coe_mem).2

@[simp]
theorem centralSupport_mul_self (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a * a = a := by
  have hid := (M.centralSupportProjection a).isStarProjection.isIdempotentElem
  rw [← coe_centralSupportProjection, isIdempotentElem_mul_eq_right_iff hid,
    ← Projection.toSubmodule_closedRange, centralSupportProjection, Projection.closedRange_sInf,
    sInf_image, ClosedSubmodule.toSubmodule_iInf]
  refine le_iInf fun z => ?_
  rw [ClosedSubmodule.toSubmodule_iInf]
  exact le_iInf fun hz =>
    (isIdempotentElem_mul_eq_right_iff z.isStarProjection.isIdempotentElem).1 hz

theorem mul_centralSupport_self {M : VonNeumannAlgebra H} {a : H →L[ℂ] H} (ha : a ∈ M) :
    a * M.centralSupport a = a := by
  rw [mem_commutant_iff.1 (M.centralSupport_mem_commutant a) a ha,
    M.centralSupport_mul_self a]

/-- Universal property of `M.centralSupportProjection`: a central projection `z` lies above
`M.centralSupportProjection a` if and only if `z * a = a`. -/
theorem centralSupportProjection_le_iff {M : VonNeumannAlgebra H} {a : H →L[ℂ] H}
    {z : (M ⊓ M.commutant).Projection} :
    M.centralSupportProjection a ≤ z ↔ (z : H →L[ℂ] H) * a = a :=
  ⟨fun h => (isIdempotentElem_mul_eq_right_iff z.isStarProjection.isIdempotentElem).2 <|
      ((isIdempotentElem_mul_eq_right_iff
        (M.isStarProjection_centralSupport a).isIdempotentElem).1
          (M.centralSupport_mul_self a)).trans (Projection.le_iff_range_le.1 h),
    fun hz => sInf_le hz⟩

/-- Universal property of `M.centralSupport`: for a central projection `z` of `M`,
`M.centralSupport a ≤ z ↔ z * a = a`. -/
theorem centralSupport_le_iff {M : VonNeumannAlgebra H} {a z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hzC : z ∈ M.commutant) :
    M.centralSupport a ≤ z ↔ z * a = a := by
  rw [← coe_centralSupportProjection,
    ← Projection.coe_mk z hz (mem_inf.2 ⟨hzM, hzC⟩), Projection.coe_le_coe]
  exact centralSupportProjection_le_iff

/-- Every star projection is bounded above by its central support. -/
theorem le_centralSupport {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    p ≤ M.centralSupport p :=
  (hp.le_iff_mul_eq_right (M.isStarProjection_centralSupport p)).2 (M.centralSupport_mul_self p)

/-- A central projection is equal to its own central support. -/
theorem centralSupport_eq_self_of_mem_commutant {M : VonNeumannAlgebra H} {z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hzC : z ∈ M.commutant) :
    M.centralSupport z = z :=
  le_antisymm ((centralSupport_le_iff hz hzM hzC).2 hz.isIdempotentElem.eq) (le_centralSupport hz)

@[simp]
theorem centralSupport_zero (M : VonNeumannAlgebra H) : M.centralSupport 0 = 0 :=
  le_antisymm
    ((centralSupport_le_iff (.zero _) (zero_mem M) (zero_mem M.commutant)).2 (zero_mul 0))
    (M.isStarProjection_centralSupport 0).nonneg

@[simp]
theorem centralSupport_one (M : VonNeumannAlgebra H) : M.centralSupport 1 = 1 :=
  centralSupport_eq_self_of_mem_commutant (.one _) (one_mem M) (one_mem M.commutant)

/-- Conjugating an operator by a unitary in `M` preserves its bundled central support. -/
@[simp]
theorem centralSupportProjection_unitary_conj {M : VonNeumannAlgebra H} {u a : H →L[ℂ] H}
    (huM : u ∈ M) (hu : u ∈ unitary (H →L[ℂ] H)) :
    M.centralSupportProjection (u * a * star u) = M.centralSupportProjection a := by
  unfold centralSupportProjection
  congr 1
  ext z
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  have hzu : (z : H →L[ℂ] H) * u = u * z :=
    (mem_commutant_iff.1 (mem_inf.1 z.coe_mem).2 u huM).symm
  have hconj : (z : H →L[ℂ] H) * (u * a * star u) = u * ((z : H →L[ℂ] H) * a) * star u := by
    simp only [← mul_assoc, hzu]
  rw [hconj]
  constructor
  · intro h
    have hu1 : ∀ x : H →L[ℂ] H, star u * (u * x * star u) * u = x := fun x => by
      rw [mul_assoc, mul_assoc, hu.1, mul_one, ← mul_assoc, hu.1, one_mul]
    simpa only [hu1] using congrArg (fun x => star u * x * u) h
  · intro h
    rw [h]

/-- Conjugating an operator by a unitary in `M` preserves its central support. -/
@[simp]
theorem centralSupport_unitary_conj {M : VonNeumannAlgebra H} {u a : H →L[ℂ] H}
    (huM : u ∈ M) (hu : u ∈ unitary (H →L[ℂ] H)) :
    M.centralSupport (u * a * star u) = M.centralSupport a :=
  congrArg Projection.val (M.centralSupportProjection_unitary_conj huM hu)

/-- **Geometric formula for the central support.** For `a ∈ M`, `M.centralSupport a` is the
orthogonal projection onto the closure of the linear span of `{x (a ξ) | x ∈ M, ξ ∈ H}`. -/
theorem centralSupport_eq_starProjection_closure_span {M : VonNeumannAlgebra H} {a : H →L[ℂ] H}
    (ha : a ∈ M) :
    M.centralSupport a =
      (Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}).topologicalClosure.starProjection
      := by
  set W : Submodule ℂ H := Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}
  set K : Submodule ℂ H := W.topologicalClosure
  -- Step 1: `W` is invariant under both `M.commutant` and `M = M.commutant.commutant`, so
  -- `K.starProjection` lies in `M ⊓ M.commutant`.
  have hW_comm : ∀ y ∈ M.commutant, W ∈ Module.End.invtSubmodule y := by
    intro y hy
    rw [Module.End.mem_invtSubmodule, Submodule.span_le]
    rintro _ ⟨x, hx, ξ, rfl⟩
    refine Submodule.subset_span ⟨x, hx, y ξ, ?_⟩
    have hcomm : y * (x * a) = (x * a) * y :=
      (mem_commutant_iff.1 hy (x * a) (mul_mem hx ha)).symm
    exact congr($hcomm ξ).symm
  have hW_M : ∀ m ∈ M, W ∈ Module.End.invtSubmodule m := by
    intro m hm
    rw [Module.End.mem_invtSubmodule, Submodule.span_le]
    rintro _ ⟨x, hx, ξ, rfl⟩
    exact Submodule.subset_span ⟨m * x, mul_mem hm hx, ξ, rfl⟩
  have hKM : K.starProjection ∈ M := by
    rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection]
    exact fun y hy => Submodule.topologicalClosure_mem_invtSubmodule (hW_comm y hy)
  have hKC : K.starProjection ∈ M.commutant := by
    rw [IsStarProjection.mem_iff isStarProjection_starProjection M.commutant,
      Submodule.range_starProjection]
    exact fun m hm => Submodule.topologicalClosure_mem_invtSubmodule
      (hW_M m (by simpa only [M.commutant_commutant] using hm))
  -- Step 2: `K.starProjection * a = a` since `a ξ = 1 (a ξ) ∈ W ≤ K`.
  have hKa : K.starProjection * a = a := by
    rw [isIdempotentElem_mul_eq_right_iff K.isIdempotentElem_starProjection,
      Submodule.range_starProjection]
    rintro _ ⟨ξ, rfl⟩
    exact W.le_topologicalClosure (Submodule.subset_span ⟨1, one_mem M, ξ, rfl⟩)
  -- Step 3: Every central projection `z` with `z * a = a` contains `W`, hence `K`, in its range.
  refine le_antisymm
    ((centralSupport_le_iff isStarProjection_starProjection hKM hKC).2 hKa) ?_
  rw [← coe_centralSupportProjection]
  set z := M.centralSupportProjection a
  rw [← z.starProjection_range, Submodule.starProjection_le_starProjection_iff]
  refine W.topologicalClosure_minimal ?_
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range z.isStarProjection.isIdempotentElem)
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, ξ, rfl⟩
  have hzx : (z : H →L[ℂ] H) * x = x * z :=
    (mem_commutant_iff.1 (mem_inf.1 z.coe_mem).2 x hx).symm
  have hza : (z : H →L[ℂ] H) * a = a := M.centralSupport_mul_self a
  refine ⟨x (a ξ), ?_⟩
  calc (z : H →L[ℂ] H) (x (a ξ))
    _ = ((z : H →L[ℂ] H) * x) (a ξ) := rfl
    _ = (x * z) (a ξ) := by rw [hzx]
    _ = x (((z : H →L[ℂ] H) * a) ξ) := rfl
    _ = x (a ξ) := by rw [hza]

/-- **Central-support kernel theorem.** For `a ∈ M` and `y ∈ M.commutant`, `y * a = 0` holds if and
only if `y * M.centralSupport a = 0`. -/
theorem commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero {M : VonNeumannAlgebra H}
    {a y : H →L[ℂ] H} (ha : a ∈ M) (hy : y ∈ M.commutant) :
    y * a = 0 ↔ y * M.centralSupport a = 0 := by
  refine ⟨fun hya => ?_, fun hyc => by
    rw [← M.centralSupport_mul_self a, ← mul_assoc, hyc, zero_mul]⟩
  rw [centralSupport_eq_starProjection_closure_span ha]
  set W : Submodule ℂ H := Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}
  have hW_ker : W.topologicalClosure ≤ y.ker := by
    refine W.topologicalClosure_minimal ?_ y.isClosed_ker
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, ξ, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hyx : y * x = x * y := (mem_commutant_iff.1 hy x hx).symm
    calc y (x (a ξ))
      _ = (y * x) (a ξ) := rfl
      _ = (x * y) (a ξ) := by rw [hyx]
      _ = x ((y * a) ξ) := rfl
      _ = 0 := by rw [hya, zero_apply, map_zero]
  ext ξ
  exact hW_ker (Submodule.starProjection_apply_mem _ ξ)

end CentralSupport

end VonNeumannAlgebra
