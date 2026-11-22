/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteSublattice
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Algebra.Order.Star.Projection
import TauCeti.Topology.Algebra.Module.ClosedSubmodule

/-!
# The projection lattice in von Neumann algebras

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
* inclusions `M ≤ N` induce order embeddings `VonNeumannAlgebra.Projection.inclusion hMN` and
  complete lattice homomorphisms `VonNeumannAlgebra.Projection.inclusionHom hMN` preserving
  complements and all lattice operations;
* unitaries `u ∈ M` act as order automorphisms `VonNeumannAlgebra.Projection.unitaryConjOrderIso`
  preserving complements.

## Main declarations

* `VonNeumannAlgebra.starProjection_iInf_mem`,
  `VonNeumannAlgebra.starProjection_topologicalClosure_iSup_mem`: lattice closure of orthogonal
  projections in `M`.
* `VonNeumannAlgebra.Projection`, `VonNeumannAlgebra.Projection.closedProjectionSublattice`,
  `VonNeumannAlgebra.Projection.closedRangeOrderIso`,
  `VonNeumannAlgebra.Projection.closedRangeHom`: bundled star projections in `M` and the
  complete-sublattice isomorphism with invariant closed subspaces.
* `VonNeumannAlgebra.Projection.complOrderIso`: orthocomplementation as an order isomorphism
  `M.Projection ≃o M.Projectionᵒᵈ`, yielding binary, indexed, and set-indexed De Morgan laws.
* `VonNeumannAlgebra.Projection.inclusion`, `VonNeumannAlgebra.Projection.inclusionHom`: order
  embedding and complete lattice homomorphism `M.Projection → N.Projection` for `M ≤ N`.
* `VonNeumannAlgebra.Projection.unitaryConjOrderIso`: unitary conjugation order automorphism on
  `M.Projection`.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  §2.5 and §5.5.
* M. Takesaki, *Theory of Operator Algebras I*, Proposition II.3.6.
-/

public section

open scoped InnerProduct

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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
    ClosedSubmodule.toSubmodule_iSup, Submodule.toSubmodule_closure]
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

/-- Every bundled projection in `M` is the orthogonal projection onto `p.closedRange`. -/
theorem starProjection_closedRange (p : M.Projection) :
    p.closedRange.toSubmodule.starProjection = (p : H →L[ℂ] H) := by
  simp only [toSubmodule_closedRange, starProjection_range]

theorem starProjection_closedRange_mem (p : M.Projection) :
    p.closedRange.toSubmodule.starProjection ∈ M := by
  rw [starProjection_closedRange]
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

noncomputable instance : CompleteLattice M.Projection :=
  Equiv.completeLattice
    { toFun p := ⟨p.closedRange, mem_closedProjectionSublattice.2 p.starProjection_closedRange_mem⟩
      invFun U := ofClosedSubmodule U.val (mem_closedProjectionSublattice.1 U.property)
      left_inv p := Projection.ext <| by
        rw [coe_ofClosedSubmodule]
        exact starProjection_closedRange p
      right_inv U := Subtype.ext <|
        closedRange_ofClosedSubmodule U.val (mem_closedProjectionSublattice.1 U.property) }

/-- Order isomorphism between `M.Projection` and `closedProjectionSublattice M`. -/
noncomputable def closedRangeOrderIso (M : VonNeumannAlgebra H) :
    M.Projection ≃o closedProjectionSublattice M where
  toFun p := ⟨p.closedRange, mem_closedProjectionSublattice.2 p.starProjection_closedRange_mem⟩
  invFun U := ofClosedSubmodule U.val (mem_closedProjectionSublattice.1 U.property)
  left_inv p := Projection.ext <| by
    rw [coe_ofClosedSubmodule]
    exact starProjection_closedRange p
  right_inv U := Subtype.ext <|
    closedRange_ofClosedSubmodule U.val (mem_closedProjectionSublattice.1 U.property)
  map_rel_iff' := Iff.rfl

@[simp]
theorem closedRangeOrderIso_apply (p : M.Projection) :
    (closedRangeOrderIso M p : ClosedSubmodule ℂ H) = p.closedRange :=
  (rfl)

/-- `closedRange` as a complete lattice homomorphism into `ClosedSubmodule ℂ H`. -/
noncomputable def closedRangeHom (M : VonNeumannAlgebra H) :
    CompleteLatticeHom M.Projection (ClosedSubmodule ℂ H) :=
  (closedProjectionSublattice M).subtype.comp
    (CompleteLatticeHom.OrderIso.toCompleteLatticeHom (closedRangeOrderIso M))

@[simp]
theorem closedRangeHom_apply (M : VonNeumannAlgebra H) (p : M.Projection) :
    closedRangeHom M p = p.closedRange := by
  simp [closedRangeHom]

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
theorem closedRange_bot : (⊥ : M.Projection).closedRange = ⊥ := by
  simpa only [closedRangeHom_apply] using map_bot (closedRangeHom M)

@[simp]
theorem closedRange_top : (⊤ : M.Projection).closedRange = ⊤ := by
  simpa only [closedRangeHom_apply] using map_top (closedRangeHom M)

@[simp]
theorem closedRange_sup (p q : M.Projection) :
    (p ⊔ q).closedRange = p.closedRange ⊔ q.closedRange := by
  rw [← closedRangeHom_apply M (p ⊔ q), ← closedRangeHom_apply M p, ← closedRangeHom_apply M q]
  exact map_sup (closedRangeHom M) p q

@[simp]
theorem closedRange_inf (p q : M.Projection) :
    (p ⊓ q).closedRange = p.closedRange ⊓ q.closedRange := by
  rw [← closedRangeHom_apply M (p ⊓ q), ← closedRangeHom_apply M p, ← closedRangeHom_apply M q]
  exact map_inf (closedRangeHom M) p q

@[simp]
theorem closedRange_iSup {ι : Sort*} (p : ι → M.Projection) :
    (⨆ i, p i).closedRange = ⨆ i, (p i).closedRange := by
  simpa only [closedRangeHom_apply] using map_iSup (closedRangeHom M) p

@[simp]
theorem closedRange_iInf {ι : Sort*} (p : ι → M.Projection) :
    (⨅ i, p i).closedRange = ⨅ i, (p i).closedRange := by
  simpa only [closedRangeHom_apply] using map_iInf (closedRangeHom M) p

@[simp]
theorem closedRange_sSup (S : Set M.Projection) :
    (sSup S).closedRange = sSup (closedRange '' S) := by
  rw [← closedRangeHom_apply M (sSup S)]
  refine (map_sSup (closedRangeHom M) S).trans (congrArg sSup ?_)
  ext U
  simp [closedRangeHom_apply]

@[simp]
theorem closedRange_sInf (S : Set M.Projection) :
    (sInf S).closedRange = sInf (closedRange '' S) := by
  rw [← closedRangeHom_apply M (sInf S)]
  refine (map_sInf (closedRangeHom M) S).trans (congrArg sInf ?_)
  ext U
  simp [closedRangeHom_apply]

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
    Submodule.toSubmodule_closure, toSubmodule_closedRange, toSubmodule_closedRange]

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
    Submodule.toSubmodule_closure]

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
theorem inclusion_rfl {M : VonNeumannAlgebra H} (p : M.Projection) :
    inclusion (le_rfl : M ≤ M) p = p :=
  (rfl)

@[simp]
theorem inclusion_inclusion {M N P : VonNeumannAlgebra H} (hMN : M ≤ N) (hNP : N ≤ P)
    (p : M.Projection) :
    inclusion hNP (inclusion hMN p) = inclusion (hMN.trans hNP) p :=
  (rfl)

@[simp]
theorem inclusion_compl {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p : M.Projection) :
    inclusion hMN pᶜ = (inclusion hMN p)ᶜ :=
  (rfl)

/-- Transport of projections along an inclusion `M ≤ N` as a complete lattice homomorphism. -/
noncomputable def inclusionHom {M N : VonNeumannAlgebra H} (hMN : M ≤ N) :
    CompleteLatticeHom M.Projection N.Projection where
  toFun := inclusion hMN
  map_sSup' S := closedRange_injective <| by
    simp only [closedRange_inclusion, closedRange_sSup, Set.image_image]
  map_sInf' S := closedRange_injective <| by
    simp only [closedRange_inclusion, closedRange_sInf, Set.image_image]

@[simp]
theorem inclusionHom_apply {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p : M.Projection) :
    inclusionHom hMN p = inclusion hMN p :=
  (rfl)

@[simp]
theorem inclusion_bot {M N : VonNeumannAlgebra H} (hMN : M ≤ N) :
    inclusion hMN ⊥ = ⊥ :=
  map_bot (inclusionHom hMN)

@[simp]
theorem inclusion_top {M N : VonNeumannAlgebra H} (hMN : M ≤ N) :
    inclusion hMN ⊤ = ⊤ :=
  map_top (inclusionHom hMN)

@[simp]
theorem inclusion_sup {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p q : M.Projection) :
    inclusion hMN (p ⊔ q) = inclusion hMN p ⊔ inclusion hMN q :=
  map_sup (inclusionHom hMN) p q

@[simp]
theorem inclusion_inf {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (p q : M.Projection) :
    inclusion hMN (p ⊓ q) = inclusion hMN p ⊓ inclusion hMN q :=
  map_inf (inclusionHom hMN) p q

@[simp]
theorem inclusion_iSup {M N : VonNeumannAlgebra H} (hMN : M ≤ N) {ι : Sort*}
    (p : ι → M.Projection) :
    inclusion hMN (⨆ i, p i) = ⨆ i, inclusion hMN (p i) :=
  map_iSup (inclusionHom hMN) p

@[simp]
theorem inclusion_iInf {M N : VonNeumannAlgebra H} (hMN : M ≤ N) {ι : Sort*}
    (p : ι → M.Projection) :
    inclusion hMN (⨅ i, p i) = ⨅ i, inclusion hMN (p i) :=
  map_iInf (inclusionHom hMN) p

@[simp]
theorem inclusion_sSup {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (S : Set M.Projection) :
    inclusion hMN (sSup S) = sSup (inclusion hMN '' S) :=
  map_sSup (inclusionHom hMN) S

@[simp]
theorem inclusion_sInf {M N : VonNeumannAlgebra H} (hMN : M ≤ N) (S : Set M.Projection) :
    inclusion hMN (sInf S) = sInf (inclusion hMN '' S) :=
  map_sInf (inclusionHom hMN) S

/-- Conjugation by a unitary operator `u ∈ M` as an order automorphism of `M.Projection`. -/
noncomputable def unitaryConjOrderIso {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) : M.Projection ≃o M.Projection :=
  let Φ := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) ⟨u, hu⟩
  { toFun p :=
      ⟨Φ p, p.isStarProjection.map Φ, by
        simpa only [Φ, Unitary.conjStarAlgAut_apply] using
          mul_mem (mul_mem huM p.coe_mem) (star_mem huM)⟩
    invFun p :=
      ⟨Φ.symm p, p.isStarProjection.map Φ.symm, by
        simpa only [Φ, Unitary.conjStarAlgAut_symm_apply] using
          mul_mem (mul_mem (star_mem huM) p.coe_mem) huM⟩
    left_inv p := Projection.ext (Φ.symm_apply_apply _)
    right_inv p := Projection.ext (Φ.apply_symm_apply _)
    map_rel_iff' {p q} := by
      rw [le_iff_mul_eq_left, le_iff_mul_eq_left]
      dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
      rw [← map_mul Φ]
      exact Φ.injective.eq_iff }

@[simp]
theorem coe_unitaryConjOrderIso {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) (p : M.Projection) :
    (unitaryConjOrderIso huM hu p : H →L[ℂ] H) = u * p * star u :=
  Unitary.conjStarAlgAut_apply (S := ℂ) ⟨u, hu⟩ p

@[simp]
theorem coe_unitaryConjOrderIso_symm {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) (p : M.Projection) :
    ((unitaryConjOrderIso huM hu).symm p : H →L[ℂ] H) = star u * p * u :=
  Unitary.conjStarAlgAut_symm_apply (S := ℂ) ⟨u, hu⟩ p

@[simp]
theorem unitaryConjOrderIso_compl {u : H →L[ℂ] H} (huM : u ∈ M)
    (hu : u ∈ unitary (H →L[ℂ] H)) (p : M.Projection) :
    unitaryConjOrderIso huM hu pᶜ = (unitaryConjOrderIso huM hu p)ᶜ :=
  Projection.ext <| by
    simp only [coe_unitaryConjOrderIso, coe_compl, mul_sub, sub_mul, mul_one, hu.2]

end Projection

end VonNeumannAlgebra
