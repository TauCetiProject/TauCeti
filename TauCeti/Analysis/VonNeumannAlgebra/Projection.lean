/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
public import TauCeti.Analysis.VonNeumannAlgebra.Polar
import Mathlib.Algebra.Order.Star.Projection
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# The projection lattice, central support, and parallelogram law in von Neumann algebras

An orthogonal projection `U.starProjection` onto a closed subspace `U ≤ H` belongs to a concrete von
Neumann algebra `M` if and only if `U` is invariant under `M.commutant`
(`VonNeumannAlgebra.IsStarProjection.mem_iff`). Since `M.commutant` is closed under adjoints, its
invariant subspaces are closed under orthogonal complements, arbitrary intersections, arbitrary
spans, and topological closures (`U.topologicalClosure = Uᗮᗮ`). Consequently, the bundled star
projections `M.Projection` in `M` form a complete ortholattice ordered by the Loewner order —
equivalently by inclusion of ranges:

* the meet `p ⊓ q` (and `⨅ i, p i`) is the orthogonal projection onto the intersection of ranges;
* the join `p ⊔ q` (and `⨆ i, p i`) is the orthogonal projection onto the closed linear span of
  ranges;
* the orthocomplement `pᶜ` is `1 - p`, projecting onto `(range p)ᗮ`, satisfying De Morgan's laws;
* monotone nets of projections converge strongly to their supremum and antitone nets to their
  infimum (`VonNeumannAlgebra.Projection.tendsto_iSup_of_monotone`,
  `VonNeumannAlgebra.Projection.tendsto_iInf_of_antitone`).

In the center `M ⊓ M.commutant`, the **central support** `M.centralSupport a` of an operator
`a : H →L[ℂ] H` is the smallest central projection `z` satisfying `z * a = a`. For `a ∈ M`, we
identify `M.centralSupport a` geometrically as the orthogonal projection onto the closed span of
`{x (a ξ) | x ∈ M, ξ ∈ H}` (`VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`) and
deduce the **central-support kernel theorem**
(`VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`): for every
`y ∈ M.commutant`, `y * a = 0 ↔ y * M.centralSupport a = 0`.

Finally, we define Murray–von Neumann equivalence `VonNeumannAlgebra.ProjectionEquivalent M p q` of
projections in `M`, prove that it is an equivalence relation on star projections in `M` preserving
central supports, show that the initial and final projections of any operator in `M` are equivalent
via its polar factor, and establish **Kaplansky's parallelogram law**
(`VonNeumannAlgebra.parallelogram_projectionEquivalent`):
`ProjectionEquivalent M ((p ⊔ q : M.Projection) - p) (q - (p ⊓ q : M.Projection))`.

## Main declarations

* `VonNeumannAlgebra.starProjection_iInf_mem`,
  `VonNeumannAlgebra.starProjection_topologicalClosure_iSup_mem`: lattice closure of orthogonal
  projections in `M`.
* `VonNeumannAlgebra.Projection`: bundled star projections in `M`, with `CompleteLattice` and
  `Compl` instances, De Morgan laws, and strong convergence of monotone/antitone families.
* `VonNeumannAlgebra.centralSupportProjection`, `VonNeumannAlgebra.centralSupport`: central support
  of an operator in `M`, its geometric span formula
  `VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`, and the kernel theorem
  `VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`.
* `VonNeumannAlgebra.ProjectionEquivalent`, `VonNeumannAlgebra.projectionEquivalent_iff`:
  Murray–von Neumann equivalence of projections in `M`, with reflexivity, symmetry, transitivity,
  orthogonal additivity, central-support invariance, polar equivalence
  `VonNeumannAlgebra.projectionEquivalent_orthogonal_ker_topologicalClosure_range`, and Kaplansky's
  parallelogram law `VonNeumannAlgebra.parallelogram_projectionEquivalent`.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  §2.5, §5.5, Proposition 5.5.2, Proposition 6.1.8, and Theorem 6.1.7.
* M. Takesaki, *Theory of Operator Algebras I*, Proposition II.3.6 and Proposition V.1.6.
-/

public section

open Filter
open scoped Topology InnerProduct

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

/-- The orthogonal projection onto the intersection of two closed subspaces whose projections lie in
`M` again lies in `M`. -/
theorem starProjection_inf_mem {M : VonNeumannAlgebra H} {U V : ClosedSubmodule ℂ H}
    (hU : U.toSubmodule.starProjection ∈ M) (hV : V.toSubmodule.starProjection ∈ M) :
    (U ⊓ V : ClosedSubmodule ℂ H).toSubmodule.starProjection ∈ M := by
  rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection]
  intro y hy
  have hUy := (IsStarProjection.mem_iff isStarProjection_starProjection M).1 hU y hy
  have hVy := (IsStarProjection.mem_iff isStarProjection_starProjection M).1 hV y hy
  rw [Submodule.range_starProjection] at hUy hVy
  exact Module.End.invtSubmodule.inf_mem hUy hVy

/-- The orthogonal projection onto the closed span of a family of closed subspaces whose projections
lie in `M` again lies in `M`. -/
theorem starProjection_topologicalClosure_iSup_mem {ι : Sort*} {M : VonNeumannAlgebra H}
    (U : ι → ClosedSubmodule ℂ H) (hU : ∀ i, (U i).toSubmodule.starProjection ∈ M) :
    (⨆ i, U i : ClosedSubmodule ℂ H).toSubmodule.starProjection ∈ M := by
  rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection,
    ClosedSubmodule.toSubmodule_iSup]
  -- `ClosedSubmodule.toSubmodule_iSup` unfolds to `(⨆ i, (U i).toSubmodule).closure`.
  change ∀ y ∈ M.commutant,
    (⨆ i, (U i).toSubmodule).topologicalClosure ∈ Module.End.invtSubmodule y
  refine fun y hy => Submodule.topologicalClosure_mem_invtSubmodule ?_
  rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_iSup]
  refine iSup_le fun i => ?_
  have hi := (IsStarProjection.mem_iff isStarProjection_starProjection M).1 (hU i) y hy
  rw [Submodule.range_starProjection, Module.End.mem_invtSubmodule_iff_map_le] at hi
  exact hi.trans (le_iSup (fun j => (U j).toSubmodule) i)

/-- The orthogonal projection onto the closed span of two closed subspaces whose projections lie in
`M` again lies in `M`. -/
theorem starProjection_topologicalClosure_sup_mem {M : VonNeumannAlgebra H}
    {U V : ClosedSubmodule ℂ H}
    (hU : U.toSubmodule.starProjection ∈ M) (hV : V.toSubmodule.starProjection ∈ M) :
    (U ⊔ V : ClosedSubmodule ℂ H).toSubmodule.starProjection ∈ M := by
  rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection,
    ClosedSubmodule.toSubmodule_sup]
  -- `ClosedSubmodule.toSubmodule_sup` unfolds to `(U.toSubmodule ⊔ V.toSubmodule).closure`.
  change ∀ y ∈ M.commutant,
    (U.toSubmodule ⊔ V.toSubmodule).topologicalClosure ∈ Module.End.invtSubmodule y
  refine fun y hy => Submodule.topologicalClosure_mem_invtSubmodule ?_
  have hUy := (IsStarProjection.mem_iff isStarProjection_starProjection M).1 hU y hy
  have hVy := (IsStarProjection.mem_iff isStarProjection_starProjection M).1 hV y hy
  rw [Submodule.range_starProjection] at hUy hVy
  exact Module.End.invtSubmodule.sup_mem hUy hVy

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

noncomputable instance : PartialOrder M.Projection :=
  PartialOrder.lift ((↑) : M.Projection → H →L[ℂ] H) coe_injective

@[simp, norm_cast]
theorem coe_le_coe {p q : M.Projection} : (p : H →L[ℂ] H) ≤ q ↔ p ≤ q :=
  Iff.rfl

theorem le_iff_range_le {p q : M.Projection} :
    p ≤ q ↔ (p : H →L[ℂ] H).range ≤ (q : H →L[ℂ] H).range := by
  rw [← Submodule.starProjection_le_starProjection_iff, p.starProjection_range,
    q.starProjection_range, coe_le_coe]

theorem le_iff_closedRange_le {p q : M.Projection} :
    p ≤ q ↔ p.closedRange ≤ q.closedRange :=
  le_iff_range_le

theorem le_iff_mul_eq_right {p q : M.Projection} :
    p ≤ q ↔ (q : H →L[ℂ] H) * p = p :=
  p.isStarProjection.le_iff_mul_eq_right q.isStarProjection

theorem le_iff_mul_eq_left {p q : M.Projection} :
    p ≤ q ↔ (p : H →L[ℂ] H) * q = p :=
  p.isStarProjection.le_iff_mul_eq_left q.isStarProjection

instance : Bot M.Projection :=
  ⟨⟨0, .zero _, zero_mem M⟩⟩

instance : Top M.Projection :=
  ⟨⟨1, .one _, one_mem M⟩⟩

@[simp, norm_cast]
theorem coe_bot : ((⊥ : M.Projection) : H →L[ℂ] H) = 0 :=
  (rfl)

@[simp, norm_cast]
theorem coe_top : ((⊤ : M.Projection) : H →L[ℂ] H) = 1 :=
  (rfl)

@[simp]
theorem closedRange_bot : (⊥ : M.Projection).closedRange = ⊥ :=
  ClosedSubmodule.toSubmodule_injective LinearMap.range_zero

@[simp]
theorem closedRange_top : (⊤ : M.Projection).closedRange = ⊤ :=
  ClosedSubmodule.toSubmodule_injective <| by
    rw [toSubmodule_closedRange, coe_top, ClosedSubmodule.toSubmodule_top,
      ← Submodule.starProjection_top', Submodule.range_starProjection]

noncomputable instance : Max M.Projection where
  max p q := ofClosedSubmodule (p.closedRange ⊔ q.closedRange)
    (starProjection_topologicalClosure_sup_mem
      p.starProjection_closedRange_mem q.starProjection_closedRange_mem)

noncomputable instance : Min M.Projection where
  min p q := ofClosedSubmodule (p.closedRange ⊓ q.closedRange)
    (starProjection_inf_mem p.starProjection_closedRange_mem q.starProjection_closedRange_mem)

noncomputable instance : SupSet M.Projection where
  sSup S := ofClosedSubmodule (sSup (closedRange '' S)) <| by
    rw [sSup_image]
    exact starProjection_topologicalClosure_iSup_mem _ fun p =>
      starProjection_topologicalClosure_iSup_mem _ fun _ => p.starProjection_closedRange_mem

noncomputable instance : InfSet M.Projection where
  sInf S := ofClosedSubmodule (sInf (closedRange '' S)) <| by
    rw [sInf_image]
    exact starProjection_iInf_mem _ fun p =>
      starProjection_iInf_mem _ fun _ => p.starProjection_closedRange_mem

@[simp]
theorem closedRange_sup (p q : M.Projection) :
    (p ⊔ q).closedRange = p.closedRange ⊔ q.closedRange :=
  closedRange_ofClosedSubmodule _ _

@[simp]
theorem closedRange_inf (p q : M.Projection) :
    (p ⊓ q).closedRange = p.closedRange ⊓ q.closedRange :=
  closedRange_ofClosedSubmodule _ _

@[simp]
theorem closedRange_sSup (S : Set M.Projection) :
    (sSup S).closedRange = sSup (closedRange '' S) :=
  closedRange_ofClosedSubmodule _ _

@[simp]
theorem closedRange_sInf (S : Set M.Projection) :
    (sInf S).closedRange = sInf (closedRange '' S) :=
  closedRange_ofClosedSubmodule _ _

noncomputable instance : CompleteLattice M.Projection :=
  closedRange_injective.completeLattice closedRange
    (fun {p q} => le_iff_closedRange_le.symm)
    (fun {p q} => by simp only [lt_iff_le_not_ge, le_iff_closedRange_le])
    closedRange_sup closedRange_inf
    (fun S => by rw [closedRange_sSup, sSup_image])
    (fun S => by rw [closedRange_sInf, sInf_image])
    closedRange_top closedRange_bot

@[simp]
theorem closedRange_iSup {ι : Sort*} (p : ι → M.Projection) :
    (⨆ i, p i).closedRange = ⨆ i, (p i).closedRange := by
  rw [iSup, closedRange_sSup, ← Set.range_comp, sSup_range]
  rfl

@[simp]
theorem closedRange_iInf {ι : Sort*} (p : ι → M.Projection) :
    (⨅ i, p i).closedRange = ⨅ i, (p i).closedRange := by
  rw [iInf, closedRange_sInf, ← Set.range_comp, sInf_range]
  rfl

/-- The meet of two projections in `M` is the orthogonal projection onto the intersection of their
closed ranges. -/
theorem coe_inf (p q : M.Projection) :
    ((p ⊓ q : M.Projection) : H →L[ℂ] H) =
      (p.closedRange ⊓ q.closedRange).toSubmodule.starProjection :=
  (rfl)

/-- The join of two projections in `M` is the orthogonal projection onto the closed span of their
ranges. -/
theorem coe_sup (p q : M.Projection) :
    ((p ⊔ q : M.Projection) : H →L[ℂ] H) =
      ((p : H →L[ℂ] H).range ⊔ (q : H →L[ℂ] H).range).topologicalClosure.starProjection :=
  (rfl)

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
  rw [← toSubmodule_closedRange, closedRange_iSup, ClosedSubmodule.toSubmodule_iSup]
  rfl

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
  rw [le_iff_closedRange_le, le_iff_closedRange_le, closedRange_compl, closedRange_compl]
  exact Submodule.orthogonal_le_orthogonal_iff

/-- A projection `p` lies below `qᶜ` if and only if `p` and `q` have orthogonal ranges
(`p * q = 0`). -/
theorem le_compl_iff_mul_eq_zero {p q : M.Projection} :
    p ≤ qᶜ ↔ (p : H →L[ℂ] H) * q = 0 := by
  rw [le_iff_mul_eq_left, coe_compl, mul_sub, mul_one, sub_eq_self]

@[simp]
theorem compl_bot : (⊥ : M.Projection)ᶜ = ⊤ :=
  Projection.ext (sub_zero (1 : H →L[ℂ] H))

@[simp]
theorem compl_top : (⊤ : M.Projection)ᶜ = ⊥ :=
  Projection.ext (sub_self (1 : H →L[ℂ] H))

@[simp]
theorem compl_sup (p q : M.Projection) : (p ⊔ q)ᶜ = pᶜ ⊓ qᶜ :=
  closedRange_injective <| by
    rw [closedRange_compl, closedRange_sup, closedRange_inf, closedRange_compl, closedRange_compl,
      ClosedSubmodule.inf_orthogonal]

@[simp]
theorem compl_inf (p q : M.Projection) : (p ⊓ q)ᶜ = pᶜ ⊔ qᶜ :=
  closedRange_injective <| by
    rw [closedRange_compl, closedRange_inf, closedRange_sup, closedRange_compl, closedRange_compl,
      ClosedSubmodule.sup_orthogonal]

theorem compl_sSup (S : Set M.Projection) : (sSup S)ᶜ = ⨅ p ∈ S, pᶜ :=
  closedRange_injective <| by
    rw [closedRange_compl, closedRange_sSup, ← ClosedSubmodule.sInf_orthogonal, iInf_image]
    simp only [closedRange_iInf, closedRange_compl]

@[simp]
theorem compl_iSup {ι : Sort*} (p : ι → M.Projection) : (⨆ i, p i)ᶜ = ⨅ i, (p i)ᶜ := by
  rw [iSup, compl_sSup, iInf_range]

@[simp]
theorem compl_iInf {ι : Sort*} (p : ι → M.Projection) : (⨅ i, p i)ᶜ = ⨆ i, (p i)ᶜ := by
  apply compl_injective
  rw [compl_compl, compl_iSup]
  simp only [compl_compl]

@[simp]
theorem inf_compl_eq_bot (p : M.Projection) : p ⊓ pᶜ = ⊥ :=
  closedRange_injective <| by
    rw [closedRange_inf, closedRange_compl, closedRange_bot]
    exact ClosedSubmodule.toSubmodule_injective (Submodule.inf_orthogonal_eq_bot _)

@[simp]
theorem sup_compl_eq_top (p : M.Projection) : p ⊔ pᶜ = ⊤ := by
  apply compl_injective
  rw [compl_sup, compl_compl, compl_top, inf_comm, inf_compl_eq_bot]

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
      rw [coe_compl, sub_apply, one_apply_eq_self, sub_sub_cancel]
  simpa only [hsub] using ht

end Projection

/-! ### Central support and the central-support kernel theorem -/

section CentralSupport

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
  rw [← coe_centralSupportProjection, ← ContinuousLinearMap.coe_inj]
  change (M.centralSupportProjection a : H →L[ℂ] H).toLinearMap.comp a.toLinearMap =
    a.toLinearMap
  rw [LinearMap.IsIdempotentElem.comp_eq_right_iff (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (M.centralSupportProjection a).isStarProjection.isIdempotentElem),
    ← Projection.toSubmodule_closedRange, centralSupportProjection, Projection.closedRange_sInf,
    sInf_image, ClosedSubmodule.toSubmodule_iInf]
  refine le_iInf fun z => ?_
  rw [ClosedSubmodule.toSubmodule_iInf]
  exact le_iInf fun hz =>
    (LinearMap.IsIdempotentElem.comp_eq_right_iff (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      z.isStarProjection.isIdempotentElem) a.toLinearMap).1
      (congrArg ContinuousLinearMap.toLinearMap hz)

theorem mul_centralSupport_self {M : VonNeumannAlgebra H} {a : H →L[ℂ] H} (ha : a ∈ M) :
    a * M.centralSupport a = a := by
  rw [mem_commutant_iff.1 (M.centralSupport_mem_commutant a) a ha,
    M.centralSupport_mul_self a]

/-- Universal property of `M.centralSupportProjection`: a central projection `z` lies above
`M.centralSupportProjection a` if and only if `z * a = a`. -/
theorem centralSupportProjection_le_iff {M : VonNeumannAlgebra H} {a : H →L[ℂ] H}
    {z : (M ⊓ M.commutant).Projection} :
    M.centralSupportProjection a ≤ z ↔ (z : H →L[ℂ] H) * a = a :=
  ⟨fun h => by
      have hrange : a.range ≤ (z : H →L[ℂ] H).range :=
        ((LinearMap.IsIdempotentElem.comp_eq_right_iff
          (ContinuousLinearMap.IsIdempotentElem.toLinearMap
            (M.isStarProjection_centralSupport a).isIdempotentElem) a.toLinearMap).1
            (congrArg ContinuousLinearMap.toLinearMap
              (M.centralSupport_mul_self a))).trans (Projection.le_iff_range_le.1 h)
      exact ContinuousLinearMap.coe_inj.1
        ((LinearMap.IsIdempotentElem.comp_eq_right_iff
          (ContinuousLinearMap.IsIdempotentElem.toLinearMap
            z.isStarProjection.isIdempotentElem) a.toLinearMap).2
          hrange),
    fun hz => sInf_le hz⟩

/-- Universal property of `M.centralSupport`: for a central projection `z` of `M`,
`M.centralSupport a ≤ z ↔ z * a = a`. -/
theorem centralSupport_le_iff {M : VonNeumannAlgebra H} {a z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hzC : z ∈ M.commutant) :
    M.centralSupport a ≤ z ↔ z * a = a :=
  centralSupportProjection_le_iff (z := ⟨z, hz, mem_inf.2 ⟨hzM, hzC⟩⟩)

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
    refine ContinuousLinearMap.coe_inj.1 <|
      (LinearMap.IsIdempotentElem.comp_eq_right_iff
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap
          (isStarProjection_starProjection (U := K)).isIdempotentElem) a.toLinearMap).2 ?_
    rw [Submodule.range_starProjection]
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

/-! ### Murray–von Neumann equivalence and Kaplansky's parallelogram law -/

section Equivalence

/-- Murray–von Neumann equivalence `p ∼ q` in `M`, oriented from initial to final projection:
some `v ∈ M` has `star v * v = p` and `v * star v = q`. -/
def ProjectionEquivalent (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧ p ∈ M ∧ q ∈ M ∧
  ∃ v : H →L[ℂ] H, v ∈ M ∧ star v * v = p ∧ v * star v = q

/-- Characterization of Murray–von Neumann equivalence `VonNeumannAlgebra.ProjectionEquivalent`. -/
theorem projectionEquivalent_iff {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} :
    ProjectionEquivalent M p q ↔
      IsStarProjection p ∧ IsStarProjection q ∧ p ∈ M ∧ q ∈ M ∧
        ∃ v : H →L[ℂ] H, v ∈ M ∧ star v * v = p ∧ v * star v = q :=
  Iff.rfl

namespace ProjectionEquivalent

variable {M : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}

theorem isStarProjection_left (h : ProjectionEquivalent M p q) : IsStarProjection p :=
  h.1

theorem isStarProjection_right (h : ProjectionEquivalent M p q) : IsStarProjection q :=
  h.2.1

theorem mem_left (h : ProjectionEquivalent M p q) : p ∈ M :=
  h.2.2.1

theorem mem_right (h : ProjectionEquivalent M p q) : q ∈ M :=
  h.2.2.2.1

/-- Recover an implementing operator `v ∈ M` for a Murray–von Neumann equivalence
`ProjectionEquivalent M p q`. -/
theorem exists_mem (h : ProjectionEquivalent M p q) :
    ∃ v : H →L[ℂ] H, v ∈ M ∧ star v * v = p ∧ v * star v = q :=
  h.2.2.2.2

private theorem witness_mul_left_eq_self {p q v : H →L[ℂ] H} (hp : IsStarProjection p)
    (hvp : star v * v = p) (hvq : v * star v = q) : q * v = v := by
  have hv_pi : v.IsPartialIsometry := by
    rw [ContinuousLinearMap.isPartialIsometry_iff_isStarProjection_adjoint_comp_self,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def, hvp]
    exact hp
  rw [← hvq, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.star_eq_adjoint]
  exact hv_pi.comp_adjoint_comp

private theorem witness_mul_right_eq_self {p q v : H →L[ℂ] H} (hp : IsStarProjection p)
    (hvp : star v * v = p) (hvq : v * star v = q) : v * p = v := by
  calc v * p
    _ = (v * star v) * v := by rw [← hvp, mul_assoc]
    _ = v := by rw [hvq, witness_mul_left_eq_self hp hvp hvq]

/-- Reflexivity of Murray–von Neumann equivalence on star projections in `M`. -/
theorem refl (hp : IsStarProjection p) (hpM : p ∈ M) : ProjectionEquivalent M p p :=
  ⟨hp, hp, hpM, hpM, p, hpM,
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Symmetry of Murray–von Neumann equivalence. -/
theorem symm (h : ProjectionEquivalent M p q) : ProjectionEquivalent M q p := by
  obtain ⟨hp, hq, hpM, hqM, v, hvM, hvp, hvq⟩ := h
  exact ⟨hq, hp, hqM, hpM, star v, star_mem hvM,
    by rwa [star_star], by rwa [star_star]⟩

/-- Transitivity of Murray–von Neumann equivalence. -/
theorem trans (hpq : ProjectionEquivalent M p q) (hqr : ProjectionEquivalent M q r) :
    ProjectionEquivalent M p r := by
  obtain ⟨hp, -, hpM, -, v, hvM, hvp, hvq⟩ := hpq
  obtain ⟨-, hr, -, hrM, w, hwM, hwq, hwr⟩ := hqr
  refine ⟨hp, hr, hpM, hrM, w * v, mul_mem hwM hvM, ?_, ?_⟩
  · calc star (w * v) * (w * v)
      _ = star v * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = star v * (v * star v) * v := by rw [hwq, ← hvq]
      _ = (star v * v) * (star v * v) := by simp only [mul_assoc]
      _ = p := by rw [hvp, hp.isIdempotentElem.eq]
  · calc w * v * star (w * v)
      _ = w * (v * star v) * star w := by simp only [star_mul, mul_assoc]
      _ = w * (star w * w) * star w := by rw [hvq, ← hwq]
      _ = (w * star w) * (w * star w) := by simp only [mul_assoc]
      _ = r := by rw [hwr, hr.isIdempotentElem.eq]

/-- Equivalent projections vanish simultaneously. -/
theorem eq_zero_iff (h : ProjectionEquivalent M p q) : p = 0 ↔ q = 0 := by
  suffices key : ∀ {e₁ e₂ : H →L[ℂ] H}, ProjectionEquivalent M e₁ e₂ → e₁ = 0 → e₂ = 0
    from ⟨key h, key h.symm⟩
  rintro e₁ e₂ ⟨-, -, -, -, v, -, hv₁, hv₂⟩ rfl
  have hv₀ : v = 0 := by
    rwa [star_mul_self_eq_zero] at hv₁
  rw [← hv₂, hv₀, zero_mul]

/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections in `M` are equivalent. -/
theorem add {p₁ p₂ q₁ q₂ : H →L[ℂ] H} (hp₁₂ : p₁ * p₂ = 0) (hq₁₂ : q₁ * q₂ = 0)
    (h₁ : ProjectionEquivalent M p₁ q₁) (h₂ : ProjectionEquivalent M p₂ q₂) :
    ProjectionEquivalent M (p₁ + p₂) (q₁ + q₂) := by
  obtain ⟨hp₁, hq₁, hp₁M, hq₁M, v₁, hv₁M, hv₁p, hv₁q⟩ := h₁
  obtain ⟨hp₂, hq₂, hp₂M, hq₂M, v₂, hv₂M, hv₂p, hv₂q⟩ := h₂
  have hqv₁ : q₁ * v₁ = v₁ := witness_mul_left_eq_self hp₁ hv₁p hv₁q
  have hqv₂ : q₂ * v₂ = v₂ := witness_mul_left_eq_self hp₂ hv₂p hv₂q
  have hv₁p_r : v₁ * p₁ = v₁ := witness_mul_right_eq_self hp₁ hv₁p hv₁q
  have hv₂p_r : v₂ * p₂ = v₂ := witness_mul_right_eq_self hp₂ hv₂p hv₂q
  have hcross₁ : star v₁ * v₂ = 0 := by
    calc star v₁ * v₂
      _ = star (q₁ * v₁) * (q₂ * v₂) := by rw [hqv₁, hqv₂]
      _ = star v₁ * (q₁ * q₂) * v₂ := by
        simp only [star_mul, hq₁.isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [hq₁₂, mul_zero, zero_mul]
  have hcross₂ : star v₂ * v₁ = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hcross₁
  have hcross₃ : v₁ * star v₂ = 0 := by
    calc v₁ * star v₂
      _ = (v₁ * p₁) * star (v₂ * p₂) := by rw [hv₁p_r, hv₂p_r]
      _ = v₁ * (p₁ * p₂) * star v₂ := by
        simp only [star_mul, hp₂.isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [hp₁₂, mul_zero, zero_mul]
  have hcross₄ : v₂ * star v₁ = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hcross₃
  refine ⟨hp₁.add hp₂ hp₁₂, hq₁.add hq₂ hq₁₂, add_mem hp₁M hp₂M, add_mem hq₁M hq₂M,
    v₁ + v₂, add_mem hv₁M hv₂M, ?_, ?_⟩
  · simp only [star_add, add_mul, mul_add, hv₁p, hv₂p, hcross₁, hcross₂, add_zero, zero_add]
  · simp only [star_add, add_mul, mul_add, hv₁q, hv₂q, hcross₃, hcross₄, add_zero, zero_add]

/-- Equivalent projections in `M` have the same central support. -/
theorem centralSupport_eq (h : ProjectionEquivalent M p q) :
    M.centralSupport p = M.centralSupport q := by
  suffices key : ∀ {e₁ e₂ : H →L[ℂ] H},
      ProjectionEquivalent M e₁ e₂ → M.centralSupportProjection e₁ ≤ M.centralSupportProjection e₂
    from congrArg Projection.val (le_antisymm (key h) (key h.symm))
  intro e₁ e₂ ⟨he₁, _, _, _, v, hvM, hv₁, hv₂⟩
  rw [centralSupportProjection_le_iff]
  set z := M.centralSupport e₂
  have hqv : e₂ * v = v := witness_mul_left_eq_self he₁ hv₁ hv₂
  have hzv : z * star v = star v * z :=
    (mem_commutant_iff.1 (M.centralSupport_mem_commutant e₂) (star v) (star_mem hvM)).symm
  calc z * e₁
    _ = (z * star v) * v := by rw [← hv₁, mul_assoc]
    _ = star v * (z * (e₂ * v)) := by rw [hzv, hqv, mul_assoc]
    _ = star v * ((z * e₂) * v) := by rw [mul_assoc]
    _ = star v * (e₂ * v) := by rw [M.centralSupport_mul_self e₂]
    _ = e₁ := by rw [hqv, hv₁]

end ProjectionEquivalent

/-- For any operator `x ∈ M`, its initial projection `x.kerᗮ.starProjection` and its final
projection `x.range.topologicalClosure.starProjection` are Murray–von Neumann equivalent in `M`,
witnessed by `x.polarFactor`. -/
theorem projectionEquivalent_orthogonal_ker_topologicalClosure_range {M : VonNeumannAlgebra H}
    {x : H →L[ℂ] H} (hx : x ∈ M) :
    ProjectionEquivalent M x.kerᗮ.starProjection x.range.topologicalClosure.starProjection := by
  refine ⟨isStarProjection_starProjection, isStarProjection_starProjection,
    starProjection_orthogonal_ker_mem hx, starProjection_topologicalClosure_range_mem hx,
    x.polarFactor, polarFactor_mem hx, ?_, ?_⟩
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      x.adjoint_polarFactor_comp_polarFactor]
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      x.polarFactor_comp_adjoint_polarFactor]

/-- Auxiliary computation for Kaplansky's parallelogram law: the initial projection of `(1 - p) * q`
is `q - (p ⊓ q)`. -/
private theorem starProjection_orthogonal_ker_one_sub_mul {M : VonNeumannAlgebra H}
    (p q : M.Projection) :
    ((1 - (p : H →L[ℂ] H)) * q).kerᗮ.starProjection =
      (q : H →L[ℂ] H) - (p ⊓ q : M.Projection) := by
  set x : H →L[ℂ] H := (1 - (p : H →L[ℂ] H)) * q
  set r : H →L[ℂ] H := (q : H →L[ℂ] H) - (p ⊓ q : M.Projection)
  have hr : IsStarProjection r :=
    ((p ⊓ q).isStarProjection.le_iff_isStarProjection_sub q.isStarProjection).1
      (Projection.coe_le_coe.2 inf_le_right)
  have hr_has : r.range.HasOrthogonalProjection :=
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range hr.isIdempotentElem
  -- Two star projections are equal once their kernels coincide.
  have hker : x.ker = r.ker := by
    ext ξ
    simp only [x, r, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      sub_apply, one_apply_eq_self, sub_eq_zero]
    rw [eq_comm (a := (q : H →L[ℂ] H) ξ), ← p.starProjection_range,
      Submodule.starProjection_eq_self_iff]
    rw [eq_comm (a := (q : H →L[ℂ] H) ξ), Projection.coe_inf]
    have hle : (p.closedRange ⊓ q.closedRange).toSubmodule ≤ (q : H →L[ℂ] H).range :=
      inf_le_right
    have hcomp := DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le hle) ξ
    rw [ContinuousLinearMap.comp_apply, q.starProjection_range] at hcomp
    rw [← hcomp, Submodule.starProjection_eq_self_iff, ClosedSubmodule.toSubmodule_inf,
      p.toSubmodule_closedRange, q.toSubmodule_closedRange, Submodule.mem_inf]
    exact (and_iff_left (LinearMap.mem_range_self _ ξ)).symm
  apply ContinuousLinearMap.IsStarProjection.ext isStarProjection_starProjection hr
  rw [Submodule.range_starProjection, ← Submodule.orthogonalComplement_eq_orthogonalComplement,
    Submodule.orthogonal_orthogonal, hker]
  conv_lhs => rw [(isStarProjection_iff_eq_starProjection_range.1 hr).2]
  rw [Submodule.ker_starProjection]

/-- **Kaplansky's parallelogram law.** For any two projections `p, q : M.Projection` in a von
Neumann algebra `M`, `(p ⊔ q) - p` and `q - (p ⊓ q)` are Murray–von Neumann equivalent in `M`. -/
theorem parallelogram_projectionEquivalent {M : VonNeumannAlgebra H} (p q : M.Projection) :
    ProjectionEquivalent M ((p ⊔ q : M.Projection) - p) (q - (p ⊓ q : M.Projection)) := by
  set x : H →L[ℂ] H := (1 - (p : H →L[ℂ] H)) * q
  have hx : x ∈ M := mul_mem (sub_mem (one_mem M) p.coe_mem) q.coe_mem
  have hinit : x.kerᗮ.starProjection = (q : H →L[ℂ] H) - (p ⊓ q : M.Projection) :=
    starProjection_orthogonal_ker_one_sub_mul p q
  -- Pass to complements `qᶜ, pᶜ` via `star x = (1 - qᶜ) * pᶜ` and De Morgan's law.
  have hstar_x : star x = (1 - ((qᶜ : M.Projection) : H →L[ℂ] H)) * (pᶜ : M.Projection) := by
    simp only [x, star_mul, star_sub, star_one, Projection.star_coe, Projection.coe_compl,
      sub_sub_cancel]
  have hfinal : x.range.topologicalClosure.starProjection =
      (p ⊔ q : M.Projection) - (p : H →L[ℂ] H) := by
    have hrange : x.range.topologicalClosure =
        ((1 - ((qᶜ : M.Projection) : H →L[ℂ] H)) * (pᶜ : M.Projection)).kerᗮ := by
      rw [← x.range.orthogonal_orthogonal_eq_closure, x.orthogonal_range,
        ← ContinuousLinearMap.star_eq_adjoint, hstar_x]
    calc x.range.topologicalClosure.starProjection
      _ = ((1 - ((qᶜ : M.Projection) : H →L[ℂ] H)) * (pᶜ : M.Projection)).kerᗮ.starProjection :=
        Submodule.starProjection_inj.2 hrange
      _ = ((pᶜ : M.Projection) : H →L[ℂ] H) - (qᶜ ⊓ pᶜ : M.Projection) :=
        starProjection_orthogonal_ker_one_sub_mul qᶜ pᶜ
      _ = (p ⊔ q : M.Projection) - (p : H →L[ℂ] H) := by
        rw [inf_comm, ← Projection.compl_sup, Projection.coe_compl, Projection.coe_compl]
        abel
  rw [← hfinal, ← hinit]
  exact (projectionEquivalent_orthogonal_ker_topologicalClosure_range hx).symm

end Equivalence

end VonNeumannAlgebra
