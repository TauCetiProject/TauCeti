/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation

/-!
# Diagonalizing commuting semisimple point actions

For a reduced finite-type affine group over an algebraically closed field, simultaneous
semisimplicity of commuting point actions makes the group-like weight spaces span every
finite-dimensional comodule. Point separation is essential: an abstract joint eigenvector
for rational points must be promoted to a weight vector of the coaction.

This connects simultaneous diagonalization with diagonalizability of affine groups. Applied
to finite-dimensional subcomodules of the regular representation, it shows that the coordinate
Hopf algebra of a commutative group with semisimple points is spanned by group-like elements.

The argument uses `TauCeti.iSup_iInf_eigenspace_eq_top_of_isSemisimple` and the point-stable
line construction in `TauCeti.Algebra.AlgebraicGroup.Solvable.Trigonalizable`.

## References

* T. A. Springer, *Linear Algebraic Groups*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
variable [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- A nonzero joint eigenvector for all rational points of a reduced affine group is a
weight vector for a group-like element of its coordinate Hopf algebra. -/
theorem exists_groupLike_coact_eq_tmul_of_basePointsRepresentation_eq_smul
    {m : M} (hm : m ≠ 0) (χ : WithConv (H →ₐ[k] k) → k)
    (hχ : ∀ g, basePointsRepresentation (H := H) M g m = χ g • m) :
    ∃ c : GroupLike k H, coact (R := k) (C := H) m = m ⊗ₜ[k] c.val := by
  have hstable : ∀ (g : H →ₐ[k] k) {x : M}, x ∈ k ∙ m →
      endOfPoint M g (1 ⊗ₜ[k] x) ∈ (k ∙ m).baseChange k := by
    intro g x hx
    rw [endOfPoint_tmul, one_smul,
      endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    apply Submodule.tmul_mem_baseChange_of_mem
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_smul, hχ]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self m))
  let L := Subcomodule.ofEndOfPointStable (K := k) (k ∙ m) hstable
  obtain ⟨c, hc, hcoact⟩ := exists_isGroupLikeElem_coact_eq_tmul_of_toSubmodule_eq_span
    L hm (Subcomodule.ofEndOfPointStable_toSubmodule _ hstable)
  exact ⟨⟨c, hc⟩, hcoact⟩

/-- The group-like weight spaces span a finite-dimensional comodule when its rational point
actions commute and are semisimple. The ambient group need not be connected or commutative. -/
theorem iSup_groupLikeWeightSpace_eq_top_of_commute_of_isSemisimple
    [Module.Finite k M]
    (hcomm : Pairwise fun g h : WithConv (H →ₐ[k] k) ↦
      Commute (basePointsRepresentation (H := H) M g)
        (basePointsRepresentation (H := H) M h))
    (hss : ∀ g : WithConv (H →ₐ[k] k),
      Module.End.IsSemisimple (basePointsRepresentation (H := H) M g)) :
    ⨆ c : GroupLike k H, c.weightSpace (M := M) = ⊤ := by
  have hspan := iSup_iInf_eigenspace_eq_top_of_isSemisimple
    (fun g ↦ basePointsRepresentation (H := H) M g) hcomm hss
  apply top_le_iff.mp
  rw [← hspan]
  refine iSup_le fun χ ↦ ?_
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    exact Submodule.zero_mem _
  · simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hm
    obtain ⟨c, hc⟩ :=
      exists_groupLike_coact_eq_tmul_of_basePointsRepresentation_eq_smul hm0 χ hm
    exact Submodule.mem_iSup_of_mem c (GroupLike.mem_weightSpace.mpr hc)

end TauCeti.Comodule
