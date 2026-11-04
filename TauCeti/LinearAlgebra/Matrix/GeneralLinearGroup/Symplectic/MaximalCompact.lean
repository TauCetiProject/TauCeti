/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Symplectic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
public import TauCeti.Topology.Algebra.Matrix.Realify

/-!
# A maximal compact subgroup of the real symplectic group

The orthogonal elements of `TauCeti.GLSymplectic n ℝ` form a maximal compact subgroup.
The existing realification isomorphism identifies this subgroup with the native complex
unitary group `Matrix.unitaryGroup n ℂ`.

The proof is direct. For an element `A = P U` of a compact symplectic subgroup containing
every orthogonal symplectic matrix, symplectic polar preservation puts `U` in that subgroup.
Thus the positive factor `P = A U⁻¹` belongs to it as well, and the trace-growth obstruction
forces `P = 1`; this is the polar-factor argument
`Matrix.GeneralLinearGroup.mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem`, with symplectic
polar preservation supplying its hypothesis.

`TauCeti.GLSymplectic.eq_inf_unitarySubgroup_of_isCompact_of_le` states maximality inside
the ambient real general linear group. `TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`
states it in the subgroup lattice of the symplectic group itself. Both include dimension zero.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition,
  Oxford University Press, 2017, Section 2.2.
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition,
  Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixOrder

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The orthogonal symplectic matrices form a compact subset of the real general linear group,
being the realified image of the complex unitary group. -/
theorem isCompact_inf_unitarySubgroup :
    IsCompact (↑(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) :
      Set (GL (n ⊕ n) ℝ)) := by
  rw [← range_realify_comp_toUnits]
  exact isCompact_range (isClosedEmbedding_realify_comp_toUnits n ℂ).continuous

/-- A compact subgroup of the real symplectic group containing every orthogonal symplectic
matrix consists entirely of orthogonal symplectic matrices. -/
theorem mem_inf_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL (n ⊕ n) ℝ)}
    (hK : IsCompact (K : Set (GL (n ⊕ n) ℝ))) (hKS : K ≤ GLSymplectic n ℝ)
    (hUK : GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) ≤ K)
    {A : GL (n ⊕ n) ℝ} (hA : A ∈ K) :
    A ∈ GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) := by
  have hU : Unitary.toUnits (Units.polarUnitary A) ∈
      GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) :=
    ⟨mem_iff_mem_symplecticGroup.2 (SymplecticGroup.polarUnitary_mem
      (mem_iff_mem_symplecticGroup.1 (hKS hA))), by simp⟩
  exact ⟨hKS hA, mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem hK hA (hUK hU)⟩

/-- **Maximal compactness in the real symplectic group.** A compact subgroup of the ambient
general linear group lying in the symplectic group and containing its orthogonal elements is
exactly their intersection. -/
theorem eq_inf_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL (n ⊕ n) ℝ)}
    (hK : IsCompact (K : Set (GL (n ⊕ n) ℝ))) (hKS : K ≤ GLSymplectic n ℝ)
    (hUK : GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) ≤ K) :
    K = GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) :=
  le_antisymm (fun _ hA ↦ mem_inf_unitarySubgroup_of_isCompact_of_le hK hKS hUK hA) hUK

/-- **The realified unitary group is maximal compact in `Sp(2n, ℝ)`.** Here it is viewed as the
subgroup of orthogonal elements of the symplectic group, with the inherited topology. -/
theorem maximal_isCompact_unitarySubgroup :
    Maximal (fun K : Subgroup (GLSymplectic n ℝ) ↦ IsCompact (K : Set (GLSymplectic n ℝ)))
      ((unitarySubgroup (GL (n ⊕ n) ℝ)).subgroupOf (GLSymplectic n ℝ)) := by
  have hcompact : IsCompact
      (((unitarySubgroup (GL (n ⊕ n) ℝ)).subgroupOf (GLSymplectic n ℝ)) :
        Set (GLSymplectic n ℝ)) := by
    have h : IsCompact
        (↑(((unitarySubgroup (GL (n ⊕ n) ℝ)).subgroupOf (GLSymplectic n ℝ)).map
          (GLSymplectic n ℝ).subtype) : Set (GL (n ⊕ n) ℝ)) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      exact isCompact_inf_unitarySubgroup
    rw [Subgroup.coe_map] at h
    exact Subtype.isCompact_iff.mpr h
  refine ⟨hcompact, fun K hK hUK ↦ ?_⟩
  have hmap : K.map (GLSymplectic n ℝ).subtype =
      GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) := by
    apply eq_inf_unitarySubgroup_of_isCompact_of_le
    · exact hK.image continuous_subtype_val
    · exact Subgroup.map_subtype_le K
    · simpa only [Subgroup.subgroupOf_map_subtype, inf_comm] using
        Subgroup.map_mono (f := (GLSymplectic n ℝ).subtype) hUK
  intro A hA
  have hAmem : (A : GL (n ⊕ n) ℝ) ∈ K.map (GLSymplectic n ℝ).subtype :=
    ⟨A, hA, rfl⟩
  rw [hmap] at hAmem
  exact hAmem.2

end TauCeti.GLSymplectic
