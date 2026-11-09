/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Symplectic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
public import TauCeti.Topology.Algebra.SymplecticGroup

/-!
# Maximal compact subgroups of the real and complex symplectic groups

Over `𝕜 = ℝ` or `ℂ`, the unitary elements of the symplectic group `TauCeti.GLSymplectic n 𝕜` form a
maximal compact subgroup. Over `ℝ` this subgroup is the orthogonal symplectic group, which the
realification isomorphism identifies with the complex unitary group `U(n)`
(`TauCeti.GLSymplectic.inf_unitarySubgroup`). Over `ℂ` it is the compact symplectic group
`Sp(n) = Sp(2n, ℂ) ∩ U(2n)`.

The intersection is compact because it is a closed subgroup of the compact unitary group. The
maximality proof is direct. For an element `A = P U` of a compact symplectic subgroup containing
every unitary symplectic matrix, the unitary polar factor `U` is again symplectic
(`SymplecticGroup.polarUnitary_mem`), so it lies in that subgroup. Thus the positive factor
`P = A U⁻¹` belongs to it as well, and the trace-growth obstruction forces `P = 1`. This is the
polar-factor argument
`Matrix.GeneralLinearGroup.mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem`, with the
symplecticity of the polar factors supplying its hypothesis.

`TauCeti.GLSymplectic.eq_inf_unitarySubgroup_of_isCompact_of_le` states maximality inside
the ambient general linear group. `TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`
states it in the subgroup lattice of the symplectic group itself. Both include dimension zero.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition,
  Oxford University Press, 2017, Section 2.2.
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition,
  Springer, 2015, Sections 1.2 and 2.5.
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixOrder ComplexOrder

namespace TauCeti.GLSymplectic

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The unitary symplectic matrices form a compact subset of the general linear group, being a
closed subset of the compact unitary group. -/
theorem isCompact_inf_unitarySubgroup :
    IsCompact (↑(GLSymplectic n 𝕜 ⊓ unitarySubgroup (GL (n ⊕ n) 𝕜)) :
      Set (GL (n ⊕ n) 𝕜)) := by
  rw [Subgroup.coe_inf]
  exact isCompact_unitarySubgroup.inter_left (isClosed_GLSymplectic n 𝕜)

/-- A compact subgroup of the symplectic group containing every unitary symplectic matrix consists
entirely of unitary symplectic matrices. -/
theorem mem_inf_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL (n ⊕ n) 𝕜)}
    (hK : IsCompact (K : Set (GL (n ⊕ n) 𝕜))) (hKS : K ≤ GLSymplectic n 𝕜)
    (hUK : GLSymplectic n 𝕜 ⊓ unitarySubgroup (GL (n ⊕ n) 𝕜) ≤ K)
    {A : GL (n ⊕ n) 𝕜} (hA : A ∈ K) :
    A ∈ GLSymplectic n 𝕜 ⊓ unitarySubgroup (GL (n ⊕ n) 𝕜) := by
  have hU : Unitary.toUnits (Units.polarUnitary A) ∈
      GLSymplectic n 𝕜 ⊓ unitarySubgroup (GL (n ⊕ n) 𝕜) :=
    ⟨mem_iff_mem_symplecticGroup.2 (SymplecticGroup.polarUnitary_mem
      (mem_iff_mem_symplecticGroup.1 (hKS hA))), by simp⟩
  exact ⟨hKS hA, mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem hK hA (hUK hU)⟩

/-- **Maximal compactness in the symplectic group.** A compact subgroup of the ambient general
linear group lying in the symplectic group and containing its unitary elements is exactly their
intersection. -/
theorem eq_inf_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL (n ⊕ n) 𝕜)}
    (hK : IsCompact (K : Set (GL (n ⊕ n) 𝕜))) (hKS : K ≤ GLSymplectic n 𝕜)
    (hUK : GLSymplectic n 𝕜 ⊓ unitarySubgroup (GL (n ⊕ n) 𝕜) ≤ K) :
    K = GLSymplectic n 𝕜 ⊓ unitarySubgroup (GL (n ⊕ n) 𝕜) :=
  le_antisymm (fun _ hA ↦ mem_inf_unitarySubgroup_of_isCompact_of_le hK hKS hUK hA) hUK

/-- **The unitary symplectic matrices form a maximal compact subgroup of `Sp(2n, 𝕜)`.** Over `ℝ`
this is the realified unitary group `U(n)` in `Sp(2n, ℝ)`, and over `ℂ` the compact symplectic group
`Sp(n)` in `Sp(2n, ℂ)`. Here it is viewed as the subgroup of unitary elements of the symplectic
group, with the inherited topology. -/
theorem maximal_isCompact_unitarySubgroup :
    Maximal (fun K : Subgroup (GLSymplectic n 𝕜) ↦ IsCompact (K : Set (GLSymplectic n 𝕜)))
      ((unitarySubgroup (GL (n ⊕ n) 𝕜)).subgroupOf (GLSymplectic n 𝕜)) := by
  have hcompact : IsCompact
      (((unitarySubgroup (GL (n ⊕ n) 𝕜)).subgroupOf (GLSymplectic n 𝕜)) :
        Set (GLSymplectic n 𝕜)) := by
    have h : IsCompact
        (↑(((unitarySubgroup (GL (n ⊕ n) 𝕜)).subgroupOf (GLSymplectic n 𝕜)).map
          (GLSymplectic n 𝕜).subtype) : Set (GL (n ⊕ n) 𝕜)) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      exact isCompact_inf_unitarySubgroup
    rw [Subgroup.coe_map] at h
    exact Subtype.isCompact_iff.mpr h
  refine ⟨hcompact, fun K hK hUK ↦ ?_⟩
  have hmap : K.map (GLSymplectic n 𝕜).subtype =
      GLSymplectic n 𝕜 ⊓ unitarySubgroup (GL (n ⊕ n) 𝕜) := by
    apply eq_inf_unitarySubgroup_of_isCompact_of_le
    · exact hK.image continuous_subtype_val
    · exact Subgroup.map_subtype_le K
    · simpa only [Subgroup.subgroupOf_map_subtype, inf_comm] using
        Subgroup.map_mono (f := (GLSymplectic n 𝕜).subtype) hUK
  intro A hA
  have hAmem : (A : GL (n ⊕ n) 𝕜) ∈ K.map (GLSymplectic n 𝕜).subtype :=
    ⟨A, hA, rfl⟩
  rw [hmap] at hAmem
  exact hAmem.2

end TauCeti.GLSymplectic
