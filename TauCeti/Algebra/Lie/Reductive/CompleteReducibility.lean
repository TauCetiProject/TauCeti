/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Reductive.Basic
import TauCeti.Algebra.Lie.Submodule.Interval
import TauCeti.Algebra.Lie.Weights.Semisimple
import Mathlib.Algebra.Lie.LieTheorem
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Order.CompactlyGenerated.Intervals

/-!
# Complete reducibility for reductive Lie algebras

A finite-dimensional module of a reductive Lie algebra in characteristic zero is completely
reducible if the center acts semisimply and its actions split over the field. In particular,
over an algebraically closed field it suffices that every central element act semisimply.
The condition on the center is essential: an abelian Lie algebra can act by a nonzero
nilpotent operator.

The center's weight spaces are submodules for the whole Lie algebra. On each such space
the center acts by scalars, so Weyl's theorem for the semisimple derived ideal supplies
complements for the whole algebra. Since these weight spaces span, their sum is completely
reducible. This is the representation-theoretic step that lets semisimple central actions
supplement Weyl's theorem when the Lie algebra has nonzero center.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§6 and 19.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 22.
* `TauCeti.Algebra.Lie.Reductive.Basic`, for the center/derived-ideal decomposition, and
  `TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility`, for Weyl's theorem.
-/

public section

open LieAlgebra LieModule

namespace TauCeti

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {L : Type v} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.HasCentralRadical K L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-- If the center acts by scalars on a finite-dimensional module of a reductive Lie algebra,
every Lie submodule has a complement. The ground field need not be algebraically closed. -/
theorem exists_isCompl_of_forall_center_lie_eq_smul
    (hZ : ∀ z ∈ center K L, ∃ c : K, ∀ m : M, ⁅z, m⁆ = c • m)
    (N : LieSubmodule K L M) : ∃ P : LieSubmodule K L M, IsCompl N P := by
  let N' : LieSubmodule K (derivedSeries K L 1) M :=
    N.restr (derivedSeries K L 1).toLieSubalgebra
  obtain ⟨P, hP⟩ := exists_isCompl_of_isKilling N'
  let Q : LieSubmodule K L M :=
    { P.toSubmodule with
      lie_mem := by
        intro x m hm
        obtain ⟨z, hz, d, hd, rfl⟩ := exists_mem_center_add_mem_derivedSeries K L x
        obtain ⟨c, hc⟩ := hZ z hz
        rw [add_lie, hc]
        exact P.add_mem (P.smul_mem c hm) (P.lie_mem (x := ⟨d, hd⟩) hm) }
  have hPQ : IsCompl N.toSubmodule Q.toSubmodule := by
    -- Q was built from P.toSubmodule, so their underlying submodules are definitionally equal.
    simpa only [N', LieSubmodule.restr_toSubmodule] using
      LieSubmodule.isCompl_toSubmodule.mpr hP
  exact ⟨Q, LieSubmodule.isCompl_toSubmodule.mp hPQ⟩

/-- A finite-dimensional module of a reductive Lie algebra is completely reducible whenever
its honest central weight spaces span. This split form works over the original field. -/
theorem complementedLattice_lieSubmodule_of_iSup_weightSpace_center_eq_top
    (hZ : ⨆ χ : center K L → K,
      (weightSpace M χ).toSubmodule = ⊤) :
    ComplementedLattice (LieSubmodule K L M) := by
  let W (χ : center K L → K) : LieSubmodule K L M := weightSpaceOfIsLieTower K M χ
  -- The tower construction changes only the Lie action, retaining the underlying weight space.
  -- Mathlib provides no named equality for this projection.
  have hW_toSubmodule (χ : center K L → K) :
      (W χ).toSubmodule = (weightSpace M χ).toSubmodule := rfl
  have hW (χ : center K L → K) : ComplementedLattice (LieSubmodule K L (W χ)) := by
    refine ⟨exists_isCompl_of_forall_center_lie_eq_smul ?_⟩
    intro z hz
    refine ⟨χ ⟨z, hz⟩, fun m ↦ ?_⟩
    have hm : (m : M) ∈ (weightSpace M χ).toSubmodule := by
      rw [← hW_toSubmodule]
      exact m.property
    apply Subtype.ext
    simpa only [LieSubmodule.coe_bracket, LieSubmodule.coe_smul,
      LieIdeal.coe_bracket_of_module] using
      (mem_weightSpace χ (m : M)).mp hm ⟨z, hz⟩
  refine complementedLattice_of_complementedLattice_Iic
    (s := Set.univ) (f := W) ?_ ?_
  · intro χ _
    have := hW χ
    exact (W χ).mapIic.complementedLattice
  · apply LieSubmodule.toSubmodule_injective
    simpa only [iSup_univ, LieSubmodule.iSup_toSubmodule,
      LieSubmodule.top_toSubmodule, hW_toSubmodule] using hZ

/-- Over a splitting field for the central action, semisimplicity of each central operator
implies complete reducibility of a finite-dimensional module of a reductive Lie algebra. -/
theorem complementedLattice_lieSubmodule_of_isSemisimple_center
    [IsTriangularizable K (center K L) M]
    (hZ : ∀ z : center K L, (toEnd K (center K L) M z).IsSemisimple) :
    ComplementedLattice (LieSubmodule K L M) := by
  apply complementedLattice_lieSubmodule_of_iSup_weightSpace_center_eq_top
  simp_rw [← genWeightSpace_eq_weightSpace_of_isFinitelySemisimple
    (fun z ↦ (hZ z).isFinitelySemisimple), ← LieSubmodule.iSup_toSubmodule,
    iSup_genWeightSpace_eq_top K (center K L) M, LieSubmodule.top_toSubmodule]

end TauCeti
