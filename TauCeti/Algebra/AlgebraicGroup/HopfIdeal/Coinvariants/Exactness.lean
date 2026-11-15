/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
import Mathlib.RingTheory.FiniteStability
import TauCeti.Algebra.AlgebraicGroup.Representation.Coinvariants
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.EquivariantHom
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.FamilyInvariant
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.WeightSumStabilizer

/-!
# Exact kernels of normal affine quotient projections

For a geometrically reduced affine group of finite type over a field, the projection
defined by the coinvariants of a normal closed subgroup has that subgroup as its
scheme-theoretic kernel. The subgroup itself need not be reduced or smooth.

Over an algebraically closed field, a Chevalley line realizes the subgroup as a line
stabilizer in a representation spanned by its subgroup character spaces. Endomorphisms
preserving each character space are subgroup-invariant in the Hom representation.
The coinvariant kernel fixes those endomorphisms, so its universal point centralizes
them and consequently stabilizes the line. Testing at the universal point retains
the full defining ideal, including infinitesimal structure. The result over an
arbitrary field follows by scalar extension to an algebraic closure and descent.

This combines `HopfIdeal.IsNormal.exists_finite_weightSum_line_stabilizer`, the
character-space centralizer criterion, the fixed-vector comparison for coinvariant
kernels, and `CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_baseChange_eq_iff`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

noncomputable section

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}
  [Algebra.FiniteType k H] {I : HopfIdeal k H}

attribute [local instance] Comodule.linearHom

private theorem kernelHopfIdeal_coinvariantsι_eq_of_isAlgClosed
    [IsAlgClosed k] [IsReduced H] (hI : I.IsNormal) :
    kernelHopfIdeal (coinvariantsι hI) = I := by
  let J := kernelHopfIdeal (coinvariantsι hI)
  let A := CommAlgCat.of k (H ⧸ J.toIdeal)
  let g : HopfAlgebra.points (R := k) (H := H) A :=
    toConv (Ideal.Quotient.mkₐ k J.toIdeal)
  obtain ⟨V, hV, χ, L, _, hL, hstab⟩ :=
    HopfIdeal.IsNormal.exists_finite_weightSum_line_stabilizer.{u, v, v} hI
  have hg : g ∈ quotientPointsSubgroup H I A := by
    apply (I.mem_quotientPointsSubgroup_iff_forall_commute_familyInvariant_of_subspace_stabilizer
      V hV χ L hL A g ((hstab A g).mpr)).mpr
    intro p hp
    have hpI : p ∈ I.weightSpace (Module.End k V) 1 :=
      (I.mem_weightSpace_linearHom_one_iff_forall_mapsTo_weightSpace hV p).mpr
        (Submodule.mem_familyInvariant.mp hp)
    have hpJ : p ∈ J.weightSpace (Module.End k V) 1 := by
      rw [HopfIdeal.mem_weightSpace, GroupLike.val_one] at hpI ⊢
      exact (hI.quotient_coact_kernel_coinvariantsι_eq_tmul_one_iff
        (Module.End k V) p).mpr hpI
    have hfixed := (J.mem_weightSpace_iff_endOfPoint 1 p).mp hpJ
    rw [GroupLike.val_one] at hfixed
    exact ((Comodule.endOfPoint_linearHom_one_tmul_eq_iff g p).mp hfixed).symm
  apply le_antisymm (kernelHopfIdeal_coinvariantsι_le hI)
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((mem_quotientPointsSubgroup_iff H I A g).mp hg x hx)

/-- **The normal affine quotient has exactly the prescribed scheme-theoretic kernel.**
For a geometrically reduced finite-type affine group over any field, the kernel of
the coinvariant projection is the original normal subgroup, including its possibly
nonreduced structure. -/
@[simp]
theorem kernelHopfIdeal_coinvariantsι_eq [Algebra.IsGeometricallyReduced k H]
    (hI : I.IsNormal) : kernelHopfIdeal (coinvariantsι hI) = I := by
  apply (kernelHopfIdeal_coinvariantsι_baseChange_eq_iff
    (K := AlgebraicClosure k) hI).mp
  exact kernelHopfIdeal_coinvariantsι_eq_of_isAlgClosed
    (isNormal_baseChangeHopfIdeal (K := AlgebraicClosure k) hI)

end

end TauCeti.CommHopfAlgCat
