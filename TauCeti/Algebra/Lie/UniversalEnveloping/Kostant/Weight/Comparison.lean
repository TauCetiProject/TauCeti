/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Lattice
public import TauCeti.Algebra.Lie.Basis.Cartan
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Basis
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Basis
public import TauCeti.Algebra.Lie.Weights.Basis
import TauCeti.Algebra.Lie.Weights.Basic
import TauCeti.Algebra.Module.Submodule.Finite

/-!
# Comparing integral and rational weight spaces

A full Kostant-stable lattice with an integral weight decomposition has the same weights as its
rational representation. Its integral weight slices span the rational generalized weight spaces.
The extended lattice weight basis consists of honest weight vectors, so no algebraic-closure
assumption is required to compare honest and generalized weight spaces.

The coordinates of a weight are its values on the Cartan generators of a Lie algebra basis.
These are fundamental-weight coordinates when those generators are the simple coroots.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 2, Corollary 1 to Theorem 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.1.
-/

public section

namespace LieAlgebra.Basis

open LieModule Module TauCeti.UniversalEnvelopingAlgebra

variable {ι L V : Type*} [Finite ι] [LieRing L] [LieAlgebra ℚ L]
  {H : LieSubalgebra ℚ L} (b : LieAlgebra.Basis ι H)
  [AddCommGroup V] [Module ℚ V] [LieRingModule L V] [LieModule ℚ L V]

/-- Joint eigenvalues on the Cartan generators specify the corresponding honest weight space. -/
theorem jointWeightSpace_eq_weightSpace (χ : Dual ℚ H) (μ : ι → ℤ)
    (hχ : ∀ j, χ (b.h' j) = (μ j : ℚ)) :
    jointWeightSpace b.h (representation ℚ L V) μ =
      (weightSpace V (χ : H → ℚ)).toSubmodule := by
  ext x
  rw [mem_jointWeightSpace_iff, isCartanWeightVector_iff, LieSubmodule.mem_toSubmodule,
    b.cartanBasis.mem_weightSpace_iff_forall_basis]
  simp only [representation_ι_apply, cartanBasis_apply, hχ]
  -- The restricted H-action is the ambient L-action, and `b.h' j` is `b.h j` bundled in H.
  rfl

variable [LieRing.IsNilpotent H] (N : Submodule ℤ V) [N.IsLattice ℚ]
  (hN : ∀ u ∈ b.kostantForm, ∀ x ∈ N, representation ℚ L V u x ∈ N)
  (hV : ∀ x ∈ N, x ∈ ⨆ μ : ι → ℤ, jointWeightSpace b.h (representation ℚ L V) μ)

include hN hV in
/-- A full admissible lattice makes generalized Cartan weight spaces honest weight spaces. -/
theorem genWeightSpace_eq_weightSpace_of_isLattice (χ : H → ℚ) :
    genWeightSpace V χ = weightSpace V χ := by
  have hN' : ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm b.rootGenerator b.h,
      ∀ x ∈ N.toAddSubgroup, representation ℚ L V u x ∈ N.toAddSubgroup := by
    intro u hu x hx
    exact hN u (by rwa [b.kostantForm_def]) x hx
  let B : Module.Basis _ ℤ N := kostantWeightBasis b.rootGenerator b.h
    (representation ℚ L V) N.toAddSubgroup hN' (fun x => hV x x.property)
  let w := fun a : (Σ μ : ι → ℤ, Module.Free.ChooseBasisIndex ℤ
      (weightSublattice b.h (representation ℚ L V) N.toAddSubgroup μ)) =>
    b.cartanBasis.constr ℚ (fun j => (a.1 j : ℚ))
  have hB : ∀ a x, ⁅x, B.extendOfIsLattice ℚ a⁆ = w a x • B.extendOfIsLattice ℚ a := by
    intro a
    apply (mem_weightSpace _ _).mp
    rw [Module.Basis.extendOfIsLattice_apply, ← LieSubmodule.mem_toSubmodule,
      ← b.jointWeightSpace_eq_weightSpace (w a) a.1
        (fun j => by simp [w, ← cartanBasis_apply]), mem_jointWeightSpace_iff]
    exact isCartanWeightVector_kostantWeightBasis b.rootGenerator b.h
      (representation ℚ L V) N.toAddSubgroup hN' (fun x => hV x x.property) a
  exact (B.extendOfIsLattice ℚ).genWeightSpace_eq_weightSpace_of_weight_basis hB χ

include hN hV in
/-- The integral weight slice of a full admissible lattice spans the rational generalized
weight space. -/
theorem span_weightSublattice_eq_genWeightSpace (χ : Dual ℚ H) (μ : ι → ℤ)
    (hχ : ∀ j, χ (b.h' j) = (μ j : ℚ)) :
    Submodule.span ℚ ((fun x : N.toAddSubgroup => (x : V)) ''
        (weightSublattice b.h (representation ℚ L V) N.toAddSubgroup μ : Set N.toAddSubgroup)) =
      (genWeightSpace V (χ : H → ℚ)).toSubmodule := by
  rw [b.genWeightSpace_eq_weightSpace_of_isLattice N hN hV]
  exact (span_weightSublattice_eq_jointWeightSpace b.h (representation ℚ L V) N
    Submodule.IsLattice.span_eq_top μ).trans (b.jointWeightSpace_eq_weightSpace χ μ hχ)

include hN hV in
/-- An integral weight occurs in a full admissible lattice exactly when the associated rational
weight occurs in its representation. -/
theorem weightSublattice_ne_bot_iff (χ : Dual ℚ H) (μ : ι → ℤ)
    (hχ : ∀ j, χ (b.h' j) = (μ j : ℚ)) :
    weightSublattice b.h (representation ℚ L V) N.toAddSubgroup μ ≠ ⊥ ↔
      genWeightSpace V (χ : H → ℚ) ≠ ⊥ := by
  simp only [ne_eq]
  apply not_congr
  rw [← LieSubmodule.toSubmodule_eq_bot,
    ← b.span_weightSublattice_eq_genWeightSpace N hN hV χ μ hχ, Submodule.span_eq_bot]
  simp only [Set.forall_mem_image, ZeroMemClass.coe_eq_zero, Submodule.eq_bot_iff]
  exact ⟨fun h x hx => h x hx, fun h x hx => h hx⟩

end LieAlgebra.Basis
