/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
-- The quaternion model and Clifford-group characterization enter only the membership proof.
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Quaternion
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Four

/-!
# Units of ternary even Clifford algebras

Every unit of the even Clifford algebra of a nondegenerate ternary quadratic space belongs to
the Lipschitz group. Thus the full quaternion unit group, including units whose norms are not
squares, acts on the quadratic space. This is the input to the quaternion description of the
special orthogonal group over the base field.

The quaternion model in `CliffordAlgebra.exists_evenQuaternionEquiv_of_finrank_eq_three`
identifies reversal with conjugation. Its norm is a nonzero scalar, so conjugation by an even
unit preserves the odd elements fixed by reversal, which in dimension three are the vectors.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion

namespace CliffordAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- The reversal of a ternary even unit is a nonzero scalar times its inverse. -/
private theorem exists_reverse_eq_scalar_mul_inv (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (x : (even Q)ˣ) :
    ∃ r : Kˣ, reverse ((x : even Q) : CliffordAlgebra Q) =
      algebraMap K _ r * ((x⁻¹ : (even Q)ˣ) : even Q) := by
  obtain ⟨a, b, e, he⟩ := exists_evenQuaternionEquiv_of_finrank_eq_three Q hQ hV
  have hn : IsUnit (QuaternionAlgebra.normForm (a : K) 0 (b : K) (e x)) :=
    (QuaternionAlgebra.isUnit_iff_normForm_isUnit _ _ _ _).mp (x.isUnit.map e)
  obtain ⟨r, hr⟩ := hn
  have hnorm : reverseEven Q (x : even Q) * x = algebraMap K _ (r : K) := by
    apply e.injective
    rw [map_mul, he, QuaternionAlgebra.star_mul_self, AlgEquiv.commutes, hr]
    rfl
  have hrev := congrArg (fun z : even Q => z * (x⁻¹ : (even Q)ˣ)) hnorm
  refine ⟨r, ?_⟩
  simpa [mul_assoc] using congrArg (fun z : even Q => (z : CliffordAlgebra Q)) hrev

/-- Every unit of a regular ternary even Clifford algebra is a Lipschitz unit. -/
theorem unitsMap_even_mem_lipschitzGroup_of_finrank_eq_three (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (x : (even Q)ˣ) :
    Units.map (even Q).val.toMonoidHom x ∈ lipschitzGroup Q := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨r, hr⟩ := exists_reverse_eq_scalar_mul_inv Q hQ hV x
  have hir : reverse (((x⁻¹ : (even Q)ˣ) : even Q) : CliffordAlgebra Q) =
      algebraMap K _ (r⁻¹ : Kˣ) * ((x : even Q) : CliffordAlgebra Q) := by
    let y := Units.map (even Q).val.toMonoidHom x
    have hn : reverse (y : CliffordAlgebra Q) * y = algebraMap K _ (r : K) := by
      -- `y` abbreviates a mapped unit: its value projection is the subalgebra inclusion of `x`.
      -- `change` unfolds these wrappers to expose the expression in `hr`.
      change reverse ((x : even Q) : CliffordAlgebra Q) *
        ((x : even Q) : CliffordAlgebra Q) = _
      rw [hr, mul_assoc]
      simp only [← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one, mul_one]
    -- The inverse projection of `Units.map` includes `x⁻¹` in the ambient algebra.
    -- `change` folds that definitional projection into `y⁻¹` for `reverse_inv_mul_inv`.
    change reverse ((y⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap K _ (r⁻¹ : Kˣ) * (y : CliffordAlgebra Q)
    rw [← reverse_inv_mul_inv hn, mul_assoc, Units.inv_mul, mul_one]
  refine mem_lipschitzGroup_of_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit fun m => ?_
  have hxe : ((x : even Q) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule Q]
    exact (x : even Q).2
  have hxie : (((x⁻¹ : (even Q)ˣ) : even Q) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule Q]
    exact ((x⁻¹ : (even Q)ˣ) : even Q).2
  -- The unit-map projection is the subalgebra inclusion, on values and inverses.
  change involute ((x : even Q) : CliffordAlgebra Q) * ι Q m *
    (((x⁻¹ : (even Q)ˣ) : even Q) : CliffordAlgebra Q) ∈ LinearMap.range (ι Q)
  rw [involute_eq_of_mem_even hxe]
  have hodd : ((x : even Q) : CliffordAlgebra Q) * ι Q m *
      (((x⁻¹ : (even Q)ˣ) : even Q) : CliffordAlgebra Q) ∈ evenOdd Q 1 := by
    exact add_zero (1 : ZMod 2) ▸ SetLike.mul_mem_graded
      (zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded hxe (ι_mem_evenOdd_one Q m)) hxie
  refine mem_range_ι_of_mem_evenOdd_one_of_reverse_eq_of_finrank_le_four Q (by omega) hodd ?_
  rw [reverse.map_mul, reverse.map_mul, reverse_ι, hr, hir]
  -- Reassociate the central scalar factors so the reverse norm and its inverse cancel.
  simp only [← mul_assoc]
  rw [mul_assoc (algebraMap K _ (r⁻¹ : Kˣ) * ((x : even Q) : CliffordAlgebra Q))
    (ι Q m) (algebraMap K _ (r : Kˣ)), ← Algebra.commutes (r : K) (ι Q m)]
  simp only [← mul_assoc]
  rw [mul_assoc (algebraMap K _ (r⁻¹ : Kˣ)) ((x : even Q) : CliffordAlgebra Q)
    (algebraMap K _ (r : Kˣ)), ← Algebra.commutes (r : K)
      ((x : even Q) : CliffordAlgebra Q)]
  simp only [← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, map_one, one_mul]

end CliffordAlgebra
