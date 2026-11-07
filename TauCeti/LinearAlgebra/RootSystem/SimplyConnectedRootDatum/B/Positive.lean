/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.SpinWeight
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic

/-!
# Raising paths between type-B spin weights

A positive simple-root step reflects a spin weight whose simple-coroot coordinate is `-1`.
Such steps join two spin weights exactly when their difference lies in the integral positive
root cone of the pinned type-B datum. This gives the weight-order criterion needed to propagate
invariant coordinate lines in the spin representation, without a restriction on characteristic.
The construction includes ranks zero and one; it does not require a valid classification index.

The proof uses the equal length of the spin weights and the invariant-form raising-path theorem
`RootPairing.InvariantForm.reflTransGen_of_sub_eq_sum`. It follows the minuscule argument in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight.Positive`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.2.
-/

public section

namespace TauCeti.DynkinType

open scoped BigOperators

variable {n : ℕ}

local notation "P" => typeBSimplyConnectedRootDatum n
local notation "μ" => typeBSpinWeight (n := n)

/-- A positive simple-root step between spin weights, indexed by their positive sign sets. -/
def TypeBSpinRaisingStep (s t : Finset (Fin n)) : Prop :=
  ∃ i : Fin n, μ s i = -1 ∧ typeBSpinReflection i s = t

/-- A raising step is a simple reflection at which the source has coroot coordinate `-1`. -/
theorem typeBSpinRaisingStep_iff (s t : Finset (Fin n)) :
    TypeBSpinRaisingStep s t ↔
      ∃ i : Fin n, μ s i = -1 ∧ typeBSpinReflection i s = t := Iff.rfl

private theorem typeBSimpleIndex_bijOn :
    Set.BijOn (typeBSimpleIndex n) Set.univ (typeBSimplyConnectedBase n).support :=
  ⟨fun i _ ↦ by simp, typeBSimpleIndex_injective.injOn,
    fun j hj ↦ ⟨⟨j, mem_typeBSimplyConnectedBase_support.mp hj⟩, trivial, Fin.ext (by simp)⟩⟩

/-- The positive root cone in Bourbaki-numbered simple-root coordinates. -/
theorem mem_typeB_posRootCone_iff {x : Fin n → ℤ} :
    x ∈ posRootCone P (typeBSimplyConnectedBase n) ↔
      ∃ c : Fin n → ℕ, x = ∑ i, c i • (P).root (typeBSimpleIndex n i) :=
  mem_posRootCone_iff_exists_nat_of_bijOn P (typeBSimplyConnectedBase n) typeBSimpleIndex_bijOn

private theorem coroot'_typeBSimpleIndex_typeBSpinWeight (i : Fin n) (s : Finset (Fin n)) :
    (P).coroot' (typeBSimpleIndex n i) (μ s) = μ s i := by
  simp

/-- **Raising paths are exactly the positive integral differences of spin weights.**
The reflexive path accounts for equal weights, including the sole weight in rank zero. -/
theorem typeBSpin_raisingPath_iff_mem_posRootCone (s t : Finset (Fin n)) :
    Relation.ReflTransGen TypeBSpinRaisingStep s t ↔
      μ t - μ s ∈ posRootCone P (typeBSimplyConnectedBase n) :=
  (P).toInvariantForm.reflTransGen_iff_sub_mem_posRootCone
    (fun _ hv hne ↦ (P).rootForm_pos_of_ne_zero hv hne) typeBSpinWeight_injective
    ((P).toInvariantForm.apply_self_eq_of_forall_exists_foldl
      typeBSimplyConnectedRootDatum_reflection_typeBSpinWeight exists_typeBSpinReflections_eq)
    typeBSimpleIndex_bijOn typeBSimplyConnectedRootDatum_reflection_typeBSpinWeight
    (fun x i hi ↦ by
      rw [coroot'_typeBSimpleIndex_typeBSpinWeight] at hi ⊢
      rcases typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one x i with h | h | h <;> omega)
    fun _ _ ↦ by simp only [coroot'_typeBSimpleIndex_typeBSpinWeight, TypeBSpinRaisingStep]

end TauCeti.DynkinType
