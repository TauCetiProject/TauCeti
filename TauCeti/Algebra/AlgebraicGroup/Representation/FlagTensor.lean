/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.HopfIdeal
public import TauCeti.Algebra.AlgebraicGroup.Representation.TensorProduct.LineStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import Mathlib.LinearAlgebra.Basis.Flag
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.LinearAlgebra.Basis.Flag

/-!
# Encoding a complete basis flag by a tensor line

For a basis with `n` elements, tensor the prefix wedges in exterior degrees `1` through `n`.
The resulting vector is unimodular, and its line stabilizer is the inverse image of the
upper-triangular subgroup under the representation's coordinate morphism. The empty basis
gives the unit vector in the trivial tensor representation.

## Main declarations

* `Module.Basis.flagTensorVector`: the tensor of the prefix wedges of a basis.
* `Module.Basis.isUnimodular_flagTensorVector`: unimodularity of this tensor.
* `Module.Basis.stabilizerHopfIdeal_span_singleton_prefixExteriorVector`: each prefix-wedge line
  detects the stabilizer of the corresponding prefix subspace.
* `Module.Basis.iSup_stabilizerHopfIdeal_flag`: the defining ideal of the complete flag
  stabilizer in a based representation.
* `Module.Basis.stabilizerHopfIdeal_span_singleton_flagTensorVector`: the defining ideal of the flag
  tensor's line stabilizer is the mapped upper-triangular defining ideal.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §21.3.
* J. S. Milne, *Algebraic Groups* (2017), §17.a.
-/

public section

open scoped TensorProduct

universe u v

noncomputable section

namespace TauCeti.Comodule

attribute [local instance] exteriorPower

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]
variable {n : ℕ}

/-- The finite family of exterior-power representations encoding a complete basis flag. -/
abbrev flagExteriorPowers (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Comodule k H V] (n : ℕ) : Fin n → FGComoduleCat.{u, v, u} k H :=
  fun i ↦ FGComoduleCat.of (⋀[k]^(i.val + 1) V)

end TauCeti.Comodule

namespace Module.Basis

open TauCeti TauCeti.Comodule

attribute [local instance] Comodule.exteriorPower

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]
variable {n : ℕ}

/-- The tensor of all nonempty prefix wedges of a basis; its empty value is the tensor unit. -/
def flagTensorVector (b : Module.Basis (Fin n) k V) :
    FGComoduleCat.tensorFin k H n (flagExteriorPowers (H := H) V n) :=
  FGComoduleCat.tensorFinVector k H (flagExteriorPowers (H := H) V n)
    (fun i ↦ prefixExteriorVector b i)

/-- The flag tensor of a basis is unimodular. -/
theorem isUnimodular_flagTensorVector (b : Module.Basis (Fin n) k V) :
    Module.IsUnimodular k (flagTensorVector (H := H) b) :=
  FGComoduleCat.isUnimodular_tensorFinVector k H _ _ (isUnimodular_prefixExteriorVector b)

/-- A prefix-wedge line and its prefix subspace have the same stabilizer Hopf ideal. -/
theorem stabilizerHopfIdeal_span_singleton_prefixExteriorVector
    (b : Module.Basis (Fin n) k V) (i : Fin n) :
    (k ∙ prefixExteriorVector b i).stabilizerHopfIdeal H =
      (b.flag i.succ).stabilizerHopfIdeal H := by
  rw [span_singleton_prefixExteriorVector]
  -- Rewrite the degree together with the exterior-power module and its coaction.
  let P (d : ℕ) : Prop :=
    (LinearMap.range (_root_.exteriorPower.map d (b.flag i.succ).subtype)).stabilizerHopfIdeal H =
      (b.flag i.succ).stabilizerHopfIdeal H
  have hP : P (Module.finrank k (b.flag i.succ)) :=
    Submodule.stabilizerHopfIdeal_range_exteriorPowerMap_finrank (H := H) (b.flag i.succ)
  rw [b.finrank_flag] at hP
  exact hP

omit [Module.Finite k V] in
/-- The intersection of all nonempty prefix-subspace stabilizers is the inverse image of
the upper-triangular subgroup under the based representation. -/
theorem iSup_stabilizerHopfIdeal_flag (b : Module.Basis (Fin n) k V) :
    (⨆ i : Fin n, (b.flag i.succ).stabilizerHopfIdeal H) =
      (GeneralLinear.UpperTriangular.definingHopfIdeal k n).map
        (coordinateBialgHom (H := H) b) := by
  apply eq_of_forall_ge_iff
  intro J
  let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
  let : Comodule k (H ⧸ J.toIdeal) V := Corestrict q.toCoalgHom
  have hflags : (⨆ i : Fin n, (b.flag i.succ).stabilizerHopfIdeal H) ≤ J ↔
      (coefficientMatrix (C := H ⧸ J.toIdeal) b).IsUpperTriangular := by
    rw [← HopfIdeal.toIdeal_le_toIdeal, HopfIdeal.iSup_toIdeal, iSup_le_iff]
    simp only [HopfIdeal.toIdeal_le_toIdeal]
    simp_rw [Submodule.stabilizerHopfIdeal_le_iff_exists_subcomodule]
    rw [coefficientMatrix_isUpperTriangular_iff]
    constructor
    · intro h r
      refine Fin.cases ?_ (fun i ↦ h i) r
      exact ⟨⊥, by simp⟩
    · exact fun h i ↦ h i.succ
  have hupper :
      (GeneralLinear.UpperTriangular.definingHopfIdeal k n).map
          (coordinateBialgHom (H := H) b) ≤ J ↔
        (coefficientMatrix (C := H ⧸ J.toIdeal) b).IsUpperTriangular := by
    rw [← HopfIdeal.toIdeal_le_toIdeal, HopfIdeal.map_toIdeal,
      Ideal.map_le_iff_le_comap, GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal,
      Ideal.span_le]
    rw [coefficientMatrix_corestrict b q.toCoalgHom]
    constructor
    · intro h i j hji
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hx := h ((GeneralLinear.UpperTriangular.mem_definingRelationSet_iff k n _).mpr
        ⟨i, j, hji, rfl⟩)
      change coordinateBialgHom (H := H) b _ ∈ J.toIdeal at hx
      rwa [coordinateBialgHom_X] at hx
    · intro h x hx
      obtain ⟨i, j, hji, rfl⟩ :=
        (GeneralLinear.UpperTriangular.mem_definingRelationSet_iff k n x).mp hx
      change coordinateBialgHom (H := H) b _ ∈ J.toIdeal
      rw [coordinateBialgHom_X]
      exact Ideal.Quotient.eq_zero_iff_mem.mp (h hji)
  exact hflags.trans hupper.symm

/-- The line stabilizer of the flag tensor is the inverse image of the upper-triangular
subgroup, as an equality of defining Hopf ideals over the ground field. -/
theorem stabilizerHopfIdeal_span_singleton_flagTensorVector (b : Module.Basis (Fin n) k V) :
    (k ∙ flagTensorVector (H := H) b).stabilizerHopfIdeal H =
      (GeneralLinear.UpperTriangular.definingHopfIdeal k n).map
        (coordinateBialgHom (H := H) b) := by
  have ht := FGComoduleCat.stabilizerHopfIdeal_span_singleton_tensorFinVector
    (flagExteriorPowers (H := H) V n) (fun i ↦ prefixExteriorVector b i)
    (isUnimodular_prefixExteriorVector b)
  change (k ∙ FGComoduleCat.tensorFinVector k H (flagExteriorPowers (H := H) V n)
    (fun i ↦ prefixExteriorVector b i)).stabilizerHopfIdeal H = _
  rw [ht]
  calc
    _ = ⨆ i : Fin n, (k ∙ prefixExteriorVector b i).stabilizerHopfIdeal H := by
      apply iSup_congr
      intro i
      -- The finite-comodule wrapper reconstructs additive inverses from scalar multiplication.
      -- Its point action agrees with the original exterior-power point action.
      apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
        (H := _root_.CommHopfAlgCat.of k H)
      intro A
      ext g
      let E := flagExteriorPowers (k := k) (H := H) V n i
      have hleft := @Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint
        k H E
        inferInstance inferInstance inferInstance (FGComoduleCat.instAddCommGroupCarrier E)
        inferInstance inferInstance (k ∙ prefixExteriorVector b i) A inferInstance inferInstance g
      exact hleft.trans
        (Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint
          (k ∙ prefixExteriorVector b i) g).symm
    _ = _ :=
      (iSup_congr fun i ↦
        b.stabilizerHopfIdeal_span_singleton_prefixExteriorVector (H := H) i).trans
        (iSup_stabilizerHopfIdeal_flag b)

end Module.Basis

end
