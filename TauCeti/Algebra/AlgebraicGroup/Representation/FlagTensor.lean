/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.HopfIdeal
public import TauCeti.Algebra.AlgebraicGroup.Representation.TensorLineStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import Mathlib.LinearAlgebra.Basis.Flag
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Corestrict
import TauCeti.LinearAlgebra.Basis.Flag

/-!
# Encoding a complete basis flag by a tensor line

For a basis with `n` elements, tensor the prefix wedges in exterior degrees `1` through `n`.
The resulting vector is unimodular, and its line stabilizer is the inverse image of the
upper-triangular subgroup under the representation's coordinate morphism. The empty basis
gives the unit vector in the trivial tensor representation.

## Main declarations

* `TauCeti.Comodule.flagTensorVector`: the tensor of the prefix wedges of a basis.
* `TauCeti.Comodule.isUnimodular_flagTensorVector`: unimodularity of this tensor.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_prefixExteriorVector`: each prefix-wedge line
  detects the stabilizer of the corresponding prefix subspace.
* `TauCeti.Comodule.iSup_stabilizerHopfIdeal_flag`: the defining ideal of the complete flag
  stabilizer in a based representation.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_flagTensorVector`: the defining ideal of the flag
  tensor's line stabilizer is the mapped upper-triangular defining ideal.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §21.3.
* J. S. Milne, *Algebraic Groups* (2017), §17.a.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v

noncomputable section

attribute [local instance] exteriorPower

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]
variable {n : ℕ}

/-- The prefix wedge through the `i`-th vector of a basis, in exterior degree `i + 1`. -/
def prefixExteriorVector (b : Module.Basis (Fin n) k V) (i : Fin n) : ⋀[k]^(i.val + 1) V :=
  b.exteriorPower (i.val + 1) ⟨Finset.Iic i, Fin.card_Iic i⟩

omit [Module.Finite k V] in
/-- A prefix wedge of a basis is unimodular. -/
theorem isUnimodular_prefixExteriorVector (b : Module.Basis (Fin n) k V) (i : Fin n) :
    Module.IsUnimodular k (prefixExteriorVector b i) :=
  (b.exteriorPower (i.val + 1)).isUnimodular _

/-- The finite family of exterior-power representations encoding a complete basis flag. -/
abbrev flagExteriorPowers (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Comodule k H V] (n : ℕ) : Fin n → FGComoduleCat.{u, v, u} k H :=
  fun i ↦ FGComoduleCat.of (⋀[k]^(i.val + 1) V)

variable (V) in
/-- The tensor of all nonempty prefix wedges of a basis; its empty value is the tensor unit. -/
def flagTensorVector (b : Module.Basis (Fin n) k V) :
    FGComoduleCat.tensorFin k H n (flagExteriorPowers (H := H) V n) :=
  FGComoduleCat.tensorFinVector k H (flagExteriorPowers (H := H) V n)
    (fun i ↦ prefixExteriorVector b i)

/-- The flag tensor of a basis is unimodular. -/
theorem isUnimodular_flagTensorVector (b : Module.Basis (Fin n) k V) :
    Module.IsUnimodular k (flagTensorVector (H := H) V b) :=
  FGComoduleCat.isUnimodular_tensorFinVector k H _ _ (isUnimodular_prefixExteriorVector b)

omit [Module.Finite k V] in
/-- A prefix wedge spans the top exterior image of the corresponding basis flag subspace. -/
theorem span_prefixExteriorVector (b : Module.Basis (Fin n) k V) (i : Fin n) :
    k ∙ prefixExteriorVector b i =
      LinearMap.range (_root_.exteriorPower.map (i.val + 1) (b.flag i.succ).subtype) := by
  apply (Submodule.map_injective_of_injective
    (Submodule.subtype_injective (⋀[k]^(i.val + 1) V))).eq_iff.mp
  rw [Submodule.map_span, Set.image_singleton, ← LinearMap.range_comp,
    _root_.exteriorPower.subtype_comp_map_eq, LinearMap.range_comp, Submodule.range_subtype,
    TauCeti.ExteriorAlgebra.exteriorPower_map_map, Submodule.range_subtype]
  have hflag : b.flag i.succ = Submodule.span k (b '' (Finset.Iic i : Set (Fin n))) := by
    simp only [Module.Basis.flag, Fin.castSucc_lt_succ_iff, Finset.coe_Iic, Set.Iic]
  rw [hflag]
  simpa only [prefixExteriorVector, Submodule.coe_subtype,
    ← ExteriorAlgebra.basis_eq_coe_basis, Fin.card_Iic] using
    (b.map_ι_span_pow_eq_span_exteriorAlgebra (Finset.Iic i)).symm

/-- A prefix-wedge line and its prefix subspace have the same stabilizer Hopf ideal. -/
theorem stabilizerHopfIdeal_span_prefixExteriorVector
    (b : Module.Basis (Fin n) k V) (i : Fin n) :
    (k ∙ prefixExteriorVector b i).stabilizerHopfIdeal H =
      (b.flag i.succ).stabilizerHopfIdeal H := by
  rw [span_prefixExteriorVector]
  -- Rewrite the degree together with the exterior-power module and its coaction.
  let P (d : ℕ) : Prop :=
    (LinearMap.range (_root_.exteriorPower.map d (b.flag i.succ).subtype)).stabilizerHopfIdeal H =
      (b.flag i.succ).stabilizerHopfIdeal H
  have hP : P (Module.finrank k (b.flag i.succ)) :=
    stabilizerHopfIdeal_range_exteriorPowerMap_finrank (H := H) (b.flag i.succ)
  rw [b.finrank_flag] at hP
  exact hP

omit [Module.Finite k V] in
private theorem stabilizer_le_iff_exists_subcomodule_quotient
    (W : Submodule k V) (J : HopfIdeal k H) :
    W.stabilizerHopfIdeal H ≤ J ↔
      letI : Comodule k (H ⧸ J.toIdeal) V :=
        Corestrict (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
      ∃ N : Subcomodule k (H ⧸ J.toIdeal) V, N.toSubmodule = W := by
  let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
  let : Comodule k (H ⧸ J.toIdeal) V := Corestrict q.toCoalgHom
  have hc (ψ : Module.Dual k (V ⧸ W)) (w : V) :
      matrixCoefficient (C := H ⧸ J.toIdeal) (ψ ∘ₗ W.mkQ) w = 0 ↔
        matrixCoefficient (C := H) (ψ ∘ₗ W.mkQ) w ∈ J := by
    rw [CoalgHom.matrixCoefficient_corestrict]
    change Ideal.Quotient.mk J.toIdeal _ = 0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem.trans HopfIdeal.mem_toIdeal
  rw [Submodule.stabilizerHopfIdeal_le_iff]
  constructor
  · intro h
    refine ⟨Subcomodule.ofSubmodule W (fun {w} hw ↦ ?_), rfl⟩
    rw [W.coact_mem_range_iff_forall_matrixCoefficient_eq_zero]
    exact fun ψ ↦ (hc ψ w).mpr (h ψ w hw)
  · rintro ⟨N, hN⟩ ψ w hw
    apply (hc ψ w).mp
    apply (W.coact_mem_range_iff_forall_matrixCoefficient_eq_zero w).mp _ ψ
    rw [← hN]
    have hwN : w ∈ N.toSubmodule := hN.symm ▸ hw
    exact N.coact_mem hwN

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
    simp_rw [stabilizer_le_iff_exists_subcomodule_quotient]
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
theorem stabilizerHopfIdeal_span_flagTensorVector (b : Module.Basis (Fin n) k V) :
    (k ∙ flagTensorVector (H := H) V b).stabilizerHopfIdeal H =
      (GeneralLinear.UpperTriangular.definingHopfIdeal k n).map
        (coordinateBialgHom (H := H) b) := by
  have ht := FGComoduleCat.stabilizerHopfIdeal_span_tensorFinVector
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
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
        CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      have hker (I : HopfIdeal k H) :
          (∀ x ∈ I, g.ofConv x = 0) ↔ I.toIdeal ≤ RingHom.ker g.ofConv := Iff.rfl
      rw [hker, hker]
      let E := flagExteriorPowers (k := k) (H := H) V n i
      have hleft := @Submodule.stabilizerHopfIdeal_le_ker_iff k H E
        inferInstance inferInstance inferInstance (FGComoduleCat.instAddCommGroupCarrier E)
        inferInstance inferInstance (k ∙ prefixExteriorVector b i) A inferInstance inferInstance g
      exact hleft.trans ((k ∙ prefixExteriorVector b i).stabilizerHopfIdeal_le_ker_iff g).symm
    _ = _ :=
      (iSup_congr fun i ↦ stabilizerHopfIdeal_span_prefixExteriorVector (H := H) b i).trans
        (iSup_stabilizerHopfIdeal_flag b)

end

end TauCeti.Comodule
