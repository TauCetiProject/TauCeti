/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Subgroup-trivial representations and coinvariants

A representation trivial on a closed subgroup has all its matrix coefficients in the
subgroup's coinvariant algebra. For a projective underlying module the converse holds as
well: linear functionals detect the restricted coaction.

For a normal subgroup, the fixed vectors of a projective representation coincide with those
of the scheme-theoretic kernel of the coinvariant projection, under the flatness hypotheses
defining that projection. In particular, subgroup-trivial representations are trivial on
this kernel. This is the coordinate bridge used to calculate a normal quotient kernel from a
representation that detects the subgroup. The subgroup and value algebras may be nonreduced.

The coefficient calculation uses `Comodule.comul_matrixCoefficient`; detection of point
actions uses `Comodule.endOfPoint_corestrict` and `Comodule.endOfPoint_trivial`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v w x

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R}
variable (I : HopfIdeal R H) (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- A matrix coefficient of a vector fixed by the restricted subgroup coaction is invariant
under right translation by that subgroup. No finiteness or projectivity is required. -/
theorem matrixCoefficient_mem_coinvariants_of_quotient_coact_eq_tmul_one
    (φ : Module.Dual R M) (m : M)
    (hm : TensorProduct.map LinearMap.id
      (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Comodule.coact (R := R) (C := H) m) =
        m ⊗ₜ[R] (1 : H ⧸ I.toIdeal)) :
    Comodule.matrixCoefficient (R := R) (C := H) φ m ∈ I.coinvariants := by
  rw [mem_coinvariants_iff, Comodule.comul_matrixCoefficient,
    ← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map]
  simp only [AlgHom.toLinearMap_id, TensorProduct.AlgebraTensorModule.map_eq,
    TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
  simpa only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_tmul, LinearMap.id_apply, Comodule.matrixCoefficientLinear_apply] using
    congrArg (TensorProduct.map (Comodule.matrixCoefficientLinear (R := R) (C := H) φ)
      LinearMap.id) hm

/-- The restricted coaction fixes a vector in a projective comodule exactly when all its
matrix coefficients restrict to their scalar counit values on the subgroup. -/
theorem quotient_coact_eq_tmul_one_iff [Module.Projective R M] (m : M) :
    TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
        (Comodule.coact (R := R) (C := H) m) = m ⊗ₜ[R] (1 : H ⧸ I.toIdeal) ↔
      ∀ φ : Module.Dual R M,
        Ideal.Quotient.mk I.toIdeal (Comodule.matrixCoefficient (R := R) (C := H) φ m) =
          algebraMap R (H ⧸ I.toIdeal) (φ m) := by
  have hcontract (φ : Module.Dual R M) (z : M ⊗[R] H) :
      LinearMap.tensorComponent φ
        (TensorProduct.comm R M (H ⧸ I.toIdeal)
          (TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap z)) =
        Ideal.Quotient.mk I.toIdeal
          (TensorProduct.lid R H (TensorProduct.map φ LinearMap.id z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul m a => simp [Algebra.smul_def]
    | add z t hz ht => simp [hz, ht]
  constructor
  · intro hm φ
    have h := congrArg (fun z ↦ LinearMap.tensorComponent φ
      (TensorProduct.comm R M (H ⧸ I.toIdeal) z)) hm
    simpa only [hcontract, ← Comodule.matrixCoefficient_def, TensorProduct.comm_tmul,
      LinearMap.tensorComponent_tmul, Algebra.smul_def, mul_one] using h
  · intro h
    apply (TensorProduct.comm R M (H ⧸ I.toIdeal)).injective
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro φ
    rw [hcontract, ← Comodule.matrixCoefficient_def, h]
    simp [Algebra.smul_def]

/-- For a projective comodule, its coefficient algebra lies in the subgroup coinvariants
exactly when the subgroup's restricted coaction is trivial. -/
theorem matrixCoefficientSubalgebra_le_coinvariants_iff [Module.Projective R M] :
    Comodule.matrixCoefficientSubalgebra (R := R) (C := H) (M := M) ≤ I.coinvariants ↔
      ∀ m : M, TensorProduct.map LinearMap.id
        (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Comodule.coact (R := R) (C := H) m) =
          m ⊗ₜ[R] (1 : H ⧸ I.toIdeal) := by
  rw [Comodule.matrixCoefficientSubalgebra_le_iff]
  refine ⟨fun h m ↦ (I.quotient_coact_eq_tmul_one_iff M m).mpr ?_, fun h φ m ↦
    I.matrixCoefficient_mem_coinvariants_of_quotient_coact_eq_tmul_one M φ m (h m)⟩
  intro φ
  simpa only [Comodule.counit_matrixCoefficient] using
    I.mk_eq_algebraMap_counit_of_mem_coinvariants (h φ m)

namespace IsNormal

variable {I} [Module.Flat R H] [Module.Flat R I.coinvariants]
  [Module.Flat R (H ⧸ Subalgebra.toSubmodule I.coinvariants)]

/-- The vectors fixed by a normal subgroup in a projective comodule are exactly those fixed
by the scheme-theoretic kernel of its coinvariant projection. This compares the whole restricted
coactions, including infinitesimal information. -/
@[simp]
theorem quotient_coact_kernel_coinvariantsι_eq_tmul_one_iff [Module.Projective R M]
    (hI : I.IsNormal) (m : M) :
    TensorProduct.map LinearMap.id
      (Ideal.Quotient.mkₐ R
        (CommHopfAlgCat.kernelHopfIdeal (CommHopfAlgCat.coinvariantsι hI)).toIdeal).toLinearMap
      (Comodule.coact (R := R) (C := H) m) =
        m ⊗ₜ[R] (1 : H ⧸
          (CommHopfAlgCat.kernelHopfIdeal (CommHopfAlgCat.coinvariantsι hI)).toIdeal) ↔
      TensorProduct.map LinearMap.id
        (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Comodule.coact (R := R) (C := H) m) =
          m ⊗ₜ[R] (1 : H ⧸ I.toIdeal) := by
  let J := CommHopfAlgCat.kernelHopfIdeal (CommHopfAlgCat.coinvariantsι hI)
  constructor
  · intro hm
    apply (I.quotient_coact_eq_tmul_one_iff M m).mpr
    intro φ
    have hc := (J.quotient_coact_eq_tmul_one_iff M m).mp hm φ
    let f := Ideal.Quotient.factorₐ R (HopfIdeal.toIdeal_le_toIdeal.mpr
      (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hI))
    have hf := congrArg f hc
    dsimp only [f] at hf
    rw [Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk,
      AlgHom.commutes] at hf
    exact hf
  · intro hm
    apply (J.quotient_coact_eq_tmul_one_iff M m).mpr
    intro φ
    let b : CommHopfAlgCat.coinvariants hI :=
      ⟨Comodule.matrixCoefficient (R := R) (C := H) φ m,
        I.matrixCoefficient_mem_coinvariants_of_quotient_coact_eq_tmul_one M φ m hm⟩
    have hv := AlgHom.congr_fun
      ((CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff
        (CommHopfAlgCat.coinvariantsι hI) (CommHopfAlgCat.mkQuotient H J).hom.toAlgHom).mp
          (by rw [CommHopfAlgCat.mkQuotient_ker])) b
    have hε := CoalgHomClass.counit_comp_apply (CommHopfAlgCat.coinvariantsι hI).hom b
    rw [CommHopfAlgCat.hopfSubalgebraι_apply, Comodule.counit_matrixCoefficient] at hε
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, Algebra.ofId_apply,
      Bialgebra.counitAlgHom_apply] at hv
    rw [CommHopfAlgCat.hopfSubalgebraι_apply, ← hε] at hv
    rw [CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk] at hv
    exact hv

/-- Every point in the scheme-theoretic kernel of a normal coinvariant projection acts
trivially on every projective representation trivial on the original subgroup.
This holds over arbitrary commutative value algebras. -/
theorem endOfPoint_eq_id_of_mem_kernel_coinvariantsι [Module.Projective R M]
    (hI : I.IsNormal)
    (hM : ∀ m : M, TensorProduct.map LinearMap.id
      (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap (Comodule.coact (R := R) (C := H) m) =
        m ⊗ₜ[R] (1 : H ⧸ I.toIdeal))
    (A : CommAlgCat.{x} R) (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup H
      (CommHopfAlgCat.kernelHopfIdeal (CommHopfAlgCat.coinvariantsι hI)) A) :
    Comodule.endOfPoint M g.ofConv = LinearMap.id := by
  let J := CommHopfAlgCat.kernelHopfIdeal (CommHopfAlgCat.coinvariantsι hI)
  obtain ⟨q, rfl⟩ := hg
  let π := (CommHopfAlgCat.mkQuotient H J).hom
  have htrivial : Comodule.Corestrict (M := M) π.toCoalgHom =
      Comodule.trivial (R := R) (C := CommHopfAlgCat.quotient H J) (M := M) := by
    apply Comodule.ext
    ext m
    simp only [Comodule.corestrict_coact_apply, Comodule.trivial_coact_apply, π]
    rw [CommHopfAlgCat.mkQuotient_toLinearMap]
    exact (hI.quotient_coact_kernel_coinvariantsι_eq_tmul_one_iff M m).mpr (hM m)
  rw [CommHopfAlgCat.quotientPointsHom_apply]
  rw [← Comodule.endOfPoint_corestrict π q.ofConv, htrivial]
  exact Comodule.endOfPoint_trivial q.ofConv

end IsNormal

end TauCeti.HopfIdeal
