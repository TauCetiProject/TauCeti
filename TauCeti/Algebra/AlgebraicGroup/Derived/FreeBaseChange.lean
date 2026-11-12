/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.BaseChange

/-!
# The derived subgroup commutes with free base change

If a commutative base algebra `K` is free over `k`, formation of the scheme-theoretic derived
subgroup commutes with extension of scalars from `k` to `K`. In particular this applies to every
field extension. No smoothness, connectedness, reducedness, or finite-type hypothesis is needed.

The coefficient Hopf ideal descends the base-changed derived ideal. Its coefficients are killed
by the original commutator morphism: evaluate the universal commutator after scalar extension
and take coefficients. The largest-Hopf-ideal characterization of the derived subgroup then
provides the reverse of the usual base-change containment.

The coefficient construction and its proof follow the existing common-kernel base-change
argument in `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 10 and 16.
-/

public section

open WithConv TensorProduct
open scoped commutatorElement

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]
variable (H : _root_.CommHopfAlgCat.{v} k)

/-- The scalar extension of the commutator coordinate map is evaluation at the scalar-extended
universal points of its two tensor factors. -/
private theorem map_commutatorAlgHom_eq_commutator :
    toConv (Algebra.TensorProduct.map (AlgHom.id K K)
      (HopfAlgebra.commutatorAlgHom (R := k) (H := H))) =
    ⁅AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
        (toConv ((Algebra.TensorProduct.includeRight (R := k) (A := K)).comp
          (Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := H) (H₂ := H)).toAlgHom)),
      AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
        (toConv ((Algebra.TensorProduct.includeRight (R := k) (A := K)).comp
          (Bialgebra.TensorProduct.includeRight (R := k) (H₁ := H) (H₂ := H)).toAlgHom))⁆ := by
  let j : (H ⊗[k] H) →ₐ[k] K ⊗[k] (H ⊗[k] H) :=
    Algebra.TensorProduct.includeRight
  let e := AlgHom.baseChangePointsMulEquiv
    (k := k) (K := K) (A := H) (R := K ⊗[k] (H ⊗[k] H))
  have he : toConv (Algebra.TensorProduct.map (AlgHom.id K K)
      (HopfAlgebra.commutatorAlgHom (R := k) (H := H))) =
      e (AlgHom.mapValue j (toConv (HopfAlgebra.commutatorAlgHom (R := k) (H := H)))) := by
    apply WithConv.ofConv_injective
    apply Algebra.TensorProduct.ext'
    intro s h
    simp [e, j, Algebra.smul_def]
  rw [he, HopfAlgebra.toConv_commutatorAlgHom]
  simp only [map_mul, map_inv, AlgHom.mapValue_apply, commutatorElement_def, e, j]

/-- Every element of the base-changed derived ideal is killed by the scalar extension of the
original commutator coordinate morphism. -/
private theorem map_commutatorAlgHom_eq_zero_of_mem_derivedDefiningIdeal
    {z : K ⊗[k] H} (hz : z ∈ derivedDefiningIdeal (R := K) (baseChange (K := K) H)) :
    Algebra.TensorProduct.map (AlgHom.id K K)
      (HopfAlgebra.commutatorAlgHom (R := k) (H := H)) z = 0 := by
  have hmem := commutator_mem_derivedPointsSubgroup (baseChange (K := K) H)
    (CommAlgCat.of K (K ⊗[k] (H ⊗[k] H)))
    (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (toConv ((Algebra.TensorProduct.includeRight (R := k) (A := K)).comp
        (Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := H) (H₂ := H)).toAlgHom)))
    (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (toConv ((Algebra.TensorProduct.includeRight (R := k) (A := K)).comp
        (Bialgebra.TensorProduct.includeRight (R := k) (H₁ := H) (H₂ := H)).toAlgHom)))
  rw [← map_commutatorAlgHom_eq_commutator H] at hmem
  exact (mem_quotientPointsSubgroup_iff _ _ _ _).mp hmem z hz

/-- **The derived subgroup commutes with free base change.** The equality of defining Hopf
ideals identifies the scalar extension of the derived subgroup with the derived subgroup of the
scalar extension. In particular, this holds for every field extension. -/
@[simp]
theorem baseChangeHopfIdeal_derivedDefiningIdeal [Module.Free k K] :
    baseChangeHopfIdeal (K := K) (derivedDefiningIdeal (R := k) H) =
      derivedDefiningIdeal (R := K) (baseChange (K := K) H) := by
  classical
  refine le_antisymm (baseChangeHopfIdeal_derivedDefiningIdeal_le H) ?_
  let b := Module.Free.chooseBasis k K
  let I := derivedDefiningIdeal (R := K) (baseChange (K := K) H)
  apply (b.coefficientHopfIdeal_le_iff_le_baseChangeHopfIdeal I _).mp
  rw [le_derivedDefiningIdeal_iff, Module.Basis.coefficientHopfIdeal_toIdeal_le_iff]
  intro z hz j
  have hzero := map_commutatorAlgHom_eq_zero_of_mem_derivedDefiningIdeal H hz
  have hlinear : (HopfAlgebra.commutatorAlgHom (R := k) (H := H)).toLinearMap.lTensor K z =
      0 := (_root_.AlgHom.lTensor_toLinearMap_apply K _ z).trans hzero
  rw [b.lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft] at hlinear
  exact RingHom.mem_ker.mpr (hlinear j)

end TauCeti.CommHopfAlgCat
