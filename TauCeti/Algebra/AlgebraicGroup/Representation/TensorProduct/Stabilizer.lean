/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.LinearAlgebra.TensorProduct.Submodule
import TauCeti.LinearAlgebra.Unimodular

/-!
# Line stabilizers in a tensor product of comodules

Over a field `k`, the scheme-theoretic stabilizer of the line spanned by a nonzero pure tensor
`m ⊗ₜ n` in the diagonal tensor product `M ⊗[k] N` of two `H`-comodules is the supremum (that is,
intersection of closed subgroups) of the line stabilizers of `m` and `n`.

## Main results

* `Submodule.stabilizerHopfIdeal_span_singleton_tmul`: the stabilizer Hopf ideal of
  `k ∙ (m ⊗ₜ[k] n)` equals `(k ∙ m).stabilizerHopfIdeal H ⊔ (k ∙ n).stabilizerHopfIdeal H`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.5.
-/

public section

open TensorProduct

namespace Submodule

section Stabilizer

universe u v w₁ w₂

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
variable {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]
variable [AddCommGroup N] [Module k N] [TauCeti.Comodule k H N]

/-- Over a field, the stabilizer Hopf ideal of the line spanned by a nonzero pure tensor `m ⊗ₜ n` is
the supremum of the line stabilizers of `m` and `n`. -/
theorem stabilizerHopfIdeal_span_singleton_tmul {m : M} (hm : m ≠ 0) {n : N} (hn : n ≠ 0) :
    (letI : TauCeti.Comodule k H (M ⊗[k] N) := TauCeti.Comodule.tensor k H M N
     (k ∙ (m ⊗ₜ[k] n)).stabilizerHopfIdeal H) =
      (k ∙ m).stabilizerHopfIdeal H ⊔ (k ∙ n).stabilizerHopfIdeal H := by
  let _ : TauCeti.Comodule k H (M ⊗[k] N) := TauCeti.Comodule.tensor k H M N
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one k hm
  obtain ⟨ψ₀, hψ₀⟩ := Module.Projective.exists_dual_eq_one k hn
  have hmU : Module.IsUnimodular k m := Module.isUnimodular_of_apply_eq_one hφ₀
  have hnU : Module.IsUnimodular k n := Module.isUnimodular_of_apply_eq_one hψ₀
  refine stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff
    (k ∙ (m ⊗ₜ[k] n)) ((k ∙ m).stabilizerHopfIdeal H ⊔ (k ∙ n).stabilizerHopfIdeal H)
    fun A _ _ g ↦ ?_
  rw [TauCeti.CommHopfAlgCat.quotientPointsSubgroup_sup, Subgroup.mem_inf,
    mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint,
    mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint]
  have hmu : Module.IsUnimodular A ((1 : A) ⊗ₜ[k] m) := hmU.one_tmul
  have hnu : Module.IsUnimodular A ((1 : A) ⊗ₜ[k] n) := hnU.one_tmul
  simp only [Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply,
    Submodule.map_span]
  let d := TensorProduct.AlgebraTensorModule.distribBaseChange k A M N
  have hinj : Function.Injective d.toLinearMap := d.injective
  rw [← (Submodule.map_injective_of_injective hinj).eq_iff]
  simp only [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe]
  have hd1 : d (TauCeti.Comodule.endOfPoint (M ⊗[k] N) g.ofConv (1 ⊗ₜ[k] (m ⊗ₜ[k] n))) =
      TauCeti.Comodule.endOfPoint M g.ofConv (1 ⊗ₜ[k] m) ⊗ₜ[A]
        TauCeti.Comodule.endOfPoint N g.ofConv (1 ⊗ₜ[k] n) := by
    have h := congrArg d (TauCeti.Comodule.endOfPoint_tensor_tmul g.ofConv (1 : A) 1 m n).symm
    simpa [d] using h
  have hd0 : d (1 ⊗ₜ[k] (m ⊗ₜ[k] n)) = (1 ⊗ₜ[k] m) ⊗ₜ[A] (1 ⊗ₜ[k] n) := by simp [d]
  rw [hd1, hd0]
  exact (hmu.span_singleton_tmul_eq_iff hnu).symm

end Stabilizer

end Submodule
