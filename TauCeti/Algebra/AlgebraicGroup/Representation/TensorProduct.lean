/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct.Contraction
import TauCeti.LinearAlgebra.TensorProduct.Submodule
import TauCeti.LinearAlgebra.Unimodular

/-!
# Points, tangent vectors, and stabilizers on a tensor product of comodules

The tensor product `M ⊗ N` of two comodules over a bialgebra `H` carries the diagonal coaction
`m ⊗ n ↦ m₀ ⊗ n₀ ⊗ m₁ n₁` (`TauCeti.Comodule.tensor`). This file computes the two actions that a
comodule representation induces on it, and characterizes the stabilizer of a pure-tensor line:

* a base-valued point `g` of `H` acts **diagonally**, `g • (m ⊗ n) = g • m ⊗ g • n`, because `g`
  is multiplicative;
* a tangent vector `d` at the identity acts by the **Leibniz rule**,
  `d • (m ⊗ n) = d • m ⊗ n + m ⊗ d • n`, because `d` is a derivation into the counit
  coefficients;
* over a field, the scheme-theoretic line stabilizer of a nonzero pure tensor `m ⊗ₜ n` is the
  supremum of the line stabilizers of `m` and `n`
  (`Submodule.stabilizerHopfIdeal_span_singleton_tmul`).

The first is the statement that the comodule tensor product integrates the tensor product of
group representations; the second, that differentiating a representation turns tensor products
of representations of the group into tensor products of representations of its Lie algebra.

## Main results

* `TauCeti.Comodule.basePointsRepresentation_tensor_tmul`: a base-valued point acts diagonally on
  the tensor product comodule.
* `TauCeti.Comodule.differential_tensor_tmul`: a tangent vector acts on the tensor product
  comodule by the Leibniz rule.
* `Submodule.stabilizerHopfIdeal_span_singleton_tmul`: over a field, the stabilizer Hopf ideal of
  the line spanned by a nonzero pure tensor `m ⊗ₜ n` is the supremum of the line stabilizers of
  `m` and `n`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.7 and I.7.11.
* J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 10.
-/

public section

open TensorProduct WithConv

namespace TauCeti.Comodule

attribute [local instance] tensor

section Points

variable {R H V W : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V] [Comodule R H V]
variable [AddCommMonoid W] [Module R W] [Comodule R H W]

/-- **A point acts diagonally on a tensor product of comodules**: a base-valued point `g` of the
Hopf algebra `H` acts on the diagonal tensor product comodule `V ⊗ W` by
`g • (v ⊗ w) = g • v ⊗ g • w`. -/
theorem basePointsRepresentation_tensor_tmul (g : WithConv (H →ₐ[R] R)) (v : V) (w : W) :
    basePointsRepresentation (H := H) (V ⊗[R] W) g (v ⊗ₜ w) =
      basePointsRepresentation (H := H) V g v ⊗ₜ basePointsRepresentation (H := H) W g w := by
  have h := endOfPoint_tensor_tmul g.ofConv 1 1 v w
  simp only [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation,
    TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, mul_one] at h
  simpa using congrArg (TensorProduct.lid R (V ⊗[R] W)) h.symm

end Points

section Tangent

variable {R H V W : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
variable [AddCommGroup V] [Module R V] [Comodule R H V]
variable [AddCommGroup W] [Module R W] [Comodule R H W]

/-- **The Leibniz rule for a tensor product of comodules**: a tangent vector `d` at the identity
acts on the diagonal tensor product comodule `V ⊗ W` by `d • (v ⊗ w) = d • v ⊗ w + v ⊗ d • w`. -/
theorem differential_tensor_tmul (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (v : V)
    (w : W) :
    differential (R := R) (H := H) (M := V ⊗[R] W) d (v ⊗ₜ w) =
      differential (R := R) (H := H) d v ⊗ₜ w + v ⊗ₜ differential (R := R) (H := H) d w := by
  rw [differential_apply, differential_apply, differential_apply, tensor_coact, tensorCoact_tmul,
    tensorComponent_tensorCombine (Bialgebra.CounitAlgebra.algEquivSelf_comp_apply_mul d)]
  simp only [← coactComponent_apply, coactComponent_counit, LinearMap.id_apply]

/-- The Leibniz rule for a tensor product of comodules, as an identity of linear maps:
a tangent vector acts on `V ⊗ W` by `d ⊗ 1 + 1 ⊗ d`. -/
theorem differential_tensor (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    differential (R := R) (H := H) (M := V ⊗[R] W) d =
      (differential (R := R) (H := H) (M := V) d).rTensor W +
        (differential (R := R) (H := H) (M := W) d).lTensor V :=
  TensorProduct.ext' fun v w ↦ by
    rw [differential_tensor_tmul, LinearMap.add_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul]

end Tangent

end TauCeti.Comodule

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
    TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff_toIdeal_le_ker,
    TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff_toIdeal_le_ker,
    stabilizerHopfIdeal_le_ker_iff, stabilizerHopfIdeal_le_ker_iff]
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
