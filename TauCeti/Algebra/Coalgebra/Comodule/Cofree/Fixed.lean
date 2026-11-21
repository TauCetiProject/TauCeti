/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed

/-!
# Coinvariants of cofree comodules over a bialgebra

For a bialgebra `H` over a commutative semiring `R` and an `R`-module `N`, the fixed subcomodule
`TauCeti.Comodule.fixedSubcomodule R H (N ⊗[R] H)` of the cofree right `H`-comodule
`TauCeti.Comodule.cofree R H N` consists of those tensors recovered from their counit contraction by
tensoring with `1 : H`. Sending `n : N` to `n ⊗ 1` therefore gives a canonical `R`-linear
equivalence `N ≃ₗ[R] Comodule.fixedSubcomodule R H (N ⊗[R] H)`.

## Main declarations

* `TauCeti.Comodule.mem_fixedSubcomodule_cofree_iff`: characterization of coinvariant tensors in
  `N ⊗[R] H` via `Coalgebra.counit`.
* `TauCeti.Comodule.cofreeFixedEquiv`: the canonical `R`-linear isomorphism
  `N ≃ₗ[R] Comodule.fixedSubcomodule R H (N ⊗[R] H)` sending `n` to `n ⊗ 1`, with inverse given by
  contracting the `H` factor against `Coalgebra.counit`.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, Chapter 2 and Theorem 4.1.1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, 1993, Section 1.9.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) (H : Type v) (N : Type w)
variable [CommSemiring R] [Semiring H] [Bialgebra R H] [AddCommMonoid N] [Module R N]

attribute [local instance] cofree

section Coalgebra

variable {R H N : Type*} [CommSemiring R] [AddCommMonoid H] [Module R H] [Coalgebra R H]
  [One H] [AddCommMonoid N] [Module R N]

/-- An invariant tensor in a cofree comodule is recovered by tensoring its counit evaluation
with `1`. The recovery only uses the coalgebra and the chosen element `1`. -/
theorem eq_counit_tmul_one_of_mem_fixedSubcomodule {z : N ⊗[R] H}
    (hz : z ∈ fixedSubcomodule R H (N ⊗[R] H)) :
    z = TensorProduct.rid R N (Coalgebra.counit.lTensor N z) ⊗ₜ[R] (1 : H) := by
  let e := (TensorProduct.rid R N).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := H)).lTensor N
  have h := congrArg (e.rTensor H) (mem_fixedSubcomodule.mp hz)
  have he : e.rTensor H (cofreeCoact R H N z) = z :=
    LinearMap.congr_fun (rTensor_rid_comp_lTensor_counit_comp_cofreeCoact
      (R := R) (C := H) (M := N)) z
  rw [cofree_coact, ← cofreeCoact_def, he] at h
  simpa [e] using h

end Coalgebra

variable {R H N} in
/-- Tensors of the form `n ⊗ 1` are invariant in the cofree comodule. -/
@[simp↓]
theorem tmul_one_mem_fixedSubcomodule (n : N) :
    n ⊗ₜ[R] (1 : H) ∈ fixedSubcomodule R H (N ⊗[R] H) := by
  rw [mem_fixedSubcomodule, cofree_coact_tmul, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def, TensorProduct.assoc_symm_tmul]

variable {R H N} in
/-- Membership in the fixed subcomodule of the cofree comodule `N ⊗[R] H`: a tensor is coinvariant
if and only if it is obtained from its counit contraction by tensoring with `1`. -/
theorem mem_fixedSubcomodule_cofree_iff (z : N ⊗[R] H) :
    z ∈ fixedSubcomodule R H (N ⊗[R] H) ↔
      (TensorProduct.rid R N (LinearMap.lTensor N (Coalgebra.counit (R := R)) z)) ⊗ₜ[R] (1 : H) =
        z := by
  refine ⟨fun hz ↦ (eq_counit_tmul_one_of_mem_fixedSubcomodule hz).symm, ?_⟩
  intro hz
  rw [← hz]
  exact tmul_one_mem_fixedSubcomodule _

/-- The fixed subcomodule of the cofree right `H`-comodule `N ⊗[R] H` is canonically `N`, via
`n ↦ n ⊗ 1`. -/
def cofreeFixedEquiv : N ≃ₗ[R] fixedSubcomodule R H (N ⊗[R] H) where
  toFun n := ⟨n ⊗ₜ[R] (1 : H), tmul_one_mem_fixedSubcomodule n⟩
  map_add' n₁ n₂ := Subtype.ext (TensorProduct.add_tmul n₁ n₂ 1)
  map_smul' r n := Subtype.ext (TensorProduct.smul_tmul' r n 1)
  invFun z :=
    TensorProduct.rid R N (LinearMap.lTensor N (Coalgebra.counit (R := R)) (z : N ⊗[R] H))
  left_inv n := by simp
  right_inv z := Subtype.ext ((mem_fixedSubcomodule_cofree_iff z.val).mp z.property)

variable {R H N}

/-- `cofreeFixedEquiv` embeds `n : N` as `n ⊗ 1`. -/
@[simp]
theorem cofreeFixedEquiv_apply (n : N) :
    (cofreeFixedEquiv R H N n : N ⊗[R] H) = n ⊗ₜ[R] (1 : H) := (rfl)

/-- The inverse of `cofreeFixedEquiv` applies the counit to the `H` factor. -/
@[simp]
theorem cofreeFixedEquiv_symm_apply (z : fixedSubcomodule R H (N ⊗[R] H)) :
    (cofreeFixedEquiv R H N).symm z =
      TensorProduct.rid R N (LinearMap.lTensor N (Coalgebra.counit (R := R)) (z : N ⊗[R] H)) :=
  (rfl)

/-- The embedding of coefficients as invariant tensors commutes with coefficient maps. -/
@[simp]
theorem fixedMap_cofreeMap_cofreeFixedEquiv {P : Type*} [AddCommMonoid P] [Module R P]
    (f : N →ₗ[R] P) (n : N) :
    (Hom.cofreeMap f).fixedMap (cofreeFixedEquiv R H N n) = cofreeFixedEquiv R H P (f n) := by
  apply Subtype.ext
  simp [Hom.cofreeMap_apply]

/-- Counit evaluation on cofree invariants commutes with coefficient maps. -/
theorem cofreeFixedEquiv_symm_naturality {P : Type*} [AddCommMonoid P] [Module R P]
    (f : N →ₗ[R] P) (z : fixedSubcomodule R H (N ⊗[R] H)) :
    (cofreeFixedEquiv R H P).symm ((Hom.cofreeMap f).fixedMap z) =
      f ((cofreeFixedEquiv R H N).symm z) := by
  apply (cofreeFixedEquiv R H P).injective
  rw [LinearEquiv.apply_symm_apply, ← fixedMap_cofreeMap_cofreeFixedEquiv f,
    LinearEquiv.apply_symm_apply]

end TauCeti.Comodule
