/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Diagonal
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Higman's criterion for tensor products with permutation modules

Let `Δ` be a finite group, `C` a normal subgroup and `D` a subgroup of `Δ ⧸ C`, both of order
prime to a prime `ℓ`, and let `N` be an `R[Δ]`-module killed by `ℓ`. The diagonal tensor product
of `N` with the permutation module `ZMod ℓ[(Δ ⧸ C) ⧸ D]`, on which `Δ` acts through `Δ ⧸ C`,
satisfies Higman's criterion: some additive `τ` has `∑ g, g τ g⁻¹ = 1`. Up to the scalar
`(|C| |D|)⁻¹`, `τ` is the projection onto the base coset, since the elements of `Δ` carrying a
coset to the base coset number `|C| |D|`.

## Main results

* `TauCeti.exists_sum_smul_inv_smul_eq_diagonalTensor_ofMulAction`: Higman's criterion for these
  diagonal tensor products.

## References

* D. G. Higman, *Modules with a group of operators*, Duke Math. J. 21 (1954), 369–376.
-/

public section

open TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

open Finset

variable {R : Type*} [Ring R] {Δ : Type*} [Group Δ] [Fintype Δ] {ℓ : ℕ} [Fact ℓ.Prime]
  (N : ModuleCat R[Δ]) [Module (ZMod ℓ) N] [SMulCommClass R[Δ] (ZMod ℓ) N]

/-- **Higman's criterion for permutation modules.** If `C` and `D` have order prime to `ℓ`, the
diagonal tensor product of `N` with the permutation module of `(Δ ⧸ C) ⧸ D` satisfies Higman's
criterion: some additive `τ` has `∑ g, g τ g⁻¹ = 1`. -/
theorem exists_sum_smul_inv_smul_eq_diagonalTensor_ofMulAction {C : Subgroup Δ} [C.Normal]
    (D : Subgroup (Δ ⧸ C)) (hC : ¬ ℓ ∣ Nat.card C) (hD : ¬ ℓ ∣ Nat.card D) :
    ∃ τ : Representation.diagonalTensor ((Representation.ofMulAction (ZMod ℓ) (Δ ⧸ C)
          ((Δ ⧸ C) ⧸ D)).comp (QuotientGroup.mk' C)) N →+
        Representation.diagonalTensor ((Representation.ofMulAction (ZMod ℓ) (Δ ⧸ C)
          ((Δ ⧸ C) ⧸ D)).comp (QuotientGroup.mk' C)) N,
      ∀ x, ∑ g : Δ, MonoidAlgebra.of R Δ g • τ (MonoidAlgebra.of R Δ g⁻¹ • x) = x := by
  classical
  set x₀ : (Δ ⧸ C) ⧸ D := QuotientGroup.mk 1
  set c : ZMod ℓ := ((Nat.card C * Nat.card D : ℕ) : ZMod ℓ)
  have hc : c ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, (Fact.out : ℓ.Prime).dvd_mul]
    tauto
  let proj : (ZMod ℓ)[(Δ ⧸ C) ⧸ D] →ₗ[ZMod ℓ] (ZMod ℓ)[(Δ ⧸ C) ⧸ D] :=
    MonoidAlgebra.lsingle x₀ ∘ₗ Finsupp.lapply x₀ ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv (ZMod ℓ)).toLinearMap
  have hproj (y : (Δ ⧸ C) ⧸ D) (r : ZMod ℓ) :
      proj (MonoidAlgebra.single y r) = if y = x₀ then MonoidAlgebra.single y r else 0 := by
    split_ifs with h
    · simp [proj, h]
    · simp [proj, h]
  set A := Representation.diagonalTensorAction (R := R)
    ((Representation.ofMulAction (ZMod ℓ) (Δ ⧸ C) ((Δ ⧸ C) ⧸ D)).comp (QuotientGroup.mk' C)) N
  have hterm (g : Δ) (y : (Δ ⧸ C) ⧸ D) (r : ZMod ℓ) (n : N) :
      A (MonoidAlgebra.of R Δ g) ((c⁻¹ • proj.rTensor N)
        (A (MonoidAlgebra.of R Δ g⁻¹) (MonoidAlgebra.single y r ⊗ₜ n))) =
        if (QuotientGroup.mk' C g)⁻¹ • y = x₀ then c⁻¹ • (MonoidAlgebra.single y r ⊗ₜ n)
        else 0 := by
    simp only [A, MonoidAlgebra.of_apply, Representation.diagonalTensorAction_single_tmul,
      MonoidHom.comp_apply, Representation.ofMulAction_single, LinearMap.smul_apply,
      LinearMap.rTensor_tmul, map_inv, hproj]
    split_ifs with h
    · simp [MonoidAlgebra.single_mul_single, smul_smul, ← MonoidAlgebra.one_def]
    · simp
  have hF : ∑ g : Δ, A (MonoidAlgebra.of R Δ g) * (c⁻¹ • proj.rTensor N) *
      A (MonoidAlgebra.of R Δ g⁻¹) = 1 := by
    refine TensorProduct.ext' fun v n ↦ ?_
    induction v using MonoidAlgebra.induction_linear with
    | zero => simp
    | add v v' hv hv' => simp only [TensorProduct.add_tmul, map_add, hv, hv']
    | single y r =>
      rw [LinearMap.sum_apply]
      have hcard : #{g : Δ | (QuotientGroup.mk' C g)⁻¹ • y = x₀} = Nat.card C * Nat.card D := by
        rw [← natCard_inv_smul_eq_mk_one C D y, Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp only [mul_apply_eq_comp, hterm, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul (ZMod ℓ), smul_smul]
      rw [mul_inv_cancel₀ hc, one_smul, one_apply_eq_self]
  refine ⟨AddMonoidHom.mk' (fun x ↦ (c⁻¹ • proj.rTensor N) x) (map_add _), fun x ↦ ?_⟩
  -- The identity `hF` of endomorphisms of `W ⊗ N`, evaluated at `x`.
  exact (LinearMap.sum_apply _ _ x).symm.trans (LinearMap.congr_fun hF x)

end TauCeti
