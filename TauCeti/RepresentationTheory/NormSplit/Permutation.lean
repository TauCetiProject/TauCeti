/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.RepresentationTheory.NormSplit.Higman
public import TauCeti.RepresentationTheory.Tensor.Diagonal
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Higman's criterion for tensor products with permutation modules

Let `Δ` be a finite group acting on a set `X` with stabilizers of order prime to a prime `ℓ`,
and let `N` be an `R[Δ]`-module killed by `ℓ`. The diagonal tensor product of `N` with the
permutation module `ZMod ℓ[X]` satisfies Higman's criterion (`TauCeti.IsHigmanProjective`): some
additive `τ` has `∑ g, g τ g⁻¹ = 1`. On `ZMod ℓ[X]`, `τ` projects onto one chosen point of each
orbit, rescaled by the inverse of the order of its stabilizer, since the elements of `Δ` carrying
a point of the orbit to the chosen one form a coset of that stabilizer.

This applies to the permutation module of `(Δ ⧸ C) ⧸ D`, on which `Δ` acts through `Δ ⧸ C`, for a
normal subgroup `C` and a subgroup `D` of `Δ ⧸ C` both of order prime to `ℓ`: the stabilizers
in `Δ` then have order `|C| |D|`.

## Main results

* `TauCeti.isHigmanProjective_diagonalTensor_ofMulAction`: Higman's criterion for the diagonal
  tensor product with a permutation module whose stabilizers have order prime to `ℓ`.
* `TauCeti.isHigmanProjective_diagonalTensor_ofMulAction_comp_mk'`: its instance for the
  permutation module of `(Δ ⧸ C) ⧸ D`, inflated from `Δ ⧸ C`.

## References

* D. G. Higman, *Modules with a group of operators*, Duke Math. J. 21 (1954), 369–376.
-/

public section

open TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

open Finset

variable {R : Type*} [Ring R] {Δ : Type*} [Group Δ] [Fintype Δ] {ℓ : ℕ} [Fact ℓ.Prime]
  (N : ModuleCat R[Δ]) [Module (ZMod ℓ) N]

/-- **Higman's criterion for permutation modules.** If the stabilizers of the action of `Δ` on `X`
have order prime to `ℓ`, the diagonal tensor product of `N` with the permutation module of `X`
satisfies Higman's criterion. -/
theorem isHigmanProjective_diagonalTensor_ofMulAction {X : Type*} [MulAction Δ X]
    (hX : ∀ x : X, ¬ ℓ ∣ Nat.card (MulAction.stabilizer Δ x)) :
    IsHigmanProjective R Δ (Representation.diagonalTensor
      (Representation.ofMulAction (ZMod ℓ) Δ X) N) := by
  classical
  -- The chosen point of the orbit of `y`, and the order of its stabilizer, read in `ZMod ℓ`.
  let o (y : X) : X := (Quotient.mk (MulAction.orbitRel Δ X) y).out
  have ho (g : Δ) (y : X) : o (g • y) = o y :=
    congrArg Quotient.out (Quotient.sound (MulAction.mem_orbit y g))
  let c (y : X) : ZMod ℓ := (Nat.card (MulAction.stabilizer Δ y) : ℕ)
  have hc (y : X) : c y ≠ 0 := (ZMod.natCast_eq_zero_iff _ ℓ).not.2 (hX y)
  let proj : (ZMod ℓ)[X] →ₗ[ZMod ℓ] (ZMod ℓ)[X] :=
    Finsupp.lsum (ZMod ℓ) (fun y ↦ if y = o y then (c y)⁻¹ • MonoidAlgebra.lsingle y else 0) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv (ZMod ℓ)).toLinearMap
  have hproj (y : X) (r : ZMod ℓ) : proj (MonoidAlgebra.single y r) =
      if y = o y then (c y)⁻¹ • MonoidAlgebra.single y r else 0 := by
    by_cases h : y = o y
    · simp [proj, ite_eq_left h]
    · simp [proj, ite_eq_right h]
  set A := Representation.diagonalTensorAction (R := R) (Representation.ofMulAction (ZMod ℓ) Δ X) N
  have hterm (g : Δ) (y : X) (r : ZMod ℓ) (n : N) :
      A (MonoidAlgebra.of R Δ g) (proj.rTensor N
        (A (MonoidAlgebra.of R Δ g⁻¹) (MonoidAlgebra.single y r ⊗ₜ n))) =
        if g⁻¹ • y = o y then (c (o y))⁻¹ • (MonoidAlgebra.single y r ⊗ₜ n) else 0 := by
    simp only [A, MonoidAlgebra.of_apply, Representation.diagonalTensorAction_single_tmul,
      Representation.ofMulAction_single, LinearMap.rTensor_tmul, hproj, ho]
    split_ifs with h
    · rw [congrArg c h, TensorProduct.smul_tmul', MonoidAlgebra.smul_single, smul_eq_mul]
      simp [MonoidAlgebra.single_mul_single, smul_smul, ← MonoidAlgebra.one_def]
    · simp
  have hF : ∑ g : Δ, A (MonoidAlgebra.of R Δ g) * proj.rTensor N *
      A (MonoidAlgebra.of R Δ g⁻¹) = 1 := by
    refine TensorProduct.ext' fun v n ↦ ?_
    induction v using MonoidAlgebra.induction_linear with
    | zero => simp
    | add v v' hv hv' => simp only [TensorProduct.add_tmul, map_add, hv, hv']
    | single y r =>
      -- The elements `g` with `g⁻¹ • y = o y` form a coset of the stabilizer of `o y`.
      have hcard : #{g : Δ | g⁻¹ • y = o y} = Nat.card (MulAction.stabilizer Δ (o y)) := by
        have h := natCard_smul_mem_eq_natCard_mul_natCard_stabilizer (G := Δ) (o y) (S := {y})
          (Set.singleton_subset_iff.2
            (MulAction.mem_orbit_symm.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out y))))
        rw [Nat.card_unique (α := ({y} : Set X)), one_mul] at h
        rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact congrArg Finset.card (Finset.filter_congr fun g _ ↦ by
          rw [inv_smul_eq_iff, Set.mem_singleton_iff, eq_comm])
      simp only [LinearMap.sum_apply, mul_apply_eq_comp, hterm, Finset.sum_ite,
        Finset.sum_const_zero, add_zero, Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul (ZMod ℓ),
        smul_smul]
      rw [mul_inv_cancel₀ (hc (o y)), one_smul, one_apply_eq_self]
  refine (isHigmanProjective_iff ..).2
    ⟨AddMonoidHom.mk' (fun x ↦ proj.rTensor N x) (map_add _), fun x ↦ ?_⟩
  -- The identity `hF` of endomorphisms of `W ⊗ N`, evaluated at `x`.
  exact (LinearMap.sum_apply _ _ x).symm.trans (LinearMap.congr_fun hF x)

/-- **Higman's criterion for permutation modules of an iterated quotient.** If `C` and `D` have
order prime to `ℓ`, the diagonal tensor product of `N` with the permutation module of
`(Δ ⧸ C) ⧸ D`, inflated from `Δ ⧸ C`, satisfies Higman's criterion. -/
theorem isHigmanProjective_diagonalTensor_ofMulAction_comp_mk' {C : Subgroup Δ} [C.Normal]
    (D : Subgroup (Δ ⧸ C)) (hC : ¬ ℓ ∣ Nat.card C) (hD : ¬ ℓ ∣ Nat.card D) :
    IsHigmanProjective R Δ (Representation.diagonalTensor ((Representation.ofMulAction (ZMod ℓ)
      (Δ ⧸ C) ((Δ ⧸ C) ⧸ D)).comp (QuotientGroup.mk' C)) N) := by
  -- Let `Δ` act through `Δ ⧸ C`; its permutation representation is then the inflated one, as
  -- `Representation.ofMulAction` is defined through the action.
  let := MulAction.compHom ((Δ ⧸ C) ⧸ D) (QuotientGroup.mk' C)
  refine isHigmanProjective_diagonalTensor_ofMulAction N fun x ↦ ?_
  -- The stabilizer of `x` in `Δ` is `C` times its stabilizer in `Δ ⧸ C`, which has the order of the
  -- stabilizer `D` of the base coset, as `x` is a translate of it.
  have h : Nat.card (MulAction.stabilizer Δ x) = Nat.card C * Nat.card D := by
    rw [card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient C x fun _ ↦ rfl]
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq : (q : (Δ ⧸ C) ⧸ D) = q • (QuotientGroup.mk 1 : (Δ ⧸ C) ⧸ D) := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [hq, card_stabilizer_smul, MulAction.stabilizer_quotient]
  rw [h, (Fact.out : ℓ.Prime).dvd_mul]
  tauto

end TauCeti
