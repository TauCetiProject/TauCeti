/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
import TauCeti.RingTheory.Polynomial.Truncated.Basic

/-!
# Amitsur's theorem on characteristic polynomials over the base ring

Let `B` be a commutative ring, `A` a commutative `B`-algebra, `Λ` a `B`-algebra, and
`ρ : Λ →ₐ[B] Matrix n n A` a `B`-algebra homomorphism into square matrices over `A`. This file
proves Amitsur's criterion for the characteristic polynomials of matrices in the image of `ρ` to
have all coefficients in the image of `B` in `A`, together with a Cayley–Hamilton consequence
lifting `det (ρ w) • 1` into `ρ(Λ)`:

* `AlgHom.exists_mul_eq_smul_one_of_charpoly_coeff_mem_range`: if the characteristic polynomial of
  `ρ w` has all coefficients in `(algebraMap B A).range`, then `det (ρ w)` lifts to `F : B` and
  there is an element `v : Λ` such that `ρ v * ρ w = ρ w * ρ v = F • 1`.
* `AlgHom.charpoly_coeff_mem_range_of_span` (**Amitsur's theorem**): if `Λ` is spanned over `B`
  by a set `S` on which every `ρ s` has characteristic polynomial with coefficients in
  `(algebraMap B A).range`, then the same holds for every `w : Λ`.
* `AlgHom.charpoly_comp_map_coeff_mem_range` (**Amitsur's formula for block matrices**): if every
  `ρ w` has characteristic polynomial with coefficients in `(algebraMap B A).range`, then so has
  the block matrix `Matrix.comp N N n n A (P.map ρ)`, with blocks `ρ (P i j)`, of every square
  matrix `P` over `Λ`.

The proof of Amitsur's theorem works modulo `X ^ e` in `AdjoinRoot (X ^ e : A[X])` over the image
`R` of `B[X]` in `AdjoinRoot (X ^ e : A[X])` and shows by descending induction on `j ≤ e` that
adding `t ^ j • γ` to `β` preserves membership of `det (1 - t • f β)` in `R`.

The block form applies Amitsur's theorem to the algebra `Matrix N N Λ`, which is spanned by the
matrices `Matrix.single i j w` with a single nonzero entry. The block matrix of such a matrix is a
product `c * r` of a column of blocks `c` and a row of blocks `r` with `r * c = ρ w` if `i = j` and
`r * c = 0` otherwise, and `Matrix.charpoly_mul_comm'` relates the characteristic polynomials of
`c * r` and `r * c` up to powers of `X`.

## References

* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear
  Algebra **8** (1980), no. 3, 177–182.
* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, LMS Lecture Note Series **414** (2014), (1.5).

## Provenance

The reduction of the block form to matrices with a single nonzero entry (`Matrix.single i j w`),
factored as a column of blocks times a row of blocks, follows
`New.amitsur_charpoly_comp_coeff_mem_range` (file
`src/New/Congruences/FirstOrder/RibetMethod.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Polynomial Submodule AdjoinRoot Matrix Algebra
open scoped TensorProduct

namespace AlgHom

variable {B A n Λ : Type*} [CommRing B] [CommRing A] [Fintype n] [DecidableEq n] [Algebra B A]
  [Semiring Λ] [Algebra B Λ]

/-- If the characteristic polynomial of `ρ w` has all coefficients in the image of `B` in `A`, then
`det (ρ w)` lifts to an element `F : B` and there exists `v : Λ` such that
`ρ v * ρ w = ρ w * ρ v = F • 1`. -/
theorem exists_mul_eq_smul_one_of_charpoly_coeff_mem_range (ρ : Λ →ₐ[B] Matrix n n A) {w : Λ}
    (hw : ∀ k : ℕ, (ρ w).charpoly.coeff k ∈ (algebraMap B A).range) :
    ∃ (v : Λ) (F : B), (ρ w).det = algebraMap B A F ∧ ρ v * ρ w = F • 1 ∧ ρ w * ρ v = F • 1 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : B[X], Q.map (algebraMap B A) = (ρ w).charpoly :=
    (lifts_iff_coeff_lifts _).2 hw
  let c : B := (-1) ^ Fintype.card n
  let v : Λ := (-c) • Q.divX.aeval w
  let F : B := c * Q.coeff 0
  have hdet : (ρ w).det = algebraMap B A F := by
    rw [det_eq_sign_charpoly_coeff, ← hQ, coeff_map]
    simp [F, c]
  have hvanish : aeval (ρ w) ((Q.divX * X + C (Q.coeff 0)).map (algebraMap B A)) = 0 := by
    rw [Q.divX_mul_X_add, hQ, aeval_self_charpoly]
  have hch : ρ (Q.divX.aeval w) * ρ w = -(Q.coeff 0 • (1 : Matrix n n A)) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [← aeval_algHom_apply, algebraMap_eq_smul_one] using hvanish
  have hvw : ρ v * ρ w = F • 1 := by
    simp [v, F, hch, mul_smul]
  have hcomm : ρ w * ρ v = ρ v * ρ w := by
    have hmul : ρ w * ρ (Q.divX.aeval w) = ρ (Q.divX.aeval w) * ρ w := by
      simpa [← aeval_algHom_apply] using congrArg (aeval (ρ w)) (X_mul (p := Q.divX))
    simp [v, hmul]
  exact ⟨v, F, hdet, hvw, hcomm.trans hvw⟩

/-- The image of `B[X]` in `AdjoinRoot (X ^ e : A[X])`. -/
private noncomputable abbrev amitsurSubalg (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]
    (e : ℕ) : Subalgebra B (AdjoinRoot (X ^ e : A[X])) :=
  (aeval (root (X ^ e : A[X]))).range

/-- The image of `X : B[X]` in `amitsurSubalg B A e`. -/
private noncomputable abbrev amitsurRoot (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]
    (e : ℕ) : amitsurSubalg B A e :=
  ⟨aeval (root (X ^ e : A[X])) (X : B[X]), X, rfl⟩

/-- Base change of `ρ : Λ →ₐ[B] Matrix n n A` to `amitsurSubalg B A e ⊗[B] Λ`. -/
private noncomputable abbrev amitsurLift (ρ : Λ →ₐ[B] Matrix n n A) (e : ℕ) :
    amitsurSubalg B A e ⊗[B] Λ →ₐ[amitsurSubalg B A e] Matrix n n (AdjoinRoot (X ^ e : A[X])) :=
  ((ofAlgHom B (X ^ e : A[X])).mapMatrix.comp ρ).liftEquiv B (amitsurSubalg B A e) _ _

/-- On pure tensors `1 ⊗ₜ s`, `det (1 - c • amitsurLift ρ e (1 ⊗ₜ s))` is the reversed
characteristic polynomial of `ρ s` evaluated at `c`. -/
private lemma det_one_sub_smul_amitsurLift_tmul (ρ : Λ →ₐ[B] Matrix n n A) (e : ℕ) (s : Λ)
    (c : amitsurSubalg B A e) :
    det (1 - c • amitsurLift ρ e (1 ⊗ₜ s)) =
      aeval (c : AdjoinRoot (X ^ e : A[X])) (ρ s).charpoly.reverse := by
  rw [reverse_charpoly, aeval_def, eval₂_eq_eval_map, ← charpolyRev_map,
    eval_charpolyRev_eq_det_one_sub_smul]
  simp [(amitsurSubalg B A e).smul_def, amitsurLift]

/-- Inductive step for Amitsur's theorem: working modulo `X ^ e` over `amitsurSubalg B A e`, adding
`t ^ j • γ` to `β` preserves membership of `det (1 - t • f β)` in `amitsurSubalg B A e`. -/
private theorem amitsur_det_one_sub_smul_mem (ρ : Λ →ₐ[B] Matrix n n A) {S : Set Λ}
    (hS : Submodule.span B S = ⊤)
    (hρ : ∀ s ∈ S, ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range) (e j : ℕ)
    (γ β : amitsurSubalg B A e ⊗[B] Λ)
    (hβ : det (1 - amitsurRoot B A e • amitsurLift ρ e β) ∈ amitsurSubalg B A e) :
    det (1 - amitsurRoot B A e • amitsurLift ρ e (β + amitsurRoot B A e ^ j • γ)) ∈
      amitsurSubalg B A e := by
  let R := amitsurSubalg B A e
  let t : R := amitsurRoot B A e
  let f := amitsurLift ρ e
  have ht_pow : t ^ e = 0 := Subtype.ext (by simp [t, ← mk_X, ← map_pow])
  rcases lt_or_ge e j with hlt | hj
  · have htj : t ^ j = 0 := by rw [← Nat.add_sub_of_le hlt.le, pow_add, ht_pow, zero_mul]
    simpa [t, htj] using hβ
  have hdet_mem (s : Λ) (hs : s ∈ S) (c : R) : det (1 - c • f (1 ⊗ₜ s)) ∈ R := by
    obtain ⟨y, hy⟩ : ∃ y : B[X], y.map (algebraMap B A) = (ρ s).charpoly :=
      (lifts_iff_coeff_lifts _).2 (hρ s hs)
    rw [det_one_sub_smul_amitsurLift_tmul, reverse, ← hy, reflect_map, aeval_map_algebraMap]
    simp
  have hspan (x : R ⊗[B] Λ) : x ∈ Submodule.span R (TensorProduct.mk B R Λ 1 '' S) := by
    simp [← Submodule.baseChange_span, hS]
  induction hj using Nat.decreasingInduction generalizing γ β with
  | self => simpa [t, ht_pow] using hβ
  | of_succ j _ ih =>
    induction hspan γ using Submodule.closure_induction generalizing β with
    | zero => simpa using hβ
    | add γ γ' _ _ ih_γ ih_γ' =>
      simpa [smul_add, ← add_assoc] using ih_γ' _ (ih_γ β hβ)
    | smul_mem c x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      let δ : R ⊗[B] Λ := c • β * 1 ⊗ₜ s
      let β' : R ⊗[B] Λ := β + t ^ j • c • (1 : R) ⊗ₜ[B] s + (-t ^ (j + 1)) • δ
      have hfactor : 1 - t • f β' = (1 - t • f β) * (1 - (t ^ (j + 1) * c) • f (1 ⊗ₜ s)) := by
        simp only [β', δ, map_add, map_smul, map_mul, sub_mul, mul_sub, mul_one, one_mul,
          smul_mul_assoc, mul_smul_comm]
        module
      have hmem : det (1 - t • f β') ∈ R := by
        rw [hfactor, det_mul]
        exact mul_mem hβ (hdet_mem s hs _)
      have hcancel : β' + t ^ (j + 1) • δ = β + t ^ j • c • (1 : R) ⊗ₜ[B] s := by
        simp only [β', add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
      have hres := ih δ β' hmem
      rwa [hcancel] at hres

/-- **Amitsur's theorem**: let `ρ : Λ →ₐ[B] Matrix n n A` be a `B`-algebra homomorphism into square
matrices over a commutative `B`-algebra `A`. If `Λ` is spanned over `B` by a set `S` such that the
characteristic polynomial of `ρ s` has all coefficients in `(algebraMap B A).range` for every
`s ∈ S`, then the same holds for every `w : Λ`. -/
theorem charpoly_coeff_mem_range_of_span (ρ : Λ →ₐ[B] Matrix n n A) {S : Set Λ}
    (hS : Submodule.span B S = ⊤)
    (hρ : ∀ s ∈ S, ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range)
    (w : Λ) (k : ℕ) : (ρ w).charpoly.coeff k ∈ (algebraMap B A).range := by
  let e : ℕ := revAt (ρ w).charpoly.natDegree k + 1
  have hmem : det (1 - amitsurRoot B A e • amitsurLift ρ e (1 ⊗ₜ w)) ∈ amitsurSubalg B A e := by
    simpa using amitsur_det_one_sub_smul_mem ρ hS hρ e 0 (1 ⊗ₜ w) 0 (by simp)
  obtain ⟨q, hq⟩ := (AlgHom.mem_range _).1 hmem
  have hroot : (amitsurRoot B A e : AdjoinRoot (X ^ e : A[X])) = root (X ^ e : A[X]) := by simp
  rw [aeval_eq_of_algebra, det_one_sub_smul_amitsurLift_tmul, hroot, aeval_eq] at hq
  have hagree : ∀ d < e, (q.map (algebraMap B A)).coeff d = (ρ w).charpoly.reverse.coeff d :=
    AdjoinRoot.mk_X_pow_eq_mk_iff.1 hq
  refine ⟨q.coeff (e - 1), ?_⟩
  simpa [e, coeff_map, coeff_reverse] using hagree (e - 1) (Nat.lt_succ_self _)

/-- **Amitsur's formula for block matrices**: let `ρ : Λ →ₐ[B] Matrix n n A` be a `B`-algebra
homomorphism such that the characteristic polynomial of every `ρ w` has all coefficients in the
image of `B` in `A`. Then for every square matrix `P` over `Λ`, the block matrix
`Matrix.comp N N n n A (P.map ρ)`, whose block at `(i, j)` is `ρ (P i j)`, has characteristic
polynomial with all coefficients in the image of `B`. -/
theorem charpoly_comp_map_coeff_mem_range {N : Type*} [Fintype N] [DecidableEq N]
    (ρ : Λ →ₐ[B] Matrix n n A)
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap B A).range)
    (P : Matrix N N Λ) (k : ℕ) :
    (Matrix.comp N N n n A (P.map ρ)).charpoly.coeff k ∈ (algebraMap B A).range := by
  let φ : Matrix N N Λ →ₐ[B] Matrix (N × n) (N × n) A :=
    (Matrix.compAlgEquiv N n A B).toAlgHom.comp ρ.mapMatrix
  let S : Set (Matrix N N Λ) := Set.range fun x : N × N × Λ ↦ single x.1 x.2.1 x.2.2
  have hS : Submodule.span B S = ⊤ := by
    refine eq_top_iff.2 fun Q _ ↦ ?_
    rw [matrix_eq_sum_single Q]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
      Submodule.subset_span ⟨(i, j, Q i j), rfl⟩
  refine charpoly_coeff_mem_range_of_span φ hS ?_ P k
  rintro _ ⟨⟨a, b, w⟩, rfl⟩ k
  -- The block matrix of `single a b w` is a column of blocks times a row of blocks.
  let c : Matrix (N × n) n A := of fun p u ↦ if p.1 = a ∧ p.2 = u then 1 else 0
  let r : Matrix n (N × n) A := of fun u p ↦ if p.1 = b then ρ w u p.2 else 0
  have hφ : φ (single a b w) = c * r := by
    ext ⟨i, s⟩ ⟨j, t⟩
    by_cases hi : a = i <;> by_cases hj : b = j <;>
      simp [φ, c, r, Matrix.mul_apply, single, hi, hj, eq_comm]
  have hrc : r * c = ρ (if a = b then w else 0) := by
    ext u v
    by_cases hab : a = b
    · subst hab
      simp [c, r, Matrix.mul_apply, Fintype.sum_prod_type, ite_and]
    · simp [c, r, Matrix.mul_apply, Fintype.sum_prod_type, ite_and, hab]
  have hmul := congrArg (fun p : A[X] ↦ p.coeff (k + Fintype.card n)) (charpoly_mul_comm' c r)
  simp only [coeff_X_pow_mul', le_add_iff_nonneg_left, zero_le, ite_true,
    Nat.add_sub_cancel] at hmul
  rw [hφ, hmul]
  split_ifs
  · rw [hrc]
    exact hρ _ _
  · exact zero_mem _

end AlgHom
