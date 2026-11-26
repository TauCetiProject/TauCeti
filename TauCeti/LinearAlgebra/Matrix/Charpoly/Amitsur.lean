/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.Module

/-!
# Amitsur's theorem on characteristic polynomials over the base ring

Let `B` be a commutative ring, `A` a commutative `B`-algebra, `Λ` a `B`-algebra, and
`ρ : Λ →ₐ[B] Matrix n n A` a `B`-algebra homomorphism into square matrices over `A`. This file
proves two algebraic criteria for the characteristic polynomials of matrices in the image of `ρ`
to have all coefficients in the image of `B` in `A`:

* `TauCeti.exists_adjugate_of_charpoly_coeff_mem_range`: if the characteristic polynomial of `ρ w`
  has all coefficients in `(algebraMap B A).range`, then `det (ρ w)` lifts to `F : B` and there is
  an element `v : Λ` whose image `ρ v` satisfies `ρ v * ρ w = ρ w * ρ v = F • 1`.
* `TauCeti.charpoly_coeff_mem_range_of_span` (**Amitsur's theorem**): if `Λ` is spanned over `B`
  by a set `S` on which every `ρ s` has characteristic polynomial with coefficients in
  `(algebraMap B A).range`, then the same holds for every `w : Λ`.

The proof of Amitsur's theorem works modulo `X ^ e` in `AdjoinRoot (X ^ e : A[X])` over the
subalgebra `R = B[X] / (X ^ e)` and shows by descending induction on `j ≤ e` that adding
`t ^ j • γ` to `β` preserves membership of `det (1 - t • f β)` in `R`.

## References

* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear
  Algebra **8** (1980), no. 3, 177–182.
* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, LMS Lecture Note Series **414** (2014), (1.5).
-/

public section

open Polynomial Submodule AdjoinRoot Matrix Algebra
open scoped TensorProduct

namespace TauCeti

variable {B A n Λ : Type*} [CommRing B] [CommRing A] [Fintype n] [DecidableEq n] [Algebra B A]
  [Ring Λ] [Algebra B Λ]

/-- If the characteristic polynomial of `ρ w` has all coefficients in the image of `B` in `A`, then
`det (ρ w)` lifts to an element `F : B` and there exists `v : Λ` such that
`ρ v * ρ w = ρ w * ρ v = F • 1`. -/
theorem exists_adjugate_of_charpoly_coeff_mem_range (ρ : Λ →ₐ[B] Matrix n n A) {w : Λ}
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

/-- Inductive step for Amitsur's theorem: working modulo `X ^ e` over the image `R` of `B[X]` in
`AdjoinRoot (X ^ e : A[X])`, adding `t ^ j • γ` to `β` preserves membership of
`det (1 - t • f β)` in `R`. -/
private theorem amitsur_det_one_sub_smul_mem (ρ : Λ →ₐ[B] Matrix n n A) {S : Set Λ}
    (hS : Submodule.span B S = ⊤)
    (hρ : ∀ s ∈ S, ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range) (e : ℕ) :
    let R : Subalgebra B (AdjoinRoot (X ^ e : A[X])) := (aeval (root (X ^ e : A[X]))).range
    let t : R := ⟨aeval (root (X ^ e : A[X])) (X : B[X]), X, rfl⟩
    let f : R ⊗[B] Λ →ₐ[R] Matrix n n (AdjoinRoot (X ^ e : A[X])) :=
      ((ofAlgHom B (X ^ e : A[X])).mapMatrix.comp ρ).liftEquiv B R _ _
    ∀ (j : ℕ), j ≤ e → ∀ (γ β : R ⊗[B] Λ),
      det (1 - t • f β) ∈ R → det (1 - t • f (β + t ^ j • γ)) ∈ R := by
  intro R t f j hj γ β
  have hdet_mem (s : Λ) (hs : s ∈ S) (c : R) : det (1 - c • f (1 ⊗ₜ s)) ∈ R := by
    obtain ⟨y, hy⟩ : ∃ y : B[X], y.map (algebraMap B A) = (ρ s).charpoly :=
      (lifts_iff_coeff_lifts _).2 (hρ s hs)
    have hdet : det (1 - c • f (1 ⊗ₜ s)) =
        (ρ s).charpoly.reverse.aeval (c : AdjoinRoot (X ^ e : A[X])) := by
      simp [f, reverse_charpoly, charpolyRev, AlgHom.map_det, R.smul_def, map_sub,
        Matrix.map_smul', Function.comp_def]
    simp [hdet, reverse, ← hy, reflect_map]
  have hspan (x : R ⊗[B] Λ) : x ∈ Submodule.span R (TensorProduct.mk B R Λ 1 '' S) := by
    simp [← Submodule.baseChange_span, hS]
  induction hj using Nat.decreasingInduction generalizing γ β with
  | self =>
    have ht_pow : t ^ e = 0 := Subtype.ext (by simp [t, ← mk_X, ← map_pow])
    simp [ht_pow]
  | of_succ j _ ih =>
    induction hspan γ using Submodule.closure_induction generalizing β with
    | zero => simp
    | add γ γ' _ _ ih_γ ih_γ' =>
      intro hβ
      simpa [smul_add, ← add_assoc] using ih_γ' _ (ih_γ β hβ)
    | smul_mem c x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro hβ
      let δ : R ⊗[B] Λ := c • β * 1 ⊗ₜ s
      let β' : R ⊗[B] Λ := β + t ^ j • c • (1 : R) ⊗ₜ[B] s - t ^ (j + 1) • δ
      have hfactor : 1 - t • f β' = (1 - t • f β) * (1 - (t ^ (j + 1) * c) • f (1 ⊗ₜ s)) := by
        simp only [β', δ, map_sub, map_add, map_smul, map_mul, sub_mul, mul_sub, mul_one, one_mul,
          smul_mul_assoc, mul_smul_comm]
        module
      have hmem : det (1 - t • f β') ∈ R := by
        rw [hfactor, det_mul]
        exact mul_mem hβ (hdet_mem s hs _)
      simpa [β'] using ih δ β' hmem

/-- **Amitsur's theorem**: let `ρ : Λ →ₐ[B] Matrix n n A` be a `B`-algebra homomorphism into square
matrices over a commutative `B`-algebra `A`. If `Λ` is spanned over `B` by a set `S` such that the
characteristic polynomial of `ρ s` has all coefficients in `(algebraMap B A).range` for every
`s ∈ S`, then the same holds for every `w : Λ`. -/
theorem charpoly_coeff_mem_range_of_span (ρ : Λ →ₐ[B] Matrix n n A) {S : Set Λ}
    (hS : Submodule.span B S = ⊤)
    (hρ : ∀ s ∈ S, ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range)
    (w : Λ) (k : ℕ) : (ρ w).charpoly.coeff k ∈ (algebraMap B A).range := by
  let e : ℕ := revAt (ρ w).charpoly.natDegree k + 1
  let R : Subalgebra B (AdjoinRoot (X ^ e : A[X])) := (aeval (root (X ^ e : A[X]))).range
  let t : R := ⟨aeval (root (X ^ e : A[X])) (X : B[X]), X, rfl⟩
  let f : R ⊗[B] Λ →ₐ[R] Matrix n n (AdjoinRoot (X ^ e : A[X])) :=
    ((ofAlgHom B (X ^ e : A[X])).mapMatrix.comp ρ).liftEquiv B R _ _
  obtain ⟨q, hq⟩ : det (1 - t • f (0 + t ^ 0 • (1 : R) ⊗ₜ[B] w)) ∈ R :=
    amitsur_det_one_sub_smul_mem ρ hS hρ e 0 e.zero_le (1 ⊗ₜ w) 0 (by simp)
  have hdet : det (1 - t • f (1 ⊗ₜ w)) =
      (ρ w).charpoly.reverse.aeval (t : AdjoinRoot (X ^ e : A[X])) := by
    simp [f, reverse_charpoly, charpolyRev, AlgHom.map_det, R.smul_def, map_sub,
      Matrix.map_smul', Function.comp_def]
  have hagree : ∀ d < e,
      algebraMap B A (q.coeff d) = (ρ w).charpoly.coeff (revAt (ρ w).charpoly.natDegree d) := by
    rw [zero_add, pow_zero, one_smul, hdet] at hq
    simpa [aeval_eq_of_algebra, t, X_pow_dvd_iff, sub_eq_zero, coeff_reverse] using hq
  exact ⟨q.coeff (e - 1), by simpa [e] using hagree (e - 1) (Nat.lt_succ_self _)⟩

end TauCeti
