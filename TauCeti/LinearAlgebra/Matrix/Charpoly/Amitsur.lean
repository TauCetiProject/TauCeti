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

* `AlgHom.exists_mul_eq_smul_one_of_charpoly_coeff_mem_range`: if the characteristic polynomial of
  `ρ w` has all coefficients in `(algebraMap B A).range`, then `det (ρ w)` lifts to `F : B` and
  there is an element `v : Λ` such that `ρ v * ρ w = ρ w * ρ v = F • 1`.
* `AlgHom.charpoly_coeff_mem_range_of_span` (**Amitsur's theorem**): if `Λ` is spanned over `B`
  by a set `S` on which every `ρ s` has characteristic polynomial with coefficients in
  `(algebraMap B A).range`, then the same holds for every `w : Λ`.

The proof of Amitsur's theorem works modulo `X ^ e` in `AdjoinRoot (X ^ e : A[X])` over the image
`R` of `B[X]` in `AdjoinRoot (X ^ e : A[X])` and shows by descending induction on `j ≤ e` that
adding `t ^ j • γ` to `β` preserves membership of `det (1 - t • f β)` in `R`.

## References

* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear
  Algebra **8** (1980), no. 3, 177–182.
* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, LMS Lecture Note Series **414** (2014), (1.5).
-/

public section

open Polynomial Submodule AdjoinRoot Matrix Algebra
open scoped TensorProduct

namespace Matrix

/-- Evaluating the reversed characteristic polynomial `M.charpoly.reverse` at `c` in a commutative
`A`-algebra `C` gives `det (1 - c • M.map (algebraMap A C))`. -/
theorem aeval_reverse_charpoly {A C n : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [Fintype n] [DecidableEq n] (M : Matrix n n A) (c : C) :
    aeval c M.charpoly.reverse = det (1 - c • M.map (algebraMap A C)) := by
  simp [reverse_charpoly, charpolyRev, AlgHom.map_det, map_sub, Matrix.map_smul',
    Function.comp_def]

end Matrix

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

/-- Equality of two polynomials in `AdjoinRoot (X ^ e : A[X])` is agreement of all coefficients of
degree strictly below `e`. -/
private lemma mk_X_pow_eq_iff {e : ℕ} {p q : A[X]} :
    AdjoinRoot.mk (X ^ e) p = AdjoinRoot.mk (X ^ e) q ↔ ∀ d < e, p.coeff d = q.coeff d := by
  rw [AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]
  simp [sub_eq_zero]

/-- Inductive step for Amitsur's theorem: working modulo `X ^ e` over `amitsurSubalg B A e`, adding
`t ^ j • γ` to `β` preserves membership of `det (1 - t • f β)` in `amitsurSubalg B A e`. -/
private theorem amitsur_det_one_sub_smul_mem (ρ : Λ →ₐ[B] Matrix n n A) {S : Set Λ}
    (hS : Submodule.span B S = ⊤)
    (hρ : ∀ s ∈ S, ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range) (e : ℕ)
    {j : ℕ} (hj : j ≤ e) (γ β : amitsurSubalg B A e ⊗[B] Λ)
    (hβ : det (1 - amitsurRoot B A e • amitsurLift ρ e β) ∈ amitsurSubalg B A e) :
    det (1 - amitsurRoot B A e • amitsurLift ρ e (β + amitsurRoot B A e ^ j • γ)) ∈
      amitsurSubalg B A e := by
  let R := amitsurSubalg B A e
  let t : R := amitsurRoot B A e
  let f := amitsurLift ρ e
  have hdet_mem (s : Λ) (hs : s ∈ S) (c : R) : det (1 - c • f (1 ⊗ₜ s)) ∈ R := by
    obtain ⟨y, hy⟩ : ∃ y : B[X], y.map (algebraMap B A) = (ρ s).charpoly :=
      (lifts_iff_coeff_lifts _).2 (hρ s hs)
    have hdet : det (1 - c • f (1 ⊗ₜ s)) = aeval (c : AdjoinRoot (X ^ e : A[X]))
        (ρ s).charpoly.reverse := by
      simpa [f, R.smul_def] using
        (aeval_reverse_charpoly (ρ s) (c : AdjoinRoot (X ^ e : A[X]))).symm
    rw [hdet, reverse, ← hy, reflect_map, aeval_map_algebraMap]
    simp
  have hspan (x : R ⊗[B] Λ) : x ∈ Submodule.span R (TensorProduct.mk B R Λ 1 '' S) := by
    simp [← Submodule.baseChange_span, hS]
  induction hj using Nat.decreasingInduction generalizing γ β with
  | self =>
    have ht_pow : t ^ e = 0 := Subtype.ext (by simp [t, ← mk_X, ← map_pow])
    simpa [t, ht_pow] using hβ
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
    simpa using amitsur_det_one_sub_smul_mem ρ hS hρ e e.zero_le (1 ⊗ₜ w) 0 (by simp)
  obtain ⟨q, hq⟩ := hmem
  have hdet : det (1 - amitsurRoot B A e • amitsurLift ρ e (1 ⊗ₜ w)) =
      aeval (root (X ^ e : A[X])) (ρ w).charpoly.reverse := by
    simpa [(amitsurSubalg B A e).smul_def] using
      (aeval_reverse_charpoly (ρ w) (root (X ^ e : A[X]))).symm
  change aeval (root (X ^ e : A[X])) q = _ at hq
  rw [aeval_eq_of_algebra, hdet, aeval_eq] at hq
  have hagree : ∀ d < e, (q.map (algebraMap B A)).coeff d = (ρ w).charpoly.reverse.coeff d :=
    mk_X_pow_eq_iff.1 hq
  refine ⟨q.coeff (e - 1), ?_⟩
  simpa [e, coeff_map, coeff_reverse] using hagree (e - 1) (Nat.lt_succ_self _)

end AlgHom
