/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import TauCeti.Algebra.BigOperators.Fin

/-!
# Composing multilinear maps valued in linear maps along a split of the inputs

For multilinear maps `G` in `j` arguments valued in linear maps `N → P` and `F` in `i` arguments
valued in linear maps `M → N`, and `i + j = n`, the map
`(a₁, …, aₙ) ↦ G (aᵢ₊₁, …, aₙ) ∘ F (a₁, …, aᵢ)` is multilinear in `n` arguments
(`MultilinearMap.compSplit`). Such composites are the terms of the composition of morphisms of
`A∞` modules, and of their relations.

Along matrices `F₁, …, Fᵢ` and `G₁, …, Gⱼ` indexed by a finite type `X`, applying `G` along the
paths `y₀ → ⋯ → yⱼ = z` in `X` to the sum of `F` along the paths ending at `y₀` is applying the
composite along the paths of length `i + j` ending at `z`, since a path of length `i + j` is a path
of length `i` followed by one of length `j` (`MultilinearMap.sum_ite_apply_sum_ite_eq_sum`). This
is how operations of `A∞` modules compose on matrix modules and on box tensor products.

## Main definitions and results

* `MultilinearMap.compSplit`: `(a₁, …, aₙ) ↦ G (aᵢ₊₁, …, aₙ) ∘ F (a₁, …, aᵢ)`.
* `MultilinearMap.sum_ite_apply_sum_ite_eq_sum`: composing two path sums of multilinear maps
  along matrices.
-/

public section

open Finset

namespace MultilinearMap

variable {R A M N P : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- The composite of `G` after `F` along the split of `n = i + j` inputs after the `i`-th:
`(a₁, …, aₙ) ↦ G (aᵢ₊₁, …, aₙ) ∘ F (a₁, …, aᵢ)`. -/
noncomputable def compSplit {i j n : ℕ}
    (G : MultilinearMap (RingHom.id R) (fun _ : Fin j => A) (N →ₗ[R] P))
    (F : MultilinearMap (RingHom.id R) (fun _ : Fin i => A) (M →ₗ[R] N)) (h : i + j = n) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] P) :=
  ((TensorProduct.lift (LinearMap.llcomp R M N P)).compMultilinearMap
    (G.domCoprod F)).domDomCongr ((Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr h)))

/-- `G.compSplit F h` applied to `(a₁, …, aₙ)` and `m` is
`G (aᵢ₊₁, …, aₙ) (F (a₁, …, aᵢ) m)`. -/
@[simp]
theorem compSplit_apply {i j n : ℕ}
    (G : MultilinearMap (RingHom.id R) (fun _ : Fin j => A) (N →ₗ[R] P))
    (F : MultilinearMap (RingHom.id R) (fun _ : Fin i => A) (M →ₗ[R] N)) (h : i + j = n)
    (a : Fin n → A) (m : M) :
    G.compSplit F h a m =
      G (fun l => a ⟨i + l, by omega⟩) (F (fun l => a ⟨l, by omega⟩) m) := by
  simp only [compSplit, domDomCongr_apply, LinearMap.compMultilinearMap_apply, domCoprod_apply,
    TensorProduct.lift.tmul, LinearMap.llcomp_apply, Equiv.trans_apply, Equiv.sumComm_apply,
    Sum.swap_inl, Sum.swap_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    finCongr_apply]
  -- `Fin.cast h (Fin.natAdd i l)` and `Fin.cast h (Fin.castAdd j l)` are `⟨i + l, _⟩` and
  -- `⟨l, _⟩` by definition.
  rfl

/-- **Composing path sums.** For multilinear maps `ψ` and `φ`, applying `ψ` along the paths
`y₀ → ⋯ → yⱼ = z` to the sum of `φ` over the paths ending at `y₀` gives the sum over the paths
`w₀ → ⋯ → wᵢ₊ⱼ = z` of `ψ(G₁ wᵢ wᵢ₊₁, …)(φ(F₁ w₀ w₁, …)(v w₀))`. -/
theorem sum_ite_apply_sum_ite_eq_sum {X : Type*} [Fintype X] [DecidableEq X] {i j n : ℕ}
    (h : i + j = n) (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin j => A) (N →ₗ[R] P))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin i => A) (M →ₗ[R] N))
    (G : Fin j → Matrix X X A) (F : Fin i → Matrix X X A) (v : X → M) (z : X) :
    ∑ y : Fin (j + 1) → X, (if y (Fin.last j) = z then
        ψ (fun l => G l (y l.castSucc) (y l.succ))
          (∑ x : Fin (i + 1) → X, if x (Fin.last i) = y 0 then
            φ (fun l => F l (x l.castSucc) (x l.succ)) (v (x 0)) else 0)
      else 0) = ∑ w : Fin (n + 1) → X,
      if w (Fin.last n) = z then
        ψ (fun l => G l (w ⟨i + l, by have := l.isLt; omega⟩)
          (w ⟨i + l + 1, by have := l.isLt; omega⟩))
          (φ (fun l => F l (w ⟨l, by have := l.isLt; omega⟩)
            (w ⟨l + 1, by have := l.isLt; omega⟩)) (v (w 0)))
      else 0 := by
  have hy (y : Fin (j + 1) → X) :
      (if y (Fin.last j) = z then ψ (fun l => G l (y l.castSucc) (y l.succ))
        (∑ x : Fin (i + 1) → X, if x (Fin.last i) = y 0 then
          φ (fun l => F l (x l.castSucc) (x l.succ)) (v (x 0)) else 0) else 0) =
      ∑ x : Fin (i + 1) → X, if x (Fin.last i) = y 0 then
        (if y (Fin.last j) = z then ψ (fun l => G l (y l.castSucc) (y l.succ))
          (φ (fun l => F l (x l.castSucc) (x l.succ)) (v (x 0))) else 0) else 0 := by
    split_ifs with hyz
    · simp only [_root_.map_sum]
      exact sum_congr rfl fun x _ => by split_ifs <;> simp
    · simp
  rw [sum_congr rfl fun y _ => hy y, sum_comm, Fin.sum_sum_ite_apply_last_eq_apply_zero h]
  refine sum_congr rfl fun w _ => ?_
  have hlast : w ⟨i + (Fin.last j : ℕ), by simp; omega⟩ = w (Fin.last n) :=
    congrArg w (Fin.ext (by simp [h]))
  have hzero : w ⟨((0 : Fin (i + 1)) : ℕ), by simp⟩ = w 0 := congrArg w (Fin.ext (by simp))
  simp only [hlast, hzero, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]

end MultilinearMap
