/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independent families split by a linear map

If a linear map `D` sends three vectors `x`, `y`, `z` to linearly independent vectors, and `v` is
a linearly independent family in the kernel of `D`, then `x`, `y`, `z` followed by `v` are linearly
independent. This is how a frame of a regular level set `D⁻¹(c)` is completed by normal vectors to
a basis of the ambient space: the tangent vectors lie in the kernel of the derivative `D`, and the
normals are detected by `D`.
-/

public section

namespace TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Three vectors whose images under a linear map `D` are linearly independent, followed by a
linearly independent family in the kernel of `D`, are linearly independent. It is stated for an
arbitrary length `k`, so that the nested `Fin.cons` indices are not normalized. -/
theorem linearIndependent_finCons_finCons_finCons_of_map (D : M →ₗ[R] N) {k : ℕ} {v : Fin k → M}
    (hv : LinearIndependent R v) (hDv : ∀ i, D (v i) = 0) {x y z : M}
    (hxyz : LinearIndependent R ![D x, D y, D z]) :
    LinearIndependent R (Fin.cons x (Fin.cons y (Fin.cons z v)) : Fin (k + 1 + 1 + 1) → M) := by
  rw [Fintype.linearIndependent_iff] at hxyz ⊢
  intro g hg
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hg
  have hD := congrArg D hg
  simp only [map_add, map_smul, map_sum, hDv, smul_zero, Finset.sum_const_zero, add_zero,
    map_zero] at hD
  have h3 := hxyz ![g 0, g (Fin.succ 0), g (Fin.succ (Fin.succ 0))] (by
    simpa [Fin.sum_univ_three, add_assoc] using hD)
  have hg0 : g 0 = 0 := h3 0
  have hg1 : g (Fin.succ 0) = 0 := h3 1
  have hg2 : g (Fin.succ (Fin.succ 0)) = 0 := h3 2
  rw [hg0, hg1, hg2] at hg
  simp only [zero_smul, zero_add] at hg
  have hrest := (Fintype.linearIndependent_iff.1 hv) _ hg
  intro i
  exact Fin.cases hg0 (fun i ↦ Fin.cases hg1 (fun i ↦ Fin.cases hg2 (fun i ↦ hrest i) i) i) i

end TauCeti
