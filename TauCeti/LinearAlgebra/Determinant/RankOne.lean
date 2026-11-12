/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Determinants of rank-one perturbations of scalars

The **matrix determinant lemma** for a scalar plus a rank-one endomorphism: on a free module of
positive finite rank `n`, `det (a • 1 + φ.smulRight u) = a ^ (n - 1) * (a + φ u)`
(`LinearMap.det_smul_one_add_smulRight`). It holds for every scalar `a`, including `a = 0`, where
it says that a rank-one endomorphism has determinant `0` in rank at least two and `φ u` in rank
one. The proof evaluates Mathlib's characteristic polynomial of a rank-one matrix,
`Matrix.charpoly_vecMulVec`, at `-a`.

If every difference `v - f v` lies in the line spanned by a nonzero vector `x`, then
`f x = det(f) • x`. Thus the determinant character is the normal character for the
action on polynomial functions of an element fixing a hyperplane pointwise.

The calculation uses the rank-one instance of the Weinstein–Aronszajn identity
`LinearMap.det_one_add_comp_comm`.
-/

public section

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If an endomorphism is the identity modulo a line, its action on that line is
multiplication by its determinant. -/
theorem apply_eq_det_smul_of_sub_mem_span (f : V →ₗ[K] V) {x : V} (hx : x ≠ 0)
    (hf : ∀ v, v - f v ∈ K ∙ x) : f x = LinearMap.det f • x := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hx
  let ψ := φ.comp (f - 1)
  have hfx (v : V) : f v - v = ψ v • x := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hf v)
    have hv : f v - v = -c • x := by rw [neg_smul, hc, neg_sub]
    simp only [ψ, LinearMap.comp_apply, LinearMap.sub_apply, one_apply_eq_self, hv,
      map_smul, hφ, smul_eq_mul, mul_one]
  have hrepr : f = 1 + (LinearMap.toSpanSingleton K V x).comp ψ := by
    ext v
    rw [LinearMap.add_apply, one_apply_eq_self, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply]
    rw [← hfx v, add_sub_cancel]
  have hd : LinearMap.det f = 1 + ψ x := by
    rw [hrepr, det_one_add_comp_comm]
    simp
  rw [hd, add_smul, one_smul, ← hfx x, add_sub_cancel]

section CommRing

variable {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- The **matrix determinant lemma** for a scalar plus a rank-one endomorphism: on a free module of
positive finite rank `n`, `det (a • 1 + φ.smulRight u) = a ^ (n - 1) * (a + φ u)`. No
invertibility of `a` is needed. -/
theorem det_smul_one_add_smulRight (hM : 0 < Module.finrank R M) (a : R) (φ : Module.Dual R M)
    (u : M) : LinearMap.det (a • 1 + φ.smulRight u) = a ^ (Module.finrank R M - 1) * (a + φ u) := by
  classical
  let b := Module.Free.chooseBasis R M
  have hdot : b.repr u ⬝ᵥ (φ ∘ b) = φ u := by
    conv_rhs => rw [← b.sum_repr u, map_sum]
    simp [dotProduct]
  rw [← det_toMatrix b, map_add, map_smul, toMatrix_one, toMatrix_smulRight]
  set V := Matrix.vecMulVec (b.repr u) (φ ∘ b)
  -- `det (a • 1 + V)` is, up to the sign `(-1) ^ n`, the characteristic polynomial of `V` at `-a`.
  have h := V.eval_charpoly (-a)
  rw [Matrix.charpoly_vecMulVec, hdot] at h
  have hdet : (a • (1 : Matrix _ _ R) + V).det =
      (-1) ^ Fintype.card (Module.Free.ChooseBasisIndex R M) * (Matrix.scalar _ (-a) - V).det := by
    rw [← Matrix.det_neg]
    congr 1
    simp [Matrix.smul_one_eq_diagonal, add_comm, sub_eq_add_neg]
  rw [hdet, ← h, ← Module.finrank_eq_card_chooseBasisIndex]
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank R M = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hM).symm⟩
  rw [hk]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_smul,
    smul_eq_mul, add_tsub_cancel_right]
  have hsq : ((-1 : R) ^ k) ^ 2 = 1 := by simp [← pow_mul]
  rw [neg_pow, neg_pow a k, pow_succ]
  linear_combination (a ^ k * (a + φ u)) * hsq

end CommRing

end LinearMap
