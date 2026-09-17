/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner
public import TauCeti.NumberTheory.ModularForms.Fricke.Matrix

/-!
# The Atkin–Lehner bar is the adjugate, conjugated by the Fricke matrix

Two different matrices in this development are called "Atkin–Lehner". The Hecke-ring
anti-involution of `TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/AtkinLehner.lean` conjugates a
transpose by the *diagonal* `w = diag(1, N)`, and the Fricke matrix of
`TauCeti/NumberTheory/ModularForms/Fricke/Matrix.lean` is `W = !![0, -1; N, 0]`. Both of those
files record that the two matrices are different; neither says how they are related. This file
says how.

The relation is that conjugating the bar by `W` deletes the transpose and leaves the adjugate:

`adjugate x = W · bar x · W⁻¹`.

Nothing here is deep — in size two, `adjugate` is itself a conjugated transpose, `adjugate g =
J · gᵀ · J⁻¹` for `J = !![0, -1; 1, 0]`, so bar and adjugate differ by conjugation by `J · w⁻¹`,
and that matrix is `W` up to a scalar, which conjugation does not see. What the identity buys is
a translation: the Petersson adjoint produces `adjugateGL`, the `α ↦ (det α) · α⁻¹` involution of
`TauCeti/NumberTheory/ModularForms/SlashAdjugate.lean`, while the Hecke ring's commutativity
argument is phrased in the bar. The two layers can now be moved between.

## Main results

* `TauCeti.adjugateGL_eq_frickeGL_conj_bar`: `adjugate x = W · bar x · W⁻¹` for `x ∈ Δ₀(N)`.
* `TauCeti.bar_eq_inv_frickeGL_conj_adjugateGL`: the same read the other way,
  `bar x = W⁻¹ · adjugate x · W`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
-/

public section

open Matrix HeckeRing.GL2

namespace TauCeti

variable (N : ℕ)

/-- **The Atkin–Lehner bar is the adjugate, conjugated by the Fricke matrix**:
`adjugate x = W · bar x · W⁻¹`, where `W = !![0, -1; N, 0]`.

The two "Atkin–Lehner" matrices of this development are the diagonal `w = diag(1, N)`, which
conjugates the transpose to give the Hecke-ring bar, and `W`, the Fricke matrix. Since in size
two the adjugate is itself a conjugated transpose, the bar and the adjugate differ by a single
conjugation, and this identifies it. -/
theorem adjugateGL_eq_frickeGL_conj_bar [NeZero N] {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    adjugateGL x = frickeGL ℚ N * (atkinLehnerAntiInvolution N).bar x hx * (frickeGL ℚ N)⁻¹ := by
  obtain ⟨A, hA, -, ⟨c, hc⟩, -⟩ := (mem_Delta0_iff N).mp hx
  refine eq_mul_inv_of_mul_eq (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, adjugateGL_val, hA, Matrix.adjugate_fin_two,
    atkinLehnerAntiInvolution_bar_val N hx A hA c hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hc, mul_comm]

/-- **The Atkin–Lehner bar, recovered from the adjugate**: `bar x = W⁻¹ · adjugate x · W`. This
is `adjugateGL_eq_frickeGL_conj_bar` read in the other direction. -/
theorem bar_eq_inv_frickeGL_conj_adjugateGL [NeZero N] {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    (atkinLehnerAntiInvolution N).bar x hx = (frickeGL ℚ N)⁻¹ * adjugateGL x * frickeGL ℚ N := by
  rw [adjugateGL_eq_frickeGL_conj_bar N hx]
  group

end TauCeti
