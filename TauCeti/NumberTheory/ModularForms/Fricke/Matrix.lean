/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The Fricke matrix

The Fricke matrix `W = !![0, -1; N, 0]`, as an element of `GL (Fin 2) K` for a field `K` in
which `N` is invertible. Its determinant is `N`, which is nonzero exactly under the standing
`[NeZero (N : K)]` hypothesis, so `W` is a unit.

The base field is a parameter rather than `ℚ`: the two consumers sit over different fields.
The weight-`k` slash is an action of `GL (Fin 2) ℝ`, while the `GL (Fin 2) ℚ` Hecke-ring stack
of `TauCeti/NumberTheory/HeckeRing/GL2/Delta0.lean` wants the rational form; both are
`frickeGL _ N`, with no transport lemmas between them. Over `ℚ` and `ℝ` a caller holding
`[NeZero N]` on the natural number gets the standing `[NeZero (N : K)]` by instance search,
through `NeZero.charZero`; the instance runs only in that direction.

This file is only the matrix. `TauCeti/NumberTheory/ModularForms/Fricke/Operator.lean` builds
the Fricke *slash operator* on `M_k(Γ₁(N))` on top of it: the raw `f ↦ f ∣[k] W`, carrying no
normalizing scalar and so not an involution. The normalization
`𝒲_N = (√N) ^ (2 - k) • (· ∣[k] W)` rescales that map to an involution in even weight.

## Main definitions

* `TauCeti.frickeGL`: the Fricke matrix as an element of `GL (Fin 2) K`.

## Main results

* `TauCeti.coe_frickeGL`: the underlying matrix is `!![0, -1; N, 0]`.
* `TauCeti.val_det_frickeGL`: the determinant is `N`.
* `TauCeti.val_det_frickeGL_pos`: over an ordered ring, that determinant is positive. This is
  about the single matrix `W`, deliberately not a general statement about `SL`-type elements.
* `TauCeti.coe_inv_frickeGL`: `W⁻¹ = !![0, N⁻¹; -1, 0]`.
* `TauCeti.frickeGL_sq`: `W² = (-N) • 1`, as a scalar element of `GL (Fin 2) K`.

## Relation to the Atkin–Lehner anti-involution

Both this matrix and the conjugating matrix of
`TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/AtkinLehner.lean` are called "Atkin–Lehner" in the
literature, and they are **different matrices**. That file conjugates by `natDiagGL 2 ![1, N]`,
the diagonal rescaling repairing the transpose's failure to preserve `Γ₀(N)`; its docstring
already records that it is *not* `!![0, -1; N, 0]`. This file is the latter.

At `N = 1` the Fricke matrix coincides numerically with the level-one `S = !![0, -1; 1, 0]` of
`TauCeti/NumberTheory/ModularForms/STransform.lean` and with `TauCeti.SU2.weylMatrix`. Those are
different objects in different settings — neither carries a determinant-`N` normalization — so
`frickeGL` is not a restatement of either.

Ported from the AINTLIB `LeanModularForms` project
(`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Fricke.lean`, Chris Birkbeck,
Apache-2.0, <https://github.com/CBirkbeck/AINTLIB>).
-/

open Matrix

namespace TauCeti

variable {K : Type*} [Field K] {N : ℕ} [NeZero (N : K)]

/-- The Fricke matrix `W = !![0, -1; N, 0]` as an element of `GL (Fin 2) K`, of determinant
`N`. -/
public noncomputable def frickeGL (K : Type*) [Field K] (N : ℕ) [NeZero (N : K)] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : K), 0]
    (by simp [NeZero.ne])

/-- The underlying matrix of `frickeGL K N`. -/
@[simp]
public theorem coe_frickeGL :
    (↑(frickeGL K N) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; (N : K), 0] := by
  simp [frickeGL]

/-- The determinant of `frickeGL K N` is `N`. -/
public theorem val_det_frickeGL : ((frickeGL K N).det : K) = N := by
  simp [Matrix.GeneralLinearGroup.val_det_apply]

/-- Over an ordered ring the determinant of `frickeGL K N` is positive. This is about the
single matrix `W`; it is deliberately not a general statement about determinants of `SL`-type
elements. -/
public theorem val_det_frickeGL_pos [PartialOrder K] [IsOrderedRing K] :
    0 < ((frickeGL K N).det : K) := by
  rw [val_det_frickeGL]
  exact (Nat.cast_nonneg N).lt_of_ne' (NeZero.ne (N : K))

/-- `W⁻¹ = !![0, N⁻¹; -1, 0]`.

Deliberately not `@[simp]`: `Matrix.coe_units_inv` is itself `simp`, so simp rewrites this
left-hand side to `(!![0, -1; N, 0])⁻¹` and it is not in simp-normal form. -/
public theorem coe_inv_frickeGL :
    (↑(frickeGL K N)⁻¹ : Matrix (Fin 2) (Fin 2) K) = !![0, (N : K)⁻¹; -1, 0] := by
  simp [Matrix.inv_def, Matrix.adjugate_fin_two_of, NeZero.ne (N : K)]

/-- `W² = (-N) • 1`, as the scalar element `Matrix.GeneralLinearGroup.scalar` of
`GL (Fin 2) K`. This is the identity behind the centrality of `W²` and the scalar the normalized
Fricke operator divides out; the scalar form is the one that mathlib's `glScalar_smul` and
`ModularForm.slash_scalar` consume. -/
@[simp]
public theorem frickeGL_sq :
    frickeGL K N ^ 2 =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (-(N : K)) (neg_ne_zero.mpr (NeZero.ne _))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq]

end TauCeti
