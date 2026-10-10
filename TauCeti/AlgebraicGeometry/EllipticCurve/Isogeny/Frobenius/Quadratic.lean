/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo

/-!
# The characteristic equation of Frobenius

Let `W` be an elliptic curve over a finite field `𝔽_q`, let `K` be a separably closed algebraic
extension of `𝔽_q`, and let `π` be the Frobenius endomorphism of `W⁄K`. This file proves that `π`
satisfies its characteristic equation in the endomorphism ring,

`π ^ 2 - a_q π + q = 0`,

where `a_q = q + 1 - #E(𝔽_q)` is `WeierstrassCurve.frobeniusTrace` (Silverman V.2.3.1(a)).
Equivalently, `a_q - π` composes with `π` on either side to `q`: `π (a_q - π) = (a_q - π) π = q`.
Classically `a_q - π` is the dual `π̂` of the Frobenius, and these are the identities
`π π̂ = π̂ π = q` and `π + π̂ = a_q`.

The proof follows Silverman V.2.3. For every `N` invertible in `K`, the action of `π` on the
`N`-torsion `E[N] ≅ (ℤ/N)²` has determinant `q`, and `1 - π` has determinant `#E(𝔽_q)`, both
computed through the Weil pairing. For a `2 × 2` matrix `det (1 - M) = 1 - tr M + det M`, so the
trace of `π` on `E[N]` is `a_q` modulo `N`. By the Cayley–Hamilton theorem `π ^ 2 - a_q π + q`
then kills `E[ℓ]` for every prime `ℓ` different from the characteristic, and an endomorphism
vanishing on infinitely many points is zero.

## Main results

* `TauCeti.Isogeny.Hom.det_torsionLinearMap_id_sub_ofIsogeny_baseChangeFrobenius`: the determinant
  of `1 - π` on `E[N]` is `#E(𝔽_q)` modulo `N`.
* `TauCeti.Isogeny.Hom.trace_torsionLinearMap_ofIsogeny_baseChangeFrobenius`: the trace of `π` on
  `E[N]` is `a_q` modulo `N`.
* `TauCeti.Isogeny.Hom.ofIsogeny_baseChangeFrobenius_sq_sub_frobeniusTrace_mul_add_card_eq_zero`:
  the characteristic equation `π ^ 2 - a_q π + q = 0`.
* `TauCeti.Isogeny.Hom.ofIsogeny_baseChangeFrobenius_mul_frobeniusTrace_sub` and
  `TauCeti.Isogeny.Hom.frobeniusTrace_sub_ofIsogeny_baseChangeFrobenius_mul`:
  `π (a_q - π) = q` and `(a_q - π) π = q`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.6 and V.2.3.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace TauCeti.Isogeny.Hom

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K] [IsSepClosed K]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **The determinant of `1 - π` on `E[N]` is the point count** `#E(𝔽_q)` modulo `N`, over a
separably closed extension in which `N` is invertible. -/
theorem det_torsionLinearMap_id_sub_ofIsogeny_baseChangeFrobenius [DecidableEq K] {N : ℕ}
    [NeZero N] (hN : (N : K) ≠ 0) :
    LinearMap.det
      ((id (W⁄K).toAffine - ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N) =
        W.pointCount := by
  -- `1 - π` is the Frobenius pencil `r π - s` at `r = s = -1`
  have h := det_torsionLinearMap_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id W hN (-1) (-1)
    (by simp)
  rw [neg_one_zsmul, neg_one_zsmul, neg_sub_neg] at h
  rw [h, degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount]

variable [Algebra.IsAlgebraic F K]

/-- **The trace of the Frobenius on `E[N]` is the Frobenius trace** `a_q = q + 1 - #E(𝔽_q)` modulo
`N`, over a separably closed algebraic extension in which `N` is invertible. -/
theorem trace_torsionLinearMap_ofIsogeny_baseChangeFrobenius [DecidableEq K] {N : ℕ} [NeZero N]
    (hN : (N : K) ≠ 0) :
    LinearMap.trace (ZMod N) _ ((ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N) =
      W.frobeniusTrace := by
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy (W⁄K) N hN
  rw [LinearMap.trace_eq_matrix_trace _ b, WeierstrassCurve.frobeniusTrace_def]
  set M := LinearMap.toMatrix b b ((ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N)
  have hdet : M.det = Nat.card F := by
    rw [LinearMap.det_toMatrix]
    exact det_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hN
  have hdet_one_sub : (1 - M).det = W.pointCount := by
    rw [← det_torsionLinearMap_id_sub_ofIsogeny_baseChangeFrobenius W hN,
      ← LinearMap.det_toMatrix b, torsionLinearMap_sub, torsionLinearMap_id, map_sub,
      LinearMap.toMatrix_id]
  -- for a `2 × 2` matrix, `det (1 - M) = det M - tr M + 1`
  have h := TauCeti.Matrix.det_smul_sub_smul_one_fin_two M (-1) (-1)
  rw [neg_one_smul, neg_one_smul, neg_sub_neg, hdet_one_sub, hdet] at h
  push_cast
  linear_combination h

/-- **The characteristic equation of Frobenius** (Silverman V.2.3.1(a)): over a separably closed
algebraic extension of the finite base, the Frobenius endomorphism `π` satisfies
`π ^ 2 - a_q π + q = 0` in the endomorphism ring, where `a_q` is `WeierstrassCurve.frobeniusTrace`
and `q = #F`. -/
theorem ofIsogeny_baseChangeFrobenius_sq_sub_frobeniusTrace_mul_add_card_eq_zero :
    ofIsogeny (baseChangeFrobenius K W) ^ 2 -
        W.frobeniusTrace * ofIsogeny (baseChangeFrobenius K W) + Nat.card F = 0 := by
  classical
  set π := ofIsogeny (baseChangeFrobenius K W)
  -- it suffices that the endomorphism kills `E[ℓ]` for every prime `ℓ` invertible in `K`
  refine ext_pointMap_of_prime_zsmul_eq_zero fun ℓ hℓ hℓK P hP ↦ ?_
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy (W⁄K) ℓ hℓK
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  -- Cayley–Hamilton for the action of `π` on the rank-two module `E[ℓ]`, whose characteristic
  -- polynomial is `X ^ 2 - a_q X + q`
  have hCH := (π.torsionLinearMap ℓ).aeval_self_charpoly
  rw [← LinearMap.charpoly_toMatrix _ b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace, trace_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hℓK,
    LinearMap.det_toMatrix, det_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hℓK] at hCH
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, map_intCast, map_natCast] at hCH
  have hzero :
      torsionRepresentation (W⁄K).toAffine ℓ (π ^ 2 - W.frobeniusTrace * π + Nat.card F) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow, map_intCast, map_natCast,
      torsionRepresentation_apply] using hCH
  have hP' : P ∈ AddSubgroup.torsionBy (W⁄K).toAffine.Point (ℓ : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).2 hP
  simpa using congrArg (fun f ↦ (f ⟨P, hP'⟩ : (W⁄K).toAffine.Point)) hzero

/-- **`a_q - π` is a right complement of the Frobenius up to `q`**: `π (a_q - π) = q`. -/
theorem ofIsogeny_baseChangeFrobenius_mul_frobeniusTrace_sub :
    ofIsogeny (baseChangeFrobenius K W) *
        (W.frobeniusTrace - ofIsogeny (baseChangeFrobenius K W)) = Nat.card F := by
  rw [mul_sub, ← Int.cast_comm, ← sq, ← sub_eq_zero, ← neg_eq_zero,
    ← ofIsogeny_baseChangeFrobenius_sq_sub_frobeniusTrace_mul_add_card_eq_zero (K := K) W]
  abel

/-- **`a_q - π` is a left complement of the Frobenius up to `q`**: `(a_q - π) π = q`. -/
theorem frobeniusTrace_sub_ofIsogeny_baseChangeFrobenius_mul :
    (W.frobeniusTrace - ofIsogeny (baseChangeFrobenius K W)) *
        ofIsogeny (baseChangeFrobenius K W) = Nat.card F := by
  rw [← ofIsogeny_baseChangeFrobenius_mul_frobeniusTrace_sub (K := K) W, mul_sub, sub_mul,
    Int.cast_comm]

end TauCeti.Isogeny.Hom

end
