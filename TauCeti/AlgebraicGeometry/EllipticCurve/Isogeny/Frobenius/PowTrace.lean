/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
-- Proof-only: `deg (1 - π ^ n)` is the point count over an extension of degree `n`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.FiniteExtension
-- Proof-only: the determinant of Frobenius on torsion is `q`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Torsion
-- Proof-only: `deg (1 - π) = #E(𝔽_q)`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Degree
-- Proof-only: the determinant of the pencil `r • M - s • 1` of a `2 × 2` matrix.
import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo
-- Proof-only: the Cayley–Hamilton recurrence for traces of powers of a `2 × 2` matrix.
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# The traces of the powers of Frobenius

Let `W` be an elliptic curve over a finite field `F` with `q` elements and `π` its `q`-power
Frobenius endomorphism. This file defines the sequence

`t n = q ^ n + 1 - deg (1 - π ^ n)`,

`WeierstrassCurve.frobeniusPowTrace`, and proves that it satisfies the linear recurrence

`t 0 = 2`, `t 1 = a_q`, `t (n + 2) = a_q * t (n + 1) - q * t n`,

where `a_q = q + 1 - #W(F)` is the Frobenius trace (Silverman V.2.3). For `n ≥ 1`, `t n` is the
Frobenius trace of `W` over an extension of `F` of degree `n`, so the recurrence determines the
point counts `#W(𝔽_{qⁿ}) = q ^ n + 1 - t n` over all finite extensions from the single number
`#W(F)`. Those counts are the coefficients of the logarithm of the zeta function
`Z(W/F, T) = exp (∑ #W(𝔽_{qⁿ}) Tⁿ / n)`, and the recurrence is what makes `Z` rational.

The sequence is defined through the degree of an endomorphism of `W` over `F` itself, so it needs
no choice of a field with `q ^ n` elements, and the degree convention `deg 0 = 0` gives `t 0 = 2`.
Over a separably closed algebraic extension and for `N` prime to `q`, `t n` is the trace of `π ^ n`
on `E[N]` modulo `N`: there `π` acts by a `2 × 2` matrix `M` over `ZMod N` with `det M = q` and
`det (1 - M ^ n) = deg (1 - π ^ n)`, and `trace A = 1 + det A - det (1 - A)` for a `2 × 2` matrix.
The recurrence is then the Cayley–Hamilton theorem for `M`, read modulo every `N` prime to `q`.

## Main definitions

* `WeierstrassCurve.frobeniusPowTrace`: the sequence `t n = q ^ n + 1 - deg (1 - π ^ n)`.

## Main results

* `WeierstrassCurve.frobeniusPowTrace_zero`, `WeierstrassCurve.frobeniusPowTrace_one`:
  `t 0 = 2` and `t 1 = a_q`.
* `WeierstrassCurve.frobeniusPowTrace_add_two`: `t (n + 2) = a_q * t (n + 1) - q * t n`.
* `WeierstrassCurve.frobeniusPowTrace_finrank`: over a finite extension `E/F` of degree `n`,
  `t n` is the Frobenius trace of `W` over `E`.
* `WeierstrassCurve.frobeniusPowTrace_eq_degree_baseChange`: `t n` may be computed from the
  base-changed Frobenius over any extension of `F`.
* `TauCeti.Isogeny.Hom.trace_torsionLinearMap_pow_ofIsogeny_baseChangeFrobenius`: `t n` is the
  trace of `π ^ n` on `E[N]` modulo `N`, over a separably closed algebraic extension.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.6 and V.2.
-/

public section

open TauCeti TauCeti.Isogeny WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The trace of the `n`th power of Frobenius**: `q ^ n + 1 - deg (1 - π ^ n)`, for an elliptic
curve `W` over a finite field with `q` elements and its `q`-power Frobenius endomorphism `π`.

At `n = 0` it is `2`, and for `n ≥ 1` it is the Frobenius trace `q ^ n + 1 - #W(𝔽_{qⁿ})` of `W`
over an extension of degree `n` (`frobeniusPowTrace_finrank`). It satisfies the linear recurrence
`t (n + 2) = a_q * t (n + 1) - q * t n` (`frobeniusPowTrace_add_two`). -/
noncomputable def frobeniusPowTrace (n : ℕ) : ℤ :=
  (Nat.card F : ℤ) ^ n + 1 - (1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ n).degree

/-- The defining equation of `frobeniusPowTrace`. -/
theorem frobeniusPowTrace_def (n : ℕ) :
    W.frobeniusPowTrace n =
      (Nat.card F : ℤ) ^ n + 1 - (1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ n).degree :=
  (rfl)

/-- `t 0 = 2`: the zeroth power of Frobenius is the identity, and `deg 0 = 0`. -/
@[simp]
theorem frobeniusPowTrace_zero : W.frobeniusPowTrace 0 = 2 := by
  rw [frobeniusPowTrace_def, pow_zero, pow_zero, sub_self, Hom.degree_zero]
  norm_num

/-- `t 1 = a_q`: the first term is the Frobenius trace, as `deg (1 - π) = #W(F)`. -/
@[simp]
theorem frobeniusPowTrace_one : W.frobeniusPowTrace 1 = W.frobeniusTrace := by
  rw [frobeniusPowTrace_def, pow_one, pow_one, ← ofIsogeny_oneSubFrobeniusIsogeny,
    Hom.degree_ofIsogeny, degree_oneSubFrobeniusIsogeny_eq_pointCount, frobeniusTrace_def]

/-- The trace of the `n`th power of Frobenius may be computed over any extension `K` of the
finite base, from the base-changed Frobenius of `W⁄K`. -/
theorem frobeniusPowTrace_eq_degree_baseChange (K : Type*) [Field K] [Algebra F K] (n : ℕ) :
    W.frobeniusPowTrace n = (Nat.card F : ℤ) ^ n + 1 -
      (1 - Hom.ofIsogeny (baseChangeFrobenius K W) ^ n).degree := by
  rw [frobeniusPowTrace_def, ← Hom.degree_map _ (algebraMap F K), Hom.map_sub, Hom.map_one,
    Hom.map_pow, Hom.ofIsogeny_map, ← baseChangeFrobenius_def]
  -- the two degrees are taken on `W.map (algebraMap F K)` and on `W⁄K`, the same curve: the
  -- base change `W⁄K` unfolds to `W.map (algebraMap F K)` only up to definitional equality
  rfl

/-- **Over an extension of degree `n`, the trace of the `n`th power of Frobenius is the Frobenius
trace**: `t n = q ^ n + 1 - #W(E)` for a finite extension `E/F` of degree `n`. -/
theorem frobeniusPowTrace_finrank (E : Type*) [Field E] [Finite E] [Algebra F E] :
    W.frobeniusPowTrace (Module.finrank F E) = (W⁄E).frobeniusTrace := by
  rw [frobeniusPowTrace_eq_degree_baseChange W (AlgebraicClosure E),
    Hom.degree_one_sub_pow_ofIsogeny_baseChangeFrobenius_eq_pointCount (E := E) W,
    frobeniusTrace_def, Module.natCard_eq_pow_finrank (K := F) (V := E), Nat.cast_pow]

end WeierstrassCurve

namespace TauCeti.Isogeny.Hom

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K] [IsSepClosed K]
  [Algebra.IsAlgebraic F K] [DecidableEq K] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
  {N : ℕ} [NeZero N]

/-- In a basis of `E[N]`, `N` invertible, the trace of the `n`th power of the matrix of Frobenius
is `t n` modulo `N`. -/
private theorem trace_toMatrix_pow_eq_frobeniusPowTrace (hN : (N : K) ≠ 0)
    (b : Module.Basis (Fin 2) (ZMod N) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)))
    (n : ℕ) :
    (LinearMap.toMatrix b b ((ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N) ^ n).trace =
      W.frobeniusPowTrace n := by
  set π := ofIsogeny (baseChangeFrobenius K W)
  set M := LinearMap.toMatrix b b (π.torsionLinearMap N)
  have hdet : (M ^ n).det = (Nat.card F : ZMod N) ^ n := by
    rw [Matrix.det_pow, LinearMap.det_toMatrix,
      det_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hN]
  -- `1 - π ^ n` is zero or a nonzero separable morphism, of determinant its degree
  have hdetOneSub : (1 - M ^ n).det = ((1 - π ^ n).degree : ZMod N) := by
    have hM : 1 - M ^ n = LinearMap.toMatrix b b ((1 - π ^ n).torsionLinearMap N) := by
      rw [← torsionRepresentation_apply, _root_.map_sub, _root_.map_one, _root_.map_pow,
        torsionRepresentation_apply, _root_.map_sub, LinearMap.toMatrix_one,
        ← LinearMap.toMatrix_pow]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have := isSeparable_toIsogeny_one_sub_pow_ofIsogeny_baseChangeFrobenius (K := K) W n hn
    rw [hM, LinearMap.det_toMatrix,
      det_torsionLinearMap hN (one_sub_pow_ofIsogeny_baseChangeFrobenius_ne_zero W n hn)]
  -- `trace A = 1 + det A - det (1 - A)` for a `2 × 2` matrix `A`
  have h := TauCeti.Matrix.det_smul_sub_smul_one_fin_two (M ^ n) (-1) (-1)
  rw [neg_one_smul, neg_one_smul, neg_sub_neg, hdetOneSub, hdet] at h
  rw [W.frobeniusPowTrace_eq_degree_baseChange K]
  push_cast
  linear_combination h

/-- **The trace of `π ^ n` on `E[N]` is `t n` modulo `N`**, over a separably closed algebraic
extension of the finite base in which `N` is invertible. -/
theorem trace_torsionLinearMap_pow_ofIsogeny_baseChangeFrobenius (hN : (N : K) ≠ 0) (n : ℕ) :
    LinearMap.trace (ZMod N) _
        ((ofIsogeny (baseChangeFrobenius K W) ^ n).torsionLinearMap N) =
      W.frobeniusPowTrace n := by
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy (W⁄K) N hN
  rw [LinearMap.trace_eq_matrix_trace (ZMod N) b, ← torsionRepresentation_apply, _root_.map_pow,
    torsionRepresentation_apply, ← LinearMap.toMatrix_pow,
    trace_toMatrix_pow_eq_frobeniusPowTrace W hN]

end TauCeti.Isogeny.Hom

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The recurrence for the traces of the powers of Frobenius**:
`t (n + 2) = a_q * t (n + 1) - q * t n`, where `a_q` is the Frobenius trace and `q` the number of
elements of the base (Silverman V.2.3). With `t 0 = 2` and `t 1 = a_q`, it determines every
point count of `W` over a finite extension from `#W(F)`. -/
theorem frobeniusPowTrace_add_two (n : ℕ) :
    W.frobeniusPowTrace (n + 2) =
      W.frobeniusTrace * W.frobeniusPowTrace (n + 1) - Nat.card F * W.frobeniusPowTrace n := by
  classical
  set X := W.frobeniusPowTrace (n + 2) -
    (W.frobeniusTrace * W.frobeniusPowTrace (n + 1) - Nat.card F * W.frobeniusPowTrace n)
  suffices hX : X = 0 from sub_eq_zero.mp hX
  -- `X` vanishes modulo `N = q |X| + 1`, which is prime to `q` and exceeds `|X|`
  set N := Nat.card F * X.natAbs + 1
  let K := AlgebraicClosure F
  have hq : (Nat.card F : K) = 0 := by
    cases nonempty_fintype F
    rw [Nat.card_eq_fintype_card, ← map_natCast (algebraMap F K), FiniteField.cast_card_eq_zero,
      map_zero]
  have hN : (N : K) ≠ 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hq, zero_mul, zero_add, Nat.cast_one]
    exact one_ne_zero
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy (W⁄K) N hN
  set M := LinearMap.toMatrix b b
    ((Hom.ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N)
  have ht (m : ℕ) : (W.frobeniusPowTrace m : ZMod N) = (M ^ m).trace :=
    (Hom.trace_toMatrix_pow_eq_frobeniusPowTrace W hN b m).symm
  have htr : M.trace = W.frobeniusTrace := by
    rw [← pow_one M, ← ht, frobeniusPowTrace_one]
  have hdet : M.det = Nat.card F := by
    rw [LinearMap.det_toMatrix, Hom.det_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hN]
  -- the Cayley–Hamilton recurrence for the traces of the powers of `M`
  have hXN : (X : ZMod N) = 0 := by
    have h := Matrix.trace_pow_add_two_fin_two M n
    rw [← ht, ← ht, ← ht, htr, hdet] at h
    simp only [X]
    push_cast
    linear_combination h
  refine Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd X N).mp hXN) ?_
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Nat.lt_succ_of_le (Nat.le_mul_of_pos_left _ Nat.card_pos)

end WeierstrassCurve

end
