/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
public import TauCeti.Analysis.Pseudodifferential.PolarDecomposition
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow

/-!
# Real powers of strictly positive homogeneous symbols

A homogeneous symbol `a` of degree `m` with values in the endomorphisms of a complex Hilbert
space `V` is *strictly positive* (`TauCeti.HomogeneousSymbol.IsStrictlyPositive`) when its value
`a (x, ξ)` is a strictly positive operator at every position `x` and every nonzero frequency `ξ`.
This is the principal symbol of a positive elliptic operator, such as `‖ξ‖ ^ 2` times the identity
for the Laplacian `1 + ∇*∇` of a metric connection, or `a† a` for an elliptic `a`. A strictly
positive symbol is elliptic and pointwise self-adjoint, and strict positivity is preserved by
sums, positive multiples and straight lines between two strictly positive symbols.

When `V` is finite-dimensional, the real powers `a (x, ξ) ^ z` of the values, given by the
continuous functional calculus, depend smoothly on `(x, ξ)` away from the zero frequency, and
`(t ^ m • A) ^ z = t ^ (m z) • A ^ z` for `t > 0` makes them positively homogeneous of degree
`m z`. So for every real `z` they form a homogeneous symbol `HomogeneousSymbol.rpow a ha z` of
degree `m z`. In Seeley's theory of complex powers, this is the principal symbol `σ(A) ^ z` of the
power `A ^ z` of a positive elliptic operator `A` of order `m`. The usual rules of real powers
hold at the level of symbols:

* `HomogeneousSymbol.rpow_zero`, `HomogeneousSymbol.rpow_one`: `a ^ 0 = 1` and `a ^ 1 = a`;
* `HomogeneousSymbol.rpow_comp_rpow`: `a ^ z ∘ a ^ w = a ^ (z + w)`;
* `HomogeneousSymbol.rpow_rpow`: `(a ^ z) ^ w = a ^ (z w)`;
* `HomogeneousSymbol.rpow_neg`, `HomogeneousSymbol.rpow_neg_one`: `a ^ (-z)` is the inverse of
  `a ^ z`, and `a ^ (-1)` is the inverse of `a`;
* `HomogeneousSymbol.smul_rpow`: `(c a) ^ z = c ^ z a ^ z` for `c > 0`;
* `HomogeneousSymbol.normRpow_rpow`: `(‖ξ‖ ^ m) ^ z = ‖ξ‖ ^ (m z)`;
* `HomogeneousSymbol.rpow_compPosition`: powers commute with restriction to positions;
* `HomogeneousSymbol.modulus_eq_rpow`: the modulus `|a| = √(a† a)` of an elliptic symbol is the
  power `(a† a) ^ (1 / 2)`.

Every power of a strictly positive symbol is again strictly positive
(`HomogeneousSymbol.isStrictlyPositive_rpow`), hence elliptic, and pointwise self-adjoint.

## References

* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307 (the principal symbol of `A ^ z` is `σ(A) ^ z`).
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, second edition, Springer
  (2001), Chapter II, §§10–11.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℝ}

/-! ### Strictly positive symbols -/

/-- A homogeneous symbol with values in the endomorphisms of a Hilbert space is strictly positive
if its value at every position and every nonzero frequency is a strictly positive operator. -/
def IsStrictlyPositive (a : HomogeneousSymbol X E V V m) : Prop :=
  ∀ x ξ, ξ ≠ 0 → _root_.IsStrictlyPositive (a.coefficient (x, ξ))

theorem isStrictlyPositive_iff {a : HomogeneousSymbol X E V V m} :
    a.IsStrictlyPositive ↔ ∀ x ξ, ξ ≠ 0 → _root_.IsStrictlyPositive (a.coefficient (x, ξ)) :=
  Iff.rfl

/-- A strictly positive symbol is elliptic. -/
theorem IsStrictlyPositive.isElliptic {a : HomogeneousSymbol X E V V m}
    (ha : a.IsStrictlyPositive) : a.IsElliptic :=
  isElliptic_iff.mpr fun x ξ hξ ↦
    ContinuousLinearMap.isInvertible_iff_isUnit.mpr (ha x ξ hξ).isUnit

/-- Transport along an equality of degrees does not change strict positivity. -/
@[simp]
theorem isStrictlyPositive_castDegree_iff {m' : ℝ} (h : m = m')
    {a : HomogeneousSymbol X E V V m} :
    (a.castDegree h).IsStrictlyPositive ↔ a.IsStrictlyPositive := by
  simp only [isStrictlyPositive_iff, coefficient_castDegree]

/-- Restricting a strictly positive symbol to positions keeps it strictly positive. -/
theorem IsStrictlyPositive.compPosition {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a : HomogeneousSymbol X E V V m} (ha : a.IsStrictlyPositive) (g : Y → X)
    (hg : ContDiff ℝ ∞ g) : (a.compPosition g hg).IsStrictlyPositive :=
  fun y ξ hξ ↦ by simpa using ha (g y) ξ hξ

variable [CompleteSpace V]

/-- A strictly positive symbol is pointwise self-adjoint. -/
theorem IsStrictlyPositive.adjoint_eq {a : HomogeneousSymbol X E V V m}
    (ha : a.IsStrictlyPositive) : a.adjoint = a :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simpa using (ha x ξ hξ).isSelfAdjoint.adjoint_eq

variable (X E V) in
/-- The identity symbol is strictly positive. -/
theorem isStrictlyPositive_id : (id X E V).IsStrictlyPositive :=
  fun _ _ hξ ↦ by
    rw [coefficient_id hξ, ← ContinuousLinearMap.one_def]
    exact isStrictlyPositive_one

variable (X V) in
/-- The symbol `‖ξ‖ ^ m` times the identity is strictly positive. -/
theorem isStrictlyPositive_normRpow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℝ) : (normRpow X E V m).IsStrictlyPositive :=
  fun _ ξ hξ ↦ by
    rw [coefficient_normRpow_of_ne_zero _ _ _ hξ, ← ContinuousLinearMap.one_def]
    exact isStrictlyPositive_one.smul (Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) m)

/-- The sum of two strictly positive symbols is strictly positive. -/
theorem IsStrictlyPositive.add {a b : HomogeneousSymbol X E V V m} (ha : a.IsStrictlyPositive)
    (hb : b.IsStrictlyPositive) : (a + b).IsStrictlyPositive :=
  fun x ξ hξ ↦ by
    simpa using _root_.IsStrictlyPositive.add_nonneg (ha x ξ hξ) (hb x ξ hξ).nonneg

/-- A positive multiple of a strictly positive symbol is strictly positive. -/
theorem IsStrictlyPositive.smul {a : HomogeneousSymbol X E V V m} (ha : a.IsStrictlyPositive)
    {c : ℝ} (hc : 0 < c) : (c • a).IsStrictlyPositive :=
  fun x ξ hξ ↦ by simpa using (ha x ξ hξ).smul hc

/-- **Positive symbols form a convex set.** The straight line between two strictly positive
symbols of the same degree consists of strictly positive symbols. -/
theorem IsStrictlyPositive.lineMap {a b : HomogeneousSymbol X E V V m}
    (ha : a.IsStrictlyPositive) (hb : b.IsStrictlyPositive) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (AffineMap.lineMap a b s).IsStrictlyPositive := by
  rw [AffineMap.lineMap_apply_module]
  rcases hs.2.lt_or_eq with hs1 | rfl
  · exact fun x ξ hξ ↦ by
      simpa using _root_.IsStrictlyPositive.add_nonneg ((ha x ξ hξ).smul (sub_pos.mpr hs1))
        (smul_nonneg hs.1 (hb x ξ hξ).nonneg)
  · simpa using hb

/-- The Gram symbol `a† a` of an elliptic symbol is strictly positive. -/
theorem IsElliptic.isStrictlyPositive_adjoint_comp {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {a : HomogeneousSymbol X E V W m}
    (ha : a.IsElliptic) : (a.adjoint.comp a).IsStrictlyPositive :=
  fun x ξ hξ ↦ by
    simpa using ContinuousLinearMap.isStrictlyPositive_adjoint_comp_self_of_isInvertible
      (isElliptic_iff.mp ha x ξ hξ)

/-! ### Real powers -/

section Rpow

variable [FiniteDimensional ℂ V]

/-- Away from the zero frequency, the real powers `a (x, ξ) ^ z` of the values of a strictly
positive symbol depend smoothly on `(x, ξ)`. -/
theorem contDiffOn_rpow_coefficient (a : HomogeneousSymbol X E V V m)
    (ha : a.IsStrictlyPositive) (z : ℝ) :
    ContDiffOn ℝ ∞ (fun p ↦ a.coefficient p ^ z) {p | p.2 ≠ 0} :=
  ((ContinuousLinearMap.contDiffOn_rpow z).restrict_scalars ℝ).comp a.contDiffOn_coefficient
    fun p hp ↦ ha p.1 p.2 hp

/-- The real power `a ^ z` of a strictly positive homogeneous symbol `a` of degree `m`: the
homogeneous symbol of degree `m z` whose value at a nonzero frequency is the real power, by the
continuous functional calculus, of the value of `a`. Its value at the zero frequency is `0`, by the
convention of `HomogeneousSymbol`. -/
noncomputable def rpow (a : HomogeneousSymbol X E V V m) (ha : a.IsStrictlyPositive) (z : ℝ) :
    HomogeneousSymbol X E V V (m * z) :=
  mk' (fun p ↦ a.coefficient p ^ z) (a.contDiffOn_rpow_coefficient ha z) fun x ξ hξ t ht ↦ by
    rw [a.homogeneous x ξ t ht, CFC.smul_rpow (Real.rpow_nonneg ht.le m) _ z (ha x ξ hξ).nonneg,
      ← Real.rpow_mul ht.le]

variable (a : HomogeneousSymbol X E V V m) (ha : a.IsStrictlyPositive)

@[simp]
theorem coefficient_rpow_of_ne_zero (z : ℝ) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.rpow ha z).coefficient (x, ξ) = a.coefficient (x, ξ) ^ z :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

/-- Every real power of a strictly positive symbol is strictly positive. -/
theorem isStrictlyPositive_rpow (z : ℝ) : (a.rpow ha z).IsStrictlyPositive :=
  fun x ξ hξ ↦ by
    rw [coefficient_rpow_of_ne_zero a ha z hξ]
    exact (ha x ξ hξ).isUnit.cfcRpow z |>.isStrictlyPositive CFC.rpow_nonneg

/-- Every real power of a strictly positive symbol is elliptic. -/
theorem isElliptic_rpow (z : ℝ) : (a.rpow ha z).IsElliptic :=
  (a.isStrictlyPositive_rpow ha z).isElliptic

/-- Every real power of a strictly positive symbol is pointwise self-adjoint. -/
@[simp]
theorem adjoint_rpow (z : ℝ) : (a.rpow ha z).adjoint = a.rpow ha z :=
  (a.isStrictlyPositive_rpow ha z).adjoint_eq

/-- The zeroth power of a strictly positive symbol is the identity symbol. -/
@[simp]
theorem rpow_zero : a.rpow ha 0 = (id X E V).castDegree (mul_zero m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_zero _ (ha x ξ hξ).nonneg, ContinuousLinearMap.one_def]

/-- The first power of a strictly positive symbol is the symbol itself. -/
@[simp]
theorem rpow_one : a.rpow ha 1 = a.castDegree (mul_one m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [hξ, CFC.rpow_one _ (ha x ξ hξ).nonneg]

/-- **Powers add under composition**: `a ^ z ∘ a ^ w = a ^ (z + w)`. -/
theorem rpow_comp_rpow (z w : ℝ) :
    (a.rpow ha z).comp (a.rpow ha w) = (a.rpow ha (z + w)).castDegree (mul_add m z w) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_add (ha x ξ hξ).isUnit, ContinuousLinearMap.mul_def]

/-- **Powers multiply under iteration**: `(a ^ z) ^ w = a ^ (z w)`. -/
theorem rpow_rpow (z w : ℝ) :
    (a.rpow ha z).rpow (a.isStrictlyPositive_rpow ha z) w =
      (a.rpow ha (z * w)).castDegree (mul_assoc m z w).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_rpow _ z w (ha x ξ hξ)]

/-- The power `a ^ (-z)` is the inverse of the power `a ^ z`. -/
theorem rpow_neg (z : ℝ) :
    a.rpow ha (-z) =
      ((a.rpow ha z).inverse (a.isElliptic_rpow ha z)).castDegree (mul_neg m z).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hA := ha x ξ hξ
    have hz : IsUnit (a.coefficient (x, ξ) ^ z) := hA.isUnit.cfcRpow z
    simp only [coefficient_rpow_of_ne_zero a ha _ hξ, coefficient_castDegree,
      coefficient_inverse, ← ContinuousLinearMap.ringInverse_eq_inverse]
    -- `a ^ (-z)` is a left inverse of the unit `a ^ z`, hence equal to its ring inverse.
    calc a.coefficient (x, ξ) ^ (-z)
        = a.coefficient (x, ξ) ^ (-z) * (a.coefficient (x, ξ) ^ z * Ring.inverse
            (a.coefficient (x, ξ) ^ z)) := by rw [Ring.mul_inverse_cancel _ hz, mul_one]
      _ = Ring.inverse (a.coefficient (x, ξ) ^ z) := by
        rw [← mul_assoc, CFC.rpow_neg_mul_rpow z hA, one_mul]

/-- The power `a ^ (-1)` is the inverse of `a`. -/
theorem rpow_neg_one :
    a.rpow ha (-1) = (a.inverse ha.isElliptic).castDegree (mul_neg_one m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, ← ContinuousLinearMap.ringInverse_eq_inverse,
      CFC.inverse_eq_rpow_neg_one (ha x ξ hξ)]

/-- Powers of a positive multiple: `(c a) ^ z = c ^ z a ^ z` for `c > 0`. -/
theorem smul_rpow {c : ℝ} (hc : 0 < c) (z : ℝ) :
    (c • a).rpow (ha.smul hc) z = c ^ z • a.rpow ha z :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.smul_rpow hc.le _ z (ha x ξ hξ).nonneg]

/-- Powers commute with restriction to positions. -/
@[simp]
theorem rpow_compPosition {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : Y → X)
    (hg : ContDiff ℝ ∞ g) (z : ℝ) :
    (a.rpow ha z).compPosition g hg = (a.compPosition g hg).rpow (ha.compPosition g hg) z :=
  ext_of_ne_zero fun y ξ hξ ↦ by simp [hξ]

end Rpow

section NormRpow

variable (X V) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℂ V]

/-- The powers of `‖ξ‖ ^ m` are `(‖ξ‖ ^ m) ^ z = ‖ξ‖ ^ (m z)`. -/
@[simp]
theorem normRpow_rpow (m z : ℝ) :
    (normRpow X E V m).rpow (isStrictlyPositive_normRpow X V m) z = normRpow X E V (m * z) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_rpow_of_ne_zero _ _ _ hξ, coefficient_normRpow_of_ne_zero _ _ _ hξ,
      coefficient_normRpow_of_ne_zero _ _ _ hξ, ← ContinuousLinearMap.one_def,
      CFC.smul_rpow (Real.rpow_nonneg (norm_nonneg ξ) m) _ z zero_le_one, CFC.one_rpow,
      ← Real.rpow_mul (norm_nonneg ξ)]

end NormRpow

/-- The modulus `|a| = √(a† a)` of an elliptic symbol is the power `(a† a) ^ (1 / 2)` of its Gram
symbol. -/
theorem modulus_eq_rpow [FiniteDimensional ℂ V] {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (a : HomogeneousSymbol X E V W m)
    (ha : a.IsElliptic) :
    a.modulus ha = ((a.adjoint.comp a).rpow ha.isStrictlyPositive_adjoint_comp (1 / 2)).castDegree
      (by ring) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, ContinuousLinearMap.modulus_eq_sqrt, CFC.sqrt_eq_rpow]

end HomogeneousSymbol

end TauCeti
