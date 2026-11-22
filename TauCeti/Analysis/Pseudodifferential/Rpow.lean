/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
public import TauCeti.Analysis.Pseudodifferential.PolarDecomposition
public import TauCeti.Analysis.Pseudodifferential.StrictlyPositive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Real powers of strictly positive homogeneous symbols

Let `a` be a strictly positive homogeneous symbol (`TauCeti.HomogeneousSymbol.IsStrictlyPositive`)
of degree `m` with values in the endomorphisms of a complex Hilbert space `V`, such as the principal
symbol of a positive elliptic operator.

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
(`HomogeneousSymbol.isStrictlyPositive_rpow`), hence elliptic, and pointwise self-adjoint. The
modulus of an elliptic symbol is strictly positive
(`HomogeneousSymbol.IsElliptic.isStrictlyPositive_modulus`, in
`TauCeti.Analysis.Pseudodifferential.PolarDecomposition`), so it has real powers as well.

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
  [NormedSpace ℝ E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {m : ℝ}

/-! ### Real powers -/

section Rpow

variable [FiniteDimensional ℂ V]

/-- Away from the zero frequency, the real powers `a (x, ξ) ^ z` of the values of a strictly
positive symbol depend smoothly on `(x, ξ)`. -/
theorem contDiffOn_rpow_coefficient (a : HomogeneousSymbol X E V V m)
    (ha : a.IsStrictlyPositive) (z : ℝ) :
    ContDiffOn ℝ ∞ (fun p ↦ a.coefficient p ^ z) {p | p.2 ≠ 0} :=
  ((ContinuousLinearMap.contDiffOn_rpow z).restrict_scalars ℝ).comp a.contDiffOn_coefficient
    fun p hp ↦ isStrictlyPositive_iff.mp ha p.1 p.2 hp

/-- The real power `a ^ z` of a strictly positive homogeneous symbol `a` of degree `m`: the
homogeneous symbol of degree `m z` whose value at a nonzero frequency is the real power, by the
continuous functional calculus, of the value of `a`. Its value at the zero frequency is `0`, by the
convention of `HomogeneousSymbol`. -/
noncomputable def rpow (a : HomogeneousSymbol X E V V m) (ha : a.IsStrictlyPositive) (z : ℝ) :
    HomogeneousSymbol X E V V (m * z) :=
  mk' (fun p ↦ a.coefficient p ^ z) (a.contDiffOn_rpow_coefficient ha z) fun x ξ hξ t ht ↦ by
    rw [a.homogeneous x ξ t ht, CFC.smul_rpow (Real.rpow_nonneg ht.le m) _ z
      (isStrictlyPositive_iff.mp ha x ξ hξ).nonneg, ← Real.rpow_mul ht.le]

variable (a : HomogeneousSymbol X E V V m) (ha : a.IsStrictlyPositive)

@[simp]
theorem coefficient_rpow_of_ne_zero (z : ℝ) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.rpow ha z).coefficient (x, ξ) = a.coefficient (x, ξ) ^ z :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

/-- Every real power of a strictly positive symbol is strictly positive. -/
theorem isStrictlyPositive_rpow (z : ℝ) : (a.rpow ha z).IsStrictlyPositive :=
  isStrictlyPositive_iff.mpr fun x ξ hξ ↦ by
    rw [coefficient_rpow_of_ne_zero a ha z hξ]
    exact (isStrictlyPositive_iff.mp ha x ξ hξ).rpow _ z

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
    simp [hξ, CFC.rpow_zero _ (isStrictlyPositive_iff.mp ha x ξ hξ).nonneg,
      ContinuousLinearMap.one_def]

/-- The first power of a strictly positive symbol is the symbol itself. -/
@[simp]
theorem rpow_one : a.rpow ha 1 = a.castDegree (mul_one m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_one _ (isStrictlyPositive_iff.mp ha x ξ hξ).nonneg]

/-- **Powers add under composition**: `a ^ z ∘ a ^ w = a ^ (z + w)`. -/
theorem rpow_comp_rpow (z w : ℝ) :
    (a.rpow ha z).comp (a.rpow ha w) = (a.rpow ha (z + w)).castDegree (mul_add m z w) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_add (isStrictlyPositive_iff.mp ha x ξ hξ).isUnit,
      ContinuousLinearMap.mul_def]

/-- **Powers multiply under iteration**: `(a ^ z) ^ w = a ^ (z w)`. -/
theorem rpow_rpow (z w : ℝ) :
    (a.rpow ha z).rpow (a.isStrictlyPositive_rpow ha z) w =
      (a.rpow ha (z * w)).castDegree (mul_assoc m z w).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_rpow _ z w (isStrictlyPositive_iff.mp ha x ξ hξ)]

/-- The power `a ^ (-z)` is the inverse of the power `a ^ z`. -/
theorem rpow_neg (z : ℝ) :
    a.rpow ha (-z) =
      ((a.rpow ha z).inverse (a.isElliptic_rpow ha z)).castDegree (mul_neg m z).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, ← ContinuousLinearMap.ringInverse_eq_inverse,
      CFC.inverse_rpow _ z (isStrictlyPositive_iff.mp ha x ξ hξ)]

/-- The power `a ^ (-1)` is the inverse of `a`. -/
theorem rpow_neg_one :
    a.rpow ha (-1) = (a.inverse ha.isElliptic).castDegree (mul_neg_one m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, ← ContinuousLinearMap.ringInverse_eq_inverse,
      CFC.inverse_eq_rpow_neg_one (isStrictlyPositive_iff.mp ha x ξ hξ)]

/-- Powers of a positive multiple: `(c a) ^ z = c ^ z a ^ z` for `c > 0`. -/
theorem smul_rpow {c : ℝ} (hc : 0 < c) (z : ℝ) :
    (c • a).rpow (ha.smul hc) z = c ^ z • a.rpow ha z :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.smul_rpow hc.le _ z (isStrictlyPositive_iff.mp ha x ξ hξ).nonneg]

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
    simp [hξ, coefficient_normRpow_of_ne_zero, ← ContinuousLinearMap.one_def,
      CFC.smul_rpow (Real.rpow_nonneg (norm_nonneg ξ) m) _ z zero_le_one,
      ← Real.rpow_mul (norm_nonneg ξ)]

end NormRpow

/-- The modulus `|a| = √(a† a)` of an elliptic symbol is the power `(a† a) ^ (1 / 2)` of its Gram
symbol. -/
theorem modulus_eq_rpow [FiniteDimensional ℂ V] {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (a : HomogeneousSymbol X E V W m)
    (ha : a.IsElliptic) :
    a.modulus ha =
      ((a.adjoint.comp a).rpow ha.isStrictlyPositive_adjoint_comp_self (1 / 2)).castDegree
        (by ring) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, ContinuousLinearMap.modulus_eq_sqrt, CFC.sqrt_eq_rpow]

end HomogeneousSymbol

end TauCeti
