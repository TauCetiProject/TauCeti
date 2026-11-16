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

A homogeneous symbol `a` of degree `m` with values in the endomorphisms of a finite-dimensional
complex inner product space `V` is *strictly positive* (`HomogeneousSymbol.IsStrictlyPositive`)
if its value `a (x, ξ)` is a strictly positive operator at every position `x` and every nonzero
frequency `ξ`. The principal symbol of a positive elliptic operator of order `d` is such a symbol
of degree `d` (`TauCeti.ClassicalSymbol.IsElliptic.isStrictlyPositive_principal`); for instance
`1 - Δ` on `ℝⁿ` has principal symbol `‖ξ‖ ^ 2` times the identity.

For every real `s`, the pointwise power

`a ^ s : (x, ξ) ↦ a (x, ξ) ^ s`,

taken in the continuous functional calculus of the strictly positive operator `a (x, ξ)`, is again
a strictly positive homogeneous symbol, of degree `m s` (`HomogeneousSymbol.rpow`). Smoothness
away from the zero frequency comes from the smoothness of real powers on strictly positive
operators in finite dimension (`ContinuousLinearMap.contDiffOn_rpow`), and homogeneity from
`(t ^ m • A) ^ s = t ^ (m s) • A ^ s` for `t ≥ 0` (`CFC.real_smul_rpow`). By Seeley's theorem,
`σ(A) ^ s` is the principal symbol of the power `A ^ s` of a positive elliptic operator `A`; this
file constructs the symbol side. The powers obey the laws of exponents for
`HomogeneousSymbol.comp`: `a ^ 0` is the identity symbol, `a ^ 1 = a`,
`a ^ s ∘ a ^ t = a ^ (s + t)`, `(a ^ s) ^ t = a ^ (s t)`, and `a ^ (-s)` is the inverse symbol
of `a ^ s`. For the scalar symbol `‖ξ‖ ^ m` the power is `‖ξ‖ ^ (m s)`.

## Main declarations

* `TauCeti.HomogeneousSymbol.IsStrictlyPositive`: strict positivity at every nonzero frequency.
  It implies ellipticity (`HomogeneousSymbol.IsStrictlyPositive.isElliptic`) and pointwise
  self-adjointness (`HomogeneousSymbol.IsStrictlyPositive.adjoint_eq`). The identity, the powers
  `‖ξ‖ ^ m` of the frequency norm and the moduli of elliptic symbols are strictly positive.
* `TauCeti.HomogeneousSymbol.rpow`: the power `a ^ s` of a strictly positive symbol `a` of
  degree `m`, a strictly positive homogeneous symbol of degree `m * s`.
* `TauCeti.HomogeneousSymbol.rpow_zero`, `TauCeti.HomogeneousSymbol.rpow_one`,
  `TauCeti.HomogeneousSymbol.rpow_comp_rpow`, `TauCeti.HomogeneousSymbol.rpow_rpow` and
  `TauCeti.HomogeneousSymbol.rpow_neg`: the laws of exponents.
* `TauCeti.HomogeneousSymbol.normRpow_rpow`: `(‖ξ‖ ^ m) ^ s = ‖ξ‖ ^ (m s)`.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §10 (the complex
  powers of an elliptic operator and their principal symbols).
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

open scoped ContDiff NNReal

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℝ}

/-! ### Strictly positive symbols -/

/-- A homogeneous symbol with values in the endomorphisms of a Hilbert space is *strictly
positive* if its value at every position and every nonzero frequency is a strictly positive
operator. -/
def IsStrictlyPositive (a : HomogeneousSymbol X E V V m) : Prop :=
  ∀ x ξ, ξ ≠ 0 → _root_.IsStrictlyPositive (a.coefficient (x, ξ))

/-- Unfolding `HomogeneousSymbol.IsStrictlyPositive`. -/
theorem isStrictlyPositive_iff {a : HomogeneousSymbol X E V V m} :
    a.IsStrictlyPositive ↔ ∀ x ξ, ξ ≠ 0 → _root_.IsStrictlyPositive (a.coefficient (x, ξ)) :=
  Iff.rfl

/-- A strictly positive symbol is elliptic. -/
theorem IsStrictlyPositive.isElliptic {a : HomogeneousSymbol X E V V m}
    (ha : a.IsStrictlyPositive) : a.IsElliptic := isElliptic_iff.mpr fun x ξ hξ ↦
  ContinuousLinearMap.isInvertible_iff_isUnit.mpr (ha x ξ hξ).isUnit

/-- Transporting the degree keeps a symbol strictly positive. -/
theorem IsStrictlyPositive.castDegree {m' : ℝ} (h : m = m') {a : HomogeneousSymbol X E V V m}
    (ha : a.IsStrictlyPositive) : (a.castDegree h).IsStrictlyPositive := by
  simpa [isStrictlyPositive_iff] using ha

/-- Pulling back the position of a strictly positive symbol keeps it strictly positive. -/
theorem IsStrictlyPositive.compPosition {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a : HomogeneousSymbol X E V V m} (ha : a.IsStrictlyPositive) (g : Y → X)
    (hg : ContDiff ℝ ∞ g) : (a.compPosition g hg).IsStrictlyPositive := fun y ξ hξ ↦ by
  simpa using ha (g y) ξ hξ

variable [CompleteSpace V]

/-- A strictly positive symbol is pointwise self-adjoint. -/
theorem IsStrictlyPositive.adjoint_eq {a : HomogeneousSymbol X E V V m}
    (ha : a.IsStrictlyPositive) : a.adjoint = a :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simpa using (ha x ξ hξ).isSelfAdjoint.adjoint_eq

/-- The sum of two strictly positive symbols is strictly positive. -/
theorem IsStrictlyPositive.add {a b : HomogeneousSymbol X E V V m} (ha : a.IsStrictlyPositive)
    (hb : b.IsStrictlyPositive) : (a + b).IsStrictlyPositive := fun x ξ hξ ↦ by
  simpa using _root_.IsStrictlyPositive.add_nonneg (ha x ξ hξ) (hb x ξ hξ).nonneg

/-- A positive multiple of a strictly positive symbol is strictly positive. -/
theorem IsStrictlyPositive.smul {a : HomogeneousSymbol X E V V m} (ha : a.IsStrictlyPositive)
    {c : ℝ} (hc : 0 < c) : (c • a).IsStrictlyPositive := fun x ξ hξ ↦ by
  simpa using (ha x ξ hξ).smul hc

variable (X E V) in
/-- The identity symbol is strictly positive. -/
theorem isStrictlyPositive_id : (id X E V).IsStrictlyPositive := fun x ξ hξ ↦ by
  simp [hξ, ← ContinuousLinearMap.one_def]

/-- The modulus `|a| = √(a† a)` of an elliptic symbol is strictly positive. -/
theorem isStrictlyPositive_modulus [FiniteDimensional ℂ V] {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (a : HomogeneousSymbol X E V W m)
    (ha : a.IsElliptic) : (a.modulus ha).IsStrictlyPositive := fun _ _ hξ ↦
  a.isStrictlyPositive_coefficient_modulus ha hξ

/-! ### Real powers -/

variable [FiniteDimensional ℂ V]

/-- The real power `(x, ξ) ↦ a (x, ξ) ^ s` of a strictly positive symbol is smooth away from the
zero frequency. -/
theorem contDiffOn_rpow_coefficient {a : HomogeneousSymbol X E V V m}
    (ha : a.IsStrictlyPositive) (s : ℝ) :
    ContDiffOn ℝ ∞ (fun p ↦ a.coefficient p ^ s) {p | p.2 ≠ 0} :=
  ((ContinuousLinearMap.contDiffOn_rpow (𝕜 := ℂ) (E := V) s).restrict_scalars ℝ).comp
    a.contDiffOn_coefficient fun p hp ↦ ha p.1 p.2 hp

/-- The real power `a ^ s` of a strictly positive homogeneous symbol `a` of degree `m`: the
homogeneous symbol of degree `m * s` whose value at a nonzero frequency is the power
`a (x, ξ) ^ s` in the continuous functional calculus. -/
noncomputable def rpow (a : HomogeneousSymbol X E V V m) (ha : a.IsStrictlyPositive) (s : ℝ) :
    HomogeneousSymbol X E V V (m * s) :=
  mk' (fun p ↦ a.coefficient p ^ s) (contDiffOn_rpow_coefficient ha s) fun x ξ hξ t ht ↦ by
    rw [a.homogeneous x ξ t ht,
      CFC.real_smul_rpow _ (Real.rpow_nonneg ht.le m) s (ha x ξ hξ).nonneg, ← Real.rpow_mul ht.le]

variable (a : HomogeneousSymbol X E V V m) (ha : a.IsStrictlyPositive)

@[simp]
theorem coefficient_rpow_of_ne_zero (s : ℝ) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.rpow ha s).coefficient (x, ξ) = a.coefficient (x, ξ) ^ s :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

/-- The powers of a strictly positive symbol are strictly positive. -/
theorem isStrictlyPositive_rpow (s : ℝ) : (a.rpow ha s).IsStrictlyPositive := fun x ξ hξ ↦ by
  simpa [hξ] using _root_.IsStrictlyPositive.rpow (a.coefficient (x, ξ)) s (ha x ξ hξ)

/-- The powers of a strictly positive symbol are elliptic. -/
theorem isElliptic_rpow (s : ℝ) : (a.rpow ha s).IsElliptic :=
  (a.isStrictlyPositive_rpow ha s).isElliptic

/-- The powers of a strictly positive symbol are pointwise self-adjoint. -/
@[simp]
theorem adjoint_rpow (s : ℝ) : (a.rpow ha s).adjoint = a.rpow ha s :=
  (a.isStrictlyPositive_rpow ha s).adjoint_eq

/-- The power `a ^ 0` is the identity symbol. -/
@[simp]
theorem rpow_zero : a.rpow ha 0 = (id X E V).castDegree (mul_zero m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_zero _ (ha x ξ hξ).nonneg, ContinuousLinearMap.one_def]

/-- The power `a ^ 1` is `a`. -/
@[simp]
theorem rpow_one : a.rpow ha 1 = a.castDegree (mul_one m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [hξ, CFC.rpow_one _ (ha x ξ hξ).nonneg]

/-- **Addition of exponents**: `a ^ s ∘ a ^ t = a ^ (s + t)`. -/
@[simp]
theorem rpow_comp_rpow (s t : ℝ) :
    (a.rpow ha s).comp (a.rpow ha t) = (a.rpow ha (s + t)).castDegree (mul_add m s t) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_add (ha x ξ hξ).isUnit, ContinuousLinearMap.mul_def]

/-- **Multiplication of exponents**: `(a ^ s) ^ t = a ^ (s t)`. -/
@[simp]
theorem rpow_rpow (s t : ℝ) :
    (a.rpow ha s).rpow (a.isStrictlyPositive_rpow ha s) t =
      (a.rpow ha (s * t)).castDegree (mul_assoc m s t).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.rpow_rpow _ s t (ha x ξ hξ)]

/-- The power `a ^ (-s)` is the inverse symbol of `a ^ s`. -/
theorem rpow_neg (s : ℝ) :
    a.rpow ha (-s) = ((a.rpow ha s).inverse (a.isElliptic_rpow ha s)).castDegree
      (mul_neg m s).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, ← ContinuousLinearMap.ringInverse_eq_inverse, CFC.inverse_rpow _ s (ha x ξ hξ)]

/-- The power `a ^ (-1)` is the inverse symbol of `a`. -/
theorem rpow_neg_one :
    a.rpow ha (-1) = (a.inverse ha.isElliptic).castDegree (mul_neg_one m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, ← ContinuousLinearMap.ringInverse_eq_inverse,
      CFC.inverse_eq_rpow_neg_one (ha x ξ hξ)]

/-- Positive multiples: `(c a) ^ s = c ^ s a ^ s` for `c > 0`. -/
theorem smul_rpow {c : ℝ} (hc : 0 < c) (s : ℝ) :
    (c • a).rpow (ha.smul hc) s = c ^ s • a.rpow ha s :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [hξ, CFC.real_smul_rpow _ hc.le s (ha x ξ hξ).nonneg]

/-- Pulling back the position commutes with taking powers. -/
theorem rpow_compPosition {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : Y → X)
    (hg : ContDiff ℝ ∞ g) (s : ℝ) :
    (a.compPosition g hg).rpow (ha.compPosition g hg) s = (a.rpow ha s).compPosition g hg :=
  ext_of_ne_zero fun y ξ hξ ↦ by simp [hξ]

end HomogeneousSymbol

/-! ### Powers of the frequency norm -/

namespace HomogeneousSymbol

variable (X : Type*) {E : Type*} (V : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

variable (E) in
/-- The symbol `‖ξ‖ ^ m` times the identity is strictly positive. -/
theorem isStrictlyPositive_normRpow (m : ℝ) : (normRpow X E V m).IsStrictlyPositive :=
  fun x ξ hξ ↦ by
    simpa [hξ, ← ContinuousLinearMap.one_def] using
      isStrictlyPositive_one.smul (Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) m)

variable [FiniteDimensional ℂ V]

variable (E) in
/-- The powers of `‖ξ‖ ^ m` are `(‖ξ‖ ^ m) ^ s = ‖ξ‖ ^ (m s)`. -/
@[simp]
theorem normRpow_rpow (m s : ℝ) :
    (normRpow X E V m).rpow (isStrictlyPositive_normRpow X E V m) s = normRpow X E V (m * s) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hξ' : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    simp [hξ, ← ContinuousLinearMap.one_def,
      CFC.real_smul_rpow (1 : V →L[ℂ] V) (Real.rpow_nonneg hξ'.le m) s, ← Real.rpow_mul hξ'.le]

end HomogeneousSymbol

end TauCeti
