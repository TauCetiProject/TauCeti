/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.Pseudodifferential.Elliptic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.InnerProductSpace.Modulus

/-!
# Strictly positive homogeneous symbols

A homogeneous symbol `a` of degree `m` with values in the endomorphisms of a complex Hilbert
space `V` is *strictly positive* (`TauCeti.HomogeneousSymbol.IsStrictlyPositive`) when its value
`a (x, ξ)` is a strictly positive operator at every position `x` and every nonzero frequency `ξ`.
This is the principal symbol of a positive elliptic operator, such as `‖ξ‖ ^ 2` times the identity
for the Laplacian `1 + ∇*∇` of a metric connection, or `a† a` for an elliptic `a`.

* `HomogeneousSymbol.IsStrictlyPositive.isElliptic`,
  `HomogeneousSymbol.IsStrictlyPositive.adjoint_eq`: a strictly positive symbol is elliptic and
  pointwise self-adjoint.
* `HomogeneousSymbol.isStrictlyPositive_id`, `HomogeneousSymbol.isStrictlyPositive_normRpow`,
  `HomogeneousSymbol.IsElliptic.isStrictlyPositive_adjoint_comp_self`: the identity, `‖ξ‖ ^ m`
  and the Gram symbol `a† a` of an elliptic `a` are strictly positive.
* `HomogeneousSymbol.IsStrictlyPositive.add`, `HomogeneousSymbol.IsStrictlyPositive.smul`,
  `HomogeneousSymbol.IsStrictlyPositive.lineMap`: strict positivity is preserved by sums,
  positive multiples and straight lines between two strictly positive symbols.

The real powers of strictly positive symbols are in
`TauCeti.Analysis.Pseudodifferential.Rpow`.

## References

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
theorem IsElliptic.isStrictlyPositive_adjoint_comp_self {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {a : HomogeneousSymbol X E V W m}
    (ha : a.IsElliptic) : (a.adjoint.comp a).IsStrictlyPositive :=
  fun x ξ hξ ↦ by
    simpa using ContinuousLinearMap.isStrictlyPositive_adjoint_comp_self_of_isInvertible
      (isElliptic_iff.mp ha x ξ hξ)

end HomogeneousSymbol

end TauCeti
