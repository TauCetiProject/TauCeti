/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.Normed.Operator.SNumbers.Hilbert

/-!
# Additive and multiplicative s-number families

Additivity and multiplicativity are mixed-index inequalities, stronger than the perturbation
and ideal axioms of an s-number sequence. They are independent properties of a family: the
approximation numbers have both, while the Hilbert numbers are additive.

`TauCeti.SNumbers.IsAdditive` and `TauCeti.SNumbers.IsMultiplicative` do not assume the
s-number axioms. Their zero-index specializations give the perturbation and two-sided ideal
bounds whenever the zeroth terms are bounded by the operator norms. In particular these
predicates can also be used for families that fail the rank or normalization axioms.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), Theorem 9.5.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped NNReal

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- An additive family satisfies the mixed-index triangle inequality. This does not require
that the family satisfy the s-number axioms. -/
structure IsAdditive (s : SNumberFamily 𝕜) : Prop where
  /-- The term at the sum of the indices is bounded by the sum of the respective terms. -/
  add_index_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (m n : ℕ),
    s (S + T) (m + n) ≤ s S m + s T n

/-- A multiplicative family satisfies the mixed-index composition inequality. This does not
require that the family satisfy the s-number axioms. -/
structure IsMultiplicative (s : SNumberFamily 𝕜) : Prop where
  /-- The term of a composition at the sum of the indices is bounded by the product. -/
  comp_add_le_mul : ∀ {X Y Z : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (m n : ℕ),
    s (S ∘L T) (m + n) ≤ s S m * s T n

variable {s : SNumberFamily 𝕜} {W X Y Z : Type u}
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Additivity implies the perturbation bound when the perturbing map has zeroth term at
most its operator norm. -/
theorem IsAdditive.add_le (hs : IsAdditive s) (S T : X →L[𝕜] Y)
    (hT : s T 0 ≤ ‖T‖₊) (n : ℕ) : s (S + T) n ≤ s S n + ‖T‖₊ := by
  simpa using (hs.add_index_le S T n 0).trans (add_le_add le_rfl hT)

/-- Multiplicativity implies the postcomposition bound when the outer map has zeroth term
at most its operator norm. -/
theorem IsMultiplicative.comp_le_left (hs : IsMultiplicative s)
    (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (hB : s B 0 ≤ ‖B‖₊) (n : ℕ) :
    s (B ∘L T) n ≤ ‖B‖₊ * s T n := by
  simpa using (hs.comp_add_le_mul B T 0 n).trans (mul_le_mul_left hB _)

/-- Multiplicativity implies the precomposition bound when the inner map has zeroth term
at most its operator norm. -/
theorem IsMultiplicative.comp_le_right (hs : IsMultiplicative s)
    (T : X →L[𝕜] Y) (A : W →L[𝕜] X) (hA : s A 0 ≤ ‖A‖₊) (n : ℕ) :
    s (T ∘L A) n ≤ s T n * ‖A‖₊ := by
  simpa using (hs.comp_add_le_mul T A n 0).trans (mul_le_mul_right hA _)

/-- Multiplicativity implies the two-sided ideal bound when the outer maps have zeroth
terms at most their operator norms. -/
theorem IsMultiplicative.comp_comp_le (hs : IsMultiplicative s)
    (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (A : W →L[𝕜] X)
    (hB : s B 0 ≤ ‖B‖₊) (hA : s A 0 ≤ ‖A‖₊) (n : ℕ) :
    s (B ∘L T ∘L A) n ≤ ‖B‖₊ * s T n * ‖A‖₊ := by
  calc
    s (B ∘L T ∘L A) n ≤ ‖B‖₊ * s (T ∘L A) n := hs.comp_le_left B _ hB n
    _ ≤ ‖B‖₊ * (s T n * ‖A‖₊) := mul_le_mul_right (hs.comp_le_right T A hA n) _
    _ = ‖B‖₊ * s T n * ‖A‖₊ := (mul_assoc _ _ _).symm

/-- Approximation numbers form an additive family. -/
theorem isAdditive_approximation : IsAdditive (approximation (𝕜 := 𝕜)) where
  add_index_le S T m n := by simpa using S.singularValue_add_index_le T m n

/-- Approximation numbers form a multiplicative family. -/
theorem isMultiplicative_approximation : IsMultiplicative (approximation (𝕜 := 𝕜)) where
  comp_add_le_mul S T m n := by simpa using S.singularValue_comp_add_le_mul T m n

end TauCeti.SNumbers

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Hilbert numbers form an additive family. -/
theorem isAdditive_hilbert : IsAdditive (hilbert (𝕜 := 𝕜)) where
  add_index_le S T m n := by simpa using S.hilbertNumber_add_index_le T m n

end TauCeti.SNumbers
