/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
public import TauCeti.Algebra.Lie.Subalgebra.RestrictScalars
public import TauCeti.Algebra.Lie.Symplectic.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Radical
import TauCeti.Algebra.Lie.Orthogonal.Killing
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# Cartan involutions of complex matrix Lie algebras viewed as real

Let `𝔩` be a complex Lie subalgebra of `𝔤𝔩_n(ℂ)`, closed under conjugate transpose and with trivial
centre. Viewed as a real Lie algebra (the range of `LieSubalgebra.restrictScalarsIncl ℝ`), its
centre is still trivial, because the real and complex brackets agree. So the matrix Cartan
criterion `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_iff` makes `θ X = -Xᴴ` a
Cartan involution of `𝔩` as a real Lie algebra (Knapp, Prop. 6.28).

This applies to the complex classical Lie algebras `𝔰𝔩_n(ℂ)`, `𝔰𝔬_n(ℂ)` (for `n ≥ 3`) and
`𝔰𝔭_{2n}(ℂ)`. Here the fixed algebra of `θ` is the compact real form of skew-Hermitian matrices
in `𝔩`, and `𝔭` consists of the Hermitian ones.

## Main definitions

* `TauCeti.slComplexReal`: `𝔰𝔩_n(ℂ)` viewed as a real Lie subalgebra of `𝔤𝔩_n(ℂ)`.
* `TauCeti.slComplexNegConjTranspose`: its Cartan involution `X ↦ -Xᴴ`.

## Main results

* `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl`: for a
  complex Lie subalgebra of `𝔤𝔩_n(ℂ)` with trivial centre closed under conjugate transpose,
  `X ↦ -Xᴴ` is a Cartan involution of the underlying real Lie algebra.
* `TauCeti.isCartanInvolution_restrictNegConjTranspose_slComplex`,
  `TauCeti.isCartanInvolution_restrictNegConjTranspose_soComplex` and
  `TauCeti.isCartanInvolution_restrictNegConjTranspose_spComplex`: the cases `𝔰𝔩_n(ℂ)`,
  `𝔰𝔬_n(ℂ)` and `𝔰𝔭_{2n}(ℂ)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2, Proposition 6.28.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n] (K : LieSubalgebra ℂ (Matrix n n ℂ))

/-- Closure of a complex Lie subalgebra under conjugate transpose passes to its underlying real
Lie algebra. -/
theorem conjTranspose_mem_range_restrictScalarsIncl (hK : ∀ X ∈ K, Xᴴ ∈ K) :
    ∀ X ∈ (K.restrictScalarsIncl ℝ).range, Xᴴ ∈ (K.restrictScalarsIncl ℝ).range := by
  intro X hX
  rw [mem_range_restrictScalarsIncl] at hX ⊢
  exact hK X hX

/-- **Knapp, Prop. 6.28, for complex Lie algebras viewed as real.** For a complex Lie subalgebra
`𝔩` of `𝔤𝔩_n(ℂ)` with trivial centre (for instance a semisimple one), closed under conjugate
transpose, `X ↦ -Xᴴ` is a Cartan involution of `𝔩` viewed as a real Lie algebra. -/
theorem isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl
    (hc : center ℂ K = ⊥) (hK : ∀ X ∈ K, Xᴴ ∈ K) :
    ((K.restrictScalarsIncl ℝ).range.restrictNegConjTranspose
      (K.conjTranspose_mem_range_restrictScalarsIncl hK)).IsCartanInvolution :=
  (isCartanInvolution_restrictNegConjTranspose_iff _ _).mpr
    (K.center_range_restrictScalarsIncl_eq_bot ℝ hc)

end LieSubalgebra

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

variable (n) in
/-- `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra, as a real Lie subalgebra of `𝔤𝔩_n(ℂ)`. -/
noncomputable abbrev slComplexReal : LieSubalgebra ℝ (Matrix n n ℂ) :=
  ((SpecialLinear.sl n ℂ).restrictScalarsIncl ℝ).range

/-- A complex matrix lies in `𝔰𝔩_n(ℂ)` viewed as real exactly when its trace vanishes. -/
theorem mem_slComplexReal_iff {A : Matrix n n ℂ} : A ∈ slComplexReal n ↔ A.trace = 0 :=
  (LieSubalgebra.mem_range_restrictScalarsIncl _ _ _).trans SpecialLinear.mem_sl_iff

variable (n) in
/-- The Cartan involution `X ↦ -Xᴴ` of `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra
(`TauCeti.isCartanInvolution_restrictNegConjTranspose_slComplex`). -/
noncomputable abbrev slComplexNegConjTranspose : slComplexReal n ≃ₗ⁅ℝ⁆ slComplexReal n :=
  (slComplexReal n).restrictNegConjTranspose
    ((SpecialLinear.sl n ℂ).conjTranspose_mem_range_restrictScalarsIncl
      fun _ ↦ SpecialLinear.conjTranspose_mem_sl)

/-- **`X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra.** -/
theorem isCartanInvolution_restrictNegConjTranspose_slComplex :
    (slComplexNegConjTranspose n).IsCartanInvolution :=
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl _
    (center_eq_bot ℂ _) fun _ ↦ SpecialLinear.conjTranspose_mem_sl

/-- **`X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔬_n(ℂ)` viewed as a real Lie algebra**, for
`n ≥ 3`. -/
theorem isCartanInvolution_restrictNegConjTranspose_soComplex (hn : 3 ≤ Fintype.card n) :
    (((Orthogonal.so n ℂ).restrictScalarsIncl ℝ).range.restrictNegConjTranspose
      ((Orthogonal.so n ℂ).conjTranspose_mem_range_restrictScalarsIncl
        fun _ ↦ Orthogonal.conjTranspose_mem_so)).IsCartanInvolution :=
  have := hasTrivialRadical_so ℂ hn
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl _
    (center_eq_bot ℂ _) fun _ ↦ Orthogonal.conjTranspose_mem_so

/-- **`X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔭_{2n}(ℂ)` viewed as a real Lie algebra.** -/
theorem isCartanInvolution_restrictNegConjTranspose_spComplex :
    (((Symplectic.sp n ℂ).restrictScalarsIncl ℝ).range.restrictNegConjTranspose
      ((Symplectic.sp n ℂ).conjTranspose_mem_range_restrictScalarsIncl
        fun _ ↦ Symplectic.conjTranspose_mem_sp)).IsCartanInvolution :=
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl _
    (center_eq_bot ℂ _) fun _ ↦ Symplectic.conjTranspose_mem_sp

end TauCeti
