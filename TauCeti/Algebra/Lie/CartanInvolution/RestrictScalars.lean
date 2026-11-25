/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
public import TauCeti.Algebra.Lie.Subalgebra.RestrictScalars
public import TauCeti.Algebra.Lie.Symplectic.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Radical
import TauCeti.Algebra.Lie.Orthogonal.Killing
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# Cartan involutions of complex matrix Lie algebras viewed as real

Let `𝔩` be a complex Lie subalgebra of `𝔤𝔩_n(ℂ)`, closed under conjugate transpose and with trivial
radical. Viewed as a real Lie algebra (the range of `LieSubalgebra.restrictScalarsIncl ℝ`), its
centre is still trivial, because the real and complex brackets agree. So the matrix Cartan
criterion `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_iff` makes `θ X = -Xᴴ` a
Cartan involution of `𝔩` as a real Lie algebra (Knapp, Prop. 6.28).

This applies to the complex classical Lie algebras `𝔰𝔩_n(ℂ)`, `𝔰𝔬_n(ℂ)` (for `n ≥ 3`) and
`𝔰𝔭_{2n}(ℂ)`. Here the fixed algebra of `θ` is the compact real form of skew-Hermitian matrices
in `𝔩`, and `𝔭` consists of the Hermitian ones.

## Main results

* `LieSubalgebra.center_range_restrictScalarsIncl_eq_bot`: a Lie subalgebra with trivial centre
  still has trivial centre after restricting scalars, for instance from `ℂ` to `ℝ`.
* `LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl`: for a
  complex Lie subalgebra of `𝔤𝔩_n(ℂ)` with trivial radical closed under conjugate transpose,
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

section Center

variable {A L : Type*} [CommRing A] [LieRing L] [LieAlgebra A L]
  (K : LieSubalgebra A L) (R : Type*) [CommRing R] [Algebra R A]
  [LieAlgebra R L] [IsScalarTower R A L]

/-- A Lie subalgebra with trivial centre over `A` still has trivial centre over a smaller scalar
ring `R`: the brackets over `R` and over `A` agree. -/
theorem center_range_restrictScalarsIncl_eq_bot (hK : center A K = ⊥) :
    center R (K.restrictScalarsIncl R).range = ⊥ := by
  refine (LieSubmodule.eq_bot_iff _).mpr fun ⟨Z, hZ⟩ hZc ↦ Subtype.ext ?_
  rw [LieModule.mem_maxTrivSubmodule] at hZc
  have hZK : Z ∈ K := (mem_range_restrictScalarsIncl K R Z).mp hZ
  have hcK : (⟨Z, hZK⟩ : K) ∈ center A K := by
    rw [LieModule.mem_maxTrivSubmodule]
    rintro ⟨X, hX⟩
    have := congrArg Subtype.val
      (hZc ⟨X, (mem_range_restrictScalarsIncl K R X).mpr hX⟩)
    exact Subtype.ext this
  rw [hK, LieSubmodule.mem_bot] at hcK
  simpa using congrArg Subtype.val hcK

end Center

variable {n : Type*} [Fintype n] [DecidableEq n] (K : LieSubalgebra ℂ (Matrix n n ℂ))

/-- Closure of a complex Lie subalgebra under conjugate transpose passes to its underlying real
Lie algebra. -/
theorem conjTranspose_mem_range_restrictScalarsIncl (hK : ∀ X ∈ K, Xᴴ ∈ K) :
    ∀ X ∈ (K.restrictScalarsIncl ℝ).range, Xᴴ ∈ (K.restrictScalarsIncl ℝ).range := by
  intro X hX
  rw [mem_range_restrictScalarsIncl] at hX ⊢
  exact hK X hX

/-- **Knapp, Prop. 6.28, for complex Lie algebras viewed as real.** For a complex Lie subalgebra
`𝔩` of `𝔤𝔩_n(ℂ)` with trivial radical (for instance a semisimple one), closed under conjugate
transpose, `X ↦ -Xᴴ` is a Cartan involution of `𝔩` viewed as a real Lie algebra. -/
theorem isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl
    [HasTrivialRadical ℂ K] (hK : ∀ X ∈ K, Xᴴ ∈ K) :
    ((K.restrictScalarsIncl ℝ).range.restrictNegConjTranspose
      (K.conjTranspose_mem_range_restrictScalarsIncl hK)).IsCartanInvolution :=
  (isCartanInvolution_restrictNegConjTranspose_iff _ _).mpr
    (K.center_range_restrictScalarsIncl_eq_bot ℝ (center_eq_bot ℂ K))

end LieSubalgebra

namespace LieAlgebra.Orthogonal

/-- **Conjugate transpose preserves the orthogonal Lie algebra** of skew-symmetric matrices, over
any commutative star ring. -/
theorem conjTranspose_mem_so {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]
    {X : Matrix n n R} (hX : X ∈ so n R) : Xᴴ ∈ so n R := by
  rw [mem_so] at hX ⊢
  have h : Xᴴ = -X.map star := by
    rw [conjTranspose, hX, Matrix.map_neg _ star_neg]
  rw [h, transpose_neg, ← transpose_map, hX, Matrix.map_neg _ star_neg, neg_neg]

end LieAlgebra.Orthogonal

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra.** -/
theorem isCartanInvolution_restrictNegConjTranspose_slComplex :
    (((SpecialLinear.sl n ℂ).restrictScalarsIncl ℝ).range.restrictNegConjTranspose
      ((SpecialLinear.sl n ℂ).conjTranspose_mem_range_restrictScalarsIncl
        fun _ ↦ SpecialLinear.conjTranspose_mem_sl)).IsCartanInvolution :=
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl _
    fun _ ↦ SpecialLinear.conjTranspose_mem_sl

/-- **`X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔬_n(ℂ)` viewed as a real Lie algebra**, for
`n ≥ 3`. -/
theorem isCartanInvolution_restrictNegConjTranspose_soComplex (hn : 3 ≤ Fintype.card n) :
    (((Orthogonal.so n ℂ).restrictScalarsIncl ℝ).range.restrictNegConjTranspose
      ((Orthogonal.so n ℂ).conjTranspose_mem_range_restrictScalarsIncl
        fun _ ↦ Orthogonal.conjTranspose_mem_so)).IsCartanInvolution :=
  have := hasTrivialRadical_so ℂ hn
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl _
    fun _ ↦ Orthogonal.conjTranspose_mem_so

/-- **`X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔭_{2n}(ℂ)` viewed as a real Lie algebra.** -/
theorem isCartanInvolution_restrictNegConjTranspose_spComplex :
    (((Symplectic.sp n ℂ).restrictScalarsIncl ℝ).range.restrictNegConjTranspose
      ((Symplectic.sp n ℂ).conjTranspose_mem_range_restrictScalarsIncl
        fun _ ↦ Symplectic.conjTranspose_mem_sp)).IsCartanInvolution :=
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose_range_restrictScalarsIncl _
    fun _ ↦ Symplectic.conjTranspose_mem_sp

end TauCeti
