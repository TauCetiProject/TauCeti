/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.CartanInvolution.RealRank
import TauCeti.Algebra.Lie.CartanInvolution.Matrix
import TauCeti.Algebra.Lie.Orthogonal.Basic
import TauCeti.Algebra.Lie.Orthogonal.Killing

/-!
# Real rank zero: `𝔤𝔩_n(ℝ)` and `𝔰𝔬(n)`

* `𝔤𝔩_n(ℝ)` for `n ≥ 1` has real rank `0` because it has no Cartan involution: `ad 1 = 0`, so the
  Killing form pairs `1` with everything to `0`, while a Cartan involution `θ` needs
  `B(1, θ 1) < 0`.
* `𝔰𝔬(n)` for `n ≥ 3`, for instance `𝔰𝔬(3)`, has negative definite Killing form, so it has real
  rank `0`: by the matrix Cartan criterion `X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔬(n)`, and it is
  the identity there.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- `𝔤𝔩_n(ℝ)`, `n ≥ 1`, has no Cartan involution: `ad 1 = 0`. -/
theorem not_isCartanInvolution_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (θ : Matrix n n ℝ ≃ₗ⁅ℝ⁆ Matrix n n ℝ) : ¬ θ.IsCartanInvolution := fun hθ ↦ by
  have had : ad ℝ (Matrix n n ℝ) 1 = 0 := LinearMap.ext fun Y ↦ by simp [Ring.lie_def]
  have := hθ.killingForm_apply_apply_neg (x := 1) one_ne_zero
  rw [killingForm_apply_apply, had, LinearMap.zero_comp, map_zero] at this
  exact this.false

/-- `𝔤𝔩_n(ℝ)`, `n ≥ 1`, has real rank `0`, since it has no Cartan involution. -/
theorem realRank_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    realRank (Matrix n n ℝ) = 0 :=
  realRank_eq_zero_of_forall_not_isCartanInvolution not_isCartanInvolution_matrix

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- The Killing form of `𝔰𝔬(n)`, `n ≥ 3`, is negative definite: `X ↦ -Xᵀ` is a Cartan involution
of `𝔰𝔬(n)` (Knapp, Prop. 6.28) fixing every `X`, since `Xᵀ = -X`. -/
theorem killingForm_so_neg (hl : 3 ≤ Fintype.card l) (X : Orthogonal.so l ℝ) (hX : X ≠ 0) :
    killingForm ℝ (Orthogonal.so l ℝ) X X < 0 := by
  have := hasTrivialRadical_so ℝ hl
  have hθ := (Orthogonal.so l ℝ).isCartanInvolution_restrictNegConjTranspose
    fun _ ↦ Orthogonal.conjTranspose_mem_so
  refine hθ.killingForm_apply_self_neg_of_mem_fixedSubalgebra ?_ hX
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom]
  refine Subtype.ext ?_
  rw [LieSubalgebra.coe_restrictNegConjTranspose_apply, conjTranspose_eq_transpose_of_trivial,
    (Orthogonal.mem_so _ _ _).mp X.property, neg_neg]

/-- `𝔰𝔬(n)`, `n ≥ 3`, has real rank `0`. -/
theorem realRank_so (hl : 3 ≤ Fintype.card l) : realRank (Orthogonal.so l ℝ) = 0 :=
  realRank_eq_zero_of_killingForm_neg (killingForm_so_neg hl)

/-- The compact Lie algebra `𝔰𝔬(3)` has real rank `0`. -/
example : realRank (Orthogonal.so (Fin 3) ℝ) = 0 :=
  realRank_so (by simp)

end TauCeti
