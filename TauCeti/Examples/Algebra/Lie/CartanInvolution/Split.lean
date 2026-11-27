/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Split
public import TauCeti.Algebra.Lie.Orthogonal.Split
public import TauCeti.Algebra.Lie.SpecialLinear.RestrictedRoot.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.RestrictedRoot.Complex.Basic

/-!
# Checks: the diagonal of `𝔰𝔩_n(ℝ)` is a Cartan subalgebra and the real diagonal of `𝔰𝔩_n(ℂ)` is not

Checks of the criterion `LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff`: a maximal abelian
subspace `𝔞` of `𝔭` is a Cartan subalgebra exactly when `𝔪 = 0`.

* On `𝔰𝔩_{r+1}(ℝ)` with `θ X = -Xᵀ`, the trace-zero diagonal matrices have `𝔪 = 0`, so they form
  a Cartan subalgebra: `𝔰𝔩_n(ℝ)` is split.
* On `𝔰𝔩_n(ℂ)` viewed as real, with `θ X = -Xᴴ`, the real trace-zero diagonal matrices `𝔞` have
  `𝔪 = i𝔞`, which is nonzero once `n` has two elements, so `𝔞` is not a Cartan subalgebra.
* `𝔰𝔬(2, 3)` is split: the span `𝔞` of `H_1 = E_(1, 1') + E_(1', 1)` and `H_2` is a Cartan
  subalgebra, so `𝔪 = 𝔰𝔬(1) = 0`. `𝔰𝔬(2, 4)` is not: the span of `H_1`, `H_2` is maximal abelian
  in `𝔭`, but `𝔪` contains the block `𝔰𝔬(2)` on the two remaining indices, so it is not a Cartan
  subalgebra. A test of `𝔨 = 0` in place of `𝔪 = 0` would call neither split.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.Examples.RestrictedRootSplit

/-- `𝔰𝔩_{r+1}(ℝ)` is split: its trace-zero diagonal matrices, maximal abelian in `𝔭` for
`θ X = -Xᵀ`, form a Cartan subalgebra, since `𝔪 = 0`. -/
example (r : ℕ) :
    (specialLinearDiagonalCartan r ℝ).IsCartanSubalgebra :=
  (LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff
    (isCartanInvolution_specialLinearNegTranspose r)
    (by rw [specialLinearDiagonalCartan_toSubmodule]
        exact isMaximalAbelianInP_specialLinearDiagonal)).mpr
    (by rw [specialLinearDiagonalCartan_toSubmodule]
        exact restrictedRootSpace_zero_inf_fixedSubalgebra_specialLinearDiagonal)

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The real trace-zero diagonal matrices of `𝔰𝔩_n(ℂ)` viewed as real, maximal abelian in `𝔭` for
`θ X = -Xᴴ`, are not a Cartan subalgebra once there are `i ≠ j`, since `𝔪 = i𝔞` contains
`i (E_ii - E_jj) ≠ 0`. (That `𝔰𝔩_n(ℂ)` viewed as real is not split follows only together with the
conjugacy of maximal abelian subspaces of `𝔭`, which is not formalised here.) -/
theorem not_isCartanSubalgebra_slComplexRealDiagonalSubalgebra {i j : n} (hij : i ≠ j) :
    ¬(slComplexRealDiagonalSubalgebra n).IsCartanSubalgebra := by
  rw [LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff
    (isCartanInvolution_slComplexNegConjTranspose (n := n))
    (by rw [slComplexRealDiagonalSubalgebra_toSubmodule]
        exact isMaximalAbelianInP_slComplexRealDiagonal)]
  rw [slComplexRealDiagonalSubalgebra_toSubmodule]
  intro h
  set H := slComplexRealDiagonalSingleSubSingle n i j
  let X : slComplexReal n := ⟨Complex.I • (((H : slComplexReal n)) : Matrix n n ℂ),
    mem_slComplexReal_iff.mpr (by
      rw [trace_smul, mem_slComplexReal_iff.mp (H : slComplexReal n).property, smul_zero])⟩
  have hX : X ∈ (slComplexRealDiagonal n).restrictedRootSpace 0 ⊓
      (slComplexNegConjTranspose n).toLieHom.fixedSubalgebra.toSubmodule :=
    mem_restrictedRootSpace_zero_inf_fixedSubalgebra_slComplexRealDiagonal_iff.mpr
      ⟨H, H.property, rfl⟩
  have h0 : X = 0 := by
    have := h ▸ hX
    simpa using this
  have hii := congrFun (congrFun (congrArg Subtype.val h0) i) i
  simp [X, H, hij.symm] at hii

/-- `𝔰𝔬(2, 3)` is split: for the inclusion `e : Fin 2 → Fin 3`, the span of the
`H_i = E_(i, e i) + E_(e i, i)` is a Cartan subalgebra. -/
example :
    (Orthogonal.splitCartanSubalgebra (Fin.castSucc : Fin 2 → Fin 3)).IsCartanSubalgebra :=
  Orthogonal.isCartanSubalgebra_splitCartanSubalgebra_castSucc (by norm_num)

/-- `𝔰𝔬(2, 3)` has `𝔪 = 0` for this `𝔞`. -/
example :
    (Orthogonal.splitCartanSubmodule (Fin.castSucc : Fin 2 → Fin 3)).restrictedRootSpace 0 ⊓
      ((Orthogonal.so' (Fin 2) (Fin 3) ℝ).restrictNegConjTranspose
        fun _ ↦ Orthogonal.conjTranspose_mem_so').toLieHom.fixedSubalgebra.toSubmodule = ⊥ :=
  (Orthogonal.restrictedRootSpace_zero_inf_fixedSubalgebra_splitCartanSubmodule_eq_bot_iff
    (Fin.castSucc_injective 2)).mpr <|
      (Orthogonal.isCartanSubalgebra_splitCartanSubalgebra_iff (by simp)
        (Fin.castSucc_injective 2)).mp <|
        Orthogonal.isCartanSubalgebra_splitCartanSubalgebra_castSucc (by norm_num)

/-- The inclusion `Fin 2 → Fin 4`, whose range misses `2` and `3`. -/
abbrev soTwoFourEmbedding : Fin 2 → Fin 4 := Fin.castLE (by norm_num)

/-- `𝔰𝔬(2, 4)` with `𝔞` the span of `H_1`, `H_2`: `𝔞` is maximal abelian in `𝔭`. -/
example : ((Orthogonal.so' (Fin 2) (Fin 4) ℝ).restrictNegConjTranspose
      fun _ ↦ Orthogonal.conjTranspose_mem_so').IsMaximalAbelianInP
      (Orthogonal.splitCartanSubmodule soTwoFourEmbedding) :=
  Orthogonal.isMaximalAbelianInP_splitCartanSubmodule (Fin.castLE_injective _)

/-- `𝔰𝔬(2, 4)` with `𝔞` the span of `H_1`, `H_2`: `𝔪 ≠ 0`, since `E_(2, 3) - E_(3, 2)` in the
second block lies in it. -/
example :
    (Orthogonal.splitCartanSubmodule soTwoFourEmbedding).restrictedRootSpace 0 ⊓
      ((Orthogonal.so' (Fin 2) (Fin 4) ℝ).restrictNegConjTranspose
        fun _ ↦ Orthogonal.conjTranspose_mem_so').toLieHom.fixedSubalgebra.toSubmodule ≠ ⊥ :=
  Submodule.ne_bot_iff _ |>.mpr ⟨_,
    Orthogonal.splitCompactElement_mem_restrictedRootSpace_zero_inf_fixedSubalgebra
      (a := 2) (b := 3) (by simp) (by simp),
    Orthogonal.splitCompactElement_ne_zero (by decide)⟩

/-- `𝔰𝔬(2, 4)` with `𝔞` the span of `H_1`, `H_2`: `𝔞` is not a Cartan subalgebra. -/
example :
    ¬(Orthogonal.splitCartanSubalgebra soTwoFourEmbedding).IsCartanSubalgebra := by
  rw [Orthogonal.isCartanSubalgebra_splitCartanSubalgebra_iff (by simp)
    (Fin.castLE_injective _)]
  intro h
  exact absurd (h (show (2 : Fin 4) ∈ _ by simp) (show (3 : Fin 4) ∈ _ by simp)) (by decide)

end TauCeti.Examples.RestrictedRootSplit
