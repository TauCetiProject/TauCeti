/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Basic
public import TauCeti.Algebra.Lie.Symplectic.Cartan
public import TauCeti.Algebra.Lie.Symplectic.Diagonal

/-!
# The real symplectic Lie algebra is split

On the symplectic Lie algebra `𝔰𝔭(2n, R)` = `LieAlgebra.Symplectic.sp l R`, with the Cartan
involution `θ X = -Xᵀ` (`LieAlgebra.Symplectic.cartanInvolution`), the diagonal matrices
`𝔞 = {diag(D, -D)}` (`LieAlgebra.Symplectic.diagonalSubalgebra`) form a maximal abelian subspace
of the `-1`-eigenspace `𝔭` (the symmetric matrices). Since `𝔞` is self-normalizing
(`LieAlgebra.Symplectic.diagonalSubalgebra_normalizer_eq_self`):

* the centralizer `𝔤_0` of `𝔞` is `𝔞` itself, and `𝔪 = 𝔤_0 ∩ 𝔨 = 0`;
* so **`𝔰𝔭(2n, ℝ)` is split**, in the sense of
  `LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff`: `𝔞` is a Cartan subalgebra
  (`LieAlgebra.Symplectic.instIsCartanSubalgebraDiagonalSubalgebra`).

These results hold over every commutative ring in which multiplication by `2` is injective, and
`𝔪 = 0` over every commutative ring in which `2` is a unit.

## Main results

* `LieAlgebra.Symplectic.restrictedRootSpace_zero_diagonalSubalgebra`: `𝔤_0 = 𝔞`.
* `LieAlgebra.Symplectic.isMaximalAbelianInP_diagonalSubalgebra`: `𝔞` is maximal abelian in `𝔭`.
* `LieAlgebra.Symplectic.restrictedRootSpace_zero_inf_fixedSubalgebra_diagonalSubalgebra`:
  `𝔪 = 0`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §§5–6.
-/

public section

open LieAlgebra Submodule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebra.Symplectic

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

/-- `𝔞` lies in the `-1`-eigenspace `𝔭` of `θ X = -Xᵀ`: diagonal matrices are symmetric. -/
theorem diagonalSubalgebra_le_cartanP :
    (diagonalSubalgebra l R).toSubmodule ≤ (cartanInvolution l R).cartanP := fun X hX ↦
  LieEquiv.mem_cartanP.mpr ((cartanInvolution_eq_neg_iff X).mpr
    (mem_diagonalSubalgebra.mp hX).isSymm.eq)

/-- **The centralizer `𝔤_0` of `𝔞` in `𝔰𝔭(2n, R)` is `𝔞` itself** once multiplication by `2` is
injective: it lies in the normalizer, which is `𝔞`. -/
theorem restrictedRootSpace_zero_diagonalSubalgebra (h2 : IsRegular (2 : R)) :
    (diagonalSubalgebra l R).toSubmodule.restrictedRootSpace 0 =
      (diagonalSubalgebra l R).toSubmodule := by
  refine le_antisymm (fun X hX ↦ ?_) (Submodule.le_restrictedRootSpace_zero
    fun _ hX _ hY ↦ lie_eq_zero_of_mem_diagonalSubalgebra hX hY)
  rw [mem_restrictedRootSpace_zero] at hX
  rw [LieSubalgebra.mem_toSubmodule, ← diagonalSubalgebra_normalizer_eq_self l R h2,
    LieSubalgebra.mem_normalizer_iff']
  exact fun Y hY ↦ hX ⟨Y, hY⟩ ▸ zero_mem _

/-- **The diagonal matrices are a maximal abelian subspace of `𝔭`** in `𝔰𝔭(2n, R)`, once
multiplication by `2` is injective. -/
theorem isMaximalAbelianInP_diagonalSubalgebra (h2 : IsRegular (2 : R)) :
    (cartanInvolution l R).IsMaximalAbelianInP (diagonalSubalgebra l R).toSubmodule := by
  refine LieEquiv.isMaximalAbelianInP_iff.mpr ⟨⟨diagonalSubalgebra_le_cartanP,
    fun _ hX _ hY ↦ lie_eq_zero_of_mem_diagonalSubalgebra hX hY⟩, fun 𝔟 h𝔟 hle Y hY ↦ ?_⟩
  rw [← restrictedRootSpace_zero_diagonalSubalgebra h2, mem_restrictedRootSpace_zero]
  exact fun H ↦ h𝔟.2 _ (hle H.property) Y hY

/-- **`𝔪 = 0`** for `𝔰𝔭(2n, R)` when `2` is a unit: no nonzero element of the fixed
subalgebra `𝔨` (the skew-symmetric matrices) centralizes `𝔞`. By
`LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff` this is the statement that `𝔰𝔭(2n, ℝ)` is
split. -/
theorem restrictedRootSpace_zero_inf_fixedSubalgebra_diagonalSubalgebra (h2 : IsUnit (2 : R)) :
    (diagonalSubalgebra l R).toSubmodule.restrictedRootSpace 0 ⊓
      (cartanInvolution l R).toLieHom.fixedSubalgebra.toSubmodule = ⊥ := by
  rw [restrictedRootSpace_zero_diagonalSubalgebra h2.isRegular, ← disjoint_iff]
  exact ((cartanInvolution l R).isCompl_fixedSubalgebra_cartanP h2
    cartanInvolution_cartanInvolution).disjoint.symm.mono_left
      diagonalSubalgebra_le_cartanP

end LieAlgebra.Symplectic
