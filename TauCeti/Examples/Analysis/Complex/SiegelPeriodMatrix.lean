/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.SiegelPeriodMatrix

/-!
# Checks: period equivariance for translations

For a symmetric integral `B`, the translation `T = [[1, B], [0, 1]]` sends `Ω` to `Ω + B` with
fibre map `R_T(Ω) = 1`, and its lattice action is `ρ(T) = T⁻ᵀ = [[1, 0], [-Bᵀ, 1]]`. Period
equivariance then says `Ω a + b = (Ω + B) a + (b - Bᵀ a)`, which uses `Bᵀ = B`: the transpose in
`ρ(T) = T⁻ᵀ` is what makes the law hold.
-/

public section

open Matrix

namespace TauCeti.Examples.SiegelPeriodMatrix

variable {g : ℕ}

/-- The lattice action of a translation is `[[1, 0], [-Bᵀ, 1]]`. -/
example (B : Matrix (Fin g) (Fin g) ℤ) :
    siegelLatticeMap (fromBlocks 1 B 0 1) = fromBlocks 1 0 (-Bᵀ) 1 := by
  simp

/-- The fibre map of a translation is the identity. -/
example (B : Matrix (Fin g) (Fin g) ℤ) (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelFiberMap (fromBlocks 1 B 0 1) Ω = 1 := by
  simp

/-- Period equivariance for a translation by a symmetric `B`, in coordinates:
`Π_Ω(a, b) = Π_{Ω + B}(a, b - Bᵀ a)`. -/
example (B : Matrix (Fin g) (Fin g) ℤ) (hB : Bᵀ = B) (Ω : Matrix (Fin g) (Fin g) ℂ)
    (a b : Fin g → ℂ) :
    siegelPeriodMatrix Ω *ᵥ Sum.elim a b =
      siegelPeriodMatrix (Ω + B.map ((↑) : ℤ → ℂ)) *ᵥ
        Sum.elim a (b - (Bᵀ.map ((↑) : ℤ → ℂ)) *ᵥ a) := by
  rw [siegelPeriodMatrix_mulVec_sumElim, siegelPeriodMatrix_mulVec_sumElim, hB, add_mulVec]
  abel

end TauCeti.Examples.SiegelPeriodMatrix
