/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.CartanInvolution.RealRank
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.Orthogonal.Cartan

/-!
# Real rank zero: `𝔤𝔩_n(ℝ)` and `𝔰𝔬(n)`

* `𝔤𝔩_n(ℝ)` for `n ≥ 1` has real rank `0` because it is not semisimple
  (`TauCeti.not_hasTrivialRadical_matrix`), so it has no Cartan involution.
* `𝔰𝔬(n)` for `n ≥ 3`, for instance `𝔰𝔬(3)`, has negative definite Killing form
  (`LieAlgebra.Orthogonal.killingForm_so_self_neg`), so it has real rank `0`.
-/

public section

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- `𝔤𝔩_n(ℝ)`, `n ≥ 1`, has real rank `0`, since it is not semisimple. -/
theorem realRank_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    realRank (Matrix n n ℝ) = 0 :=
  realRank_eq_zero_of_not_isSemisimple fun _ ↦ not_hasTrivialRadical_matrix ℝ n inferInstance

/-- `𝔰𝔬(n)`, `n ≥ 3`, has real rank `0`. -/
theorem realRank_so {l : Type*} [Fintype l] [DecidableEq l] (hl : 3 ≤ Fintype.card l) :
    realRank (Orthogonal.so l ℝ) = 0 :=
  realRank_eq_zero_of_killingForm_neg (Orthogonal.killingForm_so_self_neg hl)

/-- The compact Lie algebra `𝔰𝔬(3)` has real rank `0`. -/
example : realRank (Orthogonal.so (Fin 3) ℝ) = 0 :=
  realRank_so (by simp)

end TauCeti
