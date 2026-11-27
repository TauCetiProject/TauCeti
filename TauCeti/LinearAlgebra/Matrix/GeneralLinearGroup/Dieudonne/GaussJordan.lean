/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability.Surjective

/-!
# Diagonal factorization and normality of the elementary subgroup over a division ring

Over a division ring `D`, every invertible matrix factors as an elementary matrix times an
invertible diagonal matrix (`TauCeti.exists_mem_elementarySubgroup_mul_diagGL`), deduced from
`TauCeti.exists_mem_elementarySubgroup_eq_mul_diagGL_mulSingle`.

Since `TauCeti.elementarySubgroup n D` is normal by
`TauCeti.elementarySubgroup_normal_of_hasStableRangeLE` for `2 ≤ Fintype.card n` and trivial for
`Fintype.card n ≤ 1`, it is normal in `GL n D` at every finite matrix size
(`TauCeti.elementarySubgroup_normal`), without stabilization.

## Main results

* `TauCeti.exists_mem_elementarySubgroup_mul_diagGL`: factorization `g = e * diagGL d` in `GL n D`.
* `TauCeti.elementarySubgroup_normal`: `TauCeti.elementarySubgroup n D` is normal in `GL n D`.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France **71**
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §1–§2.
-/

public section

noncomputable section

namespace TauCeti

variable {D : Type*} [DivisionRing D]

/-- Over a division ring, every invertible matrix factors as an elementary matrix times an
invertible diagonal matrix. -/
theorem exists_mem_elementarySubgroup_mul_diagGL {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n D) :
    ∃ e ∈ elementarySubgroup n D, ∃ d : n → Dˣ, g = e * diagGL d := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_mem _, 1, Subsingleton.elim _ _⟩
  · obtain ⟨e, he, u, rfl⟩ := exists_mem_elementarySubgroup_eq_mul_diagGL_mulSingle i₀ g
    exact ⟨e, he, Pi.mulSingle i₀ u, rfl⟩

/-- **The elementary subgroup is normal over a division ring**, already at every finite matrix
size. -/
instance elementarySubgroup_normal {n : Type*} [Fintype n] [DecidableEq n] :
    (elementarySubgroup n D).Normal := by
  by_cases hn : 2 ≤ Fintype.card n
  · exact elementarySubgroup_normal_of_hasStableRangeLE (hasStableRangeLE_one_of_isLocalRing D) hn
  · have : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hbot : elementarySubgroup n D = ⊥ :=
      le_bot_iff.mp (elementarySubgroup_le_iff.2 fun i j hij _ ↦ absurd (Subsingleton.elim i j) hij)
    rw [hbot]
    infer_instance

end TauCeti

end
