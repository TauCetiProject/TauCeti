/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Heights and positive roots of the rational G₂ system

The uniform integral and rational `G₂` bases inherit the root-height and positivity formulas of
the pinned integral table. In fundamental-weight coordinates `![a, b]`, the height of a `G₂` root
is `3 * a + 5 * b`, so the six positive roots at indices `0, ..., 5` have heights `1, 1, 2, 3, 4, 5`
(`max k 1`). This identifies positive-root indices and heights for constructions using the rational
system, without importing the Lie-algebra or root-subgroup development.

The native integral coroot-height and positivity results remain in `G2.Positive`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
-/

public section

namespace TauCeti.DynkinType

/-- The height of a root of the pinned `G₂` datum in fundamental-weight coordinates is
`3 * g2Root k 0 + 5 * g2Root k 1`. -/
@[simp] theorem height_g2SimplyConnectedBase (k : Fin 12) :
    g2SimplyConnectedBase.height k = 3 * g2Root k 0 + 5 * g2Root k 1 := by
  -- The functional `3 x₀ + 5 x₁` takes value `1` on both simple roots `![2, -1]` and `![-3, 2]`.
  have h := apply_root_eq_height_zsmul g2SimplyConnectedRootDatum g2SimplyConnectedBase
    (3 • Pi.evalAddMonoidHom (fun _ : Fin 2 ↦ ℤ) 0 +
      5 • Pi.evalAddMonoidHom (fun _ : Fin 2 ↦ ℤ) 1)
    (c := 1) ?_ k
  · simpa [nsmul_eq_mul] using h.symm
  · intro j hj
    rw [g2SimplyConnectedBase_support, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [g2Root_apply]

/-- The uniform integral `G₂` base has the pinned table's root-height formula. -/
-- Rewrite before simplification normalizes the dependent root-index type to `Fin 12`.
@[simp↓] theorem height_simplyConnectedBase_G2 (ht : G2.Valid) (i : Fin G2.numRoots) :
    (G2.simplyConnectedBase ht).height i = 3 * g2Root i 0 + 5 * g2Root i 1 := by
  have hb := heq_of_eqRec_eq _ (simplyConnectedBase_G2 ht)
  have hP := simplyConnectedRootDatum_G2 ht
  have hh : (G2.simplyConnectedBase ht).height i = g2SimplyConnectedBase.height i :=
    congr_heq (by congr 1) (HEq.refl i)
  exact hh.trans (height_g2SimplyConnectedBase i)

/-- The height of a rational pinned `G₂` root in fundamental-weight coordinates. -/
-- Simplify before the dependent root-index type is normalized to `Fin 12`.
@[simp↓] theorem height_rationalBase_G2 (ht : G2.Valid) (i : Fin G2.numRoots) :
    (G2.rationalBase ht).height i = 3 * g2Root i 0 + 5 * g2Root i 1 := by
  rw [height_rationalBase, height_simplyConnectedBase_G2]

/-- The six positive roots of the rational `G₂` system at table indices `0, ..., 5` have heights
`1, 1, 2, 3, 4, 5`, namely `max (k : ℤ) 1`. -/
theorem height_rationalBase_G2_castAdd (ht : G2.Valid) (k : Fin 6) :
    (G2.rationalBase ht).height (Fin.castAdd 6 k : Fin G2.numRoots) = max (k : ℤ) 1 := by
  -- `G2.numRoots` is definitionally `6 + 6`.
  rw [height_rationalBase_G2 ht (Fin.castAdd 6 k : Fin G2.numRoots)]
  fin_cases k <;> simp [g2Root_apply]

/-- The positive roots of the rational `G₂` system are the first six entries of the native
root table, just as for the integral datum. -/
theorem mem_posRoots_rational_g2_iff (ht : G2.Valid) (k : Fin G2.numRoots) :
    k ∈ posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht) ↔ (k : ℕ) < 6 := by
  rw [posRoots_rationalRootSystem]
  -- The uniform integral base is transported to the native G₂ datum by its assembly equation.
  have hpos : posRoots (G2.simplyConnectedRootDatum ht) (G2.simplyConnectedBase ht) =
      posRoots g2SimplyConnectedRootDatum g2SimplyConnectedBase := by
    congr 1
    · exact simplyConnectedRootDatum_G2 ht
    · exact heq_of_eqRec_eq _ (simplyConnectedBase_G2 ht)
  rw [hpos]
  exact mem_posRoots_g2_iff k

end TauCeti.DynkinType
