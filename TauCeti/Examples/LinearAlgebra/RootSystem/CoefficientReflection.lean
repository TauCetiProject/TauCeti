/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient

/-!
# Coefficient reflections in types `A₁` and `B₂`

In type `B₂` the Cartan matrix is `!![2, -2; -1, 2]`, with the short root second. Reflecting the
coefficient column `(1, 0)` of the long simple root `e₁ - e₂` at the short node gives `(1, 2)`, the
column of `e₁ + e₂`, and using the transpose of the Cartan matrix instead would wrongly give
`(1, 1)`. The orbit of the long simple root has four columns and misses the short roots, while
the orbits of both simple roots together give all eight roots of the pinned datum. In type `A₁`
the orbit of the coordinate column is `{1, -1}`, which does not contain zero.
-/

public section

open Matrix Set

namespace TauCeti.Examples

/-- The Cartan matrix of type `A₁`. -/
abbrev cartanA₁ : Matrix (Fin 1) (Fin 1) ℤ := !![2]

/-- The Cartan matrix of type `B₂`, with the short root second. -/
abbrev cartanB₂ : Matrix (Fin 2) (Fin 2) ℤ := !![2, -2; -1, 2]

theorem cartanA₁_apply_same (i : Fin 1) : cartanA₁ i i = 2 := by
  fin_cases i
  rfl

theorem cartanB₂_apply_same (i : Fin 2) : cartanB₂ i i = 2 := by
  fin_cases i <;> rfl

/-- The update of `Matrix.columnReflection` at the first node of `B₂`. -/
theorem columnReflection_cartanB₂_zero (c : Fin 2 → ℤ) :
    cartanB₂.columnReflection cartanB₂_apply_same 0 c = ![-c 0 + c 1, c 1] := by
  ext i
  fin_cases i
  · simp [Fin.sum_univ_two]
    ring
  · simp

/-- The update of `Matrix.columnReflection` at the second node of `B₂`. -/
theorem columnReflection_cartanB₂_one (c : Fin 2 → ℤ) :
    cartanB₂.columnReflection cartanB₂_apply_same 1 c = ![c 0, 2 * c 0 - c 1] := by
  ext i
  fin_cases i
  · simp
  · simp [Fin.sum_univ_two]
    ring

/-- At the short node, `(1, 0)` reflects to `(1, 2)`. -/
example : cartanB₂.columnReflection cartanB₂_apply_same 1 ![1, 0] = ![1, 2] := by
  rw [columnReflection_cartanB₂_one]
  simp

/-- At the short node, `(1, 2)` reflects back to `(1, 0)`. -/
example : cartanB₂.columnReflection cartanB₂_apply_same 1 ![1, 2] = ![1, 0] := by
  rw [columnReflection_cartanB₂_one]
  simp

/-- With the transpose of the Cartan matrix, `(1, 0)` would reflect to `(1, 1)`, so the column
formula distinguishes the matrix from its transpose. -/
example :
    cartanB₂ᵀ.columnReflection (fun i ↦ (transpose_apply _ i i).trans (cartanB₂_apply_same i)) 1
      ![1, 0] = ![1, 1] := by
  rw [Matrix.columnReflection_apply]
  ext i
  fin_cases i <;> simp [Fin.sum_univ_two]

/-- Evaluation of `(1, 0)` and `(1, 2)` in fundamental-weight coordinates: these are `e₁ - e₂` and
`e₁ + e₂`, since `e₁` and `(e₁ + e₂) / 2` are the fundamental weights of `B₂`. -/
example : ![1, 0] ᵥ* cartanB₂ = ![2, -2] ∧ ![1, 2] ᵥ* cartanB₂ = ![0, 2] := by
  constructor <;> (ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two])

/-- The orbit of the column of the long simple root of `B₂`. -/
theorem orbit_cartanB₂_long :
    MulAction.orbit (cartanB₂.columnReflectionGroup cartanB₂_apply_same) ![1, 0] =
      {![1, 0], ![-1, 0], ![1, 2], ![-1, -2]} := by
  refine subset_antisymm (Matrix.orbit_columnReflectionGroup_subset (fun i c hc ↦ ?_) (by simp)) ?_
  · fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, columnReflection_cartanB₂_zero,
        columnReflection_cartanB₂_one] <;>
      rcases hc with rfl | rfl | rfl | rfl <;> simp
  · have h₀ : ![1, 0] ∈ MulAction.orbit (cartanB₂.columnReflectionGroup cartanB₂_apply_same)
        (![1, 0] : Fin 2 → ℤ) := MulAction.mem_orbit_self _
    have step₀ {c : Fin 2 → ℤ} (hc : c ∈ MulAction.orbit
        (cartanB₂.columnReflectionGroup cartanB₂_apply_same) (![1, 0] : Fin 2 → ℤ)) :
        ![-c 0 + c 1, c 1] ∈ MulAction.orbit
          (cartanB₂.columnReflectionGroup cartanB₂_apply_same) (![1, 0] : Fin 2 → ℤ) :=
      columnReflection_cartanB₂_zero c ▸
        (cartanB₂.columnReflection_mem_orbit_iff cartanB₂_apply_same 0).mpr hc
    have step₁ {c : Fin 2 → ℤ} (hc : c ∈ MulAction.orbit
        (cartanB₂.columnReflectionGroup cartanB₂_apply_same) (![1, 0] : Fin 2 → ℤ)) :
        ![c 0, 2 * c 0 - c 1] ∈ MulAction.orbit
          (cartanB₂.columnReflectionGroup cartanB₂_apply_same) (![1, 0] : Fin 2 → ℤ) :=
      columnReflection_cartanB₂_one c ▸
        (cartanB₂.columnReflection_mem_orbit_iff cartanB₂_apply_same 1).mpr hc
    rintro c (rfl | rfl | rfl | rfl)
    · exact h₀
    · simpa using step₀ h₀
    · simpa using step₁ h₀
    · simpa using step₁ (step₀ h₀)

/-- The orbit of the long simple root of `B₂` has four columns, so it misses half of the roots. -/
example :
    (MulAction.orbit (cartanB₂.columnReflectionGroup cartanB₂_apply_same)
      (![1, 0] : Fin 2 → ℤ)).ncard = 4 := by
  rw [orbit_cartanB₂_long, ← Finset.coe_singleton, ← Finset.coe_insert, ← Finset.coe_insert,
    ← Finset.coe_insert, Set.ncard_coe_finset]
  decide

/-- The Bourbaki-numbered Cartan matrix of `B₂` is the matrix used above. -/
example : (DynkinType.B 2).cartanMatrix = cartanB₂ :=
  (DynkinType.cartanMatrix_B 2).trans <| by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- **The orbits of both simple roots of the pinned `B₂` give all eight root columns.** -/
example : (⋃ i : Fin (DynkinType.B 2).rank,
    MulAction.orbit
      ((DynkinType.B 2).cartanMatrix.columnReflectionGroup (DynkinType.B 2).cartanMatrix_apply_same)
      (Pi.single i 1 : Fin (DynkinType.B 2).rank → ℤ)).ncard = 8 := by
  rw [DynkinType.iUnion_orbit_single_eq_range_simpleRootCoefficients _ (by simp),
    Set.ncard_range_of_injective (DynkinType.simpleRootCoefficients_injective _ _)]
  simp

/-- In `A₁`, the orbit of the coordinate column is `{1, -1}`, so zero is not in it. -/
example :
    MulAction.orbit (cartanA₁.columnReflectionGroup cartanA₁_apply_same)
        (Pi.single 0 1 : Fin 1 → ℤ) =
      {Pi.single 0 1, -Pi.single 0 1} := by
  refine subset_antisymm (Matrix.orbit_columnReflectionGroup_subset (fun i c hc ↦ ?_) (by simp)) ?_
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rcases hc with rfl | rfl <;> simp
  · rintro c (rfl | rfl)
    · exact MulAction.mem_orbit_self _
    · exact Matrix.neg_mem_orbit_single _ _ (MulAction.mem_orbit_self _)

end TauCeti.Examples

end
