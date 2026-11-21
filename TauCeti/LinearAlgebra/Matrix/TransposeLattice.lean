/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The transpose lattice of a linear map

For a linear map `L : ℝ^ι → ℝ^κ`, the **transpose lattice** `Lᵀ ℤ^κ ⊆ ℝ^ι`
(`ContinuousLinearMap.transposeLattice`) is the subgroup of vectors `v` whose one-form `v ⬝ᵥ ·` is
an integral combination `∑ᵢ nᵢ Lᵢ` of the components of `L`. When `L` is invertible, it is the
lattice with basis the rows of the matrix of `L`.

This file shows that the lattice determines `L` up to a change of basis by `GL(ι, ℤ)`.

## Main results

* `ContinuousLinearMap.transposeLattice_le_iff`: `L₁ᵀ ℤ^κ₁ ⊆ L₂ᵀ ℤ^κ₂` exactly when
  `L₁ = N L₂` for an integer matrix `N`.
* `ContinuousLinearMap.exists_generalLinearGroup_mulVec_eq_of_transposeLattice_eq`: two linear
  maps, the first injective, with the same transpose lattice differ by an element of `GL(ι, ℤ)`.
* `ContinuousLinearMap.transposeLattice_toLin'_comp`: conversely, composing with an element of
  `GL(κ, ℤ)` does not change the transpose lattice.
-/

public section

open Function Matrix

namespace ContinuousLinearMap

variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']

/-- The **transpose lattice** `Lᵀ ℤ^κ ⊆ ℝ^ι` of a linear map `L : ℝ^ι → ℝ^κ`: the vectors `v` whose
one-form `v ⬝ᵥ ·` is an integral combination `∑ᵢ nᵢ Lᵢ` of the components of `L`. -/
def transposeLattice (L : (ι → ℝ) →L[ℝ] (κ → ℝ)) : AddSubgroup (ι → ℝ) where
  carrier := {v | ∃ n : κ → ℤ, ∀ w, v ⬝ᵥ w = ∑ i, n i * L w i}
  add_mem' := by
    rintro v v' ⟨n, hn⟩ ⟨n', hn'⟩
    exact ⟨n + n', fun w ↦ by simp [add_dotProduct, hn, hn', add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro v ⟨n, hn⟩
    exact ⟨-n, fun w ↦ by simp [hn]⟩

/-- A vector lies in `Lᵀ ℤ^κ` exactly when its one-form is an integral combination of the
components of `L`. -/
@[simp]
theorem mem_transposeLattice {L : (ι → ℝ) →L[ℝ] (κ → ℝ)} {v : ι → ℝ} :
    v ∈ L.transposeLattice ↔ ∃ n : κ → ℤ, ∀ w, v ⬝ᵥ w = ∑ i, n i * L w i :=
  Iff.rfl

/-- `∑ᵢ nᵢ (N x)ᵢ = ∑ₖ (n N)ₖ xₖ` for an integer matrix `N`. -/
private theorem sum_intCast_mul_map_intCast_mulVec (N : Matrix κ κ' ℤ) (n : κ → ℤ)
    (x : κ' → ℝ) :
    ∑ i, (n i : ℝ) * (N.map (↑) *ᵥ x) i = ∑ k, ((n ᵥ* N) k : ℝ) * x k := by
  simp only [mulVec, vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul, Int.cast_sum,
    Int.cast_mul, Matrix.map_apply, mul_assoc]
  exact Finset.sum_comm

/-- **Comparing transpose lattices.** The lattice `L₁ᵀ ℤ^κ` lies in `L₂ᵀ ℤ^κ'` exactly when
`L₁ = N L₂` for an integer matrix `N`. -/
theorem transposeLattice_le_iff {L₁ : (ι → ℝ) →L[ℝ] (κ → ℝ)} {L₂ : (ι → ℝ) →L[ℝ] (κ' → ℝ)} :
    L₁.transposeLattice ≤ L₂.transposeLattice ↔
      ∃ N : Matrix κ κ' ℤ, ∀ w, L₁ w = N.map (↑) *ᵥ L₂ w := by
  classical
  constructor
  · intro h
    -- The `i`-th row of the matrix of `L₁` is the lattice vector with `n = eᵢ`.
    have hrow (i : κ) (w : ι → ℝ) :
        LinearMap.toMatrix' (L₁ : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) i ⬝ᵥ w = L₁ w i :=
      congrFun (LinearMap.toMatrix'_mulVec (L₁ : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) w) i
    have hmem (i : κ) :
        LinearMap.toMatrix' (L₁ : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) i ∈ L₂.transposeLattice :=
      h ⟨Pi.single i 1, fun w ↦ by simp [hrow, Pi.single_apply]⟩
    choose n hn using hmem
    refine ⟨Matrix.of n, fun w ↦ funext fun i ↦ ?_⟩
    rw [← hrow, hn]
    simp [mulVec, dotProduct]
  · -- `∑ᵢ nᵢ (L₁)ᵢ = ∑ₖ (n N)ₖ (L₂)ₖ`.
    rintro ⟨N, hN⟩ v ⟨n, hn⟩
    exact ⟨n ᵥ* N, fun w ↦ by rw [hn, hN, sum_intCast_mul_map_intCast_mulVec]⟩

/-- **Two bases of one lattice differ by an element of `GL(ι, ℤ)`.** If the injective linear map
`L` and the linear map `L'` have the same transpose lattice `Lᵀ ℤ^ι = L'ᵀ ℤ^ι`, then `L' = M L`
for an invertible integer matrix `M`. -/
theorem exists_generalLinearGroup_mulVec_eq_of_transposeLattice_eq [DecidableEq ι]
    {L L' : (ι → ℝ) →L[ℝ] (ι → ℝ)} (hL : Injective L)
    (h : L.transposeLattice = L'.transposeLattice) :
    ∃ M : GL ι ℤ, ∀ w, L' w = (M : Matrix ι ι ℤ).map (↑) *ᵥ L w := by
  obtain ⟨M, hM⟩ := transposeLattice_le_iff.1 h.ge
  obtain ⟨N, hN⟩ := transposeLattice_le_iff.1 h.le
  -- `L = N M L` and `L` is onto, so `N M = 1`.
  have hsurj : Surjective L :=
    LinearMap.injective_iff_surjective (f := (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).1 hL
  have hcast : (N * M).map ((↑) : ℤ → ℝ) = (1 : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) := by
    rw [Matrix.map_one _ Int.cast_zero Int.cast_one]
    refine Matrix.toLin'.injective (LinearMap.ext fun u ↦ ?_)
    obtain ⟨w, rfl⟩ := hsurj u
    have hmap : (N * M).map ((↑) : ℤ → ℝ) = N.map (↑) * M.map (↑) :=
      Matrix.map_mul (f := Int.castRingHom ℝ)
    simp only [Matrix.toLin'_apply, hmap, ← mulVec_mulVec, ← hM, ← hN, one_mulVec]
  have hNM : N * M = 1 := Matrix.map_injective Int.cast_injective hcast
  exact ⟨⟨M, N, mul_eq_one_comm.1 hNM, hNM⟩, hM⟩

/-- **Changing the basis by `GL(κ, ℤ)` preserves the transpose lattice.** For an invertible integer
matrix `M`, the maps `M L` and `L` have the same transpose lattice. -/
@[simp]
theorem transposeLattice_toLin'_comp [DecidableEq κ] (M : GL κ ℤ) (L : (ι → ℝ) →L[ℝ] (κ → ℝ)) :
    ((Matrix.toLin' ((M : Matrix κ κ ℤ).map (↑))).toContinuousLinearMap.comp L).transposeLattice =
      L.transposeLattice := by
  refine le_antisymm (transposeLattice_le_iff.2 ⟨M, fun w ↦ rfl⟩)
    (transposeLattice_le_iff.2 ⟨(M⁻¹ : GL κ ℤ), fun w ↦ ?_⟩)
  -- `L = M⁻¹ (M L)`.
  have hmap : ((M⁻¹ : GL κ ℤ) * M : Matrix κ κ ℤ).map ((↑) : ℤ → ℝ) =
      ((M⁻¹ : GL κ ℤ) : Matrix κ κ ℤ).map (↑) * (M : Matrix κ κ ℤ).map (↑) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  rw [comp_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, mulVec_mulVec,
    ← hmap, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ Int.cast_zero
    Int.cast_one, one_mulVec]

end ContinuousLinearMap
