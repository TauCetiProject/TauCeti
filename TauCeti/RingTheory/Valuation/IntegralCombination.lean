/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.Algebra.Module.Submodule.Union
import TauCeti.RingTheory.Valuation.Basic

/-!
# Integral combinations without cancellation

Let `v` be a valuation on a field `K` whose valuation ring has an infinite residue field. Given
finitely many vectors `l j : ι → K` (`j : m`, `m` finite, `ι` finite), some combination
`∑ j, c j • l j` with coefficients `c j` in the valuation ring has, at every coordinate `k`,
valuation at least `v (l j k)` for every `j`: no coordinate suffers cancellation.

In each coordinate `k`, divide the column `(l j k)_j` by an entry of largest valuation. The
coefficients `c` for which the normalised column sums to an element of the maximal ideal form a
proper submodule of `m → 𝒪`, since the standard basis vector at the chosen entry lies outside it.
Over a local ring with infinite residue field a module is not a finite union of proper submodules
(`Submodule.exists_forall_notMem_of_forall_ne_top_of_isLocalRing`), so some `c` avoids all of
them, and for it the sum at `k` has the valuation of the chosen entry.

The infinite residue field is necessary: for the `2`-adic valuation on `ℚ`, no integral `c₀, c₁`
make `c₀`, `c₁` and `c₀ + c₁` all units.

## Main results

* `Valuation.exists_forall_map_le_map_sum_mul`: integral coefficients `c` with
  `v (l j k) ≤ v (∑ i, c i * l i k)` for all `j` and `k`.
* `Valuation.exists_toLin_diagonal_mem_and_map_le`: a set of operators on a space with a
  finite basis `b` that contains the integral combinations of any `#m` of its members and the
  operators diagonal in `b` with eigenvalues `l k` (`k : m`) contains an operator diagonal in `b`
  whose eigenvalue `μ k` at `b k` satisfies `v (l k k) ≤ v (μ k)`.

## References

* Another formalization of the diagonal-operator statement: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
  `New/Congruences/FirstOrder/HeckeStrings` (`New.Selmer.exists_diagonal_mem_norm_ge`).
-/

public section

open IsLocalRing

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- **Integral combinations without cancellation.** Over a valued field whose valuation ring has
an infinite residue field, finitely many vectors `l j : ι → K` (`ι` finite) have a combination
with integral coefficients `c` whose `k`-th coordinate has valuation at least `v (l j k)` for
every `j` and `k`; by the ultrametric inequality it is then the largest of these valuations. -/
theorem exists_forall_map_le_map_sum_mul
    [Infinite (ResidueField v.valuationSubring)] {ι m : Type*} [Finite ι] [Fintype m]
    (l : m → ι → K) :
    ∃ c : m → v.valuationSubring, ∀ k j, v (l j k) ≤ v (∑ i, (c i : K) * l i k) := by
  classical
  rcases isEmpty_or_nonempty m with hm | hm
  · exact ⟨isEmptyElim, fun _ j ↦ isEmptyElim j⟩
  -- an entry of largest valuation in each column, and the column divided by it
  choose J hJ using fun k ↦ Finite.exists_max fun j ↦ v (l j k)
  let w (k : ι) (i : m) : v.valuationSubring :=
    ⟨l i k / l (J k) k, by simpa [div_eq_mul_inv] using v.map_mul_mul_inv_le (c := 1) (hJ k i)⟩
  -- the coefficients for which the normalised column sums into the maximal ideal
  let p (k : {k // l (J k) k ≠ 0}) : Submodule v.valuationSubring (m → v.valuationSubring) :=
    Submodule.comap (Fintype.linearCombination v.valuationSubring (w k))
      (maximalIdeal v.valuationSubring)
  have hp (k) : p k ≠ ⊤ := by
    intro htop
    have hJk : w k (J k) = 1 := Subtype.ext (div_self k.property)
    have hmem : Pi.single (J k) 1 ∈ p k := htop ▸ Submodule.mem_top
    simp [p, hJk] at hmem
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top_of_isLocalRing p hp
  refine ⟨c, fun k j ↦ ?_⟩
  rcases eq_or_ne (l (J k) k) 0 with h0 | h0
  · exact (hJ k j).trans (by rw [h0, map_zero]; exact zero_le)
  set u := Fintype.linearCombination v.valuationSubring (w k) c
  have hsum : ∑ i, (c i : K) * l i k = l (J k) k * u := by
    simp only [u, Fintype.linearCombination_apply, smul_eq_mul, w]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by field_simp
  have hu : v (u : K) = 1 :=
    le_antisymm u.property (not_lt.mp fun hlt ↦
      hc ⟨k, h0⟩ ((Valuation.mem_maximalIdeal_iff (v := v)).mpr hlt))
  rw [hsum, map_mul, hu, mul_one]
  exact hJ k j

/-- **A diagonal operator without cancellation.** Let `S` be a set of operators on a `K`-vector
space with a basis `b` indexed by a finite type `m`, containing every combination
`∑ j, c j • f j` of members `f j` of `S` (`j : m`) with integral coefficients (`v (c j) ≤ 1`).
If `S` contains, for each `k : m`, the operator diagonal in `b` with eigenvalues `l k`, then it
contains an operator diagonal in `b` with eigenvalues `μ` such that `v (l k k) ≤ v (μ k)` for
every `k`. This needs the residue field of the valuation ring to be infinite. -/
theorem exists_toLin_diagonal_mem_and_map_le
    [Infinite (ResidueField v.valuationSubring)] {m V : Type*} [Fintype m] [DecidableEq m]
    [AddCommGroup V] [Module K V] (b : Module.Basis m K V) {S : Set (Module.End K V)}
    (hS : ∀ (f : m → Module.End K V) (c : m → K), (∀ j, f j ∈ S) → (∀ j, v (c j) ≤ 1) →
      ∑ j, c j • f j ∈ S)
    (l : m → m → K) (hl : ∀ k, Matrix.toLin b b (Matrix.diagonal (l k)) ∈ S) :
    ∃ μ : m → K, Matrix.toLin b b (Matrix.diagonal μ) ∈ S ∧ ∀ k, v (l k k) ≤ v (μ k) := by
  obtain ⟨c, hc⟩ := v.exists_forall_map_le_map_sum_mul l
  refine ⟨∑ j, (c j : K) • l j, ?_, fun k ↦ ?_⟩
  · have hdiag : Matrix.toLin b b (Matrix.diagonal (∑ j, (c j : K) • l j)) =
        ∑ j, (c j : K) • Matrix.toLin b b (Matrix.diagonal (l j)) := by
      simp only [← Matrix.diagonal_smul, ← map_smul]
      exact map_sum ((Matrix.toLin b b).toAddMonoidHom.comp (Matrix.diagonalAddMonoidHom m K)) _ _
    rw [hdiag]
    exact hS _ _ hl fun j ↦ (c j).property
  · simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc k k

end Valuation
