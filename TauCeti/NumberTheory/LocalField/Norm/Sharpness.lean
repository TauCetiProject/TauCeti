/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Basic
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
import TauCeti.NumberTheory.LocalField.UnitFiltration.Map

/-!
# The norm does not preserve the depth of units in a ramified extension

For a finite extension `L/K` of nonarchimedean local fields with ramification index
`e = e(L/K)`, the norm carries `U(L, e i)` into `U(K, i)`
(`TauCeti.map_normUnits_unitFiltration_le`), and for `L/K` Galois it carries `U(L, ψℕ_{L/K}(i))`
into `U(K, i)` (`TauCeti.map_normUnits_unitFiltration_psiNat_le`). This file shows that a shift
of the depth is genuinely needed: when the degree `n = [L : K]` is prime to the residue
characteristic,

* the inclusion `N_{L/K}(U(L, e i)) ⊆ U(K, i)` is sharp at every positive depth `i`: the image
  of `U(L, e i)` is not contained in `U(K, i + 1)`;
* if moreover `L/K` is ramified, the unshifted inclusion `N_{L/K}(U(L, i)) ⊆ U(K, i)` fails at
  every depth `i ≥ 2`.

The witnesses are elements of `K` itself. A unit `x ∈ U(K, i) \ U(K, i + 1)` lies in `U(L, e i)`,
and its norm is `x ^ n`, which has the same depth as `x` because the `n`-th power map is injective
on the graded pieces of the principal units when `n` is invertible in `𝒪[K]`. For example, in a
tamely ramified quadratic extension in odd residue characteristic, some element of `U(L, 2)` has
norm outside `U(K, 2)`.

## Main results

* `TauCeti.not_map_normUnits_unitFiltration_le_succ`: for `[L : K]` invertible in `𝒪[K]`,
  `N_{L/K}(U(L, e (i + 1))) ⊄ U(K, i + 2)`.
* `TauCeti.not_map_normUnits_unitFiltration_le_of_one_lt_ramificationIndex`: for `[L : K]`
  invertible in `𝒪[K]` and `e(L/K) > 1`, `N_{L/K}(U(L, i)) ⊄ U(K, i)` for every `i ≥ 2`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §§2–3 and §6.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField Module

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

variable (K L) in
/-- **The ramification shift of the norm is sharp.** If the degree `[L : K]` is invertible in
`𝒪[K]`, then for every `i` the norm does not carry `U(L, e(L/K) (i + 1))` into `U(K, i + 2)`. Thus
the inclusion `N_{L/K}(U(L, e(L/K) i)) ⊆ U(K, i)` of `map_normUnits_unitFiltration_le` cannot be
improved by one step at any positive depth. -/
theorem not_map_normUnits_unitFiltration_le_succ (hn : IsUnit (finrank K L : 𝒪[K])) (i : ℕ) :
    ¬ (unitFiltration L (ramificationIndex K L * (i + 1))).map (Algebra.normUnits K) ≤
      unitFiltration K (i + 2) := by
  intro h
  -- A unit of `K` of depth exactly `i + 1`.
  obtain ⟨x, hx, hx'⟩ := IsConcreteLE.not_le_iff_exists.mp
    ((unitFiltration_le_unitFiltration_iff (K := K) (i := i + 2) (j := i + 1)
      (Or.inl (by omega))).not.mpr (by omega))
  -- Its norm from `L` is `x ^ [L : K]`, which has the same depth as `x`.
  have hN := h ⟨_, unitsMap_algebraMap_mem_unitFiltration (L := L) hx, rfl⟩
  rw [Algebra.normUnits_unitsMap_algebraMap] at hN
  exact hx' ((pow_mem_unitFiltration_succ_iff_of_isUnit hn
    (unitFiltration_antitone (by omega) hx) (i + 1)).mp hN)

variable (K L) in
/-- **The unshifted norm inclusion fails in a ramified extension.** If the degree `[L : K]` is
invertible in `𝒪[K]` and `L/K` is ramified, then for every depth `i ≥ 2` the norm does not carry
`U(L, i)` into `U(K, i)`. -/
theorem not_map_normUnits_unitFiltration_le_of_one_lt_ramificationIndex
    (hn : IsUnit (finrank K L : 𝒪[K])) (he : 1 < ramificationIndex K L) {i : ℕ} (hi : 2 ≤ i) :
    ¬ (unitFiltration L i).map (Algebra.normUnits K) ≤ unitFiltration K i := by
  -- With `k = ⌊(i - 1) / e⌋` we have `i ≤ e (k + 1)` and `k + 2 ≤ i`, because `e ≥ 2`.
  set e := ramificationIndex K L
  have h₁ : i ≤ e * ((i - 1) / e + 1) := by
    have := Nat.lt_mul_div_succ (i - 1) (show 0 < e by omega)
    omega
  have h₂ : (i - 1) / e + 2 ≤ i := by
    have := Nat.div_le_div_left (a := i - 1) (show 2 ≤ e by omega) two_pos
    omega
  intro h
  exact not_map_normUnits_unitFiltration_le_succ K L hn ((i - 1) / e)
    ((Subgroup.map_mono (unitFiltration_antitone h₁)).trans
      (h.trans (unitFiltration_antitone h₂)))

end TauCeti
