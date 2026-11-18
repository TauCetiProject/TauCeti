/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Fuchsian
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Tower
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Cusp
import TauCeti.Analysis.Complex.ModularForms.CongruenceSubgroups.Degree
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The cusps of `Γ(N)`

Every cusp of `Γ(N)` has width `N`, and the number `ε∞` of cusps of `Γ(N)` satisfies
`2 N ε∞ = |SL(2, ℤ / N)|` for `N ≥ 3`, while `Γ(1)` has one cusp and `Γ(2)` has three. These are
the cusp counts of the dimension formulas for `Γ(N)`. Cusps are counted as the cusp orbits of the
effective image of `Γ(N)` in `PSL(2, ℝ)`, the boundary orbits adjoined to its analytic quotient
`X(N)`.

The width of a cusp is the local multiplicity of the map `X(N) → X(1)` there. For `N > 0` the cusp
`∞` has width `N`: the normalized cusp datum `TauCeti.cuspDatumInftyGamma` of the image of `Γ(N)`
has width `N`, and the level-one datum has width `1`. Since `Γ(N)` is normal in `SL(2, ℤ)`, its
image is normal in the level-one group, and all cusps of `X(N)` lie over the single cusp of `X(1)`,
so every cusp has the width of `∞`
(`localMultiplicity_compactifiedQuotientMap_ofCusp_eq_of_cuspOrbitMap_eq`).
The widths add up to the degree `[SL(2, ℤ) : ±Γ(N)]`
(`Subgroup.finsum_localMultiplicity_compactifiedQuotientMap_map_sl2zToPSL2R_ofCusp`), so `N ε∞`
is that index, which is half of `|SL(2, ℤ / N)|` exactly when `-I ∉ Γ(N)`, that is, for `N ≥ 3`.

At level `0` the group `Γ(0)` is trivial, so it has no cusps, and `±Γ(0)` has index `0` in
`SL(2, ℤ)`: the statements hold there too.

## Main results

* `TauCeti.localMultiplicity_compactifiedQuotientMap_Gamma_ofCusp`: every cusp of `X(N)` has local
  multiplicity `N` over `X(1)`.
* `TauCeti.mul_card_cuspOrbit_Gamma`: `N ε∞ = [SL(2, ℤ) : ±Γ(N)]`.
* `TauCeti.two_mul_mul_card_cuspOrbit_Gamma`: `2 N ε∞ = |SL(2, ℤ / N)|` for `N ≥ 3`.
* `TauCeti.card_cuspOrbit_Gamma_one`, `TauCeti.card_cuspOrbit_Gamma_two`: `Γ(1)` has one cusp and
  `Γ(2)` has three.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.8–3.9.
-/

public section

open MulAction OnePoint Subgroup Subgroup.CompactifiedQuotient CongruenceSubgroup
open TauCeti.RiemannSurface
open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ)

/-- `Γ(0)` is trivial, so its image has no cusps: a cusp needs a parabolic element. -/
instance isEmpty_cuspOrbit_map_Gamma_zero : IsEmpty ((Gamma 0).map sl2zToPSL2R).CuspOrbit := by
  refine ⟨fun C ↦ ?_⟩
  obtain ⟨c, -⟩ := cuspOrbitMk_surjective C
  obtain ⟨g, hg, -⟩ :=
    isCuspPoint_iff_exists_parabolicFixedPoint_eq.mp (mem_cuspPoints.mp c.property)
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.mp g.property
  rw [Gamma_zero_bot, Subgroup.mem_bot] at hγ
  rw [← hγg, hγ, map_one] at hg
  exact Matrix.ProjectiveSpecialLinearGroup.not_isParabolic_one hg

/-- **Every cusp of `X(N)` has local multiplicity `N` over `X(1)`**, that is, every cusp of `Γ(N)`
has width `N`. All cusps of `X(N)` lie over the single cusp of `X(1)` and the image of `Γ(N)` is
normal in the level-one group, so they all have the multiplicity of the cusp `∞`, which is the
width `N` of `TauCeti.cuspDatumInftyGamma`. -/
@[simp]
theorem localMultiplicity_compactifiedQuotientMap_Gamma_ofCusp
    (C : ((Gamma N).map sl2zToPSL2R).CuspOrbit) :
    localMultiplicity
      (compactifiedQuotientMap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) (ofCusp C) = N := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact isEmptyElim C
  have : NeZero N := ⟨hN⟩
  have h := (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
  have hσ : (cuspDatumInftyGamma N).scaling = ModularGroup.cuspDatumInfty.scaling := by
    rw [cuspDatumInftyGamma_scaling, ModularGroup.cuspDatumInfty_scaling]
  have hw := Subgroup.CuspDatum.width_eq_widthIndex_mul h (cuspDatumInftyGamma N)
    ModularGroup.cuspDatumInfty hσ
  rw [cuspDatumInftyGamma_width, ModularGroup.cuspDatumInfty_width, mul_one] at hw
  rw [localMultiplicity_compactifiedQuotientMap_ofCusp_eq_of_cuspOrbitMap_eq h
      (Subsingleton.elim _ (cuspOrbitMap h (cuspDatumInftyGamma N).cuspOrbit)),
    localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex h _ _ hσ]
  exact_mod_cast hw.symm

/-- **The cusp count of `Γ(N)` times its width is the index of `±Γ(N)`**: the widths of the cusps
of `X(N)` are all `N` and add up to `[SL(2, ℤ) : ±Γ(N)]`. At level `0` both sides are `0`. -/
theorem mul_card_cuspOrbit_Gamma :
    N * Nat.card ((Gamma N).map sl2zToPSL2R).CuspOrbit = (Gamma N).withCenter.index := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [zero_mul, ← Subgroup.relIndex_mul_index (withCenter_le_Gamma0 (Gamma_le_Gamma0 0)),
      Gamma0_zero_index, mul_zero]
  have : NeZero N := ⟨hN⟩
  have := Fintype.ofFinite ((Gamma N).map sl2zToPSL2R).CuspOrbit
  rw [← Subgroup.finsum_localMultiplicity_compactifiedQuotientMap_map_sl2zToPSL2R_ofCusp,
    finsum_eq_sum_of_fintype]
  simp only [localMultiplicity_compactifiedQuotientMap_Gamma_ofCusp, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

/-- **The count `ε∞(Γ(N))` for `N ≥ 3`**: `2 N ε∞ = |SL(2, ℤ / N)|`, as `-I ∉ Γ(N)`. -/
theorem two_mul_mul_card_cuspOrbit_Gamma {N : ℕ} (hN : 3 ≤ N) :
    2 * N * Nat.card ((Gamma N).map sl2zToPSL2R).CuspOrbit = Nat.card SL(2, ZMod N) := by
  have hneg : (-1 : SL(2, ℤ)) ∉ Gamma N := fun h ↦ by
    have := Nat.le_of_dvd two_pos (neg_one_mem_Gamma_iff.mp h)
    omega
  rw [mul_assoc, mul_card_cuspOrbit_Gamma, ← index_Gamma,
    Matrix.SpecialLinearGroup.index_eq_two_mul_index_withCenter_of_neg_one_notMem hneg]

/-- **`Γ(1)` has one cusp**, as `Γ(1) = SL(2, ℤ)`. -/
@[simp]
theorem card_cuspOrbit_Gamma_one : Nat.card ((Gamma 1).map sl2zToPSL2R).CuspOrbit = 1 := by
  simpa [Gamma_one_top, Subgroup.withCenter_def] using mul_card_cuspOrbit_Gamma 1

/-- **`Γ(2)` has three cusps**: there `-I ∈ Γ(2)`, so `2 ε∞ = |SL(2, ℤ / 2)| = 6`. -/
@[simp]
theorem card_cuspOrbit_Gamma_two : Nat.card ((Gamma 2).map sl2zToPSL2R).CuspOrbit = 3 := by
  have h := mul_card_cuspOrbit_Gamma 2
  have h6 : Nat.card SL(2, ZMod 2) = 6 := by
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  rw [Subgroup.withCenter_eq_self_iff.mpr (Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr
    (neg_one_mem_Gamma_iff.mpr dvd_rfl)), index_Gamma, h6] at h
  omega

end TauCeti
