/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Fuchsian
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Cusp.Fiber
import TauCeti.Analysis.Complex.Fuchsian.Compactification.LevelOne
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Tower
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Cusp
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The cusps of `Γ(N)`

Every cusp of `Γ(N)` has width `N`, and the number `ε∞` of cusps of `Γ(N)` satisfies
`2 N ε∞ = |SL(2, ℤ / N)|` for `N ≥ 3`, while `Γ(2)` has three cusps. These are the cusp counts of
the dimension formulas for `Γ(N)`. Cusps are counted as the cusp orbits of the effective image of
`Γ(N)` in `PSL(2, ℝ)`, the boundary orbits adjoined to its analytic quotient `X(N)`.

The cusp `∞` has width `N`: the normalized cusp datum `TauCeti.cuspDatumInftyGamma` of the image
of `Γ(N)` has width `N`, and the level-one datum has width `1`. Since `Γ(N)` is normal in
`SL(2, ℤ)`, its image is normal in the level-one group, and conjugating by an element carrying `∞`
to another cusp shows that every cusp has width `N`. That width is the local multiplicity of the map
`X(N) → X(1)` at the cusp, and the multiplicities over the single cusp of `X(1)` sum to the degree
`[SL(2, ℤ) : ±Γ(N)]`. So `N ε∞` is that index, which is half of `|SL(2, ℤ / N)|` exactly when
`-I ∉ Γ(N)`, that is, for `N ≥ 3`.

## Main results

* `TauCeti.localMultiplicity_compactifiedQuotientMap_Gamma_ofCusp`: every cusp of `X(N)` has local
  multiplicity `N` over `X(1)`.
* `TauCeti.mul_card_cuspOrbit_Gamma`: `N ε∞ = [SL(2, ℤ) : ±Γ(N)]`.
* `TauCeti.two_mul_mul_card_cuspOrbit_Gamma`: `2 N ε∞ = |SL(2, ℤ / N)|` for `N ≥ 3`.
* `TauCeti.card_cuspOrbit_Gamma_two`: `Γ(2)` has three cusps.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.8–3.9.
-/

public section

open MulAction OnePoint Subgroup Subgroup.CompactifiedQuotient CongruenceSubgroup
open TauCeti.RiemannSurface
open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ)

/-- The image of `Γ(N)` is normal in the level-one group, as `Γ(N)` is normal in `SL(2, ℤ)`. -/
instance normal_subgroupOf_map_Gamma :
    (((Gamma N).map sl2zToPSL2R).subgroupOf psl2zToPSL2R.range).Normal where
  conj_mem x hx g := by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨γ, hγ⟩ : (g : PSL(2, ℝ)) ∈ sl2zToPSL2R.range := by
      rw [range_sl2zToPSL2R_eq_range_psl2zToPSL2R]
      exact g.2
    refine Subgroup.mem_map.mpr ⟨γ * y * γ⁻¹, (Gamma_normal N).conj_mem y hy γ, ?_⟩
    simp [map_mul, map_inv, hγ, hyx]

/-- `Γ(0)` is trivial, so its image has no cusps: a cusp needs a parabolic element. -/
private theorem isEmpty_cuspOrbit_Gamma_zero : IsEmpty ((Gamma 0).map sl2zToPSL2R).CuspOrbit := by
  refine ⟨fun C ↦ ?_⟩
  obtain ⟨c, -⟩ := cuspOrbitMk_surjective C
  obtain ⟨g, hg, -⟩ := isCuspPoint_iff_exists_parabolicFixedPoint_eq.mp (mem_cuspPoints.mp c.2)
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.mp g.2
  rw [Gamma_zero_bot, Subgroup.mem_bot] at hγ
  rw [← hγg, hγ, map_one] at hg
  exact Matrix.ProjectiveSpecialLinearGroup.not_isParabolic_one hg

/-- The centre `{±1}` of `SL(2, ℤ)` has infinite index, as the powers of `T` are distinct. -/
private theorem index_center_SL2Z : (Subgroup.center SL(2, ℤ)).index = 0 := by
  have : Infinite SL(2, ℤ) := Infinite.of_injective (fun n : ℤ ↦ ModularGroup.T ^ n) fun m n h ↦ by
    simpa [ModularGroup.coe_T_zpow] using
      congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
  have : Finite (Subgroup.center SL(2, ℤ)) :=
    ((Set.toFinite ({1, -1} : Set SL(2, ℤ))).subset fun g hg ↦ by
      simpa using Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hg).to_subtype
  have h := (Subgroup.center SL(2, ℤ)).card_mul_index
  rw [Nat.card_eq_zero_of_infinite (α := SL(2, ℤ))] at h
  exact (mul_eq_zero.mp h).resolve_left Nat.card_pos.ne'

/-- **Every cusp of `X(N)` has local multiplicity `N` over `X(1)`**, that is, every cusp of `Γ(N)`
has width `N`. At `∞` this is the width of `TauCeti.cuspDatumInftyGamma`. Every other cusp is a
translate `g • ∞` by an element `g` of the level-one group, whose stabilizer is the conjugate by `g`
of that of `∞`, and conjugation by `g` preserves the normal image of `Γ(N)`. -/
theorem localMultiplicity_compactifiedQuotientMap_Gamma_ofCusp
    (C : ((Gamma N).map sl2zToPSL2R).CuspOrbit) :
    localMultiplicity
      (compactifiedQuotientMap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) (ofCusp C) = N := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact (isEmpty_cuspOrbit_Gamma_zero.false C).elim
  have : NeZero N := ⟨hN⟩
  have h := (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
  have hσ : (cuspDatumInftyGamma N).scaling = ModularGroup.cuspDatumInfty.scaling := by
    rw [cuspDatumInftyGamma_scaling, ModularGroup.cuspDatumInfty_scaling]
  have hw := Subgroup.CuspDatum.width_eq_widthIndex_mul h (cuspDatumInftyGamma N)
    ModularGroup.cuspDatumInfty hσ
  rw [cuspDatumInftyGamma_width, ModularGroup.cuspDatumInfty_width, mul_one] at hw
  have hinfty : (((Gamma N).map sl2zToPSL2R).subgroupOf psl2zToPSL2R.range).relIndex
      (stabilizer psl2zToPSL2R.range (∞ : OnePoint ℝ)) = N := by
    rw [← ModularGroup.cuspDatumInfty_cusp, ← Subgroup.CuspDatum.widthIndex_eq_relIndex h _ _ hσ]
    exact_mod_cast hw.symm
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  obtain ⟨g, hg⟩ :=
    mem_orbit_iff.mp (ModularGroup.cuspPoint_mem_orbit_infty ((mem_cuspPoints.mp c.2).mono h))
  have hΔ : (((Gamma N).map sl2zToPSL2R).subgroupOf psl2zToPSL2R.range).map
      (MulAut.conj g).toMonoidHom = ((Gamma N).map sl2zToPSL2R).subgroupOf psl2zToPSL2R.range :=
    Subgroup.normal_iff_map_conj_eq.mp inferInstance g
  rw [localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk, ← hg,
    stabilizer_smul_eq_stabilizer_map_conj]
  calc _ = ((((Gamma N).map sl2zToPSL2R).subgroupOf psl2zToPSL2R.range).map
          (MulAut.conj g).toMonoidHom).relIndex
        ((stabilizer psl2zToPSL2R.range (∞ : OnePoint ℝ)).map (MulAut.conj g).toMonoidHom) := by
        rw [hΔ]
    _ = _ := Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
    _ = N := hinfty

/-- **The cusp count of `Γ(N)` times its width is the index of `±Γ(N)`.** The cusps of `X(N)` are
the fibre of `X(N) → X(1)` over its single cusp, each of multiplicity `N`, and the multiplicities
of a fibre sum to the degree `[SL(2, ℤ) : ±Γ(N)]`. At level `0` both sides are `0`. -/
theorem mul_card_cuspOrbit_Gamma :
    N * Nat.card ((Gamma N).map sl2zToPSL2R).CuspOrbit = (Gamma N).withCenter.index := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [zero_mul, Gamma_zero_bot, Subgroup.withCenter_def, bot_sup_eq, index_center_SL2Z]
  have : NeZero N := ⟨hN⟩
  have h := (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
  have : Finite ((Gamma N).map sl2zToPSL2R).CuspOrbit := (isCofinite_Gamma N).finite_cuspOrbit
  have := Fintype.ofFinite ((Gamma N).map sl2zToPSL2R).CuspOrbit
  have hsum := sum_localMultiplicity_compactifiedQuotientMap_fiber_ofCusp h
    (default : psl2zToPSL2R.range.CuspOrbit)
  let e : ((Gamma N).map sl2zToPSL2R).CuspOrbit ≃ _ :=
    (Equiv.subtypeUnivEquiv fun D ↦ Subsingleton.elim (cuspOrbitMap h D) default).symm.trans
      (cuspOrbitFiberEquivCompactifiedFiber h default)
  rw [← relIndex_map_sl2zToPSL2R, Subgroup.relIndex, ← hsum, ← finsum_comp_equiv e]
  simp only [e, Equiv.trans_apply, cuspOrbitFiberEquivCompactifiedFiber_apply,
    Equiv.subtypeUnivEquiv_symm_apply, localMultiplicity_compactifiedQuotientMap_Gamma_ofCusp]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

/-- **The count `ε∞(Γ(N))` for `N ≥ 3`**: `2 N ε∞ = |SL(2, ℤ / N)|`, as `-I ∉ Γ(N)`. -/
theorem two_mul_mul_card_cuspOrbit_Gamma {N : ℕ} (hN : 3 ≤ N) :
    2 * N * Nat.card ((Gamma N).map sl2zToPSL2R).CuspOrbit = Nat.card SL(2, ZMod N) := by
  have hneg : (-1 : SL(2, ℤ)) ∉ Gamma N := fun h ↦ by
    have := Nat.le_of_dvd two_pos (neg_one_mem_Gamma1_iff.mp (Gamma_le_Gamma1 N h))
    omega
  rw [mul_assoc, mul_card_cuspOrbit_Gamma, ← index_Gamma,
    Subgroup.index_eq_two_mul_index_withCenter
      (Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)) hneg
      fun _ hc ↦ Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc]

/-- **`Γ(2)` has three cusps**: there `-I ∈ Γ(2)`, so `2 ε∞ = |SL(2, ℤ / 2)| = 6`. -/
theorem card_cuspOrbit_Gamma_two : Nat.card ((Gamma 2).map sl2zToPSL2R).CuspOrbit = 3 := by
  have h := mul_card_cuspOrbit_Gamma 2
  have hc : Subgroup.center SL(2, ℤ) ≤ Gamma 2 := fun c hc ↦ by
    rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc with rfl | rfl
    · exact one_mem _
    · exact Gamma_mem.mpr (by decide)
  rw [Subgroup.withCenter_eq_self_iff.mpr hc, index_Gamma,
    Nat.card_eq_fintype_card (α := SL(2, ZMod 2)),
    show Fintype.card SL(2, ZMod 2) = 6 from rfl] at h
  omega

end TauCeti
