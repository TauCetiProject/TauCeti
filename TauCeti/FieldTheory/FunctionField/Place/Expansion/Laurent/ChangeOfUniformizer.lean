/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Basic

/-!
# Residues under a change of uniformizer

Let `P` be a rational place of `F / k` and let `s` and `t` both have order one at `P`. The
residue of a function `z` with respect to `s` can be computed from Laurent expansions in `t`:

`res_{P,s}(z) = coeff_{-1} (z(T) * s'(T))`,

where `z(T)` and `s(T)` are the Laurent expansions of `z` and `s` in `t` and `s'(T)` is the
formal derivative. This is Stichtenoth's transformation formula
`res_{P,s}(z) = res_{P,t}(z · ds/dt)` (Proposition 4.2.9) in terms of expansions. Whenever a
function `w` has expansion `s'(T)` in `t`, it reads `res_{P,s}(z) = res_{P,t}(z * w)`; the
function `ds/dt` of a separating uniformizer `t` is such a `w`.

The formula holds in every characteristic. Both sides are `k`-linear in `z` and vanish on
functions integral at `P`, so it suffices to compare them on the negative powers `s ^ j`. There
it is the formal identity `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative` for the expansion
of `s`, a power series of order one.

## Main results

* `TauCeti.Place.residue_eq_coeff_laurentSeriesExpansion_mul_derivative`: the residue with
  respect to `s`, computed from Laurent expansions in `t`.
* `TauCeti.Place.residue_eq_residue_mul`: `res_{P,s}(z) = res_{P,t}(z * w)` for a function `w`
  whose expansion in `t` is the derivative of that of `s`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- **Change of uniformizer for residues.** At a rational place, the residue with respect to a
uniformizer `s` is the coefficient of `T⁻¹` in `z(T) * s'(T)`, where `z(T)` and `s(T)` are the
Laurent expansions of `z` and `s` in another uniformizer `t` (Stichtenoth, Proposition 4.2.9). -/
theorem residue_eq_coeff_laurentSeriesExpansion_mul_derivative (hs : P.ord s = 1) (z : F) :
    P.residue hP hs z = (P.laurentSeriesExpansion hP ht z *
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)).coeff (-1) := by
  have hsint : s ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  -- The expansion of `s` in `t` is a power series `φ` of order one.
  have hs0 : (⟨s, hsint⟩ : P.integers) ≠ 0 := by
    intro h
    have : s = 0 := congrArg Subtype.val h
    simp [this] at hs
  have hφ : (P.powerSeriesExpansion hP ht ⟨s, hsint⟩).order = 1 := by
    rw [order_powerSeriesExpansion _ _ _ _ hs0, hs]
    simp
  have hLs := P.laurentSeriesExpansion_coe hP ht ⟨s, hsint⟩
  -- The right-hand side as a `k`-linear function of `z`.
  let R : F →ₗ[k] k :=
    { toFun z := (P.laurentSeriesExpansion hP ht z *
        LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)).coeff (-1)
      map_add' x y := by simp [add_mul]
      map_smul' c x := by
        -- The `k`-action on `k⸨X⸩` is the algebra action, multiplication by a constant series;
        -- turn it into the coefficientwise action, which commutes with `coeff`.
        rw [RingHom.id_apply, smul_eq_mul, Algebra.smul_def (A := F), map_mul, AlgHom.commutes,
          HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C,
          mul_assoc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] }
  have hR_apply (z : F) : R z = (P.laurentSeriesExpansion hP ht z *
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)).coeff (-1) := rfl
  have hR : P.residue hP hs = R := by
    refine P.linearMap_ext_zpow hP hs (m := 0) (fun z hz ↦ ?_) (fun j _ ↦ ?_)
    · -- Both sides vanish on functions integral at `P`.
      obtain ⟨x, rfl⟩ : ∃ x : P.integers, (x : F) = z := ⟨⟨z, P.mem_filtration_zero_iff.mp hz⟩, rfl⟩
      rw [P.residue_eq_zero_of_mem_integers hP hs x.2, hR_apply, laurentSeriesExpansion_coe, hLs,
        ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul, PowerSeries.coeff_coe]
      simp
    · rw [hR_apply, residue_zpow_uniformizer, map_zpow₀, hLs,
        PowerSeries.coeff_neg_one_coe_zpow_mul_derivative hφ]
  exact LinearMap.congr_fun hR z

/-- **Stichtenoth's transformation formula** `res_{P,s}(z) = res_{P,t}(z · ds/dt)`: if the
Laurent expansion of `w` in `t` is the derivative of that of `s`, then the residue of `z` with
respect to `s` is the residue of `z * w` with respect to `t`. -/
theorem residue_eq_residue_mul (hs : P.ord s = 1) {w : F}
    (hw : P.laurentSeriesExpansion hP ht w =
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht s)) (z : F) :
    P.residue hP hs z = P.residue hP ht (z * w) := by
  rw [P.residue_eq_coeff_laurentSeriesExpansion_mul_derivative hP ht hs, residue_apply, map_mul,
    hw]

end TauCeti.Place
