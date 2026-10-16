/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.CoefficientField

/-!
# Residues under a change of uniformizer

Let `P` be a rational place of `F / k` and let `s` and `t` both have order one at `P`. The
residue of a function `z` with respect to `s` can be computed from Laurent expansions in `t`:

`res_{P,s}(z) = coeff_{-1} (z(T) * s'(T))`,

where `z(T)` and `s(T)` are the Laurent expansions of `z` and `s` in `t` and `s'(T)` is the
formal derivative. This is the expansion-level form of Stichtenoth's transformation formula
`res_{P,s}(z) = res_{P,t}(z · ds/dt)` (Proposition 4.2.9). As a corollary, whenever a function
`w` has expansion `s'(T)` in `t`, `res_{P,s}(z) = res_{P,t}(z * w)`. The function-field derivative
`ds/dt` is such a `w` when `t` is separating
(`TauCeti.Place.laurentSeriesExpansion_derivativeOfSeparating`), which gives the formula in
Stichtenoth's form (`TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`).

The formula holds in every characteristic. Both sides are `k`-linear in `z` and vanish on
functions integral at `P`, so it suffices to compare them on the negative powers `s ^ j`. There
it is the formal identity `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative` for the expansion
of `s`, a power series of order one.

The same formula holds at every place `P` whose residue field `F_P` is separable over `k`, for
the `F_P`-valued residues `res_{P,s}` and `res_{P,t}` (`TauCeti.Place.residueResidueField`) and
the Laurent expansions with coefficients in `F_P`, hence also for the `k`-valued residues
`Tr_{F_P/k} ∘ res_{P,t}` (`TauCeti.Place.traceResidue`). Here the expansions in `s` and in `t`
are two identifications of the completion at `P` with `F_P((T))`. Both send the coefficient field
of the completion to the constants, so the expansion in `t` of a function, read as a series in
its expansion in `s`, is a substitution `T ↦ s(T)` fixing `F_P`. Such a substitution preserves
residues (`LaurentSeries.coeff_neg_one_map_mul_derivative`).

## Main results

* `TauCeti.Place.residue_eq_coeff_laurentSeriesExpansion_mul_derivative`: the residue with
  respect to `s`, computed from Laurent expansions in `t`.
* `TauCeti.Place.residue_eq_residue_mul`: `res_{P,s}(z) = res_{P,t}(z * w)` for a function `w`
  whose expansion in `t` is the derivative of that of `s`.
* `TauCeti.Place.residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative`
  and `TauCeti.Place.residueResidueField_eq_residueResidueField_mul`: the same at a place with
  separable residue field, with residues and coefficients in `F_P`.
* `TauCeti.Place.traceResidue_eq_traceResidue_mul`: the same for the `k`-valued residues.

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
      map_smul' c x := by simp [Algebra.smul_def, mul_assoc] }
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

/-! ### Places with separable residue field -/

section ResidueField

variable [Algebra.IsSeparable k P.ResidueField]

/-- **Change of uniformizer in the completion.** At a place with separable residue field, the
coefficient of `T⁻¹` in the expansion of a completed function `z` in a uniformizer `s` is the
coefficient of `T⁻¹` in `z(T) * s'(T)`, where `z(T)` and `s(T)` are the expansions in another
uniformizer `t`, all with coefficients in `F_P`. -/
theorem coeff_neg_one_completionEquivLaurentSeriesResidueField_mul_derivative {s t : P.Completion}
    (hs : P.completionPlace.ord s = 1) (ht : P.completionPlace.ord t = 1) (z : P.Completion) :
    (P.completionEquivLaurentSeriesResidueField ht z * LaurentSeries.derivative P.ResidueField
      (P.completionEquivLaurentSeriesResidueField ht s)).coeff (-1) =
      (P.completionEquivLaurentSeriesResidueField hs z).coeff (-1) := by
  set Φs := P.completionEquivLaurentSeriesResidueField hs
  set Φt := P.completionEquivLaurentSeriesResidueField ht
  -- The expansion of `s` in `t` is a power series `φ` of order one.
  have hsint : s ∈ P.completionPlace.integers :=
    P.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hs0 : (⟨s, hsint⟩ : P.completionPlace.integers) ≠ 0 := by
    intro h
    have : s = 0 := congrArg Subtype.val h
    simp [this] at hs
  set φ := P.completionIntegersEquivPowerSeriesResidueField ht ⟨s, hsint⟩
  have hφ : φ.order = 1 := by
    rw [order_completionIntegersEquivPowerSeriesResidueField _ _ _ hs0]
    simp [hs]
  have hΦφ : Φt s = φ := P.completionEquivLaurentSeriesResidueField_apply_integer ht ⟨s, hsint⟩
  -- Passing from the expansion in `s` to the expansion in `t` is a substitution `T ↦ φ`: it
  -- fixes the constants, which both expansions read in the coefficient field, and it preserves
  -- the valuation.
  set ψ := (Φs.symm.trans Φt).toRingHom
  have hψ (f : LaurentSeries P.ResidueField) : ψ f = Φt (Φs.symm f) := (rfl)
  have h := LaurentSeries.coeff_neg_one_map_mul_derivative ψ
    (fun c ↦ by
      rw [hψ, ← P.completionEquivLaurentSeriesResidueField_completionResidueFieldSection hs c,
        AlgEquiv.symm_apply_apply,
        P.completionEquivLaurentSeriesResidueField_completionResidueFieldSection ht c,
        P.completionEquivLaurentSeriesResidueField_completionResidueFieldSection hs c])
    (fun f hf ↦ by
      rw [← Φs.apply_symm_apply f, valuation_completionEquivLaurentSeriesResidueField] at hf
      rwa [hψ, valuation_completionEquivLaurentSeriesResidueField])
    hφ (by
      rw [hψ, ← P.completionEquivLaurentSeriesResidueField_uniformizer hs,
        AlgEquiv.symm_apply_apply, hΦφ])
    (Φs z)
  rwa [hψ, AlgEquiv.symm_apply_apply, ← hΦφ] at h

variable (hs : P.ord s = 1)

/-- **Change of uniformizer for residues at a place with separable residue field.** The residue
`res_{P,s}(z) ∈ F_P` is the coefficient of `T⁻¹` in `z(T) * s'(T)`, where `z(T)` and `s(T)` are
the Laurent expansions of `z` and `s` in another uniformizer `t`, with coefficients in `F_P`
(Stichtenoth, Proposition 4.2.9). -/
theorem residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative
    (z : F) :
    P.residueResidueField hs z = (P.laurentSeriesExpansionResidueField ht z *
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht s)).coeff
        (-1) := by
  rw [residueResidueField_apply, laurentSeriesExpansionResidueField_apply,
    laurentSeriesExpansionResidueField_apply, laurentSeriesExpansionResidueField_apply,
    coeff_neg_one_completionEquivLaurentSeriesResidueField_mul_derivative]

/-- **The transformation formula** `res_{P,s}(z) = res_{P,t}(z · w)` at a place with separable
residue field, for a function `w` whose Laurent expansion in `t` is the derivative of that of
`s`. -/
theorem residueResidueField_eq_residueResidueField_mul {w : F}
    (hw : P.laurentSeriesExpansionResidueField ht w =
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht s))
    (z : F) :
    P.residueResidueField hs z = P.residueResidueField ht (z * w) := by
  rw [P.residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative ht hs,
    residueResidueField_apply, map_mul, hw]

/-- **The transformation formula for `k`-valued residues** `Tr_{F_P/k} res_{P,s}(z) =
Tr_{F_P/k} res_{P,t}(z · w)`, for a function `w` whose Laurent expansion in `t` is the derivative
of that of `s`. -/
theorem traceResidue_eq_traceResidue_mul {w : F}
    (hw : P.laurentSeriesExpansionResidueField ht w =
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht s))
    (z : F) :
    P.traceResidue hs z = P.traceResidue ht (z * w) := by
  rw [traceResidue_apply, traceResidue_apply,
    P.residueResidueField_eq_residueResidueField_mul ht hs hw]

end ResidueField

end TauCeti.Place
