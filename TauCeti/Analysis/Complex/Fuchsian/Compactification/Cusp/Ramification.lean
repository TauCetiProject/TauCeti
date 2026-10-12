/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Cusp.Chart
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.WidthRatio

/-!
# The local form of a compactified quotient map at a cusp

For an inclusion of discrete Fuchsian groups, use cusp data with the same representative and
scaling. The larger group's cusp chart composed with the compactified quotient map is the
`n`-th power of the smaller group's cusp chart, where `n` is the ratio of their widths.
Thus the cusp-width ratio is the local ramification exponent of the map.

The coordinate convention follows Diamond and Shurman, *A First Course in Modular Forms*,
§2.4.
-/

public noncomputable section

open MulAction TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Δ Γ : Subgroup PSL(2, ℝ)}

variable [DiscreteTopology Δ] [DiscreteTopology Γ]

/-- In cusp charts with common scaling, the map of compactified quotients is the power map
whose exponent is the ratio of the cusp widths. -/
theorem cuspChart_compactifiedQuotientMap_eq_pow (h : Δ ≤ Γ)
    (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : D.cusp = E.cusp) (hσ : D.scaling = E.scaling)
    {n : ℕ} (hw : D.width = n * E.width)
    {A : ℝ} (hD : D.width ≤ A)
    {x : Δ.CompactifiedQuotient} (hx : x ∈ cuspNhd D A) :
    cuspChart E (width_le_of_width_eq_nat_mul D E hw hD) (compactifiedQuotientMap h x) =
      (cuspChart D hD x) ^ n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by
    intro hn
    simp only [hn, Nat.cast_zero, zero_mul] at hw
    exact D.width_pos.ne' hw)
  have hE : E.width ≤ A := width_le_of_width_eq_nat_mul D E hw hD
  cases x with
  | ofCusp C =>
      have hC : C = D.cuspOrbit := (ofCusp_mem_cuspNhd_iff D A).mp hx
      subst C
      rw [compactifiedQuotientMap_ofCusp,
        cuspOrbitMap_cuspOrbit_eq_of_cusp_eq h hc.symm,
        cuspChart_ofCusp, cuspChart_ofCusp, zero_pow hn.ne']
  | ofQuotient p =>
      obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D A).mp hx
      have hzE : z ∈ horodisc E A := by
        simpa only [mem_horodisc, ← hσ] using hz
      rw [compactifiedQuotientMap_ofQuotient, TauCeti.Setoid.map_of_le_mk,
        cuspChart_ofQuotient_mk E hE hzE, cuspChart_ofQuotient_mk D hD hz]
      exact (coordinate_pow_eq D E hσ hw z).symm

end Subgroup.CompactifiedQuotient
