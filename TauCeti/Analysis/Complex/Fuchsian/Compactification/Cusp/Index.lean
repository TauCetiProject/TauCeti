/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Cusp.Ramification
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Tower

/-!
# The cusp index as a local ramification exponent

The canonical width index of compatible cusp data is the exponent of the compactified
quotient map in their cusp coordinates. Its tower law therefore describes composition of
these local power maps, including at the adjoined cusp.

The cusp-coordinate convention follows Diamond and Shurman, *A First Course in Modular
Forms*, §2.4.
-/

public noncomputable section

open TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Δ Γ : Subgroup PSL(2, ℝ)}
variable [DiscreteTopology Δ] [DiscreteTopology Γ]

/-- The compactified quotient map has local exponent equal to the canonical cusp width index. -/
theorem cuspChart_compactifiedQuotientMap_eq_pow_widthIndex (h : Δ ≤ Γ)
    (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : D.cusp = E.cusp) (hσ : D.scaling = E.scaling)
    {A : ℝ} (hD : D.width ≤ A)
    {x : Δ.CompactifiedQuotient} (hx : x ∈ cuspNhd D A) :
    cuspChart E (width_le_of_width_eq_nat_mul D E
      (width_eq_widthIndex_mul h D E hc hσ) hD) (compactifiedQuotientMap h x) =
      (cuspChart D hD x) ^ widthIndex h D E hc hσ :=
  cuspChart_compactifiedQuotientMap_eq_pow h D E hc hσ
    (width_eq_widthIndex_mul h D E hc hσ) hD hx

end Subgroup.CompactifiedQuotient
