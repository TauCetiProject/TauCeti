/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Congruence subgroups as cofinite Fuchsian groups

At every positive level, the effective images of `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)` in
`PSL(2, ℝ)` are cofinite. Their cusp points are precisely the rational boundary points.
The existing finiteness
theorem for cusp orbits therefore applies to their compactified analytic modular curves.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.3–2.4.
-/

public noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint Subgroup CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ) [NeZero N]

/-- The effective image of the principal congruence subgroup is cofinite. -/
theorem isCofinite_Gamma :
    ((Gamma N).map sl2zToPSL2R).IsCofinite :=
  Subgroup.isCofinite_map_sl2zToPSL2R (Gamma N)

/-- The effective image of `Γ₀(N)` is cofinite. -/
theorem isCofinite_Gamma0 :
    ((Gamma0 N).map sl2zToPSL2R).IsCofinite :=
  Subgroup.isCofinite_map_sl2zToPSL2R (Gamma0 N)

/-- The effective image of `Γ₁(N)` is cofinite. -/
theorem isCofinite_Gamma1 :
    ((Gamma1 N).map sl2zToPSL2R).IsCofinite :=
  Subgroup.isCofinite_map_sl2zToPSL2R (Gamma1 N)

/-- A boundary point is a cusp of `Γ(N)` exactly when it is rational. -/
theorem isCuspPoint_Gamma_iff_rat (c : OnePoint ℝ) :
    ((Gamma N).map sl2zToPSL2R).IsCuspPoint c ↔
      c ∈ Set.range (OnePoint.map Rat.cast) :=
  Subgroup.isCuspPoint_map_sl2zToPSL2R_iff_rat (Gamma N) c

/-- A boundary point is a cusp of `Γ₀(N)` exactly when it is rational. -/
theorem isCuspPoint_Gamma0_iff_rat (c : OnePoint ℝ) :
    ((Gamma0 N).map sl2zToPSL2R).IsCuspPoint c ↔
      c ∈ Set.range (OnePoint.map Rat.cast) :=
  Subgroup.isCuspPoint_map_sl2zToPSL2R_iff_rat (Gamma0 N) c

/-- A boundary point is a cusp of `Γ₁(N)` exactly when it is rational. -/
theorem isCuspPoint_Gamma1_iff_rat (c : OnePoint ℝ) :
    ((Gamma1 N).map sl2zToPSL2R).IsCuspPoint c ↔
      c ∈ Set.range (OnePoint.map Rat.cast) :=
  Subgroup.isCuspPoint_map_sl2zToPSL2R_iff_rat (Gamma1 N) c

end TauCeti
