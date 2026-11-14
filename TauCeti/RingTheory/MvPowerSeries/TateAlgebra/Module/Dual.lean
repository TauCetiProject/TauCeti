/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Expand

/-!
# Continuous-dual projections on restricted coefficient families

Over a nontrivially normed ultrametric field `K`, any continuous `K`-linear functional
`f_dual : StrongDual K E` on an ultrametric seminormed `K`-module `E` is operator-norm bounded, so
applying it coefficientwise via `IsRestrictedFamily.toSubringDualOfBound` defines a
`K{X / c}`-linear functional `IsRestrictedFamily.toSubringDual` on
`IsRestrictedFamily.addSubgroup E c`.

Combined with `restrictedExpandComponentFamily`, this yields Gauss-norm-bounded `K{X / c}`-linear
projections (`norm_toSubringDual_restrictedExpandComponentFamily_le`) that separate nonzero series
in `K'{X / r}` with coefficients in a `K`-submodule `E ⊆ K'` whenever `StrongDual K E` separates
points (`exists_toSubringDual_restrictedExpandComponentFamily_ne_zero`).
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section SubringDual

variable {σ K E : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace K E] {c : σ → ℝ}

namespace IsRestrictedFamily

/-- Applying a continuous `K`-linear functional `f_dual : StrongDual K E` coefficientwise to an
`E`-valued restricted family produces a `K{X / c}`-linear functional on
`IsRestrictedFamily.addSubgroup E c`. -/
noncomputable def toSubringDual (f_dual : StrongDual K E) :
    Module.Dual (IsRestricted.subring (R := K) c) (IsRestrictedFamily.addSubgroup E c) :=
  toSubringDualOfBound f_dual.toLinearMap f_dual.le_opNorm

@[simp]
theorem coeff_coe_toSubringDual (f_dual : StrongDual K E)
    (v : IsRestrictedFamily.addSubgroup E c) (α : σ →₀ ℕ) :
    _root_.MvPowerSeries.coeff α (toSubringDual f_dual v : _root_.MvPowerSeries σ K) =
      f_dual ((v : (σ →₀ ℕ) → E) α) :=
  coeff_coe_toSubringDualOfBound f_dual.toLinearMap f_dual.le_opNorm v α

end IsRestrictedFamily

end SubringDual

section ComponentDual

variable {σ K K' : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NormedCommRing K'] [IsUltrametricDist K'] [NormedAlgebra K K']

/-- Gauss-norm bound on `toSubringDual f_dual (restrictedExpandComponentFamily hq hr ν E z hz)`. -/
theorem norm_toSubringDual_restrictedExpandComponentFamily_le
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K') (f_dual : StrongDual K E)
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ‖IsRestrictedFamily.toSubringDual f_dual (restrictedExpandComponentFamily hq hr ν E z hz)‖ ≤
      (‖f_dual‖ / ν.prod (r · ^ ·)) * ‖z‖ :=
  norm_toSubringDualOfBound_restrictedExpandComponentFamily_le hq hr ν E f_dual.toLinearMap
    (norm_nonneg f_dual) f_dual.le_opNorm z hz

/-- When `StrongDual K E` separates points of `E`, any nonzero restricted series `z ∈ K'{X / r}`
whose coefficients lie in `E` has a nonzero projection
`toSubringDual f_dual (restrictedExpandComponentFamily hq hr ν E z hz)` for some remainder `ν`
(`∀ i, ν i < q`) and some `f_dual : StrongDual K E`. -/
theorem exists_toSubringDual_restrictedExpandComponentFamily_ne_zero
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (E : Submodule K K') [SeparatingDual K E]
    {z : IsRestricted.subring (R := K') r} (hz_ne : z ≠ 0)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ∃ (ν : σ →₀ ℕ) (_ : ∀ i, ν i < q) (f_dual : StrongDual K E),
      IsRestrictedFamily.toSubringDual f_dual
        (restrictedExpandComponentFamily hq hr ν E z hz) ≠ 0 := by
  obtain ⟨ν, hν, μ, hμE_ne⟩ :=
    exists_coeff_restrictedExpandComponentFamily_ne_zero hq hr E hz_ne hz
  obtain ⟨f_dual, hf_ne⟩ := SeparatingDual.exists_ne_zero (R := K) hμE_ne
  refine ⟨ν, hν, f_dual, fun h0 ↦ ?_⟩
  have hcoeff0 : coeff μ (IsRestrictedFamily.toSubringDual f_dual
      (restrictedExpandComponentFamily hq hr ν E z hz) : _root_.MvPowerSeries σ K) = 0 := by
    rw [h0, ZeroMemClass.coe_zero, map_zero]
  rw [IsRestrictedFamily.coeff_coe_toSubringDual] at hcoeff0
  exact hf_ne hcoeff0

end ComponentDual

end TauCeti.MvPowerSeries
