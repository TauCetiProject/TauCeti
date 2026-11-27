/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate

/-!
# Splitting the first variable of a restricted power series

`MvPowerSeries.restrictedFinSuccEquiv` is the Gauss-isometric algebra equivalence that treats
`X 0` as the univariate variable and uses restricted series in the remaining variables as
coefficients, at the polyradius `Fin.tail r`. It specializes
`MvPowerSeries.restrictedSplitEquiv`, which combines `MvPowerSeries.IsRestricted.renameAlgEquivOfEq`
and `MvPowerSeries.restrictedOptionEquiv`. Mathlib's `MvPowerSeries.finSuccEquiv` compares the
underlying formal series and gives the coefficient formulas in both directions.
-/

public section

namespace MvPowerSeries

variable {n : ℕ} {r : Fin (n + 1) → ℝ}

local notation "cOption" => Option.elim' (r 0) (Fin.tail r)

-- The radius equation supplies the source type for the renaming in this construction.
private theorem option_elim_comp_finSuccEquiv : cOption ∘ _root_.finSuccEquiv n = r := by
  funext i
  cases i using Fin.cases <;>
    simp only [Function.comp_apply, finSuccEquiv_zero, finSuccEquiv_succ, Option.elim',
      Fin.tail_def]

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [∀ i, Fact (0 < r i)]

local instance (i : Option (Fin n)) : Fact (0 < cOption i) :=
  match i with
  | none => inferInstanceAs (Fact (0 < r 0))
  | some j => inferInstanceAs (Fact (0 < r j.succ))

-- Use composition in the signature so the existing positivity instance applies to `Fin.tail r`.
local notation "Inner" => IsRestricted.subring (R := R) (r ∘ Fin.succ)
local notation "Outer" => PowerSeries.IsRestricted.subring (R := Inner) (r 0)

/-- Split off `X 0` at radius `r 0`, with coefficients restricted at `Fin.tail r`. -/
noncomputable def restrictedFinSuccEquiv :
    IsRestricted.subring (R := R) r ≃ₐ[R] Outer :=
  restrictedSplitEquiv (c := cOption) (_root_.finSuccEquiv n) option_elim_comp_finSuccEquiv

/-- After forgetting restrictedness, splitting off the first variable agrees with Mathlib's
formal comparison. -/
@[simp]
theorem map_subtype_restrictedFinSuccEquiv (f : IsRestricted.subring (R := R) r) :
    PowerSeries.map (Inner).subtype (restrictedFinSuccEquiv f : PowerSeries Inner) =
      finSuccEquiv R n (f : MvPowerSeries (Fin (n + 1)) R) := by
  simpa only [restrictedFinSuccEquiv, finSuccEquiv, AlgEquiv.trans_apply] using!
    map_subtype_restrictedSplitEquiv (c := cOption) (_root_.finSuccEquiv n)
      option_elim_comp_finSuccEquiv f

/-- Flattening agrees with the inverse of Mathlib's formal comparison. -/
theorem coe_restrictedFinSuccEquiv_symm (g : Outer) :
    (restrictedFinSuccEquiv.symm g : MvPowerSeries (Fin (n + 1)) R) =
      (finSuccEquiv R n).symm (PowerSeries.map (Inner).subtype (g : PowerSeries Inner)) := by
  apply (finSuccEquiv R n).injective
  rw [AlgEquiv.apply_symm_apply, ← map_subtype_restrictedFinSuccEquiv, AlgEquiv.apply_symm_apply]

/-- Taking first the coefficient of degree `k` in `X 0` and then the coefficient at `t` in the
remaining variables gives the original coefficient at `t.cons k`. -/
@[simp]
theorem coeff_coeff_restrictedFinSuccEquiv (f : IsRestricted.subring (R := R) r)
    (k : ℕ) (t : Fin n →₀ ℕ) :
    coeff t (PowerSeries.coeff (R := Inner) k (restrictedFinSuccEquiv f : PowerSeries Inner) :
      MvPowerSeries (Fin n) R) = coeff (t.cons k) (f : MvPowerSeries (Fin (n + 1)) R) := by
  simpa only [PowerSeries.coeff_map, Subring.subtype_apply, coeff_coeff_finSuccEquiv] using
    congrArg (fun F ↦ coeff t (PowerSeries.coeff k F)) (map_subtype_restrictedFinSuccEquiv f)

/-- The coefficient at `t` after flattening is read at degree `t 0` in the outer series
and at `t.tail` in the coefficient series. -/
@[simp]
theorem coeff_restrictedFinSuccEquiv_symm (f : Outer) (t : Fin (n + 1) →₀ ℕ) :
    coeff t ((restrictedFinSuccEquiv.symm f : IsRestricted.subring (R := R) r) :
      MvPowerSeries (Fin (n + 1)) R) =
      coeff t.tail (PowerSeries.coeff (R := Inner) (t 0) (f : PowerSeries Inner) :
        MvPowerSeries (Fin n) R) := by
  simpa only [AlgEquiv.apply_symm_apply, Finsupp.cons_tail] using
    (coeff_coeff_restrictedFinSuccEquiv (restrictedFinSuccEquiv.symm f) (t 0) t.tail).symm

/-- The first variable becomes the outer univariate variable. -/
@[simp]
theorem coe_restrictedFinSuccEquiv_X_zero :
    (restrictedFinSuccEquiv (⟨X 0, isRestricted_X r 0⟩ :
      IsRestricted.subring (R := R) r) : PowerSeries Inner) = PowerSeries.X := by
  simpa only [restrictedFinSuccEquiv, finSuccEquiv_symm_none] using!
    (coe_restrictedSplitEquiv_X_none (R := R) (c := cOption) (_root_.finSuccEquiv n)
      option_elim_comp_finSuccEquiv)

/-- Each remaining variable becomes an outer constant with value the corresponding
variable of the coefficient algebra. -/
@[simp]
theorem coe_restrictedFinSuccEquiv_X_succ (i : Fin n) :
    (restrictedFinSuccEquiv (⟨X i.succ, isRestricted_X r i.succ⟩ :
      IsRestricted.subring (R := R) r) : PowerSeries Inner) =
        PowerSeries.C ⟨X i, isRestricted_X _ i⟩ := by
  simpa only [restrictedFinSuccEquiv, finSuccEquiv_symm_some] using!
    (coe_restrictedSplitEquiv_X_some (R := R) (c := cOption) (_root_.finSuccEquiv n)
      option_elim_comp_finSuccEquiv i)

/-- Splitting off the first variable preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedFinSuccEquiv (f : IsRestricted.subring (R := R) r) :
    ‖restrictedFinSuccEquiv f‖ = ‖f‖ :=
  norm_restrictedSplitEquiv (c := cOption) (_root_.finSuccEquiv n) option_elim_comp_finSuccEquiv f

/-- Splitting off the first variable is an isometry for the Gauss norms. -/
theorem isometry_restrictedFinSuccEquiv :
    Isometry (restrictedFinSuccEquiv (R := R) (r := r)) :=
  isometry_restrictedSplitEquiv (c := cOption) (_root_.finSuccEquiv n)
    option_elim_comp_finSuccEquiv

end MvPowerSeries
