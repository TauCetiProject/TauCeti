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
coefficients, at the polyradius `Fin.tail r`. It combines
`MvPowerSeries.IsRestricted.renameAlgEquivOfEq` and
`MvPowerSeries.restrictedOptionEquiv`. After forgetting restrictedness it is Mathlib's
`MvPowerSeries.finSuccEquiv`.
-/

public section

namespace MvPowerSeries

variable {n : ℕ} {r : Fin (n + 1) → ℝ}

local notation "c" => Option.elim' (r 0) (Fin.tail r)

-- The radius equation supplies the source type for the renaming in this construction.
private theorem option_elim_comp_finSuccEquiv : c ∘ _root_.finSuccEquiv n = r := by
  funext i
  cases i using Fin.cases <;>
    simp only [Function.comp_apply, finSuccEquiv_zero, finSuccEquiv_succ, Option.elim',
      Fin.tail_def]

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [∀ i, Fact (0 < r i)]

local instance (i : Option (Fin n)) : Fact (0 < c i) :=
  match i with
  | none => inferInstanceAs (Fact (0 < r 0))
  | some j => inferInstanceAs (Fact (0 < r j.succ))

-- Use composition in the signature so the existing positivity instance applies to `Fin.tail r`.
local notation "Inner" => IsRestricted.subring (R := R) (r ∘ Fin.succ)
local notation "Outer" => PowerSeries.IsRestricted.subring (R := Inner) (r 0)

/-- Split off `X 0` at radius `r 0`, with coefficients restricted at `Fin.tail r`. -/
noncomputable def restrictedFinSuccEquiv :
    IsRestricted.subring (R := R) r ≃ₐ[R] Outer :=
  (IsRestricted.renameAlgEquivOfEq (_root_.finSuccEquiv n) c option_elim_comp_finSuccEquiv).trans
    restrictedOptionEquiv

-- Keep the choice of option radii internal. The coefficient rules below are the simp interface.
private theorem restrictedFinSuccEquiv_apply (f : IsRestricted.subring (R := R) r) :
    restrictedFinSuccEquiv f = restrictedOptionEquiv
      (IsRestricted.renameAlgEquivOfEq (_root_.finSuccEquiv n) c option_elim_comp_finSuccEquiv f) :=
  (rfl)

/-- The square relating restricted and formal iteration commutes as ring homomorphisms. -/
theorem map_subtype_comp_restrictedFinSuccEquiv :
    (PowerSeries.map (Inner).subtype).comp
        ((Outer).subtype.comp (restrictedFinSuccEquiv (R := R) (r := r)).toRingHom) =
      (finSuccEquiv R n).toRingHom.comp (IsRestricted.subring (R := R) r).subtype := by
  ext f : 1
  -- Compare the underlying series using the defining composite of the formal comparison.
  change PowerSeries.map (Inner).subtype (restrictedFinSuccEquiv f : PowerSeries Inner) =
    finSuccEquiv R n (f : MvPowerSeries (Fin (n + 1)) R)
  have h := map_subtype_restrictedOptionEquiv
    (IsRestricted.renameAlgEquivOfEq (_root_.finSuccEquiv n) c option_elim_comp_finSuccEquiv f)
  rw [IsRestricted.coe_renameAlgEquivOfEq] at h
  rw [restrictedFinSuccEquiv_apply]
  exact h

/-- Taking first the coefficient of degree `k` in `X 0` and then the coefficient at `t` in the
remaining variables gives the original coefficient at `t.cons k`. -/
@[simp]
theorem coeff_coeff_restrictedFinSuccEquiv (f : IsRestricted.subring (R := R) r)
    (k : ℕ) (t : Fin n →₀ ℕ) :
    coeff t (PowerSeries.coeff (R := Inner) k (restrictedFinSuccEquiv f : PowerSeries Inner) :
      MvPowerSeries (Fin n) R) = coeff (t.cons k) (f : MvPowerSeries (Fin (n + 1)) R) := by
  have h : PowerSeries.map (Inner).subtype (restrictedFinSuccEquiv f : PowerSeries Inner) =
      finSuccEquiv R n (f : MvPowerSeries (Fin (n + 1)) R) :=
    DFunLike.congr_fun map_subtype_comp_restrictedFinSuccEquiv f
  simpa only [PowerSeries.coeff_map, Subring.subtype_apply, coeff_coeff_finSuccEquiv] using
    congrArg (fun F ↦ coeff t (PowerSeries.coeff k F)) h

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
theorem restrictedFinSuccEquiv_X_zero :
    (restrictedFinSuccEquiv (⟨X 0, isRestricted_X r 0⟩ :
      IsRestricted.subring (R := R) r) : PowerSeries Inner) = PowerSeries.X := by
  apply PowerSeries.map_injective (Inner).subtype Subtype.val_injective
  let f : IsRestricted.subring (R := R) r := ⟨X 0, isRestricted_X r 0⟩
  have h : PowerSeries.map (Inner).subtype (restrictedFinSuccEquiv f : PowerSeries Inner) =
      finSuccEquiv R n (X 0) :=
    DFunLike.congr_fun map_subtype_comp_restrictedFinSuccEquiv f
  simpa only [finSuccEquiv_X_zero, PowerSeries.map_X, Subring.subtype_apply] using h

/-- Each remaining variable becomes an outer constant with value the corresponding
variable of the coefficient algebra. -/
@[simp]
theorem restrictedFinSuccEquiv_X_succ (i : Fin n) :
    (restrictedFinSuccEquiv (⟨X i.succ, isRestricted_X r i.succ⟩ :
      IsRestricted.subring (R := R) r) : PowerSeries Inner) =
        PowerSeries.C ⟨X i, isRestricted_X _ i⟩ := by
  apply PowerSeries.map_injective (Inner).subtype Subtype.val_injective
  let f : IsRestricted.subring (R := R) r := ⟨X i.succ, isRestricted_X r i.succ⟩
  have h : PowerSeries.map (Inner).subtype (restrictedFinSuccEquiv f : PowerSeries Inner) =
      finSuccEquiv R n (X i.succ) :=
    DFunLike.congr_fun map_subtype_comp_restrictedFinSuccEquiv f
  simpa only [finSuccEquiv_X_succ, PowerSeries.map_C, Subring.subtype_apply] using h

/-- Splitting off the first variable is an isometry for the Gauss norms. -/
theorem isometry_restrictedFinSuccEquiv :
    Isometry (restrictedFinSuccEquiv (R := R) (r := r)) := by
  refine (AddMonoidHomClass.isometry_iff_norm _).mpr fun f ↦ ?_
  have h := norm_restrictedOptionEquiv
    (IsRestricted.renameAlgEquivOfEq (_root_.finSuccEquiv n) c option_elim_comp_finSuccEquiv f)
  rw [IsRestricted.norm_renameAlgEquivOfEq] at h
  rw [restrictedFinSuccEquiv_apply]
  exact h

end MvPowerSeries
