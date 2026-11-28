/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.MvPowerSeries.Order
import Mathlib.Algebra.MvPolynomial.Funext
import TauCeti.RingTheory.MvPowerSeries.Rescale

/-!
# Restricting multivariate power series to lines

Substituting `v i * X` for the `i`-th variable evaluates the degree-`n` homogeneous
polynomial at `v` in coefficient `n`. Over an infinite integral domain this makes the
line restrictions jointly determine the power series. This lets one identify a multivariate
Taylor series using identities of univariate Taylor series in every direction.

The extensionality statement is the one used in `New.mvPowerSeries_eq_of_forall_line`
in `grh/src/New/Derivatives/Vacuum/TightFrames.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

public noncomputable section

open Finsupp

namespace MvPowerSeries

variable {σ R : Type*} [Finite σ]

section CommSemiring

variable [CommSemiring R]

/-- Restriction to the formal line `t ↦ t • v`, sending the `i`-th variable to `v i • X`. -/
def substLine (v : σ → R) : MvPowerSeries σ R →ₐ[R] PowerSeries R :=
  { (rename (fun _ : σ ↦ ()) : MvPowerSeries σ R →ₐ[R] MvPowerSeries Unit R).toRingHom.comp
      (rescale v) with
    commutes' r := by
      -- The inherited `toFun` is the composite ring homomorphism.
      change rename (fun _ : σ ↦ ()) (rescale v (algebraMap R (MvPowerSeries σ R) r)) = _
      have h : rescale v (algebraMap R (MvPowerSeries σ R) r) = algebraMap R _ r := by
        classical
        ext d
        by_cases hd : d = 0 <;> simp [algebraMap_apply, coeff_C, hd]
      rw [h]
      exact (rename (fun _ : σ ↦ ()) : MvPowerSeries σ R →ₐ[R] MvPowerSeries Unit R).commutes r }

/-- Line restriction rescales each variable and then identifies all variables. -/
theorem substLine_apply (v : σ → R) (f : MvPowerSeries σ R) :
    substLine v f = rename (fun _ : σ ↦ ()) (rescale v f) := (rfl)

/-- Restriction sends a coordinate variable to its scalar multiple of the line parameter. -/
@[simp]
theorem substLine_X (v : σ → R) (i : σ) :
    substLine v (X i) = v i • (PowerSeries.X : PowerSeries R) := by
  rw [substLine_apply, rescale_X, map_mul, rename_C, rename_X, Algebra.smul_def,
    ← PowerSeries.C_eq_algebraMap]
  rfl

/-- The `n`-th coefficient of the series on a line is the degree-`n` homogeneous polynomial
of the original series evaluated at the direction of the line. -/
theorem coeff_substLine (v : σ → R) (f : MvPowerSeries σ R) (n : ℕ) :
    PowerSeries.coeff n (substLine v f) =
      MvPolynomial.eval v (homogeneousComponentPolynomial n f) := by
  classical
  have hdegree (d : σ →₀ ℕ) : d.mapDomain (fun _ : σ ↦ ()) = single () n ↔ d.degree = n := by
    have hsingle (x : Unit →₀ ℕ) : x = single () x.degree := by
      have hx := unique_single x
      have hd : x.degree = x () := by simpa only [degree_single] using congrArg degree hx
      rw [hd]
      exact hx
    rw [hsingle (d.mapDomain (fun _ : σ ↦ ())), degree_mapDomain, unique_single_eq_iff]
  have hcoeff (d : σ →₀ ℕ) :
      (homogeneousComponentPolynomial n f).coeff d = if d.degree = n then coeff d f else 0 := by
    rw [← MvPolynomial.coeff_coe, coe_homogeneousComponentPolynomial, coeff_homogeneousComponent]
  rw [substLine_apply, PowerSeries.coeff_def (s := single () n) (single_eq_same ..), coeff_rename,
    MvPolynomial.eval_eq]
  -- The support of the homogeneous polynomial lies in the degree fiber used by renaming.
  symm
  refine (Finset.sum_subset ?_ ?_).trans (Finset.sum_congr rfl ?_)
  · intro d hd
    have h := MvPolynomial.mem_support_iff.mp hd
    rw [hcoeff] at h
    have hd' : d.degree = n := by contrapose! h; simp [h]
    simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] using
      (hdegree d).mpr hd'
  · intro d _ hnot
    rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
  · intro d hd
    have hd' := (hdegree d).mp (by simpa only [Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff] using hd)
    simp [hcoeff, hd', coeff_rescale, Finsupp.prod, mul_comm]

end CommSemiring

section CommRing

variable [CommRing R]

/-- Restriction to a line agrees with substituting the scaled univariate indeterminate. -/
theorem substLine_eq_subst (v : σ → R) (f : MvPowerSeries σ R) :
    substLine v f = f.subst (fun i ↦ v i • (PowerSeries.X : PowerSeries R)) := by
  rw [substLine_apply, rename_eq_subst, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X v) (HasSubst.X_comp _)]
  congr 1
  funext i
  simp [Pi.smul_apply', subst_smul (HasSubst.X_comp _), subst_X (HasSubst.X_comp _),
    PowerSeries.X]

/-- Over an infinite integral domain, two formal power series agree if their restrictions
agree along every line through the origin. -/
theorem eq_of_forall_substLine_eq [IsDomain R] [Infinite R] {f g : MvPowerSeries σ R}
    (h : ∀ v : σ → R, substLine v f = substLine v g) : f = g := by
  ext d
  have hp : homogeneousComponentPolynomial d.degree f = homogeneousComponentPolynomial d.degree g :=
    MvPolynomial.funext fun v ↦ by
      simpa only [coeff_substLine] using congrArg (PowerSeries.coeff d.degree) (h v)
  have hc := congrArg (fun p : MvPolynomial σ R ↦ coeff d (p : MvPowerSeries σ R)) hp
  simpa [coe_homogeneousComponentPolynomial, coeff_homogeneousComponent] using hc

end CommRing

end MvPowerSeries
