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

The coefficient of `T^n` in `f(v₁T, …, vₖT)` is the degree-`n` homogeneous
part of `f` evaluated at the direction `v`. Over an infinite integral domain, this
lets one compare multivariate jets by comparing their restrictions to lines through zero.

The line test for jets is used in `New.mvPowerSeries_eq_of_forall_line` in
`New/Derivatives/Vacuum/TightFrames.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

namespace MvPowerSeries

variable {σ R : Type*} [Finite σ]

/-- Restrict a formal power series to the line through zero with direction `v`,
by substituting `v i • T` for each variable `i`. -/
noncomputable def substLine [CommSemiring R] (v : σ → R) :
    MvPowerSeries σ R →ₐ[R] PowerSeries R where
  toRingHom := (rename (fun _ : σ ↦ ())).toRingHom.comp (rescale v)
  commutes' r := by
    have hC : rescale v (C r) = C r := by
      classical
      ext d
      rw [coeff_rescale, coeff_C]
      by_cases hd : d = 0 <;> simp [hd]
    -- The structure field is phrased using the inherited `toFun` projection.
    change rename (fun _ : σ ↦ ()) (rescale v (algebraMap R (MvPowerSeries σ R) r)) = _
    rw [← c_eq_algebraMap, hC, rename_C, PowerSeries.algebraMap_eq, PowerSeries.C_apply]

/-- Restrict to a line by scaling the variables and then identifying them. -/
theorem substLine_eq_rename_rescale [CommSemiring R] (v : σ → R) (f : MvPowerSeries σ R) :
    substLine v f = rename (fun _ : σ ↦ ()) (rescale v f) := (rfl)

/-- The line restriction agrees with formal substitution of the scaled univariate variable. -/
theorem substLine_eq_subst [CommRing R] (v : σ → R) (f : MvPowerSeries σ R) :
    substLine v f = f.subst (fun i ↦ v i • (PowerSeries.X : PowerSeries R)) := by
  rw [substLine_eq_rename_rescale, rescale_eq_subst, rename_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X v) (HasSubst.X_comp _)]
  congr 1
  funext i
  simp only [Pi.smul_apply', subst_smul (HasSubst.X_comp _), subst_X (HasSubst.X_comp _),
    PowerSeries.X_apply, Function.comp_apply]

/-- The `i`-th variable restricts to the univariate variable scaled by `v i`. -/
@[simp]
theorem substLine_X [CommSemiring R] (v : σ → R) (i : σ) :
    substLine v (X i) = v i • (PowerSeries.X : PowerSeries R) := by
  rw [substLine_eq_rename_rescale, rescale_X, map_mul, rename_X, rename_C,
    PowerSeries.X_apply, c_eq_algebraMap, ← Algebra.smul_def]

/-- A constant has the same value after restriction to a line. -/
@[simp]
theorem substLine_C [CommSemiring R] (v : σ → R) (r : R) :
    substLine v (C r) = PowerSeries.C r := by
  simpa only [← c_eq_algebraMap, PowerSeries.algebraMap_eq, PowerSeries.C_apply] using
    (substLine v).commutes r

/-- Restriction to a line through zero preserves the constant coefficient. -/
@[simp]
theorem constantCoeff_substLine [CommSemiring R] (v : σ → R) (f : MvPowerSeries σ R) :
    PowerSeries.constantCoeff (substLine v f) = constantCoeff f := by
  rw [PowerSeries.constantCoeff_eq, substLine_eq_rename_rescale, constantCoeff_rename,
    ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp

/-- The coefficient of degree `n` of a line restriction is the value of the degree-`n`
homogeneous part at the direction of the line. -/
theorem coeff_substLine [CommSemiring R] (v : σ → R) (f : MvPowerSeries σ R) (n : ℕ) :
    PowerSeries.coeff n (substLine v f) =
      MvPolynomial.eval v (homogeneousComponentPolynomial n f) := by
  classical
  rw [substLine_eq_rename_rescale, PowerSeries.coeff_def Finsupp.single_eq_same,
    coeff_rename, MvPolynomial.eval_eq]
  have hcoeff (d : σ →₀ ℕ) : (homogeneousComponentPolynomial n f).coeff d =
      if d.degree = n then coeff d f else 0 := by
    rw [← MvPolynomial.coeff_coe, coe_homogeneousComponentPolynomial, coeff_homogeneousComponent]
  -- Identifying the variables with the single variable collects exactly one total degree.
  have hdegree (d : σ →₀ ℕ) : d.mapDomain (fun _ ↦ ()) = Finsupp.single () n ↔ d.degree = n := by
    constructor
    · intro h
      simpa only [Finsupp.degree_mapDomain, Finsupp.degree_single] using congrArg Finsupp.degree h
    · intro hd
      let e := d.mapDomain (fun _ ↦ ())
      have he := Finsupp.unique_single e
      have hn : e () = n := by
        calc
          e () = e.degree := by
            simpa only [Finsupp.degree_single] using (congrArg Finsupp.degree he).symm
          _ = n := (Finsupp.degree_mapDomain _ d).trans hd
      exact he.trans (congrArg (Finsupp.single ()) hn)
  have hs : (homogeneousComponentPolynomial n f).support ⊆
      (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset := by
    intro d hd
    by_contra h
    have hn : d.degree ≠ n := fun hn ↦ h ((Set.Finite.mem_toFinset _).mpr hn)
    exact (MvPolynomial.mem_support_iff.mp hd) (by simp [hcoeff, hn])
  refine Eq.trans ?_ (Finset.sum_subset (f := fun d ↦
    (homogeneousComponentPolynomial n f).coeff d * ∏ i ∈ d.support, v i ^ d i) hs
    (fun d _ hd ↦ by simp [MvPolynomial.notMem_support_iff.mp hd])).symm
  have hfiber : (Filter.TendstoCofinite.finite_preimage_singleton
      (Finsupp.mapDomain (fun _ : σ ↦ ())) (Finsupp.single () n)).toFinset =
        (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset := by
    ext d
    simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      using hdegree d
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d.degree = n := (Set.Finite.mem_toFinset _).mp hd
  simp only [coeff_rescale, hcoeff, ite_eq_left hdn, Finsupp.prod, mul_comm]

variable [CommRing R]

/-- Line restrictions in an infinite box of directions determine a power series over
an integral domain. The coordinate sets may differ from one variable to the next. -/
theorem ext_of_forall_substLine_eq_on [IsDomain R] {s : σ → Set R}
    (hs : ∀ i, (s i).Infinite) {f g : MvPowerSeries σ R}
    (h : ∀ v ∈ Set.pi Set.univ s, substLine v f = substLine v g) : f = g := by
  ext d
  have hp : homogeneousComponentPolynomial d.degree f = homogeneousComponentPolynomial d.degree g :=
    MvPolynomial.funext_set s hs fun v hv ↦ by
      simpa only [coeff_substLine] using congrArg (PowerSeries.coeff d.degree) (h v hv)
  have hc := congrArg (fun p : MvPolynomial σ R ↦ coeff d (p : MvPowerSeries σ R)) hp
  simpa only [coe_homogeneousComponentPolynomial, coeff_homogeneousComponent, ite_true] using hc

/-- Over an infinite integral domain, equality on every line through zero implies equality
of multivariate formal power series. -/
theorem ext_of_forall_substLine_eq [IsDomain R] [Infinite R] {f g : MvPowerSeries σ R}
    (h : ∀ v, substLine v f = substLine v g) : f = g :=
  ext_of_forall_substLine_eq_on (s := fun _ ↦ Set.univ) (fun _ ↦ Set.infinite_univ) fun v _ ↦ h v

end MvPowerSeries
