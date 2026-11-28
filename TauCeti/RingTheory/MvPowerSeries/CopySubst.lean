/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.Derivative

/-!
# Diagonal copy substitution on multivariate power series

For finite index types X and K and weights  : K → R, the algebra homomorphism
TauCeti.copySubst a : MvPowerSeries X R →ₐ[R] MvPowerSeries (X × K) R sends each variable z_x
to the linear combination ∑ k : K, a k • z_(x, k) of its K-indexed copies.

## Main definitions and results

* TauCeti.copySubst: the diagonal copy substitution F ↦ F (∑ k, a k • z_k).
* TauCeti.pderiv_copySubst: chain rule ∂_(x, k) (copySubst a F) = a k • copySubst a (∂_x F).
* TauCeti.map_copySubst: naturality of copySubst with respect to ring homomorphisms.
* TauCeti.killCompl_copySubst: setting all copies except k to zero recovers escale.
* TauCeti.rescale_copySubst: uniform rescaling commutes with copySubst.

## Provenance

Adapted from New.copySubst, New.pderiv_copySubst, New.map_copySubst,
New.killCompl_copySubst, and New.rescale_copySubst in
src/New/Derivatives/Sharpness/LeastValuation.lean of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
72fead102f663d5c7a407964a13dc0cf9d977207 (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Finset MvPowerSeries

section CopySubst

variable {X K R : Type*} [Fintype X] [Fintype K] [CommRing R]

/-- The substitution F ↦ F (∑ k, a k • z_k) of a linear combination of copies z_k of the
variables z, with the same coefficients  k for all variables. The copy k of the variable
x is (x, k). -/
noncomputable def copySubst (a : K → R) : MvPowerSeries X R →ₐ[R] MvPowerSeries (X × K) R :=
  substAlgHom (a := fun x : X ↦ ∑ k : K, a k • MvPowerSeries.X (x, k))
    (hasSubst_of_constantCoeff_zero (by simp))

/-- Chain rule for diagonal copy substitution: differentiating F (∑ l, a l • z_l) with respect to
the k-th copy of x gives  k times (∂_x F) (∑ l, a l • z_l). -/
theorem pderiv_copySubst (a : K → R) (F : MvPowerSeries X R) (x : X) (k : K) :
    pderiv (x, k) (copySubst a F) = a k • copySubst a (pderiv x F) := by
  classical
  have h_form (y : X) : pderiv (x, k) (∑ k' : K, a k' • MvPowerSeries.X (y, k')) =
      if y = x then a k • (1 : MvPowerSeries (X × K) R) else 0 := by
    simp [pderiv_X, Pi.single_apply, Prod.ext_iff, ite_and]
  have ha : HasSubst fun y : X ↦
      ∑ k' : K, a k' • (MvPowerSeries.X (y, k') : MvPowerSeries (X × K) R) :=
    hasSubst_of_constantCoeff_zero (by simp)
  simp [copySubst, substAlgHom_apply, MvPowerSeries.pderiv_subst ha, h_form, -map_sum]

/-- Diagonal copy substitution commutes with coefficient-ring homomorphisms. -/
theorem map_copySubst {S : Type*} [CommRing S] (f : R →+* S) (a : K → R)
    (F : MvPowerSeries X R) :
    map f (copySubst a F) = copySubst (fun k : K ↦ f (a k)) (map f F) := by
  have ha : HasSubst fun x : X ↦
      ∑ k : K, a k • (MvPowerSeries.X (x, k) : MvPowerSeries (X × K) R) :=
    hasSubst_of_constantCoeff_zero (by simp)
  rw [copySubst, copySubst, substAlgHom_apply, substAlgHom_apply, map_subst ha]
  simp [smul_eq_C_mul]

/-- Setting all copies except the k-th to zero turns F (∑ l, a l • z_l) into F (a k • z). -/
theorem killCompl_copySubst (a : K → R) (F : MvPowerSeries X R) (k : K) :
    killCompl (Function.Embedding.sectL X k) (copySubst a F) = rescale (fun _ : X ↦ a k) F := by
  have ha : HasSubst fun x : X ↦
      ∑ k' : K, a k' • (MvPowerSeries.X (x, k') : MvPowerSeries (X × K) R) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have h_form (x : X) : killCompl (Function.Embedding.sectL X k)
      (∑ k' : K, a k' • MvPowerSeries.X (x, k')) = a k • MvPowerSeries.X (R := R) x := by
    rw [map_sum, sum_eq_single_of_mem k (mem_univ k), map_smul]
    · exact congrArg (a k • ·) (killCompl_X x)
    · exact fun k' _ hk' ↦ by simp [killCompl_X_eq_zero, Prod.ext_iff, hk'.symm]
  ext d
  rw [coeff_killCompl, copySubst, substAlgHom_apply, coeff_subst ha, rescale_eq_subst,
    coeff_subst (HasSubst.smul_X _)]
  refine finsum_congr fun n ↦ ?_
  simp only [← coeff_killCompl, map_finsuppProd, map_pow, h_form, Pi.smul_apply']

/-- Uniform rescaling of all variables by  commutes with diagonal copy substitution. -/
theorem rescale_copySubst (a : K → R) (r : R) (F : MvPowerSeries X R) :
    rescale (fun _ : X × K ↦ r) (copySubst a F) = copySubst a (rescale (fun _ : X ↦ r) F) := by
  have ha : HasSubst fun x : X ↦
      ∑ k : K, a k • (MvPowerSeries.X (x, k) : MvPowerSeries (X × K) R) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hr := HasSubst.smul_X (σ := X × K) (fun _ ↦ r)
  simp only [copySubst, substAlgHom_apply]
  rw [rescale_eq_subst, rescale_eq_subst, subst_comp_subst_apply ha hr,
    subst_comp_subst_apply (HasSubst.smul_X _) ha]
  congr 1
  funext x
  trans ∑ k : K, r • a k • (MvPowerSeries.X (x, k) : MvPowerSeries (X × K) R)
  · simp only [← coe_substAlgHom hr, map_sum, map_smul, substAlgHom_X, Pi.smul_apply', smul_comm r]
  · symm
    rw [Pi.smul_apply', ← coe_substAlgHom ha, map_smul, substAlgHom_X, smul_sum]

end CopySubst

end TauCeti
