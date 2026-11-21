/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial

/-!
# Splitting `Fin (k + m)` in Gauss-normed restricted power series

For positive polyradii `r : Fin (k + m) → ℝ`, splitting the variables into the first `k` indices
`Fin.castAdd m i` and the last `m` indices `Fin.natAdd k j` identifies restricted series in `k + m`
variables with restricted series in the last `m` variables over the ring of restricted series in
the first `k` variables:

```text
R{X₁/r₁, …, X_{k+m}/r_{k+m}} ≅ R{X₁/r₁, …, Xₖ/rₖ}{X_{k+1}/r_{k+1}, …, X_{k+m}/r_{k+m}}.
```

The splitting isomorphisms `TauCeti.MvPowerSeries.restrictedFinAddEquiv` and
`TauCeti.MvPowerSeries.restrictedFinAddAlgEquiv`, together with their values on variables and
their Gauss-norm preservation, are defined in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Sum`.
This file computes their coefficients across `finSumFinEquiv`, by comparing with the direct
construction that reindexes `Fin (k + m)` to `Fin m ⊕ Fin k` via
`finSumFinEquiv.symm.trans (Equiv.sumComm _ _)` and then applies `restrictedSumEquiv`.

## Main results

* `TauCeti.MvPowerSeries.coeff_coeff_restrictedFinAddEquiv` and
  `TauCeti.MvPowerSeries.coeff_restrictedFinAddEquiv_symm`: the coefficient formulas across
  `finSumFinEquiv`.
* `TauCeti.MvPowerSeries.restrictedFinAddEquiv_symm_algebraMap_X` and
  `TauCeti.MvPowerSeries.restrictedFinAddEquiv_symm_X`: the inverse on variables.
* `TauCeti.MvPowerSeries.restrictedFinAddEquiv_polynomialToRestricted`: compatibility with
  multivariate polynomial inclusions.
* `TauCeti.MvPowerSeries.restrictedFinAddEquiv_restrictedMap`: compatibility with bounded
  coefficient maps.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section Split

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {r : Fin (k + m) → ℝ} [∀ l, Fact (0 < r l)]

local notation "Inner" => IsRestricted.subring (R := R) (r ∘ Fin.castAdd m)
local notation "Flat" => IsRestricted.subring (R := R) r
local notation "Iter" => IsRestricted.subring (R := Inner) (r ∘ Fin.natAdd k)

/-- The bijection sending the first `k` indices of `Fin (k + m)` to `.inr` (the inner variables of
`restrictedSumEquiv`) and the last `m` indices to `.inl` (the outer variables). -/
private def finAddSwapEquiv (k m : ℕ) : Fin (k + m) ≃ Fin m ⊕ Fin k :=
  finSumFinEquiv.symm.trans (Equiv.sumComm (Fin k) (Fin m))

private theorem finAddSwapEquiv_castAdd (i : Fin k) :
    finAddSwapEquiv k m (Fin.castAdd m i) = .inr i := by
  simp [finAddSwapEquiv, finSumFinEquiv_symm_apply_castAdd]

private theorem finAddSwapEquiv_natAdd (j : Fin m) :
    finAddSwapEquiv k m (Fin.natAdd k j) = .inl j := by
  simp [finAddSwapEquiv, finSumFinEquiv_symm_apply_natAdd]

private theorem sumElim_comp_finAddSwapEquiv (r : Fin (k + m) → ℝ) :
    Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m) ∘ finAddSwapEquiv k m = r := by
  funext l
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) l
  · simp [finAddSwapEquiv_castAdd]
  · simp [finAddSwapEquiv_natAdd]

/-- The splitting isomorphism built directly from `finAddSwapEquiv` and `restrictedSumEquiv`; it
agrees with `restrictedFinAddEquiv` (see `restrictedFinAddEquiv_apply_eq_aux`) and is used to
compute coefficients. -/
private noncomputable def finAddEquivAux : Flat ≃+* Iter :=
  (IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
    (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
    (sumElim_comp_finAddSwapEquiv r)).toRingEquiv.trans restrictedSumEquiv

private theorem finAddEquivAux_algebraMap (s : R) :
    finAddEquivAux (algebraMap R Flat s) = algebraMap R Iter s := by
  have hs :
      IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
          (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (sumElim_comp_finAddSwapEquiv r) (algebraMap R Flat s) =
        algebraMap R _ s := by
    apply Subtype.ext
    simp
  simp only [finAddEquivAux, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hs,
    restrictedSumEquiv_algebraMap]

private theorem finAddEquivAux_X_castAdd (i : Fin k) :
    finAddEquivAux (⟨X (Fin.castAdd m i), isRestricted_X r _⟩ : Flat) =
      algebraMap Inner Iter ⟨X i, isRestricted_X (r ∘ Fin.castAdd m) i⟩ := by
  have hX :
      IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
          (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (sumElim_comp_finAddSwapEquiv r) ⟨X (Fin.castAdd m i), isRestricted_X r _⟩ =
        (⟨X (.inr i), isRestricted_X _ _⟩ :
          IsRestricted.subring (R := R) (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))) := by
    apply Subtype.ext
    simp [IsRestricted.coe_renameAlgEquivOfEq, finAddSwapEquiv_castAdd]
  simp only [finAddEquivAux, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hX,
    restrictedSumEquiv_X_inr]

private theorem finAddEquivAux_X_natAdd (j : Fin m) :
    finAddEquivAux (⟨X (Fin.natAdd k j), isRestricted_X r _⟩ : Flat) =
      ⟨X j, isRestricted_X (r ∘ Fin.natAdd k) j⟩ := by
  have hX :
      IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
          (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (sumElim_comp_finAddSwapEquiv r) ⟨X (Fin.natAdd k j), isRestricted_X r _⟩ =
        (⟨X (.inl j), isRestricted_X _ _⟩ :
          IsRestricted.subring (R := R) (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))) := by
    apply Subtype.ext
    simp [IsRestricted.coe_renameAlgEquivOfEq, finAddSwapEquiv_natAdd]
  simp only [finAddEquivAux, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hX,
    restrictedSumEquiv_X_inl]

private theorem continuous_finAddEquivAux : Continuous (finAddEquivAux (R := R) (r := r)) :=
  (AddMonoidHomClass.isometry_iff_norm _ |>.mpr fun f ↦ by
    simp only [finAddEquivAux, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      norm_restrictedSumEquiv, IsRestricted.norm_renameAlgEquivOfEq]).continuous

/-- `restrictedFinAddEquiv` agrees with `finAddEquivAux`: both are continuous and agree on
polynomials, which are dense. -/
private theorem restrictedFinAddEquiv_apply_eq_aux (f : Flat) :
    restrictedFinAddEquiv f = finAddEquivAux f := by
  have hpoly : (restrictedFinAddEquiv (R := R) (r := r)).toRingHom.comp
        (polynomialToRestricted (R := R) r).toRingHom =
      (finAddEquivAux (R := R) (r := r)).toRingHom.comp
        (polynomialToRestricted (R := R) r).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun l ↦ ?_)
    · have hC : (polynomialToRestricted (R := R) r).toRingHom (MvPolynomial.C a) =
          algebraMap R Flat a := (polynomialToRestricted (R := R) r).commutes a
      simp only [RingHom.coe_comp, Function.comp_apply, hC, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, restrictedFinAddEquiv_algebraMap, finAddEquivAux_algebraMap]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        polynomialToRestricted_X, RingEquiv.toRingHom_eq_coe]
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) l
      · rw [restrictedFinAddEquiv_X_castAdd, finAddEquivAux_X_castAdd]
      · rw [restrictedFinAddEquiv_X_natAdd, finAddEquivAux_X_natAdd]
  exact congrFun (denseRange_polynomialToRestricted.equalizer
    isometry_restrictedFinAddEquiv.continuous continuous_finAddEquivAux
    (funext fun p ↦ DFunLike.congr_fun hpoly p)) f

private theorem equivMapDomain_finAddSwapEquiv (a : Fin m →₀ ℕ) (b : Fin k →₀ ℕ) :
    ((b.sumElim a).equivMapDomain finSumFinEquiv).equivMapDomain (finAddSwapEquiv k m) =
      a.sumElim b := by
  ext s
  rcases s with j | i
  · simp [finAddSwapEquiv, Finsupp.equivMapDomain_apply]
  · simp [finAddSwapEquiv, Finsupp.equivMapDomain_apply]

/-- The coefficient of `xᵇ` in the coefficient of `yᵃ` of `restrictedFinAddEquiv f` is the
coefficient of `f` at `b` and `a` concatenated along `finSumFinEquiv`. -/
@[simp]
theorem coeff_coeff_restrictedFinAddEquiv (f : Flat) (a : Fin m →₀ ℕ) (b : Fin k →₀ ℕ) :
    coeff b ((coeff a (restrictedFinAddEquiv f : MvPowerSeries (Fin m) Inner) : Inner) :
        MvPowerSeries (Fin k) R) =
      coeff ((b.sumElim a).equivMapDomain finSumFinEquiv) (f : MvPowerSeries (Fin (k + m)) R) := by
  rw [restrictedFinAddEquiv_apply_eq_aux]
  simp [finAddEquivAux, ← equivMapDomain_finAddSwapEquiv a b]

/-- The coefficient of `restrictedFinAddEquiv.symm g` at `b` and `a` concatenated along
`finSumFinEquiv` is the `b`-th inner coefficient of the `a`-th outer coefficient of `g`. -/
@[simp]
theorem coeff_restrictedFinAddEquiv_symm (g : Iter) (a : Fin m →₀ ℕ) (b : Fin k →₀ ℕ) :
    coeff ((b.sumElim a).equivMapDomain finSumFinEquiv)
        (restrictedFinAddEquiv.symm g : MvPowerSeries (Fin (k + m)) R) =
      coeff b ((coeff a (g : MvPowerSeries (Fin m) Inner) : Inner) : MvPowerSeries (Fin k) R) := by
  rw [← coeff_coeff_restrictedFinAddEquiv, RingEquiv.apply_symm_apply]

/-- The inverse of `restrictedFinAddEquiv` sends an inner variable viewed as a constant to the
corresponding variable among the first `k` indices. -/
@[simp]
theorem restrictedFinAddEquiv_symm_algebraMap_X (i : Fin k) :
    restrictedFinAddEquiv.symm
        (algebraMap Inner Iter ⟨X i, isRestricted_X (r ∘ Fin.castAdd m) i⟩) =
      ⟨X (Fin.castAdd m i), isRestricted_X r _⟩ := by
  rw [RingEquiv.symm_apply_eq, restrictedFinAddEquiv_X_castAdd]

/-- The inverse of `restrictedFinAddEquiv` sends the `j`-th outer variable to
`X (Fin.natAdd k j)`. -/
@[simp]
theorem restrictedFinAddEquiv_symm_X (j : Fin m) :
    restrictedFinAddEquiv.symm (⟨X j, isRestricted_X (r ∘ Fin.natAdd k) j⟩ : Iter) =
      ⟨X (Fin.natAdd k j), isRestricted_X r _⟩ := by
  rw [RingEquiv.symm_apply_eq, restrictedFinAddEquiv_X_natAdd]

/-- `restrictedFinAddEquiv` is compatible with the polynomial inclusions: a polynomial in
`Fin (k + m)` maps to the polynomial in the outer `Fin m` variables whose coefficients are its
polynomial slices in the inner `Fin k` variables. -/
theorem restrictedFinAddEquiv_polynomialToRestricted (p : MvPolynomial (Fin (k + m)) R) :
    restrictedFinAddEquiv (polynomialToRestricted r p) =
      polynomialToRestricted (r ∘ Fin.natAdd k)
        ((MvPolynomial.sumAlgEquiv R (Fin m) (Fin k)
          (MvPolynomial.rename (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin k) (Fin m))) p)).map
          (polynomialToRestricted (R := R) (r ∘ Fin.castAdd m) :
            MvPolynomial (Fin k) R →+* Inner)) := by
  have hp :
      IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
          (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (sumElim_comp_finAddSwapEquiv r) (polynomialToRestricted r p) =
        polynomialToRestricted (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (MvPolynomial.rename (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin k) (Fin m))) p) := by
    apply Subtype.ext
    simp [finAddSwapEquiv, rename_coe]
  simp only [restrictedFinAddEquiv_apply_eq_aux, finAddEquivAux, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, hp,
    restrictedSumEquiv_polynomialToRestricted]

end Split

section Map

variable {k m : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {r : Fin (k + m) → ℝ} [∀ l, Fact (0 < r l)]
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- Splitting `Fin (k + m)` commutes with bounded coefficient maps: applying `restrictedMap` on all
`k + m` variables and then splitting agrees with splitting first and applying `restrictedMap`
induced by the inner `restrictedMap`. -/
theorem restrictedFinAddEquiv_restrictedMap (f : IsRestricted.subring (R := R) r) :
    restrictedFinAddEquiv (restrictedMap φ hφ f) =
      restrictedMap (restrictedMap φ hφ) (norm_restrictedMap_le φ hφ)
        (restrictedFinAddEquiv f) := by
  refine Subtype.ext <| MvPowerSeries.ext fun a ↦ Subtype.ext <| MvPowerSeries.ext fun b ↦ ?_
  simp only [coeff_restrictedMap, coeff_coeff_restrictedFinAddEquiv]

end Map

end TauCeti.MvPowerSeries
