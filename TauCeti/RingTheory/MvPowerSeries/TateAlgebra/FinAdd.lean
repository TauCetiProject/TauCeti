/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Splitting `Fin (k + m)` in Gauss-normed restricted power series

For positive polyradii `r : Fin (k + m) → ℝ`, splitting the variables into the first `k` indices
`Fin.castAdd m i` and the last `m` indices `Fin.natAdd k j` identifies restricted series in `k + m`
variables with restricted series in the last `m` variables over the ring of restricted series in
the first `k` variables:

```text
R{X₁/r₁, …, X_{k+m}/r_{k+m}} ≅ R{X₁/r₁, …, Xₖ/rₖ}{X_{k+1}/r_{k+1}, …, X_{k+m}/r_{k+m}}.
```

Because `TauCeti.MvPowerSeries.restrictedSumEquiv` places the outer variables in the left summand
and the inner variables in the right summand, this block decomposition reindexes `Fin (k + m)` to
`Fin m ⊕ Fin k` via `finSumFinEquiv.symm.trans (Equiv.sumComm _ _)` and then applies
`restrictedSumEquiv`. Both factors preserve Gauss norms, so the resulting ring and algebra
equivalences are isometries.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedFinAddEquiv`: the ring isomorphism splitting `Fin (k + m)` into
  an inner `Fin k` block and an outer `Fin m` block.
* `TauCeti.MvPowerSeries.restrictedFinAddAlgEquiv`: the same isomorphism as an `S`-algebra
  equivalence over every coefficient algebra `S` of `R`.

## Main results

* `TauCeti.MvPowerSeries.coeff_coeff_restrictedFinAddEquiv` and
  `TauCeti.MvPowerSeries.coeff_restrictedFinAddEquiv_symm`: the coefficient formulas across
  `finSumFinEquiv`.
* `TauCeti.MvPowerSeries.restrictedFinAddEquiv_X_castAdd` and
  `TauCeti.MvPowerSeries.restrictedFinAddEquiv_X_natAdd`: the first `k` variables become inner
  constants and the last `m` variables become outer variables.
* `TauCeti.MvPowerSeries.restrictedFinAddEquiv_polynomialToRestricted`: compatibility with
  multivariate polynomial inclusions.
* `TauCeti.MvPowerSeries.norm_restrictedFinAddEquiv` and
  `TauCeti.MvPowerSeries.isometry_restrictedFinAddEquiv`: the splitting preserves Gauss norms.
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

/-- **Splitting `Fin (k + m)` in Gauss-normed restricted series.** Restricted series in `k + m`
variables at polyradii `r` are isomorphic as rings to restricted series in the last `m` variables
over restricted series in the first `k` variables. -/
noncomputable def restrictedFinAddEquiv : Flat ≃+* Iter :=
  (IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
    (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
    (sumElim_comp_finAddSwapEquiv r)).toRingEquiv.trans restrictedSumEquiv

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
  simp [restrictedFinAddEquiv, ← equivMapDomain_finAddSwapEquiv a b]

/-- The coefficient of `restrictedFinAddEquiv.symm g` at `b` and `a` concatenated along
`finSumFinEquiv` is the `b`-th inner coefficient of the `a`-th outer coefficient of `g`. -/
@[simp]
theorem coeff_restrictedFinAddEquiv_symm (g : Iter) (a : Fin m →₀ ℕ) (b : Fin k →₀ ℕ) :
    coeff ((b.sumElim a).equivMapDomain finSumFinEquiv)
        (restrictedFinAddEquiv.symm g : MvPowerSeries (Fin (k + m)) R) =
      coeff b ((coeff a (g : MvPowerSeries (Fin m) Inner) : Inner) : MvPowerSeries (Fin k) R) := by
  rw [← coeff_coeff_restrictedFinAddEquiv, RingEquiv.apply_symm_apply]

/-- `restrictedFinAddEquiv` sends constants to constants over any coefficient algebra `S` of `R`. -/
@[simp]
theorem restrictedFinAddEquiv_algebraMap {S : Type*} [CommSemiring S] [Algebra S R] (s : S) :
    restrictedFinAddEquiv (algebraMap S Flat s) = algebraMap S Iter s := by
  have hs :
      IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
          (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (sumElim_comp_finAddSwapEquiv r) (algebraMap S Flat s) =
        algebraMap S _ s := by
    apply Subtype.ext
    simp [IsRestricted.coe_renameAlgEquivOfEq, coe_algebraMap_isRestrictedSubring_apply]
  simp only [restrictedFinAddEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hs,
    restrictedSumEquiv_algebraMap]

/-- **Splitting `Fin (k + m)` as an `S`-algebra isomorphism** over every coefficient algebra `S`
of `R`. -/
noncomputable def restrictedFinAddAlgEquiv {S : Type*} [CommSemiring S] [Algebra S R] :
    Flat ≃ₐ[S] Iter :=
  AlgEquiv.ofRingEquiv restrictedFinAddEquiv_algebraMap

/-- `restrictedFinAddAlgEquiv` has the same underlying map as `restrictedFinAddEquiv`. -/
@[simp]
theorem coe_restrictedFinAddAlgEquiv {S : Type*} [CommSemiring S] [Algebra S R] :
    ⇑(restrictedFinAddAlgEquiv (S := S) (R := R) (r := r)) = restrictedFinAddEquiv := (rfl)

/-- The inverse of `restrictedFinAddAlgEquiv` has the same underlying map as
`restrictedFinAddEquiv.symm`. -/
@[simp]
theorem coe_restrictedFinAddAlgEquiv_symm {S : Type*} [CommSemiring S] [Algebra S R] :
    ⇑(restrictedFinAddAlgEquiv (S := S) (R := R) (r := r)).symm =
      ⇑(restrictedFinAddEquiv (R := R) (r := r)).symm := (rfl)

/-- On the first `k` variables, `restrictedFinAddEquiv` sends `X (Fin.castAdd m i)` to the `i`-th
variable of the inner algebra, viewed as a constant series of the outer algebra. -/
@[simp]
theorem restrictedFinAddEquiv_X_castAdd (i : Fin k) :
    restrictedFinAddEquiv (⟨X (Fin.castAdd m i), isRestricted_X r _⟩ : Flat) =
      algebraMap Inner Iter ⟨X i, isRestricted_X (r ∘ Fin.castAdd m) i⟩ := by
  have hX :
      IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
          (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (sumElim_comp_finAddSwapEquiv r) ⟨X (Fin.castAdd m i), isRestricted_X r _⟩ =
        (⟨X (.inr i), isRestricted_X _ _⟩ :
          IsRestricted.subring (R := R) (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))) := by
    apply Subtype.ext
    simp [IsRestricted.coe_renameAlgEquivOfEq, finAddSwapEquiv_castAdd]
  simp only [restrictedFinAddEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hX,
    restrictedSumEquiv_X_inr]

/-- On the last `m` variables, `restrictedFinAddEquiv` sends `X (Fin.natAdd k j)` to the `j`-th
variable of the outer algebra. -/
@[simp]
theorem restrictedFinAddEquiv_X_natAdd (j : Fin m) :
    restrictedFinAddEquiv (⟨X (Fin.natAdd k j), isRestricted_X r _⟩ : Flat) =
      ⟨X j, isRestricted_X (r ∘ Fin.natAdd k) j⟩ := by
  have hX :
      IsRestricted.renameAlgEquivOfEq (finAddSwapEquiv k m)
          (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))
          (sumElim_comp_finAddSwapEquiv r) ⟨X (Fin.natAdd k j), isRestricted_X r _⟩ =
        (⟨X (.inl j), isRestricted_X _ _⟩ :
          IsRestricted.subring (R := R) (Sum.elim (r ∘ Fin.natAdd k) (r ∘ Fin.castAdd m))) := by
    apply Subtype.ext
    simp [IsRestricted.coe_renameAlgEquivOfEq, finAddSwapEquiv_natAdd]
  simp only [restrictedFinAddEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hX,
    restrictedSumEquiv_X_inl]

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
  simp only [restrictedFinAddEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hp,
    restrictedSumEquiv_polynomialToRestricted]

/-- `restrictedFinAddEquiv` preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedFinAddEquiv (f : Flat) : ‖restrictedFinAddEquiv f‖ = ‖f‖ := by
  simp only [restrictedFinAddEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    norm_restrictedSumEquiv, IsRestricted.norm_renameAlgEquivOfEq]

/-- The inverse of `restrictedFinAddEquiv` preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedFinAddEquiv_symm (g : Iter) : ‖restrictedFinAddEquiv.symm g‖ = ‖g‖ := by
  simpa only [RingEquiv.apply_symm_apply] using
    (norm_restrictedFinAddEquiv (restrictedFinAddEquiv.symm g)).symm

/-- `restrictedFinAddEquiv` is an isometry for the Gauss norms. -/
theorem isometry_restrictedFinAddEquiv :
    Isometry (restrictedFinAddEquiv (R := R) (r := r)) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_restrictedFinAddEquiv

/-- The inverse of `restrictedFinAddEquiv` is an isometry for the Gauss norms. -/
theorem isometry_restrictedFinAddEquiv_symm :
    Isometry (restrictedFinAddEquiv (R := R) (r := r)).symm :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr norm_restrictedFinAddEquiv_symm

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
