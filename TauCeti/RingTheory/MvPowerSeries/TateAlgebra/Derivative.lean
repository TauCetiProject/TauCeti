/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.HasseDeriv.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst

/-!
# Partial derivatives of restricted power series and the chain rule

Let `R` be an ultrametric normed commutative ring and `c` a positive polyradius. The partial
derivative `∂/∂Xᵢ` of Mathlib's `MvPowerSeries.pderiv` preserves restrictedness at `c`, so it is
an `R`-derivation of the restricted-series ring `R{X/c}`. It is the first Hasse derivative in
`Xᵢ`, and satisfies the Cauchy estimate `‖∂ᵢ f‖ ≤ cᵢ⁻¹ ‖f‖`; in particular it is continuous for
the Gauss norm.

Over a complete coefficient ring, partial derivatives obey the **chain rule** for analytic
substitution: for series `gᵢ ∈ R{Y/s}` with `‖gᵢ‖ ≤ rᵢ` and `f ∈ R{X/r}`,

```text
∂ⱼ (f(g)) = ∑ᵢ (∂ᵢ f)(g) · ∂ⱼ gᵢ.
```

Unlike the formal chain rule `MvPowerSeries.pderiv_subst`, the `gᵢ` may have arbitrary, even
non-nilpotent, constant terms: the substitution is the convergent sum
`TauCeti.MvPowerSeries.restrictedAnalyticSubst`. In particular, translation `Xᵢ ↦ Xᵢ + aᵢ` of a
closed polydisc commutes with every partial derivative.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedPDeriv`: the partial derivative `∂/∂Xᵢ` as an `R`-derivation of
  `R{X/c}`.

## Main results

* `TauCeti.MvPowerSeries.restrictedHasseDeriv_single_one`: the first Hasse derivative in `Xᵢ` is
  the partial derivative.
* `TauCeti.MvPowerSeries.norm_restrictedPDeriv_le`: the Cauchy estimate `‖∂ᵢ f‖ ≤ cᵢ⁻¹ ‖f‖`.
* `TauCeti.MvPowerSeries.restrictedPDeriv_restrictedAnalyticSubst`: the chain rule for analytic
  substitution.
* `TauCeti.MvPowerSeries.restrictedPDeriv_restrictedTranslate`: partial derivatives commute with
  translation.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section PDeriv

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}
  [∀ i, Fact (0 < c i)]

/-- The partial derivative `∂/∂Xᵢ`, as an `R`-derivation of the ring `R{X/c}` of series
restricted at a positive polyradius `c`. -/
noncomputable def restrictedPDeriv (i : σ) :
    Derivation R (IsRestricted.subring (R := R) c) (IsRestricted.subring (R := R) c) where
  toFun f := ⟨pderiv i (f : MvPowerSeries σ R), f.2.pderiv (Fact.out : 0 < c i).ne'⟩
  map_add' f g := Subtype.ext (map_add (pderiv i) (f : MvPowerSeries σ R) g)
  map_smul' a f := Subtype.ext (by simp)
  map_one_eq_zero' := Subtype.ext (pderiv_one (R := R))
  leibniz' f g := Subtype.ext (by simp [smul_eq_mul])

/-- The partial derivative of a restricted series is its partial derivative as a formal series. -/
@[simp]
theorem coe_restrictedPDeriv (i : σ) (f : IsRestricted.subring (R := R) c) :
    (restrictedPDeriv i f : MvPowerSeries σ R) = pderiv i f :=
  (rfl)

/-- The first Hasse derivative in `Xᵢ` is the partial derivative in `Xᵢ`. -/
@[simp]
theorem restrictedHasseDeriv_single_one (i : σ) (f : IsRestricted.subring (R := R) c) :
    restrictedHasseDeriv (Finsupp.single i 1) f = restrictedPDeriv i f :=
  Subtype.ext (by simp [hasseDeriv_single_one])

/-- The partial derivative of `Xᵢ` in `Xᵢ` is `1`. -/
@[simp]
theorem restrictedPDeriv_X_self (i : σ) :
    restrictedPDeriv i ⟨X i, isRestricted_monomial c (Finsupp.single i 1) (1 : R)⟩ = 1 :=
  Subtype.ext (by simp)

/-- The partial derivative of `Xⱼ` in `Xᵢ` is `0` for `j ≠ i`. -/
@[simp]
theorem restrictedPDeriv_X_of_ne {i j : σ} (h : j ≠ i) :
    restrictedPDeriv i ⟨X j, isRestricted_monomial c (Finsupp.single j 1) (1 : R)⟩ = 0 :=
  Subtype.ext (by simp [pderiv_X_of_ne h])

/-- The partial derivatives of the variables: `∂Xⱼ/∂Xᵢ = δᵢⱼ`. -/
theorem restrictedPDeriv_X [DecidableEq σ] (i j : σ) :
    restrictedPDeriv i ⟨X j, isRestricted_monomial c (Finsupp.single j 1) (1 : R)⟩ =
      Pi.single (M := fun _ ↦ IsRestricted.subring (R := R) c) i 1 j := by
  obtain rfl | h := eq_or_ne j i
  · simp
  · simp [h]

/-- **The Cauchy estimate for partial derivatives**: `‖∂ᵢ f‖ ≤ cᵢ⁻¹ ‖f‖` for the Gauss norm at
the polyradius `c`. -/
theorem norm_restrictedPDeriv_le (i : σ) (f : IsRestricted.subring (R := R) c) :
    ‖restrictedPDeriv i f‖ ≤ (c i)⁻¹ * ‖f‖ := by
  simpa using norm_restrictedHasseDeriv_le (Finsupp.single i 1) f

/-- Partial derivatives are continuous for the Gauss norm. -/
@[continuity]
theorem continuous_restrictedPDeriv (i : σ) :
    Continuous (restrictedPDeriv (R := R) (c := c) i) :=
  AddMonoidHomClass.continuous_of_bound _ _ (norm_restrictedPDeriv_le i)

end PDeriv

section ChainRule

variable {k : ℕ} {τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r : Fin k → ℝ} {s : τ → ℝ} [∀ i, Fact (0 < r i)] [∀ j, Fact (0 < s j)]

/-- **The chain rule for analytic substitution**: for series `gᵢ ∈ R{Y/s}` with `‖gᵢ‖ ≤ rᵢ`
and `f ∈ R{X/r}`, `∂ⱼ (f(g)) = ∑ᵢ (∂ᵢ f)(g) · ∂ⱼ gᵢ`. The `gᵢ` may have nonzero constant
terms. -/
theorem restrictedPDeriv_restrictedAnalyticSubst (g : Fin k → IsRestricted.subring (R := R) s)
    (hg : ∀ i, ‖g i‖ ≤ r i) (j : τ) (f : IsRestricted.subring (R := R) r) :
    restrictedPDeriv j (restrictedAnalyticSubst g hg f) =
      ∑ i, restrictedAnalyticSubst g hg (restrictedPDeriv i f) * restrictedPDeriv j (g i) := by
  classical
  set Φ := restrictedAnalyticSubst g hg
  -- the series satisfying the chain rule form a subalgebra
  let E : Subalgebra R (IsRestricted.subring (R := R) r) :=
    { carrier := {f | restrictedPDeriv j (Φ f) =
        ∑ i, Φ (restrictedPDeriv i f) * restrictedPDeriv j (g i)}
      mul_mem' := fun {f h} hf hh ↦ by
        simp only [Set.mem_ofPred_eq, map_mul, Derivation.leibniz, smul_eq_mul, map_add, add_mul,
          Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hf hh ⊢
        rw [hf, hh]
      add_mem' := fun {f h} hf hh ↦ by
        simp only [Set.mem_ofPred_eq, map_add, add_mul, Finset.sum_add_distrib] at hf hh ⊢
        rw [hf, hh]
      algebraMap_mem' := fun a ↦ by simp }
  have hE (f) : f ∈ E ↔ restrictedPDeriv j (Φ f) =
      ∑ i, Φ (restrictedPDeriv i f) * restrictedPDeriv j (g i) := Iff.rfl
  -- it contains the variables
  have hX (l : Fin k) : ⟨X l, isRestricted_monomial r (Finsupp.single l 1) (1 : R)⟩ ∈ E := by
    rw [hE, restrictedAnalyticSubst_X, Finset.sum_eq_single l (fun i _ hi ↦ by
      rw [restrictedPDeriv_X_of_ne (Ne.symm hi), map_zero, zero_mul]) (by simp)]
    simp
  -- so it contains the polynomials, which are dense, and both sides are continuous in `f`
  refine congrFun (Continuous.ext_on (dense_closure_monomial dense_univ)
    (f := fun f ↦ restrictedPDeriv j (Φ f))
    (g := fun f ↦ ∑ i, Φ (restrictedPDeriv i f) * restrictedPDeriv j (g i))
    ((continuous_restrictedPDeriv j).comp (continuous_restrictedAnalyticSubst g hg))
    (continuous_finsetSum _ fun i _ ↦ ((continuous_restrictedAnalyticSubst g hg).comp
      (continuous_restrictedPDeriv i)).mul continuous_const)
    fun f hf ↦ (hE f).1 ((AddSubgroup.closure_le E.toSubring.toAddSubgroup).mpr ?_ hf)) f
  rintro _ ⟨⟨t, a⟩, -, rfl⟩
  dsimp only
  rw [mk_monomial_eq_algebraMap_mul_prod]
  exact E.mul_mem (E.algebraMap_mem a) (prod_mem fun l _ ↦ pow_mem (hX l) _)

/-- **Translation commutes with partial derivatives**: `∂ᵢ (f(X + a)) = (∂ᵢ f)(X + a)`. -/
theorem restrictedPDeriv_restrictedTranslate [NormOneClass R] (a : Fin k → R)
    (ha : ∀ i, ‖a i‖ ≤ r i) (i : Fin k) (f : IsRestricted.subring (R := R) r) :
    restrictedPDeriv i (restrictedTranslate a ha f) =
      restrictedTranslate a ha (restrictedPDeriv i f) := by
  rw [restrictedTranslate_def, restrictedPDeriv_restrictedAnalyticSubst,
    Finset.sum_eq_single i (fun l _ hl ↦ by simp [restrictedPDeriv_X_of_ne hl]) (by simp)]
  simp

end ChainRule

end TauCeti.MvPowerSeries
