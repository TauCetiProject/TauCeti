/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.AnalyticSubst
public import TauCeti.RingTheory.Dagger.Subst
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Derivative
public import Mathlib.RingTheory.Finiteness.Defs

import TauCeti.RingTheory.Dagger.NoetherNormalization
import TauCeti.RingTheory.Derivation.Ideal
import TauCeti.RingTheory.Ideal.KrullIntersection

/-!
# Derivatives of overconvergent power series

Over an ultrametric normed commutative ring `R`, the Hasse derivative

```text
∂^d (∑ₘ aₘ Xᵐ) = ∑ₘ (∏ⱼ (mⱼ + dⱼ choose dⱼ)) aₘ₊d Xᵐ
```

preserves restrictedness at every positive radius, with the Cauchy estimate
`ρᵈ ‖∂^d f‖_ρ ≤ ‖f‖_ρ` for the Gauss norms (`MvPowerSeries.IsRestricted.hasseDeriv`,
`MvPowerSeries.norm_restrictedHasseDeriv_le`). Since this holds at each radius `ρ > 1`
separately, Hasse derivatives, and in particular the partial derivatives `∂/∂Xᵢ = ∂^(eᵢ)`,
preserve the Monsky–Washnitzer algebra `W = R⟨X⟩†` of overconvergent series. Only natural-number
multiples of coefficients occur, so no assumption on the characteristic is needed. The identity
`k! • ∂^(k eᵢ) = (∂/∂Xᵢ)^[k]` holds over every `R`; when `k!` is invertible in `R` it exhibits
`∂^(k eᵢ)` as `(∂/∂Xᵢ)ᵏ / k!`, but in characteristic `p` this division is not available for
`k ≥ p` while `∂^(k eᵢ)` still is.

The partial derivatives are packaged as `R`-derivations of `W`. They are the derivations through
which the differential `dg = ∑ᵢ (∂g/∂Xᵢ) dXᵢ` of the overconvergent de Rham complex is written.
The Hasse derivatives `∂^d` are `R`-linear endomorphisms of `W` satisfying
`k! • ∂^(k eᵢ) = (∂/∂Xᵢ)^[k]`, and they remain available in characteristic `p`.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.hasseDeriv d`: the `d`-th Hasse derivative, an `R`-linear
  endomorphism of `W`.
* `TauCeti.Dagger.washnitzerAlgebra.pderiv i`: the partial derivative `∂/∂Xᵢ`, an
  `R`-derivation of `W`.

## Main results

* `TauCeti.Dagger.hasseDeriv_mem_washnitzerAlgebra` and
  `TauCeti.Dagger.pderiv_mem_washnitzerAlgebra`: Hasse and partial derivatives of overconvergent
  series are overconvergent.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_hasseDeriv`,
  `TauCeti.Dagger.washnitzerAlgebra.toTate_pderiv`,
  `TauCeti.Dagger.washnitzerAlgebra.hasseDeriv_ofRestricted`, and
  `TauCeti.Dagger.washnitzerAlgebra.pderiv_ofRestricted`: compatibility with `toTate`, polyradius
  inclusions, and bounded coefficient maps, together with Gauss-norm contractivity and continuity.
* `TauCeti.Dagger.washnitzerAlgebra.pderiv_analyticSubst`,
  `TauCeti.Dagger.washnitzerAlgebra.pderiv_translate`, and
  `TauCeti.Dagger.washnitzerAlgebra.pderiv_subst`: the chain rule for analytic and polynomial
  substitutions, and commutation of partial derivatives with translations.
* `TauCeti.Dagger.washnitzerAlgebra.hasseDeriv_mul`: the Leibniz rule
  `∂^d (f g) = ∑_{a + b = d} ∂^a f · ∂^b g`, and
  `TauCeti.Dagger.washnitzerAlgebra.hasseDeriv_comp`: the composition rule, from which
  `TauCeti.Dagger.washnitzerAlgebra.hasseDeriv_comm` shows that Hasse derivatives commute.
* `TauCeti.Dagger.washnitzerAlgebra.factorial_smul_hasseDeriv_single`:
  `k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`.
* `TauCeti.Dagger.washnitzerAlgebra.pderiv_X`: `∂Xⱼ/∂Xᵢ = δᵢⱼ`, and
  `TauCeti.Dagger.washnitzerAlgebra.pderiv_ofMvPolynomial`: on polynomials the partial derivatives
  are the polynomial ones.
* `TauCeti.Dagger.washnitzerAlgebra.pderiv_primitive`: over a field of characteristic zero,
  `∂/∂Xᵢ` is a left inverse of the termwise primitive in `Xᵢ`.
* `TauCeti.Dagger.washnitzerAlgebra.derivation_ext`: over a complete ultrametric field, two
  derivations of `W` in finitely many variables into a finite module agreeing on the variables are
  equal.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- **Hasse derivatives of overconvergent series are overconvergent.** See
`MvPowerSeries.IsRestricted.hasseDeriv` for the radius-by-radius version. -/
theorem hasseDeriv_mem_washnitzerAlgebra {f : MvPowerSeries σ R}
    (hf : f ∈ washnitzerAlgebra σ R) (d : σ →₀ ℕ) :
    hasseDeriv d f ∈ washnitzerAlgebra σ R := by
  obtain ⟨ρ, hρ, hf⟩ := mem_washnitzerAlgebra.1 hf
  exact mem_washnitzerAlgebra.2 ⟨ρ, hρ, hf.hasseDeriv fun _ _ ↦ (zero_lt_one.trans hρ).ne'⟩

/-- **Partial derivatives of overconvergent series are overconvergent.** -/
theorem pderiv_mem_washnitzerAlgebra {f : MvPowerSeries σ R}
    (hf : f ∈ washnitzerAlgebra σ R) (i : σ) :
    pderiv i f ∈ washnitzerAlgebra σ R := by
  simpa using hasseDeriv_mem_washnitzerAlgebra hf (Finsupp.single i 1)

namespace washnitzerAlgebra

variable (σ R) in
/-- The `d`-th Hasse derivative `∂^d`, as an `R`-linear endomorphism of the Monsky–Washnitzer
algebra. -/
noncomputable def hasseDeriv (d : σ →₀ ℕ) : washnitzerAlgebra σ R →ₗ[R] washnitzerAlgebra σ R :=
  (MvPowerSeries.hasseDeriv d ∘ₗ (washnitzerAlgebra σ R).toSubmodule.subtype).codRestrict
    (washnitzerAlgebra σ R).toSubmodule fun f ↦ hasseDeriv_mem_washnitzerAlgebra f.property d

/-- The Hasse derivative in `W` is the Hasse derivative of the underlying series. -/
@[simp]
theorem coe_hasseDeriv (d : σ →₀ ℕ) (f : washnitzerAlgebra σ R) :
    (hasseDeriv σ R d f : MvPowerSeries σ R) = MvPowerSeries.hasseDeriv d f :=
  (rfl)

/-- The Hasse derivative of order zero is the identity. -/
@[simp]
theorem hasseDeriv_zero : hasseDeriv σ R 0 = LinearMap.id :=
  LinearMap.ext fun f ↦ Subtype.ext (by simp [MvPowerSeries.hasseDeriv_zero])

/-- Every Hasse derivative of positive order kills the constant `1` of `W`. -/
@[simp]
theorem hasseDeriv_one {d : σ →₀ ℕ} (hd : d ≠ 0) :
    hasseDeriv σ R d (1 : washnitzerAlgebra σ R) = 0 :=
  Subtype.ext (by simp [hd])

/-- Every Hasse derivative of positive order kills the constants of `W`. -/
@[simp]
theorem hasseDeriv_algebraMap {d : σ →₀ ℕ} (hd : d ≠ 0) (a : R) :
    hasseDeriv σ R d (algebraMap R (washnitzerAlgebra σ R) a) = 0 :=
  Subtype.ext (by simp [MvPowerSeries.algebraMap_apply, hd])

variable (σ R) in
/-- The partial derivative `∂/∂Xᵢ`, as an `R`-derivation of the Monsky–Washnitzer algebra. -/
noncomputable def pderiv (i : σ) :
    Derivation R (washnitzerAlgebra σ R) (washnitzerAlgebra σ R) where
  toFun f := ⟨MvPowerSeries.pderiv i f, pderiv_mem_washnitzerAlgebra f.property i⟩
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.pderiv i) f.val g.val)
  map_smul' r f := Subtype.ext ((MvPowerSeries.pderiv i).map_smul r f.val)
  map_one_eq_zero' := Subtype.ext (MvPowerSeries.pderiv_one (R := R))
  leibniz' f g := Subtype.ext <| by simp [smul_eq_mul]

/-- The partial derivative in `W` is the partial derivative of the underlying series. -/
@[simp]
theorem coe_pderiv (i : σ) (f : washnitzerAlgebra σ R) :
    (pderiv σ R i f : MvPowerSeries σ R) = MvPowerSeries.pderiv i f :=
  (rfl)

/-- The first Hasse derivative in `Xᵢ` is the partial derivative in `Xᵢ`. -/
@[simp]
theorem hasseDeriv_single_one (i : σ) (f : washnitzerAlgebra σ R) :
    hasseDeriv σ R (Finsupp.single i 1) f = pderiv σ R i f :=
  Subtype.ext (by simp)

/-- `k!` times the Hasse derivative `∂^(k eᵢ)` is the `k`-th iterated partial derivative in
`Xᵢ`: `k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`. -/
theorem factorial_smul_hasseDeriv_single (i : σ) (k : ℕ) (f : washnitzerAlgebra σ R) :
    k.factorial • hasseDeriv σ R (Finsupp.single i k) f = (pderiv σ R i)^[k] f :=
  Subtype.ext <| by
    rw [Subalgebra.coe_smul, coe_hasseDeriv, MvPowerSeries.factorial_smul_hasseDeriv_single]
    exact ((Function.Semiconj.iterate_right (f := Subtype.val) (coe_pderiv i) k).eq f).symm

/-- Differentiating `∂^(k eᵢ) f` in `Xᵢ` gives `(k + 1) ∂^((k + 1) eᵢ) f` in `W`. -/
@[simp]
theorem pderiv_hasseDeriv_single (i : σ) (k : ℕ) (f : washnitzerAlgebra σ R) :
    pderiv σ R i (hasseDeriv σ R (Finsupp.single i k) f) =
      (k + 1) • hasseDeriv σ R (Finsupp.single i (k + 1)) f :=
  Subtype.ext (by simp)

/-- The **Leibniz rule** for Hasse derivatives in `W`: `∂^d (f g) = ∑_{a + b = d} ∂^a f · ∂^b g`. -/
theorem hasseDeriv_mul [DecidableEq σ] (d : σ →₀ ℕ) (f g : washnitzerAlgebra σ R) :
    hasseDeriv σ R d (f * g) =
      ∑ x ∈ Finset.antidiagonal d, hasseDeriv σ R x.1 f * hasseDeriv σ R x.2 g :=
  Subtype.ext (by simp [MvPowerSeries.hasseDeriv_mul])

/-- The composition rule for Hasse derivatives in `W`:
`∂^a ∘ ∂^b = (∏ⱼ (aⱼ + bⱼ choose aⱼ)) • ∂^(a + b)`. -/
theorem hasseDeriv_comp (a b : σ →₀ ℕ) :
    (hasseDeriv σ R a).comp (hasseDeriv σ R b) =
      (a.prod fun j k ↦ (k + b j).choose k) • hasseDeriv σ R (a + b) :=
  LinearMap.ext fun f ↦ Subtype.ext (by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, coe_hasseDeriv,
      Subalgebra.coe_smul] using
      LinearMap.congr_fun (MvPowerSeries.hasseDeriv_comp a b) f.val)

/-- Hasse derivatives in `W` commute: `∂^a ∘ ∂^b = ∂^b ∘ ∂^a`. -/
theorem hasseDeriv_comm (a b : σ →₀ ℕ) :
    (hasseDeriv σ R a).comp (hasseDeriv σ R b) = (hasseDeriv σ R b).comp (hasseDeriv σ R a) :=
  LinearMap.ext fun f ↦ Subtype.ext
    (LinearMap.congr_fun (MvPowerSeries.hasseDeriv_comm (R := R) a b) f.val)

/-- Partial derivatives of overconvergent series commute. -/
theorem pderiv_comm (i j : σ) (f : washnitzerAlgebra σ R) :
    pderiv σ R i (pderiv σ R j f) = pderiv σ R j (pderiv σ R i f) := by
  simpa only [LinearMap.comp_apply, hasseDeriv_single_one] using
    LinearMap.congr_fun (hasseDeriv_comm (σ := σ) (R := R)
      (Finsupp.single i 1) (Finsupp.single j 1)) f

/-- Over a torsion-free coefficient ring, an overconvergent function has all partial derivatives
zero exactly when it is a scalar. This also holds for an infinite variable type. -/
theorem forall_pderiv_eq_zero_iff [HasUniqueDiv R] (g : washnitzerAlgebra σ R) :
    (∀ i, pderiv σ R i g = 0) ↔ ∃ c : R, algebraMap R (washnitzerAlgebra σ R) c = g := by
  constructor
  · intro hg
    refine ⟨constantCoeff g.val, Subtype.ext ?_⟩
    apply MvPowerSeries.pderiv.ext
    · intro i
      simpa [MvPowerSeries.algebraMap_apply] using
        (congrArg Subtype.val (hg i)).symm
    · simp [MvPowerSeries.algebraMap_apply]
  · rintro ⟨c, rfl⟩ i
    exact (pderiv σ R i).map_algebraMap c

/-- Hasse derivatives of polynomials in `W` are the polynomial Hasse derivatives. -/
@[simp]
theorem hasseDeriv_ofMvPolynomial (d : σ →₀ ℕ) (p : MvPolynomial σ R) :
    hasseDeriv σ R d (ofMvPolynomial σ R p) = ofMvPolynomial σ R (MvPolynomial.hasseDeriv d p) :=
  Subtype.ext (by simp [MvPowerSeries.hasseDeriv_coe])

/-- Partial derivatives of polynomials in `W` are the polynomial partial derivatives. -/
@[simp]
theorem pderiv_ofMvPolynomial (i : σ) (p : MvPolynomial σ R) :
    pderiv σ R i (ofMvPolynomial σ R p) = ofMvPolynomial σ R (MvPolynomial.pderiv i p) :=
  Subtype.ext (by simp [MvPowerSeries.pderiv_coe])

/-- The partial derivative of `Xᵢ` in `Xᵢ` is `1`. -/
@[simp]
theorem pderiv_X_self (i : σ) : pderiv σ R i (X σ R i) = 1 :=
  Subtype.ext (by simp)

/-- The partial derivative of `Xⱼ` in `Xᵢ` is `0` for `j ≠ i`. -/
@[simp]
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv σ R i (X σ R j) = 0 :=
  Subtype.ext (by simp [MvPowerSeries.pderiv_X_of_ne h])

/-- The partial derivatives of the variables: `∂Xⱼ/∂Xᵢ = δᵢⱼ`. -/
theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv σ R i (X σ R j) = Pi.single (M := fun _ ↦ washnitzerAlgebra σ R) i 1 j := by
  obtain rfl | h := eq_or_ne j i
  · simp
  · simp [h]

/-- The inclusion into the Tate algebra intertwines the Hasse derivatives of `W` and of the
unit-radius Tate algebra. -/
@[simp]
theorem toTate_hasseDeriv (d : σ →₀ ℕ) (f : washnitzerAlgebra σ R) :
    toTate σ R (hasseDeriv σ R d f) = restrictedHasseDeriv d (toTate σ R f) :=
  Subtype.ext (by simp)

/-- **The Cauchy estimate at unit radius**: Hasse derivatives do not increase the unit Gauss norm
of an overconvergent series. -/
theorem norm_hasseDeriv_le (d : σ →₀ ℕ) (f : washnitzerAlgebra σ R) :
    ‖hasseDeriv σ R d f‖ ≤ ‖f‖ := by
  rw [← norm_toTate, toTate_hasseDeriv]
  simpa using norm_restrictedHasseDeriv_le d (toTate σ R f)

/-- Hasse derivatives are continuous for the unit Gauss norm on `W`. -/
@[continuity]
theorem continuous_hasseDeriv (d : σ →₀ ℕ) : Continuous (hasseDeriv σ R d) :=
  AddMonoidHomClass.continuous_of_bound (hasseDeriv σ R d) 1 fun f ↦ by
    simpa using norm_hasseDeriv_le d f

/-- The inclusion into the Tate algebra intertwines the partial derivatives of `W` and of the
unit-radius Tate algebra. -/
@[simp]
theorem toTate_pderiv (i : σ) (f : washnitzerAlgebra σ R) :
    toTate σ R (pderiv σ R i f) = TauCeti.MvPowerSeries.restrictedPDeriv i (toTate σ R f) :=
  Subtype.ext (by simp)

/-- Partial derivatives do not increase the unit Gauss norm on `W`. -/
theorem norm_pderiv_le (i : σ) (f : washnitzerAlgebra σ R) :
    ‖pderiv σ R i f‖ ≤ ‖f‖ := by
  simpa only [hasseDeriv_single_one] using norm_hasseDeriv_le (Finsupp.single i 1) f

/-- Partial derivatives are continuous for the unit Gauss norm on `W`. -/
@[continuity]
theorem continuous_pderiv (i : σ) : Continuous (pderiv σ R i) :=
  AddMonoidHomClass.continuous_of_bound (pderiv σ R i) 1 fun f ↦ by
    simpa using norm_pderiv_le i f

/-- Polyradius inclusions `ofRestricted` intertwine `restrictedHasseDeriv` and `hasseDeriv`. -/
@[simp]
theorem hasseDeriv_ofRestricted {c : σ → ℝ} [∀ j, Fact (0 < c j)] {ρ : ℝ}
    (hρ : 1 < ρ) (hc : ∀ j, ρ ≤ c j) (d : σ →₀ ℕ) (f : IsRestricted.subring (R := R) c) :
    hasseDeriv σ R d (ofRestricted hρ hc f) = ofRestricted hρ hc (restrictedHasseDeriv d f) :=
  Subtype.ext (by simp)

/-- Polyradius inclusions `ofRestricted` intertwine `restrictedPDeriv` and `pderiv`. -/
@[simp]
theorem pderiv_ofRestricted {c : σ → ℝ} [∀ j, Fact (0 < c j)] {ρ : ℝ}
    (hρ : 1 < ρ) (hc : ∀ j, ρ ≤ c j) (i : σ) (f : IsRestricted.subring (R := R) c) :
    pderiv σ R i (ofRestricted hρ hc f) =
      ofRestricted hρ hc (TauCeti.MvPowerSeries.restrictedPDeriv i f) :=
  Subtype.ext (by simp)

/-- Finite-variable polyradius inclusions `ofOneLt` intertwine `restrictedHasseDeriv` and
`hasseDeriv`. -/
@[simp]
theorem hasseDeriv_ofOneLt [Finite σ] {c : σ → ℝ} [∀ j, Fact (0 < c j)] (hc : ∀ j, 1 < c j)
    (d : σ →₀ ℕ) (f : IsRestricted.subring (R := R) c) :
    hasseDeriv σ R d (ofOneLt hc f) = ofOneLt hc (restrictedHasseDeriv d f) :=
  Subtype.ext (by simp)

/-- Finite-variable polyradius inclusions `ofOneLt` intertwine `restrictedPDeriv` and `pderiv`. -/
@[simp]
theorem pderiv_ofOneLt [Finite σ] {c : σ → ℝ} [∀ j, Fact (0 < c j)] (hc : ∀ j, 1 < c j)
    (i : σ) (f : IsRestricted.subring (R := R) c) :
    pderiv σ R i (ofOneLt hc f) =
      ofOneLt hc (TauCeti.MvPowerSeries.restrictedPDeriv i f) :=
  Subtype.ext (by simp)

/-- Bounded coefficient maps commute with Hasse derivatives on `W`. -/
@[simp]
theorem map_hasseDeriv {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    (φ : R →+* S) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (d : σ →₀ ℕ)
    (f : washnitzerAlgebra σ R) :
    map φ hφ (hasseDeriv σ R d f) = hasseDeriv σ S d (map φ hφ f) :=
  Subtype.ext <| MvPowerSeries.ext fun m ↦ by
    simp [MvPowerSeries.coeff_hasseDeriv]

/-- Bounded coefficient maps commute with partial derivatives on `W`. -/
@[simp]
theorem map_pderiv {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    (φ : R →+* S) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (i : σ)
    (f : washnitzerAlgebra σ R) :
    map φ hφ (pderiv σ R i f) = pderiv σ S i (map φ hφ f) := by
  simpa only [hasseDeriv_single_one] using map_hasseDeriv φ hφ (Finsupp.single i 1) f

/-- **Chain rule for polynomial substitutions in `W`.** -/
theorem pderiv_subst [Fintype σ] [NormOneClass R] {τ : Type*}
    (a : σ → MvPolynomial τ R) (ha₀ : ∀ s, (a s).constantCoeff = 0)
    (ha₁ : ∀ s t, ‖(a s).coeff t‖ ≤ 1) (j : τ) (f : washnitzerAlgebra σ R) :
    pderiv τ R j (subst a ha₀ ha₁ f) =
      ∑ s, subst a ha₀ ha₁ (pderiv σ R s f) * ofMvPolynomial τ R (MvPolynomial.pderiv j (a s)) := by
  apply Subtype.ext
  rw [coe_pderiv, coe_subst, MvPowerSeries.pderiv_subst (hasSubst_coe ha₀)]
  simp [MvPowerSeries.pderiv_coe]

/-- **The overconvergent chain rule for analytic substitution.** Over a complete ultrametric normed
commutative ring `R`, for `g₁, …, g_k ∈ R⟨Y⟩†` with `‖gᵢ‖₁ ≤ 1` and `f ∈ R⟨X₁, …, X_k⟩†`,
`∂ⱼ (f(g)) = ∑ᵢ (∂ᵢ f)(g) · ∂ⱼ gᵢ`. -/
theorem pderiv_analyticSubst [CompleteSpace R] {k : ℕ} {τ : Type*}
    (g : Fin k → washnitzerAlgebra τ R) (hg : ∀ i, ‖toTate τ R (g i)‖ ≤ 1)
    (j : τ) (f : washnitzerAlgebra (Fin k) R) :
    pderiv τ R j (analyticSubst g hg f) =
      ∑ i, analyticSubst g hg (pderiv (Fin k) R i f) * pderiv τ R j (g i) := by
  apply toTate_injective
  simpa only [toTate_pderiv, toTate_analyticSubst, map_sum, map_mul] using
    TauCeti.MvPowerSeries.restrictedPDeriv_restrictedAnalyticSubst
      (fun i ↦ toTate τ R (g i)) hg j (toTate (Fin k) R f)

/-- **Translations commute with partial derivatives in `W`**: `∂ᵢ (f(X + a)) = (∂ᵢ f)(X + a)`. -/
theorem pderiv_translate [CompleteSpace R] [NormOneClass R] {k : ℕ}
    (a : Fin k → R) (ha : ∀ i, ‖a i‖ ≤ 1) (i : Fin k) (f : washnitzerAlgebra (Fin k) R) :
    pderiv (Fin k) R i (translate a ha f) = translate a ha (pderiv (Fin k) R i f) := by
  apply toTate_injective
  simpa only [toTate_pderiv, toTate_translate] using
    TauCeti.MvPowerSeries.restrictedPDeriv_restrictedTranslate a ha i (toTate (Fin k) R f)

section Primitive

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- **The derivative of the primitive**: in `W`, `∂/∂Xᵢ (∫ f dXᵢ) = f`. -/
@[simp]
theorem pderiv_primitive (i : σ) (f : washnitzerAlgebra σ K) :
    pderiv σ K i (primitive σ K i f) = f :=
  Subtype.ext (by simp)

/-- Differentiation in another variable commutes with termwise integration in `W`. -/
@[simp]
theorem pderiv_primitive_of_ne {i j : σ} (hij : i ≠ j) (f : washnitzerAlgebra σ K) :
    pderiv σ K j (primitive σ K i f) = primitive σ K i (pderiv σ K j f) := by
  apply Subtype.ext
  simpa only [coe_pderiv, coe_primitive] using MvPowerSeries.pderiv_primitive_of_ne hij f.val

end Primitive

section Ext

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W" σ => washnitzerAlgebra σ K

/-- **Derivations into finite modules are determined by the variables.** Two `K`-derivations of
the Monsky–Washnitzer algebra in finitely many variables into a finite module are equal as soon as
they agree on the variables. -/
theorem derivation_ext {σ : Type*} [Finite σ] {M : Type*} [AddCommGroup M] [Module (W σ) M]
    [Module K M] [Module.Finite (W σ) M]
    {D₁ D₂ : Derivation K (W σ) M} (h : ∀ i, D₁ (X σ K i) = D₂ (X σ K i)) : D₁ = D₂ := by
  rw [← sub_eq_zero]
  set D := D₁ - D₂
  have hX (i : σ) : D (X σ K i) = 0 := by simp [D, h]
  have hpoly (p : MvPolynomial σ K) : D (ofMvPolynomial σ K p) = 0 := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [← MvPolynomial.algebraMap_eq]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [Derivation.leibniz, hp, hX]
  ext g
  -- `D g` lies in `m ^ n M` for every maximal ideal `m` and every `n`.
  have hmem (m : Ideal (W σ)) (hm : m.IsMaximal) (n : ℕ) :
      D g ∈ m ^ n • (⊤ : Submodule (W σ) M) := by
    have : (m ^ (n + 1)).radical.IsMaximal := by
      rwa [Ideal.radical_pow m n.succ_ne_zero, hm.isPrime.radical]
    have : Module.Finite K ((W σ) ⧸ m ^ (n + 1)) :=
      finite_quotient_of_isMaximal_radical (AlgHom.Finite.id K (W σ)) _
    obtain ⟨p, hp⟩ := surjective_mkₐ_comp_ofMvPolynomial (m ^ (n + 1)) (Ideal.Quotient.mk _ g)
    have hgp : g - ofMvPolynomial σ K p ∈ m ^ (n + 1) := Ideal.Quotient.eq.mp hp.symm
    simpa [hpoly] using D.apply_mem_pow_smul_top_of_mem_pow_succ hgp
  -- Powers of the maximal ideals separate the finite module `M`.
  have hg : D g ∈ (⨅ (m : Ideal (W σ)) (_ : m.IsMaximal) (n : ℕ) (_ : 0 < n),
      m ^ n • ⊤ : Submodule (W σ) M) := by
    simp only [Submodule.mem_iInf]
    exact fun m hm n _ ↦ hmem m hm n
  rw [Ideal.iInf_isMaximal_pow_smul_eq_bot, Submodule.mem_bot] at hg
  simpa using hg

end Ext

end washnitzerAlgebra

end TauCeti.Dagger
