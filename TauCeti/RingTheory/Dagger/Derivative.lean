/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.MvPowerSeries.HasseDeriv.GaussNorm

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
multiples of coefficients occur, so no assumption on the characteristic is needed; in
characteristic zero `∂^(k eᵢ)` is `(∂/∂Xᵢ)ᵏ / k!`, but in characteristic `p` this division is not
available for `k ≥ p` while `∂^(k eᵢ)` still is.

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
* `TauCeti.Dagger.washnitzerAlgebra.toTate_hasseDeriv` and
  `TauCeti.Dagger.washnitzerAlgebra.norm_toTate_hasseDeriv_le`: the inclusion into the Tate
  algebra intertwines the Hasse derivatives, which do not increase the Gauss norm.
* `TauCeti.Dagger.washnitzerAlgebra.hasseDeriv_mul`: the Leibniz rule
  `∂^d (f g) = ∑_{a + b = d} ∂^a f · ∂^b g`, and
  `TauCeti.Dagger.washnitzerAlgebra.hasseDeriv_comp`: the composition rule.
* `TauCeti.Dagger.washnitzerAlgebra.factorial_smul_hasseDeriv_single`:
  `k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`.
* `TauCeti.Dagger.washnitzerAlgebra.pderiv_X`: `∂Xⱼ/∂Xᵢ = δᵢⱼ`, and
  `TauCeti.Dagger.washnitzerAlgebra.pderiv_ofMvPolynomial`: on polynomials the partial derivatives
  are the polynomial ones.
* `TauCeti.Dagger.washnitzerAlgebra.pderiv_primitive`: over a field of characteristic zero,
  `∂/∂Xᵢ` is a left inverse of the termwise primitive in `Xᵢ`.

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
    (washnitzerAlgebra σ R).toSubmodule fun f ↦ hasseDeriv_mem_washnitzerAlgebra f.2 d

/-- The Hasse derivative in `W` is the Hasse derivative of the underlying series. -/
@[simp]
theorem coe_hasseDeriv (d : σ →₀ ℕ) (f : washnitzerAlgebra σ R) :
    (hasseDeriv σ R d f : MvPowerSeries σ R) = MvPowerSeries.hasseDeriv d f :=
  (rfl)

/-- The Hasse derivative of order zero is the identity. -/
@[simp]
theorem hasseDeriv_zero : hasseDeriv σ R 0 = LinearMap.id :=
  LinearMap.ext fun f ↦ Subtype.ext (by simp [MvPowerSeries.hasseDeriv_zero])

variable (σ R) in
/-- The partial derivative `∂/∂Xᵢ`, as an `R`-derivation of the Monsky–Washnitzer algebra. -/
noncomputable def pderiv (i : σ) :
    Derivation R (washnitzerAlgebra σ R) (washnitzerAlgebra σ R) where
  toFun f := ⟨MvPowerSeries.pderiv i f, pderiv_mem_washnitzerAlgebra f.2 i⟩
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.pderiv i) f.1 g.1)
  map_smul' r f := Subtype.ext ((MvPowerSeries.pderiv i).map_smul r f.1)
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

/-- The Hasse derivative `∂^(k eᵢ)` is the `k`-th partial derivative in `Xᵢ` divided by `k!`:
`k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`. -/
theorem factorial_smul_hasseDeriv_single (i : σ) (k : ℕ) (f : washnitzerAlgebra σ R) :
    k.factorial • hasseDeriv σ R (Finsupp.single i k) f = (pderiv σ R i)^[k] f :=
  Subtype.ext <| by
    rw [Subalgebra.coe_smul, coe_hasseDeriv, MvPowerSeries.factorial_smul_hasseDeriv_single]
    exact ((Function.Semiconj.iterate_right (f := Subtype.val) (coe_pderiv i) k).eq f).symm

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
      LinearMap.congr_fun (MvPowerSeries.hasseDeriv_comp a b) f.1)

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
theorem toTate_hasseDeriv (d : σ →₀ ℕ) (f : washnitzerAlgebra σ R) :
    toTate σ R (hasseDeriv σ R d f) = restrictedHasseDeriv d (toTate σ R f) :=
  Subtype.ext (by simp)

/-- **The Cauchy estimate at unit radius**: Hasse derivatives do not increase the Gauss norm of an
overconvergent series. -/
theorem norm_toTate_hasseDeriv_le (d : σ →₀ ℕ) (f : washnitzerAlgebra σ R) :
    ‖toTate σ R (hasseDeriv σ R d f)‖ ≤ ‖toTate σ R f‖ := by
  simpa [toTate_hasseDeriv] using norm_restrictedHasseDeriv_le d (toTate σ R f)

section Primitive

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- **The derivative of the primitive**: in `W`, `∂/∂Xᵢ (∫ f dXᵢ) = f`. -/
@[simp]
theorem pderiv_primitive (i : σ) (f : washnitzerAlgebra σ K) :
    pderiv σ K i (primitive σ K i f) = f :=
  Subtype.ext (by simp)

end Primitive

end washnitzerAlgebra

end TauCeti.Dagger
