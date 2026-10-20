/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.HasseDeriv.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Hasse derivatives of restricted multivariate power series

Over an ultrametric (semi)normed ring, a natural-number multiple of an element has at most the
norm of that element. The coefficients of the Hasse derivative `∂^d f` are natural-number multiples
of the coefficients of `f`, shifted down by the multi-index `d`, so at positive polyradii `c`
the **Cauchy estimate**

```text
‖∂^d f‖_c ≤ (∏ᵢ cᵢ ^ dᵢ)⁻¹ ‖f‖_c
```

holds for the Gauss norms, and `∂^d` preserves restrictedness. For a constant polyradius `ρ` the
factor is `ρ^(-|d|)`. Neither a multiplicative norm nor `‖1‖ = 1` is needed, and the coefficients
need not commute. The estimate is stated for Hasse derivatives rather than for
`(∂/∂X)^[k] / k!`, so it holds in every characteristic. In particular the Hasse derivatives, and
over a commutative ring the partial derivatives, act on the Tate algebra of every closed polydisc
of positive polyradius, and hence on the overconvergent series, those restricted at some radius
greater than one.

## Main results

* `MvPowerSeries.norm_coeff_hasseDeriv_le`: `‖[Xᵐ] ∂^d f‖ ≤ ‖[Xᵐ⁺ᵈ] f‖`.
* `MvPowerSeries.HasGaussNorm.hasseDeriv` and `MvPowerSeries.gaussNorm_hasseDeriv_le`: at
  positive polyradii `c`, Hasse derivatives preserve bounded weighted coefficients, and
  `gaussNorm c (∂^d f) ≤ (∏ᵢ cᵢ ^ dᵢ)⁻¹ * gaussNorm c f`.
* `MvPowerSeries.IsRestricted.hasseDeriv` and `MvPowerSeries.IsRestricted.pderiv`: Hasse
  derivatives and partial derivatives preserve restrictedness at nonzero polyradii.
* `MvPowerSeries.restrictedHasseDeriv`: the Hasse derivative on the restricted-series ring at
  positive polyradii, with the Cauchy estimate `MvPowerSeries.norm_restrictedHasseDeriv_le` and
  its continuity.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.
* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*, J. Reine Angew.
  Math. 519 (2000), §1.2.
-/

public section

namespace MvPowerSeries

open Filter
open scoped Topology

section SeminormedRing

variable {σ R : Type*} [SeminormedRing R] [IsUltrametricDist R] {c : σ → ℝ}
  {f : MvPowerSeries σ R}

variable (f) in
/-- Over an ultrametric ring, a coefficient of a Hasse derivative has at most the norm of the
coefficient of `f` it is a multiple of. -/
theorem norm_coeff_hasseDeriv_le (d m : σ →₀ ℕ) :
    ‖coeff m (hasseDeriv d f)‖ ≤ ‖coeff (m + d) f‖ := by
  rw [coeff_hasseDeriv, ← nsmul_eq_mul]
  exact IsUltrametricDist.norm_nsmul_le _ _

variable (f) in
/-- The weighted coefficient norms of `∂^d f` at positive polyradii `c` are bounded by
`(∏ᵢ cᵢ ^ dᵢ)⁻¹` times the weighted coefficient norms of `f`. -/
theorem norm_coeff_hasseDeriv_mul_prod_le (hc : ∀ i, 0 < c i) (d m : σ →₀ ℕ) :
    ‖coeff m (hasseDeriv d f)‖ * m.prod (c · ^ ·) ≤
      (d.prod (c · ^ ·))⁻¹ * (‖coeff (m + d) f‖ * (m + d).prod (c · ^ ·)) := by
  have hd : 0 < d.prod (c · ^ ·) := Finset.prod_pos fun i _ ↦ pow_pos (hc i) _
  have h : (d.prod (c · ^ ·))⁻¹ * (‖coeff (m + d) f‖ * (m.prod (c · ^ ·) * d.prod (c · ^ ·))) =
      ‖coeff (m + d) f‖ * m.prod (c · ^ ·) := by
    field_simp
  rw [prod_pow_add, h]
  exact mul_le_mul_of_nonneg_right (norm_coeff_hasseDeriv_le f d m)
    (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i).le _)

variable (f) in
/-- The weighted coefficient norms of `∂^d f` at positive polyradii `c` are bounded by
`(∏ᵢ cᵢ ^ dᵢ)⁻¹` times the Gauss norm of `f`. -/
theorem norm_coeff_hasseDeriv_mul_prod_le_gaussNorm (hc : ∀ i, 0 < c i)
    (hf : HasGaussNorm norm c f) (d m : σ →₀ ℕ) :
    ‖coeff m (hasseDeriv d f)‖ * m.prod (c · ^ ·) ≤ (d.prod (c · ^ ·))⁻¹ * gaussNorm norm c f :=
  (norm_coeff_hasseDeriv_mul_prod_le f hc d m).trans <|
    mul_le_mul_of_nonneg_left (le_gaussNorm _ _ _ hf _)
      (inv_nonneg.mpr (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i).le _))

/-- At positive polyradii, Hasse derivatives preserve bounded weighted coefficients. -/
theorem HasGaussNorm.hasseDeriv (hc : ∀ i, 0 < c i) (hf : HasGaussNorm norm c f)
    (d : σ →₀ ℕ) : HasGaussNorm norm c (hasseDeriv d f) :=
  ⟨_, Set.forall_mem_range.mpr (norm_coeff_hasseDeriv_mul_prod_le_gaussNorm f hc hf d)⟩

/-- **The Cauchy estimate for Hasse derivatives.** At positive polyradii `c`,
`gaussNorm c (∂^d f) ≤ (∏ᵢ cᵢ ^ dᵢ)⁻¹ * gaussNorm c f`. -/
theorem gaussNorm_hasseDeriv_le (hc : ∀ i, 0 < c i) (hf : HasGaussNorm norm c f)
    (d : σ →₀ ℕ) :
    gaussNorm norm c (hasseDeriv d f) ≤ (d.prod (c · ^ ·))⁻¹ * gaussNorm norm c f :=
  ciSup_le (norm_coeff_hasseDeriv_mul_prod_le_gaussNorm f hc hf d)

end SeminormedRing

section NormedRing

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- Over an ultrametric normed ring, Hasse derivatives preserve restrictedness at polyradii with
nonzero entries. -/
theorem IsRestricted.hasseDeriv (hc : ∀ i, c i ≠ 0) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (d : σ →₀ ℕ) : IsRestricted c (hasseDeriv d f) := by
  rw [← isRestricted_abs_iff] at hf ⊢
  refine squeeze_zero (fun m ↦ mul_nonneg (norm_nonneg _) (prod_abs_pow_nonneg m))
    (norm_coeff_hasseDeriv_mul_prod_le f (fun i ↦ abs_pos.mpr (hc i)) d) ?_
  simpa using (hf.comp (add_left_injective d).tendsto_cofinite).const_mul _

variable [∀ i, Fact (0 < c i)]

/-- The `d`-th Hasse derivative on the ring of series restricted at positive polyradii `c`. -/
noncomputable def restrictedHasseDeriv (d : σ →₀ ℕ) :
    IsRestricted.subring (R := R) c →+ IsRestricted.subring (R := R) c :=
  AddMonoidHom.mk' (fun f ↦ ⟨hasseDeriv d (f : MvPowerSeries σ R),
      f.2.hasseDeriv (fun i ↦ (Fact.out : 0 < c i).ne') d⟩)
    fun f g ↦ Subtype.ext (map_add (hasseDeriv d) (f : MvPowerSeries σ R) g)

/-- The Hasse derivative of a restricted series is its Hasse derivative as a formal series. -/
@[simp]
theorem coe_restrictedHasseDeriv (d : σ →₀ ℕ) (f : IsRestricted.subring (R := R) c) :
    (restrictedHasseDeriv d f : MvPowerSeries σ R) = hasseDeriv d f :=
  (rfl)

/-- **The Cauchy estimate on the restricted-series ring.** At positive polyradii `c`,
`‖∂^d f‖ ≤ (∏ᵢ cᵢ ^ dᵢ)⁻¹ ‖f‖` for the Gauss norm. -/
theorem norm_restrictedHasseDeriv_le (d : σ →₀ ℕ) (f : IsRestricted.subring (R := R) c) :
    ‖restrictedHasseDeriv d f‖ ≤ (d.prod (c · ^ ·))⁻¹ * ‖f‖ := by
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, coe_restrictedHasseDeriv]
  exact gaussNorm_hasseDeriv_le (fun i ↦ Fact.out) f.2.hasGaussNorm d

/-- The Hasse derivative on the restricted-series ring is Lipschitz with constant
`(∏ᵢ cᵢ ^ dᵢ)⁻¹`. -/
theorem lipschitzWith_restrictedHasseDeriv (d : σ →₀ ℕ) :
    LipschitzWith (d.prod (c · ^ ·))⁻¹.toNNReal (restrictedHasseDeriv (R := R) (c := c) d) :=
  AddMonoidHomClass.lipschitz_of_bound _ _ (norm_restrictedHasseDeriv_le d)

/-- The Hasse derivative on the restricted-series ring is continuous for the Gauss norm. -/
@[continuity]
theorem continuous_restrictedHasseDeriv (d : σ →₀ ℕ) :
    Continuous (restrictedHasseDeriv (R := R) (c := c) d) :=
  (lipschitzWith_restrictedHasseDeriv d).continuous

end NormedRing

section NormedCommRing

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- Over an ultrametric normed commutative ring, partial derivatives preserve restrictedness at
polyradii with nonzero entries. -/
theorem IsRestricted.pderiv (hc : ∀ i, c i ≠ 0) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (i : σ) : IsRestricted c (pderiv i f) := by
  simpa using hf.hasseDeriv hc (Finsupp.single i 1)

end NormedCommRing

end MvPowerSeries
