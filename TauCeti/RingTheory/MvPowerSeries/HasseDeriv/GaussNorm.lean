/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import TauCeti.RingTheory.MvPowerSeries.HasseDeriv.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Hasse derivatives of restricted multivariate power series

Over an ultrametric (semi)normed ring, a natural-number multiple of an element has at most the
norm of that element. The coefficients of the Hasse derivative `∂^d f` are natural-number
multiples of the coefficients of `f`, shifted down by `d`, so for a polyradius `c ≥ 0`

```text
cᵈ ‖∂^d f‖_c ≤ ‖f‖_c,    cᵈ = ∏ᵢ cᵢ ^ dᵢ,
```

for the Gauss norms, and `∂^d` preserves restrictedness whenever `cᵢ ≠ 0` in every variable `Xᵢ`
in which it differentiates. Neither a multiplicative norm nor `‖1‖ = 1` is needed, and the
coefficients need not commute. These are the estimates that make Hasse derivatives act on Tate
algebras of closed polydiscs of any positive polyradius.

The condition on the polyradius cannot be dropped: at `c = (0, 1)` in the variables `X, Y`, the
series `∑ₙ X Yⁿ` is restricted, since every weight involving `X` vanishes, but its derivative
`∑ₙ Yⁿ` in `X` is not.

## Main results

* `MvPowerSeries.norm_coeff_hasseDeriv_le`: `‖[Xᵐ] ∂^d f‖ ≤ ‖[X^(m + d)] f‖`.
* `MvPowerSeries.prod_pow_mul_gaussNorm_hasseDeriv_le`: `cᵈ ‖∂^d f‖_c ≤ ‖f‖_c` whenever `f` has
  bounded weighted coefficient norms.
* `MvPowerSeries.HasGaussNorm.hasseDeriv` and `MvPowerSeries.IsRestricted.hasseDeriv`: Hasse
  derivatives preserve bounded weighted coefficient norms and restrictedness.
* `MvPowerSeries.IsRestricted.pderiv`: over a commutative ring, the partial derivative in `Xᵢ`
  preserves restrictedness whenever `cᵢ ≠ 0`.
* `MvPowerSeries.restrictedHasseDeriv`: the Hasse derivative on the ring of series restricted at
  a positive polyradius `c`, with the Cauchy estimate
  `MvPowerSeries.norm_restrictedHasseDeriv_le`, `‖∂^d f‖ ≤ (∏ᵢ cᵢ ^ dᵢ)⁻¹ ‖f‖`, its continuity,
  and over a commutative ring its `R`-linearity `MvPowerSeries.restrictedHasseDeriv_smul` and its
  agreement `MvPowerSeries.restrictedHasseDeriv_polynomial` with `MvPolynomial.hasseDeriv`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.
* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2.
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
/-- For a polyradius `c ≥ 0`, the weighted coefficient norms of `∂^d f`, multiplied by `cᵈ`, are
bounded by those of `f`. -/
theorem prod_pow_mul_norm_coeff_hasseDeriv_le (hc : 0 ≤ c) (d m : σ →₀ ℕ) :
    d.prod (c · ^ ·) * (‖coeff m (hasseDeriv d f)‖ * m.prod (c · ^ ·)) ≤
      ‖coeff (m + d) f‖ * (m + d).prod (c · ^ ·) := by
  have hprod (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _
  calc d.prod (c · ^ ·) * (‖coeff m (hasseDeriv d f)‖ * m.prod (c · ^ ·))
      = ‖coeff m (hasseDeriv d f)‖ * (m + d).prod (c · ^ ·) := by rw [prod_pow_add]; ring
    _ ≤ ‖coeff (m + d) f‖ * (m + d).prod (c · ^ ·) :=
      mul_le_mul_of_nonneg_right (norm_coeff_hasseDeriv_le f d m) (hprod _)

/-- **The Gauss-norm estimate for Hasse derivatives**: for a polyradius `c ≥ 0`,
`cᵈ ‖∂^d f‖_c ≤ ‖f‖_c` whenever `f` has bounded weighted coefficient norms. -/
theorem prod_pow_mul_gaussNorm_hasseDeriv_le (hc : 0 ≤ c) (hf : f.HasGaussNorm norm c)
    (d : σ →₀ ℕ) :
    d.prod (c · ^ ·) * gaussNorm norm c (hasseDeriv d f) ≤ gaussNorm norm c f := by
  have hd : 0 ≤ d.prod (c · ^ ·) := Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _
  rw [gaussNorm, Real.mul_iSup_of_nonneg hd]
  exact Real.iSup_le (fun m ↦ (prod_pow_mul_norm_coeff_hasseDeriv_le f hc d m).trans
    (le_gaussNorm norm c f hf (m + d))) (gaussNorm_nonneg norm c f norm_nonneg)

/-- For a polyradius `c ≥ 0` that is nonzero in every variable in which `∂^d` differentiates,
Hasse derivatives preserve boundedness of the weighted coefficient norms. -/
theorem HasGaussNorm.hasseDeriv (hc : 0 ≤ c) {d : σ →₀ ℕ} (hd : ∀ i ∈ d.support, c i ≠ 0)
    (hf : f.HasGaussNorm norm c) : (hasseDeriv d f).HasGaussNorm norm c := by
  have hpos : 0 < d.prod (c · ^ ·) :=
    Finset.prod_pos fun i hi ↦ pow_pos ((hc i).lt_of_ne' (hd i hi)) _
  refine ⟨(d.prod (c · ^ ·))⁻¹ * gaussNorm norm c f, Set.forall_mem_range.2 fun m ↦ ?_⟩
  rw [le_inv_mul_iff₀ hpos]
  exact (prod_pow_mul_norm_coeff_hasseDeriv_le f hc d m).trans (le_gaussNorm norm c f hf (m + d))

end SeminormedRing

section NormedRing

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R] {c : σ → ℝ} {f : MvPowerSeries σ R}

/-- Over an ultrametric normed ring, Hasse derivatives preserve restrictedness at every polyradius
which is nonzero in each variable in which they differentiate. -/
theorem IsRestricted.hasseDeriv {d : σ →₀ ℕ} (hd : ∀ i ∈ d.support, c i ≠ 0)
    (hf : IsRestricted c f) : IsRestricted c (hasseDeriv d f) := by
  rw [← isRestricted_abs_iff] at hf ⊢
  have hc : (0 : σ → ℝ) ≤ |c| := fun i ↦ abs_nonneg (c i)
  have hpos : 0 < d.prod (|c| · ^ ·) :=
    Finset.prod_pos fun i hi ↦ pow_pos (abs_pos.2 (hd i hi)) _
  -- the weighted coefficient norms of `∂^d f` are those of `f`, shifted by `d` and divided by `cᵈ`
  refine squeeze_zero (fun m ↦ mul_nonneg (norm_nonneg _) (prod_abs_pow_nonneg m))
    (fun m ↦ (le_inv_mul_iff₀ hpos).2 (prod_pow_mul_norm_coeff_hasseDeriv_le f hc d m)) ?_
  simpa using ((hf.comp (add_left_injective d).tendsto_cofinite).const_mul
    (d.prod (|c| · ^ ·))⁻¹)

variable [∀ i, Fact (0 < c i)]

/-- The `d`-th Hasse derivative on the ring of series restricted at a positive polyradius `c`. -/
noncomputable def restrictedHasseDeriv (d : σ →₀ ℕ) :
    IsRestricted.subring (R := R) c →+ IsRestricted.subring (R := R) c :=
  AddMonoidHom.mk' (fun f ↦ ⟨hasseDeriv d (f : MvPowerSeries σ R),
      f.2.hasseDeriv fun i _ ↦ (Fact.out : 0 < c i).ne'⟩)
    fun f g ↦ Subtype.ext (map_add (hasseDeriv d) (f : MvPowerSeries σ R) g)

/-- The Hasse derivative of a restricted series is its Hasse derivative as a formal series. -/
@[simp]
theorem coe_restrictedHasseDeriv (d : σ →₀ ℕ) (f : IsRestricted.subring (R := R) c) :
    (restrictedHasseDeriv d f : MvPowerSeries σ R) = hasseDeriv d f :=
  (rfl)

/-- **The Cauchy estimate on the restricted-series ring.** At a positive polyradius `c`,
`‖∂^d f‖ ≤ (∏ᵢ cᵢ ^ dᵢ)⁻¹ ‖f‖` for the Gauss norm. -/
theorem norm_restrictedHasseDeriv_le (d : σ →₀ ℕ) (f : IsRestricted.subring (R := R) c) :
    ‖restrictedHasseDeriv d f‖ ≤ (d.prod (c · ^ ·))⁻¹ * ‖f‖ := by
  have hpos : 0 < d.prod (c · ^ ·) := Finset.prod_pos fun i _ ↦ pow_pos Fact.out _
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, coe_restrictedHasseDeriv, le_inv_mul_iff₀ hpos]
  exact prod_pow_mul_gaussNorm_hasseDeriv_le (fun i ↦ (Fact.out : 0 < c i).le) f.2.hasGaussNorm d

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

/-- Over an ultrametric normed commutative ring, the partial derivative in `Xᵢ` preserves
restrictedness at every polyradius with `cᵢ ≠ 0`. -/
theorem IsRestricted.pderiv {i : σ} (hi : c i ≠ 0) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) : IsRestricted c (pderiv i f) := by
  have hd : ∀ j ∈ (Finsupp.single i 1).support, c j ≠ 0 := fun j hj ↦ by
    rwa [Finset.mem_singleton.1 (Finsupp.support_single_subset hj)]
  simpa using hf.hasseDeriv hd

variable [∀ i, Fact (0 < c i)]

/-- Over a commutative ring, the Hasse derivative on the restricted-series ring is `R`-linear. -/
@[simp]
theorem restrictedHasseDeriv_smul (d : σ →₀ ℕ) (r : R) (f : IsRestricted.subring (R := R) c) :
    restrictedHasseDeriv d (r • f) = r • restrictedHasseDeriv d f :=
  Subtype.ext (by
    rw [TauCeti.MvPowerSeries.coe_smul_isRestrictedSubring, coe_restrictedHasseDeriv,
      coe_restrictedHasseDeriv, TauCeti.MvPowerSeries.coe_smul_isRestrictedSubring, map_smul])

/-- On a polynomial, the Hasse derivative on the restricted-series ring is the polynomial Hasse
derivative `MvPolynomial.hasseDeriv`. -/
@[simp]
theorem restrictedHasseDeriv_polynomial (d : σ →₀ ℕ) (p : MvPolynomial σ R) :
    restrictedHasseDeriv d ⟨(p : MvPowerSeries σ R), p.isRestricted c⟩ =
      ⟨(MvPolynomial.hasseDeriv d p : MvPowerSeries σ R),
        (MvPolynomial.hasseDeriv d p).isRestricted c⟩ :=
  Subtype.ext (by rw [coe_restrictedHasseDeriv, hasseDeriv_coe])

end NormedCommRing

end MvPowerSeries
