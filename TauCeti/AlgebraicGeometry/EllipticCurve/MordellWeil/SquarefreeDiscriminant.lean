/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroupA
import TauCeti.Algebra.Order.GroupWithZero.WithZeroInt
import TauCeti.RingTheory.DedekindDomain.AdicValuation.FieldNorm
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# Step 6 of weak Mordell–Weil at primes where `disc f` is squarefree

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal form
over the fraction field `K` of a Dedekind domain `R`, and let `v` be a prime of `R` at which `a₂`,
`a₄` and `a₆` are integral. Step 6 of the weak Mordell–Weil theorem
(`WeierstrassCurve.Affine.range_μ_le_selmerGroupA`) shows that the `x - T` map is unramified above
`v` when the discriminant `disc f` of the cubic is a `v`-unit. This file shows that the same holds
when `disc f` vanishes to order at most `1` at `v`, that is when `exp (-1) ≤ v (disc f)`.

The argument is a parity count over all primes `w` above `v` of all field factors `K[X] ⧸ (p)` of
the étale algebra, with `θ` the image of `T` in each factor. Since `N(f'(T)) = -disc f`
(`WeierstrassCurve.Affine.norm_mk_derivative_f`), the valuation of a norm
(`IsDedekindDomain.HeightOneSpectrum.valuation_norm`) gives
`∏_{(p, w)} w(f' θ) ^ f(w ∣ v) = v (disc f) ≥ exp (-1)`, with every factor integral. So `f' θ` is a
`w`-unit at every pair `(p, w)` except at most one, and an exceptional pair has inertia degree `1`.
At the pairs where `f' θ` is a unit, the valuation of `x - θ` is even by the arithmetic core of
Step 6 (`WeierstrassCurve.Affine.even_valuationOfNeZero_sub_root`). For a point `(x, y)` with
`f x ≠ 0` the same formula applied to `N(x - T) = f(x) = y²` gives
`∏_{(p, w)} w(x - θ) ^ f(w ∣ v) = v(y)²`, and since the exceptional pair enters with exponent `1`
its valuation is even as well. At a rational root `x` of `f`, the factorization
`disc f = disc(f / (X - x)) · f'(x)²` (`WeierstrassCurve.Affine.discr_f_eq_mul_sq_of_eval_eq_zero`)
shows that `f'(x)` is a `v`-unit, since `exp (-1)` is not a square.

Over a number field this means that the `2`-Selmer group is unramified outside the primes at which
a coefficient has a pole or `disc f` vanishes to order at least `2`. For instance for
`y² = x³ - x + 1` over `ℚ`, with `disc f = -23` squarefree, no finite prime imposes ramification.

The norm formula uses the relative norm of ideals, so `K` is assumed to be a perfect field, as it
is in the arithmetic applications, where `K` is a number field or one of its completions.

## Main results

* `WeierstrassCurve.Affine.valuation_deriv_eval_eq_one_of_exp_neg_one_le`: at a root `x` of `f`,
  with integral coefficients and `exp (-1) ≤ ν (disc f)`, the derivative `f' x` is a `ν`-unit.
* `WeierstrassCurve.Affine.even_valuationOfNeZero_sub_root_of_exp_neg_one_le`: with integral
  coefficients and `exp (-1) ≤ v (disc f)`, the valuation of `x - θ` is even at every prime above
  `v` of every field factor.
* `WeierstrassCurve.Affine.range_μ_le_selmerGroupA_of_exp_neg_one_le`: Step 6 for every set `S`
  outside which the coefficients are integral and `exp (-1) ≤ v (disc f)`.

## Provenance

The argument follows Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0), revision `3bfe124`:
`EllipticCurves/SelmerGroup.lean`, section `OddPlace` (the critical-factor parity argument, there
over the completion of a number field at a place, with the unique prime of each local field factor)
and section `WithZeroArith` (the value-group lemmas, adapted in
`TauCeti.Algebra.Order.GroupWithZero.WithZeroInt`), and
`EllipticCurves/WeakMordellWeil.lean`, section `DerivativeUnit`
(`valuation_deriv_eval_eq_one_of_exp_neg_one_le`, there `valuation_deriv_eval_eq_one`). Here the
statements are proved over a Dedekind domain, with the norm formula summed over all primes above
`v`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1 and X.1.
-/

public section

open Polynomial IsDedekindDomain WithZero TauCeti

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to this file: for a monic irreducible factor `p` of `f`, `𝕃 p` is the field
factor `K[X] ⧸ (p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding, and `θ p` is the image
of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

/-- At a root `x` of `f`, if `a₂`, `a₄` and `a₆` are `ν`-integral and `exp (-1) ≤ ν (disc f)`, then
`f' x = 3x² + 2a₂x + a₄` is a `ν`-unit: `disc f` is the integral discriminant of the cofactor
`f / (X - x)` times `(f' x)²`, and `exp (-1)` is not a square. -/
theorem valuation_deriv_eval_eq_one_of_exp_neg_one_le {ν : Valuation K ℤᵐ⁰} {x : K}
    (hx : W.f.eval x = 0) (ha₂ : ν W.a₂ ≤ 1) (ha₄ : ν W.a₄ ≤ 1) (ha₆ : ν W.a₆ ≤ 1)
    (hd : exp (-1) ≤ ν W.f.discr) :
    ν (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 := by
  have hx1 : x ∈ ν.integer := ν.le_one_of_root_cubic ha₂ ha₄ ha₆ (by rwa [eval_f] at hx)
  have ha₂' : W.a₂ ∈ ν.integer := ha₂
  have ha₄' : W.a₄ ∈ ν.integer := ha₄
  have hfx : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∈ ν.integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx1 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) ha₂') hx1)) ha₄'
  have hcd : (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) ∈ ν.integer :=
    sub_mem (pow_mem (add_mem hx1 ha₂') 2)
      (mul_mem (ofNat_mem _ 4) (add_mem (add_mem (pow_mem hx1 2) (mul_mem ha₂' hx1)) ha₄'))
  rw [W.discr_f_eq_mul_sq_of_eval_eq_zero hx, map_mul, map_pow] at hd
  exact eq_one_of_exp_neg_one_le_sq hfx (hd.trans (mul_le_of_le_one_left' hcd))

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- The `x - T` representative of a point with `f x ≠ 0`, projected to a field factor, is a unit. -/
private lemma isUnit_algebraMap_sub_root {x : K} (hx : W.f.eval x ≠ 0) (p : W.f.Factors) :
    IsUnit (ι p x - θ p) := by
  have h := (isUnit_mk_sub_X_of_eval_f_ne_zero hx).map
    (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)
  rwa [W.projFactor_mk_C_sub_X] at h

variable [PerfectField K]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/- The ring of integers of a field factor is a finite `R`-module: the field factor is a finite
separable extension of `K`. -/
private instance instModuleFiniteRingOfIntegersFactor (p : W.f.Factors) :
    Module.Finite R (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.finite R K (𝕃 p) _

/- `f` has finitely many factors, and each field factor finitely many primes above a prime of
`R`; these instances index the products below. -/
private noncomputable instance instFintypeFactors : Fintype W.f.Factors :=
  have := Polynomial.Factors.finite W.f_ne_zero
  Fintype.ofFinite _

private noncomputable instance instFintypeLiesOver (v : HeightOneSpectrum R) (q : W.f.Factors) :
    Fintype {w : HeightOneSpectrum (W.ringOfIntegersFactor R q) // w.asIdeal.LiesOver v.asIdeal} :=
  Fintype.ofFinite _

/-- The pairs of a field factor `K[X] ⧸ (q)` and a prime of its ring of integers above `v`. -/
private abbrev PrimesAboveFactors (v : HeightOneSpectrum R) : Type _ :=
  Σ q : W.f.Factors,
    {w : HeightOneSpectrum (W.ringOfIntegersFactor R q) // w.asIdeal.LiesOver v.asIdeal}

/-- The `v`-adic valuation of a norm from the étale algebra is the product, over the pairs of a
field factor and a prime `w` above `v`, of the `w`-adic valuations of the components, weighted by
the inertia degrees. -/
private lemma valuation_norm_eq_prod (v : HeightOneSpectrum R) (a : W.A) :
    v.valuation K (Algebra.norm K a) = ∏ i : W.PrimesAboveFactors R v,
      i.2.1.valuation (𝕃 i.1) (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f i.1 a) ^
        i.2.1.asIdeal.inertiaDeg R := by
  rw [AdjoinRoot.norm_eq_prod_norm_projFactor W.f_ne_zero W.squarefree_f, map_prod,
    ← Finset.univ_sigma_univ, Finset.prod_sigma]
  exact Finset.prod_congr rfl fun q _ ↦
    HeightOneSpectrum.valuation_norm (K := K) (L := 𝕃 q) (B := W.ringOfIntegersFactor R q) v _

/-- Since `N(f'(T)) = -disc f`, the weighted product over the pairs `(q, w)` above `v` of the
`w`-adic valuations of `f' θ` is `v (disc f)`. -/
private lemma prod_valuation_deriv_root (v : HeightOneSpectrum R) :
    ∏ i : W.PrimesAboveFactors R v, i.2.1.valuation (𝕃 i.1)
      (3 * θ i.1 ^ 2 + 2 * ι i.1 W.a₂ * θ i.1 + ι i.1 W.a₄) ^ i.2.1.asIdeal.inertiaDeg R =
      v.valuation K W.f.discr := by
  rw [← Valuation.map_neg, ← W.norm_mk_derivative_f, W.valuation_norm_eq_prod R v]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [AdjoinRoot.projFactor_mk, derivative_f]
  simp [AdjoinRoot.mk_C, map_ofNat, ← AdjoinRoot.algebraMap_eq]

/-- Since `N(x - T) = f x`, the weighted product over the pairs `(q, w)` above `v` of the `w`-adic
valuations of `x - θ` is `v (f x)`. -/
private lemma prod_valuation_algebraMap_sub_root (v : HeightOneSpectrum R) (x : K) :
    ∏ i : W.PrimesAboveFactors R v,
      i.2.1.valuation (𝕃 i.1) (ι i.1 x - θ i.1) ^ i.2.1.asIdeal.inertiaDeg R =
      v.valuation K (W.f.eval x) := by
  rw [← AdjoinRoot.norm_algebraMap_sub_root W.monic_f x, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X,
    ← map_sub, W.valuation_norm_eq_prod R v]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [W.projFactor_mk_C_sub_X]

/-- **The arithmetic core of Step 6 where `disc f` has valuation at most `1`.** For `(x, y)` on `W`
with `f x ≠ 0`, and `w` a prime of the ring of integers of the field factor `K[X] ⧸ (p)` such that
`a₂`, `a₄` and `a₆` are integral and `exp (-1) ≤ v (disc f)` at the prime `v` under `w`, the
`w`-adic valuation of `x - θ` is even.

When `f' θ` is a `w`-unit this is `even_valuationOfNeZero_sub_root`. Otherwise the norm of `f'(T)`
shows that `w` has inertia degree `1` over `v` and that `f' θ` is a unit at all the other primes
above `v` of all the field factors, and the norm `N(x - T) = y²` transfers the parity from those
primes to `w`. -/
theorem even_valuationOfNeZero_sub_root_of_exp_neg_one_le (p : W.f.Factors) {x y : K}
    (h : W.Equation x y) (hx : W.f.eval x ≠ 0) (u : (𝕃 p)ˣ) (hu : (u : 𝕃 p) = ι p x - θ p)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
    (ha₂ : (HeightOneSpectrum.under R w).valuation K W.a₂ ≤ 1)
    (ha₄ : (HeightOneSpectrum.under R w).valuation K W.a₄ ≤ 1)
    (ha₆ : (HeightOneSpectrum.under R w).valuation K W.a₆ ≤ 1)
    (hd : exp (-1) ≤ (HeightOneSpectrum.under R w).valuation K W.f.discr) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  classical
  by_cases hw : w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1
  · exact W.even_valuationOfNeZero_sub_root R p h hx u hu w ha₂ ha₄ ha₆ hw
  set v := HeightOneSpectrum.under R w
  -- the pairs `i = (q, w')` of a field factor and a prime above `v`, with `w` among them
  let i₀ : W.PrimesAboveFactors R v := ⟨p, w, inferInstance⟩
  have hv (i : W.PrimesAboveFactors R v) : HeightOneSpectrum.under R i.2.1 = v :=
    HeightOneSpectrum.under_eq_of_liesOver i.2.2
  have he (i : W.PrimesAboveFactors R v) : 1 ≤ i.2.1.asIdeal.inertiaDeg R :=
    Ideal.inertiaDeg_pos i.2.1.asIdeal R
  -- `f' θ` is a unit at every pair but `i₀`, which has inertia degree `1`
  obtain ⟨he₀, hrest⟩ := eq_one_and_forall_eq_one_of_exp_neg_one_le_prod (i₀ := i₀)
    (t := fun i : W.PrimesAboveFactors R v ↦ i.2.1.valuation (𝕃 i.1)
      (3 * θ i.1 ^ 2 + 2 * ι i.1 W.a₂ * θ i.1 + ι i.1 W.a₄))
    (fun i ↦ W.valuation_deriv_root_le_one R i.1 (by rwa [hv]) (by rwa [hv]) (by rwa [hv])) he
    (hd.trans_eq (W.prod_valuation_deriv_root R v).symm) hw
  -- the valuations of `x - θ` are even away from `i₀`, with product `v(y)²`
  have hlog (i : W.PrimesAboveFactors R v) :
      log (i.2.1.valuation (𝕃 i.1) (ι i.1 x - θ i.1)) = Multiplicative.toAdd
        (i.2.1.valuationOfNeZero (W.isUnit_algebraMap_sub_root hx i.1).unit) := by
    conv_lhs => rw [← IsUnit.unit_spec (W.isUnit_algebraMap_sub_root hx i.1)]
    rw [← HeightOneSpectrum.valuationOfNeZero_eq]
    rfl
  have hev := two_dvd_log_of_prod_eq_sq (i₀ := i₀) (c := v.valuation K y)
    (s := fun i : W.PrimesAboveFactors R v ↦ i.2.1.valuation (𝕃 i.1) (ι i.1 x - θ i.1))
    (e := fun i : W.PrimesAboveFactors R v ↦ i.2.1.asIdeal.inertiaDeg R)
    (fun i ↦ (Valuation.ne_zero_iff _).mpr (W.isUnit_algebraMap_sub_root hx i.1).ne_zero) he₀
    (fun i hi ↦ by
      rw [hlog]
      exact W.even_valuationOfNeZero_sub_root R i.1 h hx _ (IsUnit.unit_spec _) i.2.1
        (by rwa [hv]) (by rwa [hv]) (by rwa [hv]) (hrest i hi)) (by
      rw [W.prod_valuation_algebraMap_sub_root R v, (equation_iff_eval_f_eq_sq W x y).mp h,
        map_pow])
  rw [hlog] at hev
  have hu' : (W.isUnit_algebraMap_sub_root hx p).unit = u := Units.ext (by simp [hu])
  rwa [hu'] at hev

variable {R} {S : Set (HeightOneSpectrum R)}
  (ha₂ : ∀ v ∉ S, v.valuation K W.a₂ ≤ 1) (ha₄ : ∀ v ∉ S, v.valuation K W.a₄ ≤ 1)
  (ha₆ : ∀ v ∉ S, v.valuation K W.a₆ ≤ 1)
  (hd : ∀ v ∉ S, exp (-1) ≤ v.valuation K W.f.discr)

include ha₂ ha₄ ha₆ hd

/-- The `p`-component of `μX x` lies in the `2`-Selmer group of the factor `K[X] ⧸ (p)`. -/
private lemma μX_component_mem_selmerGroupFactor_of_exp_neg_one_le {x y : K} (h : W.Equation x y)
    (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R S p := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_eq_zero R ha₂ ha₄ ha₆ hx (fun v hv ↦
      W.valuation_deriv_eval_eq_one_of_exp_neg_one_le hx (ha₂ v hv) (ha₄ v hv) (ha₆ v hv)
        (hd v hv)) p
  · rw [μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit,
      W.mem_selmerGroupFactor_unit_iff R _ p]
    intro w hw
    rw [HeightOneSpectrum.mem_primesAbove_iff] at hw
    exact W.even_valuationOfNeZero_sub_root_of_exp_neg_one_le R p h hx _
      ((IsUnit.unit_spec _).trans (W.projFactor_mk_C_sub_X x p)) w (ha₂ _ hw) (ha₄ _ hw)
      (ha₆ _ hw) (hd _ hw)

variable [DecidableEq K]

/-- **Step 6 where `disc f` is squarefree**: the image of the descent map `μ` is contained in
`A(S,2)` for every set `S` of primes of `R` outside which `a₂`, `a₄` and `a₆` are integral and
`disc f` has valuation at most `1`, that is `exp (-1) ≤ v (disc f)`. This weakens the hypothesis of
`range_μ_le_selmerGroupA`, which asks `disc f` to be a unit outside `S`. -/
theorem range_μ_le_selmerGroupA_of_exp_neg_one_le : (μ (W := W)).range ≤ W.selmerGroupA R S := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor_of_exp_neg_one_le ha₂ ha₄ ha₆ hd h.1 p

end WeierstrassCurve.Affine

end
