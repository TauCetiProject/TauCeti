/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: Green's identity for the fourth derivative.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Green's identity for the fourth derivative under free-end boundary conditions

For `u` and `v` four times differentiable on `[0,1]` with the **free-end**
boundary conditions

```
u'' 0 = u'' 1 = u''' 0 = u''' 1 = 0,   v'' 0 = v'' 1 = v''' 0 = v''' 1 = 0,
```

the fourth derivative moves across the `L²` pairing:

```
∫₀¹ u'''' v = ∫₀¹ u v''''.
```

This is the symmetry at the heart of self-adjointness for the free-beam operator
of Davis--Kahan 1970 Section 9, and it is the first brick of the analytic model
that section's numerical example is stated against.

## Why the boundary conditions enter where they do

Four integrations by parts produce four boundary terms, and each is killed by a
*different* one of the eight conditions:

| step | boundary term | killed by |
|---|---|---|
| 1 | `[v u''']` | `u''' 0 = u''' 1 = 0` |
| 2 | `[v' u'']` | `u'' 0 = u'' 1 = 0` |
| 3 | `[u' v'']` | `v'' 0 = v'' 1 = 0` |
| 4 | `[u v''']` | `v''' 0 = v''' 1 = 0` |

So all eight are used and none is redundant — which is the concrete sense in
which "free-end" is exactly the boundary condition that makes `d⁴/dx⁴`
symmetric.

## Formulation

The derivative chain is passed explicitly, as `HasDerivAt` hypotheses relating
ten functions, rather than through `deriv` or a Sobolev space.  That matches how
`DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamCharacteristic.lean` already
presents the free-beam mode functions (`mode`, `modeD1`, ..., `modeD4` with
`hasDerivAt_mode` and siblings), so the beam modes can be fed to this lemma
directly with no bridging.  It also keeps the statement free of any Sobolev
theory, which the pinned Mathlib does not have for an interval.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib.
-/

public section

namespace TauCeti

open intervalIntegral MeasureTheory

/-- One integration by parts on `[0,1]`, with the hypotheses in the globally
continuous form the derivative chains below supply.

Mathlib's `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` asks for continuity on
the interval, differentiability on its interior, and interval integrability of
the two derivatives; all three follow from global continuity plus a global
`HasDerivAt`, and stating the specialization once keeps the four applications
below to one line each. -/
theorem integral_mul_deriv_eq_deriv_mul_unitInterval
    {f f' g g' : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hf' : Continuous f') (hg' : Continuous g')
    (hff' : ∀ x, HasDerivAt f (f' x) x) (hgg' : ∀ x, HasDerivAt g (g' x) x) :
    ∫ x in (0 : ℝ)..1, f x * g' x =
      f 1 * g 1 - f 0 * g 0 - ∫ x in (0 : ℝ)..1, f' x * g x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hf.continuousOn hg.continuousOn
    (fun x _ => hff' x) (fun x _ => hgg' x)
    (hf'.intervalIntegrable 0 1) (hg'.intervalIntegrable 0 1)

/-- **Green's identity for the fourth derivative under free-end boundary
conditions.**

`∫₀¹ u'''' v = ∫₀¹ u v''''` whenever both `u` and `v` satisfy
`u'' = u''' = 0` at both endpoints.  This is the symmetry of the free-beam
operator, and every one of the eight boundary conditions is used exactly once —
see the module docstring for which kills which. -/
theorem integral_fourthDeriv_mul_eq_mul_fourthDeriv
    {u u1 u2 u3 u4 v v1 v2 v3 v4 : ℝ → ℝ}
    (hu : Continuous u) (hu1 : Continuous u1) (hu2 : Continuous u2)
    (hu3 : Continuous u3) (hu4 : Continuous u4)
    (hv : Continuous v) (hv1 : Continuous v1) (hv2 : Continuous v2)
    (hv3 : Continuous v3) (hv4 : Continuous v4)
    (hdu : ∀ x, HasDerivAt u (u1 x) x) (hdu1 : ∀ x, HasDerivAt u1 (u2 x) x)
    (hdu2 : ∀ x, HasDerivAt u2 (u3 x) x) (hdu3 : ∀ x, HasDerivAt u3 (u4 x) x)
    (hdv : ∀ x, HasDerivAt v (v1 x) x) (hdv1 : ∀ x, HasDerivAt v1 (v2 x) x)
    (hdv2 : ∀ x, HasDerivAt v2 (v3 x) x) (hdv3 : ∀ x, HasDerivAt v3 (v4 x) x)
    (hu2zero : u2 0 = 0) (hu2one : u2 1 = 0)
    (hu3zero : u3 0 = 0) (hu3one : u3 1 = 0)
    (hv2zero : v2 0 = 0) (hv2one : v2 1 = 0)
    (hv3zero : v3 0 = 0) (hv3one : v3 1 = 0) :
    ∫ x in (0 : ℝ)..1, v x * u4 x = ∫ x in (0 : ℝ)..1, u x * v4 x := by
  -- Step 1: move `u4` back to `u3`; the boundary term dies on `u3`.
  have step1 : ∫ x in (0 : ℝ)..1, v x * u4 x = -∫ x in (0 : ℝ)..1, v1 x * u3 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hv hu3 hv1 hu4 hdv hdu3
    rw [h, hu3zero, hu3one]
    ring
  -- Step 2: again; the boundary term dies on `u2`.
  have step2 : ∫ x in (0 : ℝ)..1, v1 x * u3 x = -∫ x in (0 : ℝ)..1, v2 x * u2 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hv1 hu2 hv2 hu3 hdv1 hdu2
    rw [h, hu2zero, hu2one]
    ring
  -- Step 3: now push derivatives onto `v`; the boundary term dies on `v2`.
  have step3 : ∫ x in (0 : ℝ)..1, u1 x * v3 x = -∫ x in (0 : ℝ)..1, u2 x * v2 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu1 hv2 hu2 hv3 hdu1 hdv2
    rw [h, hv2zero, hv2one]
    ring
  -- Step 4: last one; the boundary term dies on `v3`.
  have step4 : ∫ x in (0 : ℝ)..1, u x * v4 x = -∫ x in (0 : ℝ)..1, u1 x * v3 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu hv3 hu1 hv4 hdu hdv3
    rw [h, hv3zero, hv3one]
    ring
  -- The two middle integrals agree after commuting the product.
  have hmid : ∫ x in (0 : ℝ)..1, v2 x * u2 x = ∫ x in (0 : ℝ)..1, u2 x * v2 x := by
    simp_rw [mul_comm]
  rw [step1, step2, step4, step3, hmid]

/-- **The quadratic form of the free-beam operator**: under free-end boundary
conditions the fourth derivative pairs with `u` as the square of the second
derivative,

`∫₀¹ u ⬝ (d⁴u/dx⁴) = ∫₀¹ (d²u/dx²)²`.

Two integrations by parts rather than four, and only `u`'s own four boundary
conditions are used.  This is the form identity behind positivity: the right-hand
side is a square, so the operator is nonnegative on its free-end domain, which is
what a Friedrichs-style construction of the self-adjoint realisation rests on.

It is the diagonal case of `integral_fourthDeriv_mul_eq_mul_fourthDeriv` made
quantitative — the symmetry says the form is symmetric, this says what the form
*is*. -/
theorem integral_mul_fourthDeriv_self_eq_integral_secondDeriv_sq
    {u u1 u2 u3 u4 : ℝ → ℝ}
    (hu : Continuous u) (hu1 : Continuous u1) (hu2 : Continuous u2)
    (hu3 : Continuous u3) (hu4 : Continuous u4)
    (hdu : ∀ x, HasDerivAt u (u1 x) x) (hdu1 : ∀ x, HasDerivAt u1 (u2 x) x)
    (hdu2 : ∀ x, HasDerivAt u2 (u3 x) x) (hdu3 : ∀ x, HasDerivAt u3 (u4 x) x)
    (hu2zero : u2 0 = 0) (hu2one : u2 1 = 0)
    (hu3zero : u3 0 = 0) (hu3one : u3 1 = 0) :
    ∫ x in (0 : ℝ)..1, u x * u4 x = ∫ x in (0 : ℝ)..1, u2 x ^ 2 := by
  have stepA : ∫ x in (0 : ℝ)..1, u x * u4 x = -∫ x in (0 : ℝ)..1, u1 x * u3 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu hu3 hu1 hu4 hdu hdu3
    rw [h, hu3zero, hu3one]
    ring
  have stepB : ∫ x in (0 : ℝ)..1, u1 x * u3 x = -∫ x in (0 : ℝ)..1, u2 x * u2 x := by
    have h := integral_mul_deriv_eq_deriv_mul_unitInterval hu1 hu2 hu2 hu3 hdu1 hdu2
    rw [h, hu2zero, hu2one]
    ring
  have hsq : ∫ x in (0 : ℝ)..1, u2 x * u2 x = ∫ x in (0 : ℝ)..1, u2 x ^ 2 := by
    congr 1 with x
    ring
  rw [stepA, stepB, hsq]
  ring

end TauCeti
