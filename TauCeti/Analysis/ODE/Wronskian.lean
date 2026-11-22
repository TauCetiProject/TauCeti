/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Wronskian of a scalar second-order linear equation

For two solutions `φ`, `ψ` of the equation `f'' = q f` over `ℝ` or `ℂ`, without a first-order
term, the Wronskian `ψ φ' - φ ψ'` has derivative `ψ q φ - φ q ψ = 0`, so it is constant. For the
fundamental pair with `φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1` it is identically one.

More generally, for two solutions `u`, `v` of a Sturm–Liouville equation `(p y')' = q y` on an
open preconnected domain `s`, the weighted Wronskian `u (p v') - (p u') v` has zero derivative and
is therefore constant on `s`.

## Main results

* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` is
  constant.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
* `TauCeti.hasDerivAt_weightedWronskian`: the weighted Wronskian of two solutions of
  `(p y')' = q y` has zero derivative.
* `TauCeti.weightedWronskian_eq_of_hasDerivAtOn`: the weighted Wronskian of two solutions of
  `(p y')' = q y` on an open preconnected set is constant.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {q φ φ' ψ ψ' : 𝕜 → 𝕜}

/-- The Wronskian `ψ φ' - φ ψ'` of two solutions of `f'' = q f` on `ℝ` or `ℂ` is constant. -/
theorem wronskian_eq_of_hasDerivAt
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t) (t a : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = ψ a * φ' a - φ a * ψ' a := by
  have hderiv : ∀ t, HasDerivAt (fun r ↦ ψ r * φ' r - φ r * ψ' r) 0 t := fun t ↦
    (((hψ t).mul (hφ' t)).sub ((hφ t).mul (hψ' t))).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun t ↦ (hderiv t).differentiableAt)
    (fun t ↦ (hderiv t).deriv) t a

/-- The Wronskian `ψ φ' - φ ψ'` of the fundamental pair of solutions of `f'' = q f` at `a`, with
`φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1`, is identically one. The value `ψ'(a)` is irrelevant,
since it is multiplied by `φ(a) = 0`. -/
theorem wronskian_eq_one_of_hasDerivAt {a : 𝕜}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (t : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = 1 := by
  rw [wronskian_eq_of_hasDerivAt hφ hφ' hψ hψ' t a, hφa, hφ'a, hψa]
  ring

/-- The weighted Wronskian `u (p v') - (p u') v` of two solutions of the Sturm–Liouville equation
`(p y')' = q y` has zero derivative. -/
theorem hasDerivAt_weightedWronskian {p q u u' v v' : 𝕜 → 𝕜} {t : 𝕜}
    (hu : HasDerivAt u (u' t) t) (hpu : HasDerivAt (fun r ↦ p r * u' r) (q t * u t) t)
    (hv : HasDerivAt v (v' t) t) (hpv : HasDerivAt (fun r ↦ p r * v' r) (q t * v t) t) :
    HasDerivAt (fun r ↦ u r * (p r * v' r) - (p r * u' r) * v r) 0 t :=
  ((hu.mul hpv).sub (hpu.mul hv)).congr_deriv (by ring)

/-- The weighted Wronskian `u (p v') - (p u') v` of two solutions of the Sturm–Liouville equation
`(p y')' = q y` on an open preconnected set `s` is constant on `s`. -/
theorem weightedWronskian_eq_of_hasDerivAtOn {p q u u' v v' : 𝕜 → 𝕜} {s : Set 𝕜}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s)
    (hu : ∀ t ∈ s, HasDerivAt u (u' t) t)
    (hpu : ∀ t ∈ s, HasDerivAt (fun r ↦ p r * u' r) (q t * u t) t)
    (hv : ∀ t ∈ s, HasDerivAt v (v' t) t)
    (hpv : ∀ t ∈ s, HasDerivAt (fun r ↦ p r * v' r) (q t * v t) t)
    {t a : 𝕜} (ht : t ∈ s) (ha : a ∈ s) :
    u t * (p t * v' t) - (p t * u' t) * v t = u a * (p a * v' a) - (p a * u' a) * v a := by
  have hderiv : ∀ r ∈ s,
      HasDerivAt (fun x ↦ u x * (p x * v' x) - (p x * u' x) * v x) 0 r := fun r hr ↦
    hasDerivAt_weightedWronskian (hu r hr) (hpu r hr) (hv r hr) (hpv r hr)
  exact hs_open.is_const_of_deriv_eq_zero hs_conn
    (fun r hr ↦ (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hderiv r hr).deriv) ht ha

end TauCeti
