/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Complex.SquaredDistance
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Examples: squared distance on a punctured complex space

Milnor's proof that a closed complex submanifold of `ℂᴺ` of complex dimension `n` has the
homotopy type of a CW complex of dimension at most `n` uses two properties of the squared
distance `ρ_a x = ‖x - a‖²` along the inclusion. It is strictly plurisubharmonic, so that its
critical points have Morse index at most `n`; this holds along every holomorphic immersion. And
it is proper, so that its sublevels are compact; this needs the inclusion to be closed.

The punctured space `ℂ² ∖ {0}`, with its ordinary inclusion into `ℂ²`, shows that closedness
cannot be dropped. It is an open subset of `ℂ²`, hence a complex manifold whose inclusion is a
holomorphic open embedding. Along it every `ρ_a` is strictly plurisubharmonic, and its only
possible critical point is the centre `a` itself. Nevertheless, for `r > ‖a‖²` the bounded
sublevel `{x ∈ ℂ² ∖ {0} | ρ_a x ≤ r}` accumulates at the missing origin and is not compact, and
`ρ_a` is not a proper map. The punctured space is homotopy equivalent to the unit sphere
(`TauCeti.complSingletonHomotopyEquivSphere`), here the three-sphere.

The general results live with the APIs they extend; this file assembles them for `ℂ² ∖ {0}`.

## Used results

* `TauCeti.isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_subtypeVal`: along the inclusion of
  an open subset, squared distance is strictly plurisubharmonic at every point.
* `TauCeti.mvfderiv_norm_sq_sub_subtypeVal_eq_zero_iff`: along the inclusion of an open subset,
  the only critical point of `ρ_a` is `a`.
* `TauCeti.not_isCompact_compl_singleton_inter_preimage_Iic`: the sublevel `{ρ_a ≤ r}` of the
  space punctured at `y` is not compact when `ρ_a y < r`.
* `TauCeti.not_isProperMap_norm_sq_sub_compl_singleton`: `ρ_a` is not proper on a normed group
  punctured at a non-isolated point.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

open Set TopologicalSpace
open scoped Manifold

namespace TauCeti

/- The punctured plane `ℂ² ∖ {0}` with its ordinary inclusion into `ℂ²`: every squared distance is
strictly plurisubharmonic along the inclusion, yet its bounded sublevels with level strictly above
the origin's value are not compact. -/
example (a : EuclideanSpace ℂ (Fin 2)) {r : ℝ} (hr : ‖a‖ ^ 2 < r) :
    (∀ x : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℂ (Fin 2))),
      IsManifoldStrictlyPlurisubharmonicAt (EuclideanSpace ℂ (Fin 2))
        (fun y : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℂ (Fin 2))) ↦
          ‖(y : EuclideanSpace ℂ (Fin 2)) - a‖ ^ 2) x) ∧
    ¬IsCompact (({0}ᶜ : Set (EuclideanSpace ℂ (Fin 2))) ∩ (fun v ↦ ‖v - a‖ ^ 2) ⁻¹' Iic r) :=
  ⟨isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_subtypeVal _ a,
    not_isCompact_compl_singleton_inter_preimage_Iic (by simpa using hr)⟩

/- On `ℂ² ∖ {0}`, the only possible critical point of a squared distance is its centre. -/
example (a : EuclideanSpace ℂ (Fin 2))
    (x : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℂ (Fin 2)))) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
        (fun y : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℂ (Fin 2))) ↦
          ‖(y : EuclideanSpace ℂ (Fin 2)) - a‖ ^ 2) x = 0 ↔
      (x : EuclideanSpace ℂ (Fin 2)) = a :=
  mvfderiv_norm_sq_sub_subtypeVal_eq_zero_iff _ a x

end TauCeti
