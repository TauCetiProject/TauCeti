/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic

/-!
# Stable and unstable sets of the height function on the sphere

Let `v` be a unit vector and `X` **any** pseudo-gradient field adapted to the height function
`sphereHeight v` on the unit sphere `Sⁿ`. The height function has two critical points, the north
pole `v` (its strict global maximum, of index `n`) and the south pole `-v` (its strict global
minimum, of index `0`). For the flow of `X`:

* nothing flows into the north pole: `W^s(v) = {v}`;
* nothing flows out of the south pole: `W^u(-v) = {-v}`;
* everything except the south pole flows out of the north pole: `W^u(v) = Sⁿ \ {-v}`;
* everything except the north pole flows into the south pole: `W^s(-v) = Sⁿ \ {v}`.

These are the stable and unstable sets of the standard Morse function on the sphere. They do not
depend on the choice of `X`.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.stableSet_sphereHeight_self`,
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_sphereHeight_neg`,
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_sphereHeight_self` and
  `TauCeti.IsAdaptedPseudoGradient.stableSet_sphereHeight_neg`: the four sets.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Function Metric Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] {v : sphere (0 : E) 1}
  {X : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}

/-- **Nothing flows into the north pole.** The stable set of the north pole `v` is `{v}`. -/
@[simp]
theorem stableSet_sphereHeight_self (hX : IsAdaptedPseudoGradient (sphereHeight v) X) :
    hX.flow.stableSet v = {v} :=
  hX.stableSet_eq_singleton_of_lt
    ((contMDiff_sphereHeight (n := n) (m := 1) v).mdifferentiable one_ne_zero)
    fun _ ↦ sphereHeight_lt_self

/-- **Nothing flows out of the south pole.** The unstable set of the south pole `-v` is `{-v}`. -/
@[simp]
theorem unstableSet_sphereHeight_neg (hX : IsAdaptedPseudoGradient (sphereHeight v) X) :
    hX.flow.unstableSet (-v) = {-v} :=
  hX.unstableSet_eq_singleton_of_lt
    ((contMDiff_sphereHeight (n := n) (m := 1) v).mdifferentiable one_ne_zero)
    fun _ ↦ sphereHeight_neg_lt

/-- **Everything except the south pole flows out of the north pole.** The unstable set of the
north pole `v` is the complement of the south pole `-v`. -/
@[simp]
theorem unstableSet_sphereHeight_self (hX : IsAdaptedPseudoGradient (sphereHeight v) X) :
    hX.flow.unstableSet v = {-v}ᶜ :=
  hX.unstableSet_eq_compl_of_critical_eq_or_eq (isMorse_sphereHeight v)
    (fun y ↦ (mfderiv_sphereHeight_eq_zero_iff v y).1) (ne_neg_of_mem_unit_sphere ℝ v)
    hX.unstableSet_sphereHeight_neg

/-- **Everything except the north pole flows into the south pole.** The stable set of the south
pole `-v` is the complement of the north pole `v`. -/
@[simp]
theorem stableSet_sphereHeight_neg (hX : IsAdaptedPseudoGradient (sphereHeight v) X) :
    hX.flow.stableSet (-v) = {v}ᶜ :=
  hX.stableSet_eq_compl_of_critical_eq_or_eq (isMorse_sphereHeight v)
    (fun y ↦ (mfderiv_sphereHeight_eq_zero_iff v y).1) (ne_neg_of_mem_unit_sphere ℝ v)
    hX.stableSet_sphereHeight_self

end IsAdaptedPseudoGradient

end TauCeti
