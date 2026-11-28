/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Depth.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.SupportedCohomology.Basic
import TauCeti.RingTheory.Depth.LocalCohomology

/-!
# Depth vanishing for supported sheaf cohomology on an affine scheme

Over a Noetherian ring `R`, transferring algebraic depth vanishing
(`localCohomology.isZero_obj_of_lt_depth`) across the local-cohomology comparison
`TauCeti.AlgebraicGeometry.supportedModuleHTopTildeLinearEquivLocalCohomology` shows that
`H^q_{V(I)}(Spec R, M~)` vanishes for `q < I.depth M` when `M` is a finite `R`-module
(Stacks Project, Tag 0AVZ).

## Main results

* `TauCeti.AlgebraicGeometry.subsingleton_supportedModuleH_tilde_of_lt_depth` (Stacks 0AVZ):
  `H^q_{V(I)}(Spec R, M~)` vanishes for `q < I.depth M` when `R` is Noetherian and `M` is finite.

## References

* [The Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- **Geometric depth vanishing.** For a finite module `M` over a Noetherian ring `R` and an ideal
`I`, the supported sheaf cohomology `H^q_{V(I)}(Spec R, M~)` vanishes for `q < I.depth M`. -/
@[stacks 0AVZ]
theorem subsingleton_supportedModuleH_tilde_of_lt_depth {R : CommRingCat.{u}} [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] {q : ℕ} (hq : (q : ℕ∞) < I.depth M) :
    Subsingleton ((modulesSpecToSheaf.obj (tilde M)).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q) := by
  have := ModuleCat.subsingleton_of_isZero (localCohomology.isZero_obj_of_lt_depth I M hq)
  exact (supportedModuleHTopTildeLinearEquivLocalCohomology I M q).subsingleton

end TauCeti.AlgebraicGeometry
