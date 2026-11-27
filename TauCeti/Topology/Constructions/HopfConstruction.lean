/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.Join
public import TauCeti.Topology.Constructions.UnreducedSuspension

/-!
# The Hopf construction

The **Hopf construction** of a map `μ : X × Y → Z` is the map

`H(μ) : X * Y → SZ`, `[x, y, t] ↦ [μ (x, y), t]`

from the join of `X` and `Y` to the unreduced suspension of `Z`
(`TauCeti.Join.hopfConstruction`). It is well defined because both ends of the join go to the two
cone points of `SZ`, whatever `μ` does. When `X`, `Y` and `Z` are spheres, the join `Sⁿ * Sᵐ` is
`Sⁿ⁺ᵐ⁺¹` and the suspension of `Sⁿ` is `Sⁿ⁺¹`, so `H(μ)` is a map of spheres
(`TauCeti.sphereHopfMap`). Applied to the multiplications of `ℂ` and of `ℍ` on their unit
spheres it gives `(a, b) ↦ (2 a b, ‖a‖² - ‖b‖²)` (`TauCeti.coe_sphereHopfMap_mul`), which up to
conjugating one coordinate are the Hopf fibrations `S³ → S²` and `S⁷ → S⁴`.
Classically, applied to a multiplication on `Sⁿ` with a two-sided unit it gives a map
`S²ⁿ⁺¹ → Sⁿ⁺¹` of Hopf invariant `±1`, which is how a tangent frame on `Sⁿ` leads to a map of
Hopf invariant one.

The construction is natural in `X`, `Y` and `Z` (`TauCeti.Join.hopfConstruction_comp_map` and
`TauCeti.Join.hopfConstruction_comp`).

## References

* H. Hopf, *Über die Abbildungen von Sphären auf Sphären niedrigerer Dimension*, Fund. Math. 25
  (1935), 427–440.
* A. Hatcher, [*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf),
  §2.3, the Hopf construction.
-/

public section

noncomputable section

namespace TauCeti

namespace Join

open unitInterval

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The **Hopf construction** `[x, y, t] ↦ [μ (x, y), t]` of a map `μ : X × Y → Z`, from the join
of `X` and `Y` to the unreduced suspension of `Z`. -/
def hopfConstruction (μ : C(X × Y, Z)) : C(Join X Y, UnreducedSuspension Z) :=
  lift ⟨fun p => UnreducedSuspension.mk Z (μ (p.1, p.2.1), p.2.2), by fun_prop⟩
    (fun _ _ _ => UnreducedSuspension.mk_zero_eq _ _)
    (fun _ _ _ => UnreducedSuspension.mk_one_eq _ _)

@[simp]
theorem hopfConstruction_mk (μ : C(X × Y, Z)) (x : X) (y : Y) (t : I) :
    hopfConstruction μ (mk X Y (x, y, t)) = UnreducedSuspension.mk Z (μ (x, y), t) := by
  simp [hopfConstruction]

/-- The Hopf construction is natural in the two factors of the join: precomposing `μ` with
`f × g` precomposes its Hopf construction with the map of joins `f * g`. -/
theorem hopfConstruction_comp_map {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    (μ : C(X × Y, Z)) (f : C(X', X)) (g : C(Y', Y)) :
    hopfConstruction (μ.comp (f.prodMap g)) = (hopfConstruction μ).comp (map f g) :=
  hom_ext fun ⟨_, _, _⟩ => by simp

/-- The Hopf construction is natural in the target: postcomposing `μ` with `h` postcomposes its
Hopf construction with the suspension of `h`. -/
theorem hopfConstruction_comp {Z' : Type*} [TopologicalSpace Z'] (h : C(Z, Z'))
    (μ : C(X × Y, Z)) :
    hopfConstruction (h.comp μ) = (UnreducedSuspension.map h).comp (hopfConstruction μ) :=
  hom_ext fun ⟨_, _, _⟩ => by simp

end Join

end TauCeti
