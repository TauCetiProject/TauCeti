/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.AddCircle
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit.Naturality

/-!
# Integral classes of closed suspension orbits and their tori

A point of period `d` determines an integral one-cycle in the mapping torus: push forward
the circuit class of `AddCircle d` along its closed orbit. The cross product of this class
with the independent unit circle is the integral class of the parametrized orbit torus.
We identify this cross product with the pushforward along the actual periodic-torus map.

Traversing an orbit `k` times multiplies both classes by `k`. The proof uses the reduction
map `AddCircle (k * d) → AddCircle d`, which factors the actual orbit parametrizations,
and its action on the circuit class. Thus multiple covers retain their integral
multiplicity, although their images coincide. These statements need no symplectic form
or compactness of the fiber manifold.

The classes are natural in the periodic orbit:

* **Change of starting point.** The closed orbits through `x` and through `φ^[j] x` differ by a
  rotation of the period circle, which is homotopic to the identity, so they have the same
  integral class, and so do their orbit tori.
* **Conjugacies.** The map `[t, y] ↦ [t, g y]` of mapping tori induced by a continuous map `g`
  intertwining `φ` and `ψ` sends the class of the closed orbit through `x` to that of the closed
  orbit through `g x`, and likewise for the orbit tori.
* **Iterates.** For `k ≠ 0` and `d > 0`, the map `Y_(φ^k) → Y_φ`, `[t, x] ↦ [k t, x]`, sends the
  class of the closed orbit of `φ ^ k` through `x` to `k.sign` times the class of the closed orbit
  of `φ` through `x` of period `k.natAbs * d`. The parameter map is the rescaling `[t] ↦ [k t]`
  of period circles, which reverses orientation exactly when `k < 0`. The orbit tori behave in
  the same way.

## Main results

* `TauCeti.SmoothMappingTorus.singularHomologyMap_orbitTorus_addCircleProdFundamentalClass`: the
  orbit-torus class is the pushforward of the class of the parameter torus.
* `TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_const_mul`,
  `TauCeti.SmoothMappingTorus.orbitTorusHomologyClass_const_mul`: traversing an orbit `k` times
  multiplies its class by `k`.
* `TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_apply_iterate`,
  `TauCeti.SmoothMappingTorus.orbitTorusHomologyClass_apply_iterate`: the classes do not depend
  on the starting point in the periodic orbit.
* `TauCeti.SmoothMappingTorus.singularHomologyMap_map_closedOrbitHomologyClass`,
  `TauCeti.SmoothMappingTorus.singularHomologyMap_prodMap_map_orbitTorusHomologyClass`:
  naturality under conjugacies.
* `TauCeti.SmoothMappingTorus.singularHomologyMap_iterateMap_closedOrbitHomologyClass`,
  `TauCeti.SmoothMappingTorus.singularHomologyMap_prodMap_iterateMap_orbitTorusHomologyClass`:
  the iterate map multiplies the classes by the sign of the iterate.

## References

* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2.
* A. Hatcher, *Algebraic Topology*, Theorem 2A.1 and Section 3.B.
-/

public noncomputable section

open CategoryTheory AlgebraicTopology MonoidalCategory
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {φ : M ≃ₘ^n⟮I, I⟯ M} {d : ℕ} {x : M}

/-- The integral class obtained by pushing the circuit of the period quotient along the
closed orbit. For positive period the parameter follows the positive real time direction. -/
def closedOrbitHomologyClass (hx : Function.IsPeriodicPt φ d x) :
    ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1 :=
  ContinuousMap.singularHomologyMap ℤ 1 ⟨closedOrbit φ hx, continuous_closedOrbit hx⟩
    (AddCircle.fundamentalClass d)

/-- The orbit class is the pushforward of the circuit class of its period circle. -/
theorem closedOrbitHomologyClass_def (hx : Function.IsPeriodicPt φ d x) :
    closedOrbitHomologyClass hx =
      ContinuousMap.singularHomologyMap ℤ 1 ⟨closedOrbit φ hx, continuous_closedOrbit hx⟩
        (AddCircle.fundamentalClass d) := (rfl)

/-- The cross product of the independent unit circle with the closed suspension orbit.
For positive orbit period this is the integral class of the parametrized periodic torus. -/
def orbitTorusHomologyClass (hx : Function.IsPeriodicPt φ d x) :
    ((singularChains ℤ).obj (TopCat.of (UnitAddCircle × SmoothMappingTorus φ))).homology 2 :=
  TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
    (TopCat.of (SmoothMappingTorus φ)) 1 1 2 rfl
      (AddCircle.fundamentalClass 1) (closedOrbitHomologyClass hx)

/-- The orbit-torus class is the ordered cross product of the two one-dimensional classes. -/
theorem orbitTorusHomologyClass_def (hx : Function.IsPeriodicPt φ d x) :
    orbitTorusHomologyClass hx =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) 1 1 2 rfl
          (AddCircle.fundamentalClass 1) (closedOrbitHomologyClass hx) := (rfl)

/-- The cross-product class is represented by the actual periodic-torus parametrization,
with the orientation given by the independent circle followed by the orbit circle. -/
theorem singularHomologyMap_orbitTorus_addCircleProdFundamentalClass
    (hx : Function.IsPeriodicPt φ d x) :
    ContinuousMap.singularHomologyMap ℤ 2
        ⟨orbitTorus φ hx, continuous_orbitTorus hx⟩
        (addCircleProdFundamentalClass 1 d) = orbitTorusHomologyClass hx := by
  have hmap : (ContinuousMap.id UnitAddCircle).prodMap
      ⟨closedOrbit φ hx, continuous_closedOrbit hx⟩ =
      ⟨orbitTorus φ hx, continuous_orbitTorus hx⟩ := by
    apply ContinuousMap.ext
    intro p
    exact (orbitTorus_apply hx p).symm
  rw [addCircleProdFundamentalClass_def, ← hmap,
    TopCat.singularHomologyCrossBilinear_naturality_right, orbitTorusHomologyClass_def,
    closedOrbitHomologyClass_def]

/-- Repeated traversal multiplies the integral closed-orbit class by `k`. The factorization
is through the actual reduction map from the circle of length `k * d` to that of length `d`. -/
theorem closedOrbitHomologyClass_const_mul (hx : Function.IsPeriodicPt φ d x)
    [Fact (0 < (d : ℝ))] (k : ℕ) :
    closedOrbitHomologyClass (hx.const_mul k) = k • closedOrbitHomologyClass hx := by
  have hdm : ((k * d : ℕ) : ℝ) ∈ AddSubgroup.zmultiples (d : ℝ) := by
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨(k : ℤ), ?_⟩
    simp [Nat.cast_mul]
  have hcomp :
      (⟨closedOrbit φ hx, continuous_closedOrbit hx⟩ : C(AddCircle (d : ℝ), _)).comp
        ⟨AddCircle.coverMap hdm, AddCircle.continuous_coverMap hdm⟩ =
      ⟨closedOrbit φ (hx.const_mul k), continuous_closedOrbit (hx.const_mul k)⟩ := by
    ext θ
    exact closedOrbit_coverMap hx (hx.const_mul k) hdm θ
  rw [closedOrbitHomologyClass_def, ← hcomp, ContinuousMap.singularHomologyMap_comp,
    AddCircle.singularHomologyMap_coverMap_fundamentalClass hdm (k : ℤ)
      (by simp [Nat.cast_mul])]
  rw [map_zsmul, closedOrbitHomologyClass_def, natCast_zsmul]

/-- Repeated traversal multiplies the integral orbit-torus class. For `k > 0` the orbit
tori have the same image, while their parametrized classes retain the factor `k`. -/
theorem orbitTorusHomologyClass_const_mul (hx : Function.IsPeriodicPt φ d x)
    [Fact (0 < (d : ℝ))] (k : ℕ) :
    orbitTorusHomologyClass (hx.const_mul k) = k • orbitTorusHomologyClass hx := by
  rw [orbitTorusHomologyClass_def, closedOrbitHomologyClass_const_mul hx k, map_nsmul,
    orbitTorusHomologyClass_def]

/-! ### Change of starting point -/

/-- Starting the closed orbit at `φ^[j] x` instead of `x` does not change its integral class:
the two parametrizations differ by a rotation of the period circle, which is homotopic to the
identity. -/
@[simp]
theorem closedOrbitHomologyClass_apply_iterate (hx : Function.IsPeriodicPt φ d x) (j : ℕ) :
    closedOrbitHomologyClass (hx.apply_iterate j) = closedOrbitHomologyClass hx := by
  have hcomp : (⟨closedOrbit φ (hx.apply_iterate j), continuous_closedOrbit _⟩ :
      C(AddCircle (d : ℝ), SmoothMappingTorus φ)) =
      (⟨closedOrbit φ hx, continuous_closedOrbit hx⟩ : C(AddCircle (d : ℝ), _)).comp
        (ContinuousMap.addRight ((j : ℝ) : AddCircle (d : ℝ))) := by
    ext θ
    exact closedOrbit_apply_iterate hx j θ
  rw [closedOrbitHomologyClass_def, hcomp, ContinuousMap.singularHomologyMap_comp,
    AddCircle.singularHomologyMap_addRight, closedOrbitHomologyClass_def]

/-- Starting the orbit torus at `φ^[j] x` instead of `x` does not change its integral class. -/
@[simp]
theorem orbitTorusHomologyClass_apply_iterate (hx : Function.IsPeriodicPt φ d x) (j : ℕ) :
    orbitTorusHomologyClass (hx.apply_iterate j) = orbitTorusHomologyClass hx := by
  rw [orbitTorusHomologyClass_def, closedOrbitHomologyClass_apply_iterate,
    orbitTorusHomologyClass_def]

/-! ### Conjugacies -/

section Map

variable {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {ψ : N ≃ₘ^n⟮J, J⟯ N} {g : M → N} (hgc : Continuous g) (hg : Function.Semiconj g φ ψ)

/-- The map of mapping tori induced by a continuous map `g` intertwining `φ` and `ψ` sends the
integral class of the closed orbit through `x` to that of the closed orbit through `g x`. -/
theorem singularHomologyMap_map_closedOrbitHomologyClass (hx : Function.IsPeriodicPt φ d x) :
    ContinuousMap.singularHomologyMap ℤ 1 ⟨map φ ψ g hg, continuous_map φ ψ g hg hgc⟩
      (closedOrbitHomologyClass hx) = closedOrbitHomologyClass (hx.map hg) := by
  have hcomp : (⟨map φ ψ g hg, continuous_map φ ψ g hg hgc⟩ :
      C(SmoothMappingTorus φ, SmoothMappingTorus ψ)).comp
        ⟨closedOrbit φ hx, continuous_closedOrbit hx⟩ =
      ⟨closedOrbit ψ (hx.map hg), continuous_closedOrbit _⟩ := by
    ext θ
    exact map_closedOrbit g hg hx θ
  rw [closedOrbitHomologyClass_def, ← ContinuousMap.singularHomologyMap_comp, hcomp,
    closedOrbitHomologyClass_def]

/-- The map `(s, [t, y]) ↦ (s, [t, g y])` induced by a continuous map `g` intertwining `φ` and
`ψ` sends the integral class of the orbit torus through `x` to that of the orbit torus through
`g x`. -/
theorem singularHomologyMap_prodMap_map_orbitTorusHomologyClass
    (hx : Function.IsPeriodicPt φ d x) :
    ContinuousMap.singularHomologyMap ℤ 2
        ((ContinuousMap.id UnitAddCircle).prodMap ⟨map φ ψ g hg, continuous_map φ ψ g hg hgc⟩)
        (orbitTorusHomologyClass hx) = orbitTorusHomologyClass (hx.map hg) := by
  rw [orbitTorusHomologyClass_def, TopCat.singularHomologyCrossBilinear_naturality_right,
    singularHomologyMap_map_closedOrbitHomologyClass hgc hg hx, orbitTorusHomologyClass_def]

end Map

/-! ### Iterates -/

section Iterate

variable (k : ℤ) (hx : Function.IsPeriodicPt (φ ^ k) d x)
  (hx' : Function.IsPeriodicPt φ (k.natAbs * d) x)

/-- For nonzero `k` and positive `d`, the iterate map `Y_(φ^k) → Y_φ` sends the integral class of
the closed orbit of `φ ^ k` through `x` to `k.sign` times the integral class of the closed orbit
of `φ` through `x`, of period `k.natAbs * d`: the parameter map is the rescaling
`[t] ↦ [k t]`, which reverses orientation exactly when `k` is negative. -/
theorem singularHomologyMap_iterateMap_closedOrbitHomologyClass [Fact (0 < (d : ℝ))]
    (hk : k ≠ 0) :
    ContinuousMap.singularHomologyMap ℤ 1 ⟨iterateMap φ k, continuous_iterateMap φ k⟩
      (closedOrbitHomologyClass hx) = k.sign • closedOrbitHomologyClass hx' := by
  have hd : (d : ℝ) ≠ 0 := (Fact.out : (0 : ℝ) < d).ne'
  have hkd : ((k.natAbs * d : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Int.natAbs_ne_zero.2 hk)) hd
  have hcomp : (⟨iterateMap φ k, continuous_iterateMap φ k⟩ :
      C(SmoothMappingTorus (φ ^ k), SmoothMappingTorus φ)).comp
        ⟨closedOrbit (φ ^ k) hx, continuous_closedOrbit hx⟩ =
      (⟨closedOrbit φ hx', continuous_closedOrbit hx'⟩ : C(_, SmoothMappingTorus φ)).comp
        ((AddCircle.homeomorphAddCircle _ _ hd hkd : C(_, _)).comp
          ⟨fun θ : AddCircle (d : ℝ) ↦ k.sign • θ, continuous_zsmul _⟩) := by
    ext θ
    exact congrFun (iterateMap_comp_closedOrbit k hx hx' hd hkd) θ
  rw [closedOrbitHomologyClass_def, ← ContinuousMap.singularHomologyMap_comp, hcomp,
    ContinuousMap.singularHomologyMap_comp, ContinuousMap.singularHomologyMap_comp,
    AddCircle.singularHomologyMap_zsmul_fundamentalClass, map_zsmul,
    AddCircle.singularHomologyMap_homeomorphAddCircle_fundamentalClass, map_zsmul,
    closedOrbitHomologyClass_def]

/-- For nonzero `k` and positive `d`, the map `(s, y) ↦ (s, iterateMap φ k y)` sends the integral
class of the orbit torus of `φ ^ k` through `x` to `k.sign` times the integral class of the orbit
torus of `φ` through `x`, of period `k.natAbs * d`. -/
theorem singularHomologyMap_prodMap_iterateMap_orbitTorusHomologyClass [Fact (0 < (d : ℝ))]
    (hk : k ≠ 0) :
    ContinuousMap.singularHomologyMap ℤ 2
        ((ContinuousMap.id UnitAddCircle).prodMap ⟨iterateMap φ k, continuous_iterateMap φ k⟩)
        (orbitTorusHomologyClass hx) = k.sign • orbitTorusHomologyClass hx' := by
  rw [orbitTorusHomologyClass_def, TopCat.singularHomologyCrossBilinear_naturality_right,
    singularHomologyMap_iterateMap_closedOrbitHomologyClass k hx hx' hk, map_zsmul,
    orbitTorusHomologyClass_def]

end Iterate

end TauCeti.SmoothMappingTorus
