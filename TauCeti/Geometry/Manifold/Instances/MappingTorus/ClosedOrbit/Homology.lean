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
  rw [addCircleProdFundamentalClass_def, orbitTorusHomologyClass_def,
    closedOrbitHomologyClass_def]
  have h := TopCat.singularHomologyCrossBilinear_naturality ℤ
    (𝟙 (TopCat.of UnitAddCircle))
    (TopCat.ofHom ⟨closedOrbit φ hx, continuous_closedOrbit hx⟩) 1 1 2 rfl
    (AddCircle.fundamentalClass 1) (AddCircle.fundamentalClass d)
  have hmap : (ContinuousMap.id UnitAddCircle).prodMap
      ⟨closedOrbit φ hx, continuous_closedOrbit hx⟩ =
      ⟨orbitTorus φ hx, continuous_orbitTorus hx⟩ := by
    apply ContinuousMap.ext
    intro p
    exact (orbitTorus_apply hx p).symm
  rw [TopCat.hom_id, TopCat.hom_ofHom, hmap, ContinuousMap.singularHomologyMap_id] at h
  exact h

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

end TauCeti.SmoothMappingTorus
