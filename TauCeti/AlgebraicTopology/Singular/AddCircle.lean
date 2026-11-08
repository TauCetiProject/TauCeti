/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.HomologyCross
public import TauCeti.Topology.Homotopy.Homotopic.Translation
public import TauCeti.Topology.Instances.AddCircle.Cover

/-!
# The integral class of a positive circuit of an additive circle

The loop `t ↦ [t * p]` defines `AddCircle.fundamentalClass p` in the first integral singular
homology of `AddCircle p`. For positive `p`, a loop winding `n` times represents `n` times this
class. Reduction from a circle of length `k * p` to one of length `p` therefore multiplies
the circuit class by `k`. This keeps track of traversal multiplicity when closed curves are
parametrized by circles of different lengths. Likewise, the map `θ ↦ n • θ` of a positive-period
circle multiplies the circuit class by `n`, and the rescaling homeomorphism between circles of
nonzero periods `p` and `q` sends one circuit class to the other. Rotations of a circle are
homotopic to the identity, so they act trivially on its singular homology; in particular the
circuit class does not depend on the starting point of the circuit.

We use Mathlib's `AddCircle.zsmulLoop` and winding-number isomorphism, and the degree-one
Hurewicz map. The homological convention is the class of the loop itself. The ordered cross
product of two circuit classes gives the class of a product of period quotients; for positive
periods this is the positively oriented parameter torus.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.1 and Theorem 2A.1.
-/

public noncomputable section

open CategoryTheory TauCeti TauCeti.HurewiczOne Multiplicative

namespace AddCircle

variable (p : ℝ)

/-- The integral homology class of the circuit `t ↦ [t * p]` of `AddCircle p`. For `p > 0`
this follows the positive real time direction once around the circle. -/
def fundamentalClass : ((singularChains ℤ).obj (TopCat.of (AddCircle p))).homology 1 :=
  H₁AddEquivHomology _ (loopClass (X := TopCat.of (AddCircle p)) (zsmulLoop p 0 1))

/-- The circuit class is the Hurewicz class of the straight loop winding once. -/
theorem fundamentalClass_def :
    fundamentalClass p = H₁AddEquivHomology _
      (loopClass (X := TopCat.of (AddCircle p)) (zsmulLoop p 0 1)) := (rfl)

/-- Winding `n` times around a positive-period circle multiplies its circuit class by `n`.
Negative windings reverse orientation. -/
@[simp]
theorem H₁AddEquivHomology_loopClass_zsmulLoop [Fact (0 < p)] (n : ℤ) :
    H₁AddEquivHomology _ (loopClass (X := TopCat.of (AddCircle p)) (zsmulLoop p 0 n)) =
      n • fundamentalClass p := by
  have hpow : FundamentalGroup.fromPath (.mk (zsmulLoop p 0 n)) =
      (FundamentalGroup.fromPath (.mk (zsmulLoop p 0 1))) ^ n := by
    apply (windingNumberIso ((0 : ℝ) : AddCircle p)).injective
    apply Multiplicative.toAdd.injective
    have hwinding : windingNumber (x := ((0 : ℝ) : AddCircle p))
        (FundamentalGroup.fromPath (.mk (zsmulLoop p 0 n))) =
        n • windingNumber (x := ((0 : ℝ) : AddCircle p))
          (FundamentalGroup.fromPath (.mk (zsmulLoop p 0 1))) := by
      simp [windingNumber_zsmulLoop (p := p)]
    simp only [map_zpow, toAdd_zpow]
    exact hwinding
  have h := congrArg
    (fun g ↦ (hurewicz₁ (TopCat.of (AddCircle p)) ((0 : ℝ) : AddCircle p) g).toAdd) hpow
  have hclass : loopClass (X := TopCat.of (AddCircle p)) (zsmulLoop p 0 n) =
      n • loopClass (X := TopCat.of (AddCircle p)) (zsmulLoop p 0 1) := by
    simpa [hurewicz₁_mk (X := TopCat.of (AddCircle p))] using h
  rw [hclass, map_zsmul, fundamentalClass_def]

variable {p} {q : ℝ} (h : p ∈ AddSubgroup.zmultiples q)

/-- A reduction map from a circle of length `p = k * q` to the positive-period circle of
length `q` sends one circuit to `k` circuits. -/
theorem singularHomologyMap_coverMap_fundamentalClass [Fact (0 < q)] (k : ℤ)
    (hp : p = k * q) :
    ContinuousMap.singularHomologyMap ℤ 1 ⟨coverMap h, continuous_coverMap h⟩
      (fundamentalClass p) = k • fundamentalClass q := by
  rw [fundamentalClass_def, homologyMap_H₁AddEquivHomology_loopClass]
  have heq : loopClass (X := TopCat.of (AddCircle q)) ((zsmulLoop p 0 1).map
      (continuous_coverMap h)) =
      loopClass (X := TopCat.of (AddCircle q)) (zsmulLoop q 0 k) := by
    apply loopClass_eq_of_apply_eq
    intro t
    simp only [Path.map_coe, Function.comp_apply]
    rw [zsmulLoop_apply p 0 1, zsmulLoop_apply q 0 k]
    simp only [one_zsmul, coverMap_coe, coe_zero, add_zero, ← coe_zsmul,
      zsmul_eq_mul, hp]
    congr 1
    ring
  rw [heq, H₁AddEquivHomology_loopClass_zsmulLoop]

/-- **Rotations act trivially on the singular homology of a circle**: the rotation `θ ↦ θ + a`
is homotopic to the identity, since `AddCircle p` is path connected. -/
@[simp]
theorem singularHomologyMap_addRight (R : Type) [Ring R] (n : ℕ) (a : AddCircle p)
    (z : ((singularChains R).obj (TopCat.of (AddCircle p))).homology n) :
    ContinuousMap.singularHomologyMap R n (ContinuousMap.addRight a) z = z := by
  rw [← ContinuousMap.singularHomologyMap_eq_of_homotopic R n
    (PathConnectedSpace.joined 0 a).homotopic_id_addRight, ContinuousMap.singularHomologyMap_id]

/-- The map `θ ↦ n • θ` of a positive-period circle multiplies its circuit class by `n`. -/
theorem singularHomologyMap_zsmul_fundamentalClass [Fact (0 < p)] (n : ℤ) :
    ContinuousMap.singularHomologyMap ℤ 1 ⟨fun θ : AddCircle p ↦ n • θ, continuous_zsmul n⟩
      (fundamentalClass p) = n • fundamentalClass p := by
  rw [← H₁AddEquivHomology_loopClass_zsmulLoop, fundamentalClass_def,
    ContinuousMap.singularHomologyMap_loopClass]
  congr 1
  apply loopClass_eq_of_apply_eq
  intro t
  rw [Path.map_coe, Function.comp_apply, zsmulLoop_apply, zsmulLoop_apply]
  simp

/-- The rescaling homeomorphism `ℝ / pℤ ≃ ℝ / qℤ`, `[t] ↦ [t q / p]`, sends the circuit class of
`AddCircle p` to that of `AddCircle q`. -/
@[simp]
theorem singularHomologyMap_homeomorphAddCircle_fundamentalClass (hp : p ≠ 0) (hq : q ≠ 0) :
    ContinuousMap.singularHomologyMap ℤ 1 (homeomorphAddCircle p q hp hq : C(_, _))
      (fundamentalClass p) = fundamentalClass q := by
  rw [fundamentalClass_def, ContinuousMap.singularHomologyMap_loopClass, fundamentalClass_def]
  congr 1
  apply loopClass_eq_of_apply_eq
  intro t
  rw [Path.map_coe, Function.comp_apply, zsmulLoop_apply, zsmulLoop_apply]
  simp only [one_zsmul, coe_zero, add_zero, ContinuousMap.coe_ofClass,
    homeomorphAddCircle_apply_mk]
  congr 1
  field_simp

end AddCircle

namespace TauCeti

/-- The cross product of the circuit classes of `AddCircle p` and `AddCircle q`, in that
order. For positive periods this is the class of the positively oriented parameter torus. -/
def addCircleProdFundamentalClass (p q : ℝ) :
    ((singularChains ℤ).obj (TopCat.of (AddCircle p × AddCircle q))).homology 2 :=
  TopCat.singularHomologyCrossBilinear ℤ (TopCat.of (AddCircle p)) (TopCat.of (AddCircle q))
    1 1 2 rfl (AddCircle.fundamentalClass p) (AddCircle.fundamentalClass q)

/-- The class of the parameter torus is the ordered cross product of its circuit classes. -/
theorem addCircleProdFundamentalClass_def (p q : ℝ) :
    addCircleProdFundamentalClass p q =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of (AddCircle p)) (TopCat.of (AddCircle q))
        1 1 2 rfl (AddCircle.fundamentalClass p) (AddCircle.fundamentalClass q) := (rfl)

end TauCeti
