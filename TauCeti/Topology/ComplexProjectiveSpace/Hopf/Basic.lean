/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Action
public import TauCeti.Analysis.Normed.Module.Normalize
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import TauCeti.Topology.ComplexProjectiveSpace.Charts
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import all TauCeti.Topology.ComplexProjectiveSpace.Basic

/-!
# The Hopf fibration `S¹ → S²ⁿ⁺¹ → CPⁿ`

Complex projective space `CPⁿ` is the quotient of the unit sphere `S²ⁿ⁺¹` of `ℂⁿ⁺¹` by the unit
complex numbers (`TauCeti.ComplexProjectiveSpace`), and the quotient map
`TauCeti.ComplexProjectiveSpace.mk` is the **Hopf fibration**. This file shows that it is a locally
trivial bundle with fibre the unit circle `S¹ ⊆ ℂ`, and hence a Serre fibration.

The charts live over the standard affine opens `{X_k ≠ 0}`. Over such an open, the direction
`v_k / |v_k|` of the `k`th coordinate is a continuous map to the unit circle that is equivariant
for the circle action, so it trivializes the orbit projection (`TauCeti.orbitTrivialization`),
giving the chart `v ↦ ([v], v_k / |v_k|)` (`TauCeti.ComplexProjectiveSpace.hopfTrivialization`).

## Main definitions

* `TauCeti.ComplexProjectiveSpace.hopfTrivialization`: the chart of the Hopf fibration over
  `{X_k ≠ 0}`, with fibre the unit circle.
* `TauCeti.ComplexProjectiveSpace.hopfFiberHomeomorph`: the fibre of the Hopf fibration over `[v]`
  is homeomorphic to the unit circle, through `u ↦ u • v`.

## Main results

* `TauCeti.ComplexProjectiveSpace.exists_trivialization_mk`: the Hopf fibration is locally trivial
  with fibre the unit circle.
* `TauCeti.ComplexProjectiveSpace.mk_mem_serreFibrations`: the Hopf fibration is a Serre
  fibration.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  §4.2, Example 4.45.
-/

public section

noncomputable section

open Metric Set Topology

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

variable (k : Fin (n + 1))

/-- The direction `v_k / |v_k|` of the `k`th coordinate is equivariant for the unit complex
numbers on the unit vectors with `v_k ≠ 0`. -/
private theorem sphereDirection_smul_apply (c : sphere (0 : ℂ) 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) (hv : mk n v ∈ affineOpen k) :
    sphereDirection 1 ((c • v).1 k) = c * sphereDirection 1 (v.1 k) := by
  have hv' : v.1 k ≠ 0 := (mk_mem_affineOpen_iff k v).1 hv
  have h : (c • v).1 k = ‖v.1 k‖ • ((c * sphereDirection 1 (v.1 k) : sphere (0 : ℂ) 1) : ℂ) := by
    simp [← mul_smul_comm]
  rw [h, sphereDirection_smul_of_pos _ (norm_pos_iff.2 hv')]

/-- The direction `v_k / |v_k|` of the `k`th coordinate is continuous on the unit vectors with
`v_k ≠ 0`. -/
private theorem continuousOn_sphereDirection_apply :
    ContinuousOn (fun v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦ sphereDirection 1 (v.1 k))
      (mk n ⁻¹' affineOpen k) := fun v hv ↦
  ((continuousAt_sphereDirection _ ((mk_mem_affineOpen_iff k v).1 hv)).comp
    (f := fun v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦ v.1 k)
    ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℂ) k).comp
      continuous_subtype_val).continuousAt).continuousWithinAt

/-- The **chart of the Hopf fibration** over the affine open `{X_k ≠ 0}` of `CPⁿ`, with fibre the
unit circle. It is the orbit trivialization (`TauCeti.orbitTrivialization`) determined by the
equivariant map `v ↦ v_k / |v_k|`, so it sends a unit vector `v` with `v_k ≠ 0` to
`([v], v_k / |v_k|)`. -/
def hopfTrivialization : Bundle.Trivialization (sphere (0 : ℂ) 1) (mk n) :=
  orbitTrivialization (affineOpen k) (isOpen_affineOpen k)
    (fun v ↦ sphereDirection 1 (v.1 k)) (continuousOn_sphereDirection_apply k)
    (sphereDirection_smul_apply k)

variable {k}

@[simp]
theorem hopfTrivialization_baseSet : (hopfTrivialization (n := n) k).baseSet = affineOpen k :=
  orbitTrivialization_baseSet

/-- The fibre coordinate of the chart over `{X_k ≠ 0}` is the direction `v_k / |v_k|` of the
`k`th coordinate. -/
@[simp]
theorem hopfTrivialization_apply (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    hopfTrivialization k v = (mk n v, sphereDirection 1 (v.1 k)) :=
  orbitTrivialization_apply v

/-- The inverse of the chart over `{X_k ≠ 0}` sends `([v], u)` to `(u * (v_k / |v_k|)⁻¹) • v`. -/
@[simp]
theorem hopfTrivialization_symm_apply_mk {v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1}
    (hv : mk n v ∈ affineOpen k) (u : sphere (0 : ℂ) 1) :
    (hopfTrivialization k).toOpenPartialHomeomorph.symm (mk n v, u) =
      (u * (sphereDirection 1 (v.1 k))⁻¹) • v :=
  orbitTrivialization_symm_apply_mk hv u

variable (n) in
/-- **The Hopf fibration is locally trivial**: every point of `CPⁿ` lies in the base of a chart of
`S²ⁿ⁺¹ → CPⁿ` with fibre the unit circle. -/
theorem exists_trivialization_mk (p : ComplexProjectiveSpace n) :
    ∃ e : Bundle.Trivialization (sphere (0 : ℂ) 1) (mk n), p ∈ e.baseSet :=
  let ⟨k, hk⟩ := exists_mem_affineOpen p
  ⟨hopfTrivialization k, by rwa [hopfTrivialization_baseSet]⟩

variable (n) in
/-- The Hopf fibration `S²ⁿ⁺¹ → CPⁿ` as a morphism of `TopCat`. -/
abbrev hopfHom :
    _root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) ⟶
      _root_.TopCat.of (ComplexProjectiveSpace n) :=
  _root_.TopCat.ofHom ⟨mk n, continuous_mk n⟩

variable (n) in
/-- **The Hopf fibration `S²ⁿ⁺¹ → CPⁿ` is a Serre fibration**, being locally trivial with fibre the
unit circle. -/
theorem mk_mem_serreFibrations : TopCat.serreFibrations (hopfHom n) :=
  TopCat.mem_serreFibrations_of_exists_trivialization (exists_trivialization_mk n)

/-! ### The fibre -/

variable (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- The orbit map `u ↦ u • v` of the unit circle on a unit vector `v` lands in the fibre of the Hopf
fibration over `[v]`. -/
private def orbitFiber (u : sphere (0 : ℂ) 1) : mk n ⁻¹' {mk n v} :=
  ⟨u • v, by simp⟩

/-- The **fibre of the Hopf fibration** over `[v]` is homeomorphic to the unit circle, through the
orbit map `u ↦ u • v`. -/
def hopfFiberHomeomorph : sphere (0 : ℂ) 1 ≃ₜ mk n ⁻¹' {mk n v} :=
  have hc : Continuous (orbitFiber v) :=
    (continuous_id.smul continuous_const).subtype_mk _
  have hb : Function.Bijective (orbitFiber v) := by
    refine ⟨fun u u' h ↦ ?_, fun w ↦ ?_⟩
    · have h' := congrArg (fun w : mk n ⁻¹' {mk n v} ↦ (w.1 : EuclideanSpace ℂ (Fin (n + 1)))) h
      simp only [orbitFiber, Sphere.coe_sphere_smul] at h'
      exact Subtype.ext (smul_left_injective ℂ (ne_zero_of_mem_unit_sphere v) h')
    · obtain ⟨c, hc⟩ := (mk_eq_mk_iff n w v).1 w.2
      exact ⟨c, Subtype.ext hc⟩
  hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hb)

@[simp]
theorem coe_hopfFiberHomeomorph_apply (u : sphere (0 : ℂ) 1) :
    (hopfFiberHomeomorph v u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) = u • v :=
  (rfl)

/-- The unit `1` of the circle corresponds to `v` itself in the fibre over `[v]`. -/
@[simp]
theorem hopfFiberHomeomorph_one : hopfFiberHomeomorph v 1 = ⟨v, rfl⟩ :=
  Subtype.ext (one_smul _ v)

end TauCeti.ComplexProjectiveSpace
