/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
public import TauCeti.Topology.QuaternionicProjectiveSpace.Charts
import all TauCeti.Topology.QuaternionicProjectiveSpace.Basic

/-!
# The quaternionic Hopf fibration `S³ → S⁴ⁿ⁺³ → HPⁿ`

Quaternionic projective space `HPⁿ` is the quotient of the unit sphere `S⁴ⁿ⁺³` of `ℍⁿ⁺¹` by the
unit quaternions `S³ ⊆ ℍ` acting on the right (`TauCeti.QuaternionicProjectiveSpace`), and the
quotient map `TauCeti.QuaternionicProjectiveSpace.mk` is the **quaternionic Hopf fibration**. This
file shows that it is a locally trivial bundle with fibre the unit quaternions, and hence a Serre
fibration.

The charts live over the standard affine opens `{X_k ≠ 0}`. Over such an open, the direction
`v_k / ‖v_k‖` of the `k`th coordinate is a continuous map to the unit quaternions, and
`(v q)_k / ‖(v q)_k‖ = (v_k / ‖v_k‖) q` for every unit quaternion `q`. So it is equivariant for the
right action, and it trivializes the orbit projection (`TauCeti.orbitTrivialization`). This gives
the chart `v ↦ ([v], v_k / ‖v_k‖)`
(`TauCeti.QuaternionicProjectiveSpace.hopfTrivialization`), whose inverse sends `([v], q)` to
`v (v_k / ‖v_k‖)⁻¹ q`. The fibre over `[v]` is the right orbit `v S³`, a copy of the unit
quaternions (`TauCeti.QuaternionicProjectiveSpace.hopfFiberHomeomorph`).

## Main definitions

* `TauCeti.QuaternionicProjectiveSpace.hopfTrivialization`: the chart of the Hopf fibration over
  `{X_k ≠ 0}`, with fibre the unit quaternions.
* `TauCeti.QuaternionicProjectiveSpace.hopfHom`: the Hopf fibration as a morphism of `TopCat`.
* `TauCeti.QuaternionicProjectiveSpace.hopfFiberHomeomorph`: the fibre of the Hopf fibration over
  `[v]` is homeomorphic to the unit quaternions, through `q ↦ v q`.

## Main results

* `TauCeti.QuaternionicProjectiveSpace.exists_trivialization_mk`: the Hopf fibration is locally
  trivial with fibre the unit quaternions.
* `TauCeti.QuaternionicProjectiveSpace.mk_mem_serreFibrations`: the Hopf fibration is a Serre
  fibration.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  the Hopf bundles of §4.2.
-/

public section

noncomputable section

open Metric Set Topology MulOpposite
open scoped RightActions Quaternion

namespace TauCeti.QuaternionicProjectiveSpace

variable {n : ℕ} (k : Fin (n + 1))

/-- The direction `v_k / ‖v_k‖` of the `k`th coordinate is equivariant for the right action of
the unit quaternions: `(v q)_k / ‖(v q)_k‖ = (v_k / ‖v_k‖) q`. -/
private theorem sphereDirection_op_smul_apply (q : sphere (0 : ℍ) 1)
    (v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) (hv : mk n v ∈ affineOpen k) :
    sphereDirection 1 ((op q • v).1 k) = sphereDirection 1 (v.1 k) * q := by
  have hv' : v.1 k ≠ 0 := (mk_mem_affineOpen_iff k v).1 hv
  have h : (op q • v).1 k =
      ‖v.1 k‖ • ((sphereDirection 1 (v.1 k) * q : sphere (0 : ℍ) 1) : ℍ) := by
    simp only [Sphere.coe_op_sphere_smul, PiLp.smul_apply, op_smul_eq_mul, unop_op,
      Metric.unitSphere.coe_mul, ← smul_mul_assoc, norm_smul_sphereDirection]
  rw [h, sphereDirection_smul_of_pos _ (norm_pos_iff.2 hv')]

/-- The direction `v_k / ‖v_k‖` of the `k`th coordinate is continuous on the unit vectors with
`v_k ≠ 0`. -/
private theorem continuousOn_sphereDirection_apply :
    ContinuousOn
      (fun v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 ↦ sphereDirection 1 (v.1 k))
      (mk n ⁻¹' affineOpen k) := by
  -- On the chart the direction is the radial projection of a nowhere-zero coordinate.
  rw [continuousOn_iff_continuous_domRestrict]
  refine (normalizeToSphere (fun v : mk n ⁻¹' affineOpen k ↦ v.1.1 k)
    ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℍ) k).comp
      (continuous_subtype_val.comp continuous_subtype_val))
    fun v ↦ (mk_mem_affineOpen_iff k v.1).1 v.2).continuous.congr fun v ↦ Subtype.ext ?_
  rw [coe_normalizeToSphere_apply]
  exact (coe_sphereDirection_of_ne_zero _ ((mk_mem_affineOpen_iff k v.1).1 v.2)).symm

/-- The **chart of the quaternionic Hopf fibration** over the affine open `{X_k ≠ 0}` of `HPⁿ`,
with fibre the unit quaternions. It sends a unit vector `v` with `v_k ≠ 0` to
`([v], v_k / ‖v_k‖)`. It is the orbit trivialization (`TauCeti.orbitTrivialization`) determined
by the equivariant map `v ↦ v_k / ‖v_k‖`, read in the unit quaternions rather than in their
opposite group. -/
def hopfTrivialization : Bundle.Trivialization (sphere (0 : ℍ) 1) (mk n) :=
  (orbitTrivialization (affineOpen k) (isOpen_affineOpen k)
    (fun v ↦ op (sphereDirection 1 (v.1 k)))
    (continuous_op.comp_continuousOn (continuousOn_sphereDirection_apply k))
    fun g v hv ↦ by
      rw [← op_unop g, sphereDirection_op_smul_apply k _ v hv, op_mul]).transFiberHomeomorph
    opHomeomorph.symm

variable {k}

@[simp]
theorem hopfTrivialization_baseSet : (hopfTrivialization (n := n) k).baseSet = affineOpen k :=
  orbitTrivialization_baseSet

/-- The fibre coordinate of the chart over `{X_k ≠ 0}` is the direction `v_k / ‖v_k‖` of the
`k`th coordinate. -/
@[simp]
theorem hopfTrivialization_apply (v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    hopfTrivialization k v = (mk n v, sphereDirection 1 (v.1 k)) := by
  refine (Bundle.Trivialization.transFiberHomeomorph_apply _ _ v).trans ?_
  exact congrArg (Prod.map id opHomeomorph.symm) (orbitTrivialization_apply v)

/-- The inverse of the chart over `{X_k ≠ 0}` sends `([v], q)` to `v (v_k / ‖v_k‖)⁻¹ q`. -/
@[simp]
theorem hopfTrivialization_symm_apply_mk {v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hv : mk n v ∈ affineOpen k) (q : sphere (0 : ℍ) 1) :
    (hopfTrivialization k).toOpenPartialHomeomorph.symm (mk n v, q) =
      op ((sphereDirection 1 (v.1 k))⁻¹ * q) • v := by
  rw [op_mul, op_inv]
  exact orbitTrivialization_symm_apply_mk hv (op q)

variable (n) in
/-- **The quaternionic Hopf fibration is locally trivial**: every point of `HPⁿ` lies in the base
of a chart of `S⁴ⁿ⁺³ → HPⁿ` with fibre the unit quaternions. -/
theorem exists_trivialization_mk (p : QuaternionicProjectiveSpace n) :
    ∃ e : Bundle.Trivialization (sphere (0 : ℍ) 1) (mk n), p ∈ e.baseSet :=
  let ⟨k, hk⟩ := exists_mem_affineOpen p
  ⟨hopfTrivialization k, hopfTrivialization_baseSet ▸ hk⟩

variable (n) in
/-- The quaternionic Hopf fibration `S⁴ⁿ⁺³ → HPⁿ` as a morphism of `TopCat`. -/
abbrev hopfHom :
    _root_.TopCat.of (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) ⟶
      _root_.TopCat.of (QuaternionicProjectiveSpace n) :=
  _root_.TopCat.ofHom ⟨mk n, continuous_mk n⟩

variable (n) in
/-- **The quaternionic Hopf fibration `S⁴ⁿ⁺³ → HPⁿ` is a Serre fibration**, being locally trivial
with fibre the unit quaternions. -/
theorem mk_mem_serreFibrations : TopCat.serreFibrations (hopfHom n) :=
  TopCat.mem_serreFibrations_of_exists_trivialization (exists_trivialization_mk n)

/-! ### The fibre -/

variable (v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1)

/-- The orbit map `q ↦ v q` of the unit quaternions on a unit vector `v` lands in the fibre of the
Hopf fibration over `[v]`. -/
private def orbitFiber (q : sphere (0 : ℍ) 1) : mk n ⁻¹' {mk n v} :=
  ⟨op q • v, mk_op_smul n q v⟩

/-- The **fibre of the quaternionic Hopf fibration** over `[v]` is homeomorphic to the unit
quaternions, through the orbit map `q ↦ v q`. -/
def hopfFiberHomeomorph : sphere (0 : ℍ) 1 ≃ₜ mk n ⁻¹' {mk n v} :=
  have hc : Continuous (orbitFiber v) :=
    ((continuous_op.comp continuous_id).smul continuous_const).subtype_mk _
  have hb : Function.Bijective (orbitFiber v) := by
    refine ⟨fun q q' h ↦ ?_, fun w ↦ ?_⟩
    · -- Compare a nonzero coordinate of `v q = v q'` and cancel it on the left.
      obtain ⟨j, hj⟩ : ∃ j, v.1 j ≠ 0 := by
        by_contra! h0
        exact ne_zero_of_mem_unit_sphere v (PiLp.ext h0)
      have h' := congrArg (fun w : mk n ⁻¹' {mk n v} ↦ (w.1 : PiLp 2 fun _ ↦ ℍ) j) h
      simp only [orbitFiber, Sphere.coe_op_sphere_smul, PiLp.smul_apply, op_smul_eq_mul,
        unop_op] at h'
      exact Subtype.ext (mul_left_cancel₀ hj h')
    · obtain ⟨q, hq⟩ := (mk_eq_mk_iff n w v).1 w.2
      exact ⟨q, Subtype.ext (Subtype.ext (congrArg Subtype.val hq))⟩
  hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hb)

@[simp]
theorem coe_hopfFiberHomeomorph_apply (q : sphere (0 : ℍ) 1) :
    (hopfFiberHomeomorph v q : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) = op q • v :=
  (rfl)

/-- The unit `1` of the unit quaternions corresponds to `v` itself in the fibre over `[v]`. -/
@[simp]
theorem hopfFiberHomeomorph_one : hopfFiberHomeomorph v 1 = ⟨v, rfl⟩ :=
  Subtype.ext (one_smul _ v)

end TauCeti.QuaternionicProjectiveSpace
