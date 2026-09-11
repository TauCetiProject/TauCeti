/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Rotation
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Rotation paths in real Spin groups

An orthonormal pair `x, y` determines a path in the Spin group.  At angle `t` the path is the
product of the Clifford generators of `x` and `cos(t) x + sin(t) y`.  The rotating vector has
norm one, so the product belongs to Spin; at angles zero and `π` it is respectively `1` and the
scalar `-1`.

The standard coordinate pair specializes this construction to a path between the canonical
central elements `1` and `-1` of `Spin(2)`. This is the endpoint-closing path used when a lifted
rotation ends at the nontrivial point of the two-element kernel.

## Main definitions and results

* `CliffordAlgebra.spinRotationPath`: the resulting path from `1` to `-1`.
* `CliffordAlgebra.joined_one_negOne_realCliffordSpinGroupZero_two`: the two elements of the
  double-cover kernel in `Spin(2)` are joined.
* `CliffordAlgebra.joined_one_negOne_realCliffordSpinGroupZero_add_two`: the same holds in every
  compact `Spin(n)` of dimension at least two.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §6.
-/

public section

open unitInterval

open scoped Topology

namespace CliffordAlgebra

open TauCeti

noncomputable section

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]
  (Q : QuadraticForm ℝ V) (x y : V)

/-- The Spin element associated to an angle varies continuously with that angle. -/
@[fun_prop]
theorem continuous_spinRotation (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) :
    Continuous (spinRotation Q x y hx hy hxy) := by
  apply continuous_induced_rng.mpr
  have hvec : Continuous (fun t : ℝ =>
      Real.cos t • ι Q x + Real.sin t • ι Q y) :=
    ((Real.continuous_cos.smul
        (continuous_const : Continuous (fun _ : ℝ => ι Q x))).add
      (Real.continuous_sin.smul
        (continuous_const : Continuous (fun _ : ℝ => ι Q y))))
  refine ((IsModuleTopology.continuous_of_linearMap
    (LinearMap.mulLeft ℝ (ι Q x))).comp hvec).congr ?_
  intro t
  simp only [Function.comp_apply, LinearMap.mulLeft_apply, coe_spinRotation, map_add, map_smul]
  rw [mul_add, mul_smul_comm, mul_smul_comm]

/-- An orthonormal pair determines a path in the Spin group from `1` to the scalar `-1`. -/
def spinRotationPath (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) :
    Path (1 : spinGroup Q) (spinGroup.negOne Q (by
      intro hQ
      simp [hQ] at hx)) :=
  ((Path.segment (0 : ℝ) Real.pi).map
      (continuous_spinRotation Q x y hx hy hxy)).cast
    (spinRotation_zero Q x y hx hy hxy).symm
    (spinRotation_pi Q x y hx hy hxy).symm

/-- Evaluating the rotation path at `t` gives the rotation with Spin parameter `π t`. -/
@[simp]
theorem spinRotationPath_apply (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) (t : unitInterval) :
    spinRotationPath Q x y hx hy hxy t =
      spinRotation Q x y hx hy hxy (Real.pi * (t : ℝ)) := by
  simp only [spinRotationPath, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_eq_mul, zero_mul,
    zero_add, mul_comm]

private theorem spinTwoBasis_norm (i : Fin 2) :
    realCliffordForm 2 0 (Pi.basisFun ℝ (Fin 2) i) = 1 := by
  fin_cases i <;>
    norm_num [realCliffordForm_apply, Fin.sum_univ_two, Pi.basisFun_apply, Pi.single_apply]

private theorem spinTwoBasis_add_norm :
    realCliffordForm 2 0
      (Pi.basisFun ℝ (Fin 2) 0 + Pi.basisFun ℝ (Fin 2) 1) = 2 := by
  rw [realCliffordForm_apply, Fin.sum_univ_two]
  norm_num [Pi.basisFun_apply, Pi.single_apply]

private theorem spinTwoBasis_isOrtho :
    (realCliffordForm 2 0).IsOrtho
      (Pi.basisFun ℝ (Fin 2) 0) (Pi.basisFun ℝ (Fin 2) 1) := by
  rw [QuadraticMap.isOrtho_def, spinTwoBasis_add_norm, spinTwoBasis_norm,
    spinTwoBasis_norm]
  norm_num

/-- The identity and the canonical scalar `-1` are joined in the compact group `Spin(2)`. -/
theorem joined_one_negOne_realCliffordSpinGroupZero_two :
    Joined (1 : realCliffordSpinGroupZero 2)
      (spinGroup.negOne (realCliffordForm 2 0)
        (nondegenerate_realCliffordForm 2 0).ne_zero) := by
  exact ⟨spinRotationPath (realCliffordForm 2 0)
    (Pi.basisFun ℝ (Fin 2) 0) (Pi.basisFun ℝ (Fin 2) 1)
      (spinTwoBasis_norm 0) (spinTwoBasis_norm 1) spinTwoBasis_isOrtho⟩

/-- The identity and the canonical scalar `-1` are joined in every compact Spin group of
dimension at least two. -/
theorem joined_one_negOne_realCliffordSpinGroupZero_add_two (n : ℕ) :
    Joined (1 : realCliffordSpinGroupZero (n + 2))
      (spinGroup.negOne (realCliffordForm (n + 2) 0)
        (nondegenerate_realCliffordForm (n + 2) 0).ne_zero) := by
  induction n with
  | zero => simpa using joined_one_negOne_realCliffordSpinGroupZero_two
  | succ n ih =>
      have h := ih.map (continuous_realCliffordSpinInclusion (n + 2))
      simpa only [map_one, realCliffordSpinInclusion_negOne, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.reduceAdd] using h

end

end CliffordAlgebra
