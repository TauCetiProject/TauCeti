/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# Rotation paths in real Spin groups

An orthonormal pair `x, y` determines a path in the Spin group.  At angle `t` the path is the
product of the Clifford generators of `x` and `cos(t) x + sin(t) y`.  The rotating vector has
norm one, so the product belongs to Spin; at angles zero and `π` it is respectively `1` and the
scalar `-1`.

The standard coordinate pair specializes this construction to a path between the two central
elements of `Spin(2)`.  This is the endpoint-closing path used when a lifted rotation ends at the
nontrivial point of the two-element kernel.

## Main definitions and results

* `CliffordAlgebra.spinRotation`: the Spin element associated to an angle in an orthonormal
  two-plane.
* `CliffordAlgebra.spinRotationPath`: the resulting path from `1` to `-1`.
* `CliffordAlgebra.realCliffordSpinGroupZero_two_joined_one_negOne`: the two central elements of
  `Spin(2)` are joined.
* `CliffordAlgebra.realCliffordSpinGroupZero_add_two_joined_one_negOne`: the same holds in every
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

/-- The Spin element obtained by multiplying an orthonormal vector `x` by the unit vector at
angle `t` in the oriented plane spanned by `x` and `y`. -/
abbrev spinRotation (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) (t : ℝ) : spinGroup Q :=
  ⟨ι Q x * ι Q (Real.cos t • x + Real.sin t • y),
    ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one x
      (Real.cos t • x + Real.sin t • y) <| by
      rw [hx, QuadraticMap.map_add Q, Q.map_smul, Q.map_smul,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hx, hy,
        hxy.polar_eq_zero]
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero, one_mul]
      simpa only [pow_two] using Real.cos_sq_add_sin_sq t⟩

/-- The underlying Clifford element of `spinRotation`. -/
@[simp]
theorem coe_spinRotation (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) (t : ℝ) :
    (spinRotation Q x y hx hy hxy t : CliffordAlgebra Q) =
      ι Q x * ι Q (Real.cos t • x + Real.sin t • y) :=
  rfl

/-- The Spin rotation at angle zero is the identity. -/
@[simp]
theorem spinRotation_zero (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) :
    spinRotation Q x y hx hy hxy 0 = 1 := by
  apply Subtype.ext
  simp [hx]

/-- The Spin element associated to an angle varies continuously with that angle. -/
@[fun_prop]
theorem continuous_spinRotation [Module.Finite ℝ V]
    (hx : Q x = 1) (hy : Q y = 1) (hxy : Q.IsOrtho x y) :
    Continuous (spinRotation Q x y hx hy hxy) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : ℝ =>
    ι Q x * ι Q (Real.cos t • x + Real.sin t • y))
  simp_rw [map_add, map_smul]
  exact (continuous_const : Continuous (fun _ : ℝ => ι Q x)).mul
    ((Real.continuous_cos.smul
        (continuous_const : Continuous (fun _ : ℝ => ι Q x))).add
      (Real.continuous_sin.smul
        (continuous_const : Continuous (fun _ : ℝ => ι Q y))))

/-- An orthonormal pair determines a path in the Spin group from `1` to the scalar `-1`. -/
def spinRotationPath [Module.Finite ℝ V] (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.IsOrtho x y) :
    Path (1 : spinGroup Q) (spinRotation Q x y hx hy hxy Real.pi) :=
  Path.mk
    ⟨fun t : unitInterval => spinRotation Q x y hx hy hxy (Real.pi * (t : ℝ)),
      (continuous_spinRotation Q x y hx hy hxy).comp <| by fun_prop⟩
    (by simp)
    (by simp)

private def spinTwoBasis (i : Fin 2) : Fin 2 → ℝ :=
  Pi.single i 1

private theorem spinTwoBasis_norm (i : Fin 2) :
    realCliffordForm 2 0 (spinTwoBasis i) = 1 := by
  fin_cases i <;>
    norm_num [spinTwoBasis, realCliffordForm_apply, Fin.sum_univ_two, Pi.single_apply]

private theorem spinTwoBasis_add_norm :
    realCliffordForm 2 0 (spinTwoBasis 0 + spinTwoBasis 1) = 2 := by
  rw [realCliffordForm_apply, Fin.sum_univ_two]
  norm_num [spinTwoBasis, Pi.single_apply]

private theorem spinTwoBasis_isOrtho :
    (realCliffordForm 2 0).IsOrtho (spinTwoBasis 0) (spinTwoBasis 1) := by
  rw [QuadraticMap.isOrtho_def, spinTwoBasis_add_norm, spinTwoBasis_norm,
    spinTwoBasis_norm]
  norm_num

/-- The identity and the canonical scalar `-1` are joined in the compact group `Spin(2)`. -/
theorem realCliffordSpinGroupZero_two_joined_one_negOne :
    Joined (1 : realCliffordSpinGroupZero 2)
      (spinGroup.negOne (realCliffordForm 2 0)
        (nondegenerate_realCliffordForm 2 0).ne_zero) := by
  have hjoined : Joined (1 : realCliffordSpinGroupZero 2)
      (spinRotation (realCliffordForm 2 0) (spinTwoBasis 0) (spinTwoBasis 1)
        (spinTwoBasis_norm 0) (spinTwoBasis_norm 1) spinTwoBasis_isOrtho Real.pi) :=
    ⟨spinRotationPath (realCliffordForm 2 0)
      (spinTwoBasis 0) (spinTwoBasis 1) (spinTwoBasis_norm 0) (spinTwoBasis_norm 1)
        spinTwoBasis_isOrtho⟩
  convert hjoined using 1
  apply Subtype.ext
  rw [spinGroup.coe_negOne]
  simp [spinTwoBasis_norm]

/-- The identity and the canonical scalar `-1` are joined in every compact Spin group of
dimension at least two. -/
theorem realCliffordSpinGroupZero_add_two_joined_one_negOne (n : ℕ) :
    Joined (1 : realCliffordSpinGroupZero (n + 2))
      (spinGroup.negOne (realCliffordForm (n + 2) 0)
        (nondegenerate_realCliffordForm (n + 2) 0).ne_zero) := by
  induction n with
  | zero => simpa using realCliffordSpinGroupZero_two_joined_one_negOne
  | succ n ih =>
      have h := ih.map (continuous_realCliffordSpinInclusion (n + 2))
      simpa only [map_one, realCliffordSpinInclusion_negOne, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.reduceAdd] using h

end

end CliffordAlgebra
