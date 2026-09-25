/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Basic

/-!
# The anharmonic self-homeomorphisms of the thrice-punctured sphere

The six Möbius transformations permuting the three punctures `{0, 1, ∞}` of the Riemann sphere
restrict to self-homeomorphisms of the thrice-punctured sphere `U = ℂ ∖ {0, 1}`:

| map         | formula       | punctures  | image of `b = 1/2` |
| ----------- | ------------- | ---------- | ------------------ |
| identity    | `z`           | `()`       | `1/2`              |
| `mob01`     | `1 − z`       | `(0 1)`    | `1/2`              |
| `mob1Inf`   | `z / (z − 1)` | `(1 ∞)`    | `−1`               |
| `mob0Inf`   | `1 / z`       | `(0 ∞)`    | `2`                |
| `mobRot`    | `1 / (1 − z)` | `(0 1 ∞)`  | `2`                |
| `mobRotInv` | `(z − 1) / z` | `(0 ∞ 1)`  | `−1`               |

The identity is `Homeomorph.refl`, and `mob01` is defined with the thrice-punctured sphere
itself. The two involutions `mob01` and `mob1Inf` generate the other four: `mobRot` and
`mobRotInv` are *defined* as their two composites, and `mob0Inf` is the composite
`mob01 ∘ mob1Inf ∘ mob01`, which is also `mob1Inf ∘ mob01 ∘ mob1Inf` (the braid relation of
`S₃`).

Pulling covers back along these maps is the topological counterpart of the action of `S₃` on
permutation triples by permuting the branch points. The identity and `mob01` fix the basepoint
`b = 1/2`; among the nonidentity maps, only `mob01` does. The other four maps move it, so they
act on the fundamental group at `b` only after a choice of connecting path, which is why that
action is well defined only on isomorphism classes of covers.

The puncture permutations are recorded by identifying each map with the restriction of a Möbius
transformation of the Riemann sphere `OnePoint ℂ`, that is, with the action of an element of
`GL (Fin 2) ℂ` (Mathlib's `OnePoint.instGLAction`). The matrices of the two generators are
`mob01GL = !![-1, 1; 0, 1]` and `mob1InfGL = !![1, 0; 1, -1]`, and the value lemmas
`mob01GL_smul_*` and `mob1InfGL_smul_*` record where each sends `0`, `1` and `∞`.

## Main definitions

* `TauCeti.ThricePuncturedSphere.mob1Inf`: `z ↦ z / (z − 1)`, exchanging `1` and `∞`.
* `TauCeti.ThricePuncturedSphere.mob0Inf`: `z ↦ 1 / z`, exchanging `0` and `∞`.
* `TauCeti.ThricePuncturedSphere.mobRot`, `TauCeti.ThricePuncturedSphere.mobRotInv`: the two
  rotations `z ↦ 1 / (1 − z)` and `z ↦ (z − 1) / z`, inverse to each other.
* `TauCeti.ThricePuncturedSphere.mob01GL`, `TauCeti.ThricePuncturedSphere.mob1InfGL`: the
  matrices of the two generators.

## Main results

* `coe_mob1Inf`, `coe_mob0Inf`, `coe_mobRot`, `coe_mobRotInv`: the formulas.
* `mob01_mob1Inf_mob01`, `mob1Inf_mob01_mob1Inf`: `mob0Inf` is the composite of the generators
  either way round.
* `mobRot_mobRot`, `mobRot_mobRot_mobRot`: `mobRot` has order three, with square `mobRotInv`.
* `toOnePoint_mob01`, `toOnePoint_mob1Inf`, `toOnePoint_mob0Inf`, `toOnePoint_mobRot`,
  `toOnePoint_mobRotInv`: each map is the restriction of the Möbius action of a product of
  `mob01GL` and `mob1InfGL`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §§1.1 and 2.4 (Möbius transformations, and the thrice-punctured sphere as the base of
  three-point covers).
-/

public section

open OnePoint

namespace TauCeti

namespace ThricePuncturedSphere

/-! ### The generators and their composites -/

/-- `z ↦ z / (z − 1)` as a map of the thrice-punctured sphere. It is an involution
(`involutive_mob1InfFun`), and `mob1Inf` is the resulting self-homeomorphism. -/
private noncomputable def mob1InfFun (z : ThricePuncturedSphere) : ThricePuncturedSphere :=
  ⟨z / (z - 1), div_ne_zero z.ne_zero (sub_ne_zero.mpr z.ne_one), fun h ↦ by
    rw [div_eq_one_iff_eq (sub_ne_zero.mpr z.ne_one)] at h
    exact one_ne_zero (by linear_combination h)⟩

private theorem involutive_mob1InfFun : Function.Involutive mob1InfFun := fun z ↦ by
  have h₁ : (z : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr z.ne_one
  refine Subtype.ext ?_
  simp only [mob1InfFun]
  field_simp
  ring

private theorem continuous_mob1InfFun : Continuous mob1InfFun :=
  (continuous_subtype_val.div (continuous_subtype_val.sub continuous_const)
    fun z : ThricePuncturedSphere ↦ sub_ne_zero.mpr z.ne_one).subtype_mk _

/-- The self-homeomorphism `z ↦ z / (z − 1)` of the thrice-punctured sphere. It is the anharmonic
transformation exchanging the punctures `1` and `∞` and fixing `0`; it moves the basepoint `1/2`
to `−1`. -/
noncomputable def mob1Inf : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere where
  toEquiv := involutive_mob1InfFun.toPerm _
  continuous_toFun := continuous_mob1InfFun
  continuous_invFun := continuous_mob1InfFun

/-- `mob1Inf` has the formula `z ↦ z / (z - 1)`. -/
@[simp]
theorem coe_mob1Inf (z : ThricePuncturedSphere) : (mob1Inf z : ℂ) = z / (z - 1) := (rfl)

/-- `z ↦ z / (z − 1)` is an involution. -/
@[simp]
theorem mob1Inf_mob1Inf (z : ThricePuncturedSphere) : mob1Inf (mob1Inf z) = z :=
  involutive_mob1InfFun z

/-- `mob1Inf` is its own inverse. -/
@[simp]
theorem symm_mob1Inf : mob1Inf.symm = mob1Inf :=
  Homeomorph.ext fun z ↦ mob1Inf.symm_apply_eq.mpr (mob1Inf_mob1Inf z).symm

/-- The self-homeomorphism `z ↦ 1 / (1 − z)` of the thrice-punctured sphere, the composite
`mob01 ∘ mob1Inf`. It is the anharmonic transformation rotating the punctures `0 ↦ 1 ↦ ∞ ↦ 0`; it
moves the basepoint `1/2` to `2`. -/
noncomputable def mobRot : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  mob1Inf.trans mob01

/-- The self-homeomorphism `z ↦ (z − 1) / z` of the thrice-punctured sphere, the composite
`mob1Inf ∘ mob01`. It is the anharmonic transformation rotating the punctures `0 ↦ ∞ ↦ 1 ↦ 0`,
inverse to `mobRot`; it moves the basepoint `1/2` to `−1`. -/
noncomputable def mobRotInv : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  mob01.trans mob1Inf

/-- `mobRot` is `mob01 ∘ mob1Inf`. -/
theorem mobRot_apply (z : ThricePuncturedSphere) : mobRot z = mob01 (mob1Inf z) := (rfl)

/-- `mobRotInv` is `mob1Inf ∘ mob01`. -/
theorem mobRotInv_apply (z : ThricePuncturedSphere) : mobRotInv z = mob1Inf (mob01 z) := (rfl)

/-- `mobRot` has the formula `z ↦ 1 / (1 - z)`. -/
@[simp]
theorem coe_mobRot (z : ThricePuncturedSphere) : (mobRot z : ℂ) = 1 / (1 - z) := by
  have h : (z : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr z.ne_one
  have h' : 1 - (z : ℂ) ≠ 0 := sub_ne_zero.mpr z.ne_one.symm
  rw [mobRot_apply, coe_mob01, coe_mob1Inf]
  field_simp
  ring

/-- `mobRotInv` has the formula `z ↦ (z - 1) / z`. -/
@[simp]
theorem coe_mobRotInv (z : ThricePuncturedSphere) : (mobRotInv z : ℂ) = (z - 1) / z := by
  have h : (z : ℂ) ≠ 0 := z.ne_zero
  rw [mobRotInv_apply, coe_mob1Inf, coe_mob01]
  field_simp
  ring

/-- `mobRot` and `mobRotInv` are inverse when composed in this order. -/
@[simp]
theorem mobRot_mobRotInv (z : ThricePuncturedSphere) : mobRot (mobRotInv z) = z := by
  rw [mobRot_apply, mobRotInv_apply, mob1Inf_mob1Inf, mob01_mob01]

/-- `mobRotInv` and `mobRot` are inverse when composed in this order. -/
@[simp]
theorem mobRotInv_mobRot (z : ThricePuncturedSphere) : mobRotInv (mobRot z) = z := by
  rw [mobRot_apply, mobRotInv_apply, mob01_mob01, mob1Inf_mob1Inf]

/-- The inverse of `mobRot` is `mobRotInv`. -/
@[simp]
theorem symm_mobRot : mobRot.symm = mobRotInv :=
  Homeomorph.ext fun z ↦ mobRot.symm_apply_eq.mpr (mobRot_mobRotInv z).symm

/-- The inverse of `mobRotInv` is `mobRot`. -/
@[simp]
theorem symm_mobRotInv : mobRotInv.symm = mobRot := by
  rw [← symm_mobRot, Homeomorph.symm_symm]

/-- The square of the rotation `mobRot` is its inverse. -/
@[simp]
theorem mobRot_mobRot (z : ThricePuncturedSphere) : mobRot (mobRot z) = mobRotInv z :=
  Subtype.ext <| by
    have h : (z : ℂ) ≠ 0 := z.ne_zero
    have h' : 1 - (z : ℂ) ≠ 0 := sub_ne_zero.mpr z.ne_one.symm
    rw [coe_mobRot, coe_mobRot, coe_mobRotInv]
    field_simp
    ring

/-- The rotation `mobRot` has order three. -/
theorem mobRot_mobRot_mobRot (z : ThricePuncturedSphere) : mobRot (mobRot (mobRot z)) = z := by
  rw [mobRot_mobRot, mobRotInv_mobRot]

/-- The self-homeomorphism `z ↦ 1 / z` of the thrice-punctured sphere, the composite
`mob01 ∘ mob1Inf ∘ mob01`. It is the anharmonic transformation exchanging the punctures `0` and
`∞` and fixing `1`; it moves the basepoint `1/2` to `2`. -/
noncomputable def mob0Inf : ThricePuncturedSphere ≃ₜ ThricePuncturedSphere :=
  mob01.trans mobRot

/-- `mob0Inf` is `mob01 ∘ mob1Inf ∘ mob01`. -/
theorem mob01_mob1Inf_mob01 (z : ThricePuncturedSphere) :
    mob01 (mob1Inf (mob01 z)) = mob0Inf z := (rfl)

/-- `mob0Inf` has the formula `z ↦ 1 / z`. -/
@[simp]
theorem coe_mob0Inf (z : ThricePuncturedSphere) : (mob0Inf z : ℂ) = 1 / z := by
  rw [← mob01_mob1Inf_mob01, ← mobRot_apply, coe_mobRot, coe_mob01, sub_sub_cancel]

/-- The braid relation of `S₃`: `mob0Inf` is also `mob1Inf ∘ mob01 ∘ mob1Inf`. -/
theorem mob1Inf_mob01_mob1Inf (z : ThricePuncturedSphere) :
    mob1Inf (mob01 (mob1Inf z)) = mob0Inf z :=
  Subtype.ext <| by
    have h : (z : ℂ) ≠ 0 := z.ne_zero
    have h' : (z : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr z.ne_one
    rw [← mobRotInv_apply, coe_mobRotInv, coe_mob1Inf, coe_mob0Inf]
    field_simp
    ring

/-- `z ↦ 1 / z` is an involution. -/
@[simp]
theorem mob0Inf_mob0Inf (z : ThricePuncturedSphere) : mob0Inf (mob0Inf z) = z :=
  Subtype.ext <| by rw [coe_mob0Inf, coe_mob0Inf, one_div_one_div]

/-- `mob0Inf` is its own inverse. -/
@[simp]
theorem symm_mob0Inf : mob0Inf.symm = mob0Inf :=
  Homeomorph.ext fun z ↦ mob0Inf.symm_apply_eq.mpr (mob0Inf_mob0Inf z).symm

/-! ### The images of the basepoint -/

/-- `mob1Inf` sends the basepoint to `-1`. -/
theorem coe_mob1Inf_basePt : (mob1Inf basePt : ℂ) = -1 := by
  rw [coe_mob1Inf, coe_basePt]
  norm_num

/-- `mob0Inf` sends the basepoint to `2`. -/
theorem coe_mob0Inf_basePt : (mob0Inf basePt : ℂ) = 2 := by
  rw [coe_mob0Inf, coe_basePt]
  norm_num

/-- `mobRot` sends the basepoint to `2`. -/
theorem coe_mobRot_basePt : (mobRot basePt : ℂ) = 2 := by
  rw [coe_mobRot, coe_basePt]
  norm_num

/-- `mobRotInv` sends the basepoint to `-1`. -/
theorem coe_mobRotInv_basePt : (mobRotInv basePt : ℂ) = -1 := by
  rw [coe_mobRotInv, coe_basePt]
  norm_num

/-! ### The Möbius transformations of the Riemann sphere -/

/-- The matrix `!![-1, 1; 0, 1]` of the Möbius transformation `z ↦ 1 − z`, which restricts to
`mob01` on the thrice-punctured sphere. -/
noncomputable def mob01GL : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 1; 0, 1] (by simp [Matrix.det_fin_two_of])

/-- The matrix `!![1, 0; 1, -1]` of the Möbius transformation `z ↦ z / (z − 1)`, which restricts
to `mob1Inf` on the thrice-punctured sphere. -/
noncomputable def mob1InfGL : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, -1] (by simp [Matrix.det_fin_two_of])

@[simp]
theorem coe_mob01GL : (mob01GL : Matrix (Fin 2) (Fin 2) ℂ) = !![-1, 1; 0, 1] := (rfl)

@[simp]
theorem coe_mob1InfGL : (mob1InfGL : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 1, -1] := (rfl)

/-- The Möbius transformation of `mob01GL` sends `0` to `1`. -/
@[simp]
theorem mob01GL_smul_zero : mob01GL • ((0 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) := by
  simp [smul_some_eq_ite]

/-- The Möbius transformation of `mob01GL` sends `1` to `0`. -/
@[simp]
theorem mob01GL_smul_one : mob01GL • ((1 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
  simp [smul_some_eq_ite]

/-- The Möbius transformation of `mob01GL` fixes `∞`. -/
@[simp]
theorem mob01GL_smul_infty : mob01GL • (∞ : OnePoint ℂ) = ∞ := by
  simp [smul_infty_eq_ite]

/-- The Möbius transformation of `mob1InfGL` fixes `0`. -/
@[simp]
theorem mob1InfGL_smul_zero : mob1InfGL • ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
  simp [smul_some_eq_ite]

/-- The Möbius transformation of `mob1InfGL` sends `1` to `∞`. -/
@[simp]
theorem mob1InfGL_smul_one : mob1InfGL • ((1 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [smul_some_eq_ite]

/-- The Möbius transformation of `mob1InfGL` sends `∞` to `1`. -/
@[simp]
theorem mob1InfGL_smul_infty : mob1InfGL • (∞ : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) := by
  simp [smul_infty_eq_ite]

/-- `mob01` is the restriction of the Möbius transformation of `mob01GL` to the thrice-punctured
sphere. -/
theorem toOnePoint_mob01 (z : ThricePuncturedSphere) :
    toOnePoint (mob01 z) = mob01GL • toOnePoint z := by
  simp [toOnePoint_apply, smul_some_eq_ite, sub_eq_neg_add]

/-- `mob1Inf` is the restriction of the Möbius transformation of `mob1InfGL` to the
thrice-punctured sphere. -/
theorem toOnePoint_mob1Inf (z : ThricePuncturedSphere) :
    toOnePoint (mob1Inf z) = mob1InfGL • toOnePoint z := by
  have h : (z : ℂ) + -1 ≠ 0 := by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr z.ne_one
  simp [toOnePoint_apply, smul_some_eq_ite, sub_eq_add_neg, h]

/-- `mobRot` is the restriction of the Möbius transformation of `mob01GL * mob1InfGL` to the
thrice-punctured sphere. -/
theorem toOnePoint_mobRot (z : ThricePuncturedSphere) :
    toOnePoint (mobRot z) = (mob01GL * mob1InfGL) • toOnePoint z := by
  rw [mobRot_apply, toOnePoint_mob01, toOnePoint_mob1Inf, mul_smul]

/-- `mobRotInv` is the restriction of the Möbius transformation of `mob1InfGL * mob01GL` to the
thrice-punctured sphere. -/
theorem toOnePoint_mobRotInv (z : ThricePuncturedSphere) :
    toOnePoint (mobRotInv z) = (mob1InfGL * mob01GL) • toOnePoint z := by
  rw [mobRotInv_apply, toOnePoint_mob1Inf, toOnePoint_mob01, mul_smul]

/-- `mob0Inf` is the restriction of the Möbius transformation of
`mob01GL * mob1InfGL * mob01GL` to the thrice-punctured sphere. -/
theorem toOnePoint_mob0Inf (z : ThricePuncturedSphere) :
    toOnePoint (mob0Inf z) = (mob01GL * mob1InfGL * mob01GL) • toOnePoint z := by
  rw [← mob01_mob1Inf_mob01, toOnePoint_mob01, toOnePoint_mob1Inf, toOnePoint_mob01, mul_smul,
    mul_smul]

end ThricePuncturedSphere

end TauCeti
