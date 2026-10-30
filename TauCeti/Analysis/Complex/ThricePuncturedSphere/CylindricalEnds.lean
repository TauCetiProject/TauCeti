/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.Cylinder
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.CompactCore
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Cylindrical ends of the thrice-punctured sphere

The standard neighborhoods of `0`, `1` and `∞` have actual period-one half-cylinder
parameterizations. The ends at `0` and `1` use `s > 0`; the end at infinity uses `s < 0`.
Their complex lifts are holomorphic with nonzero derivative. Thus all three coordinates
preserve the complex orientation, with the same cylinder orientation `ds ∧ dt`.
The three end images are disjoint, and their complement is a compact core.

These are the standard exponential end coordinates on a punctured Riemann surface;
see Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*,
Chapter 4. The topology reuses the puncture charts and Mathlib's polar and additive-circle
homeomorphisms through `TauCeti.Complex.UnitDisc.puncturedCylinder`.
-/

public noncomputable section

open Set

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- Radial cylindrical parameterization of any puncture neighborhood.
At the two finite punctures this is the positive end coordinate. At infinity the standard
negative end is obtained by reversing both cylinder coordinates, as in `negativeEnd`. -/
def cylindricalEnd (q : Puncture) :
    Ioi (0 : ℝ) × AddCircle (1 : ℝ) ≃ₜ q.neighborhood :=
  Complex.UnitDisc.puncturedCylinder.trans q.coord.symm

/-- In puncture coordinates the radial end is the standard punctured-disc cylinder. -/
@[simp]
theorem coord_cylindricalEnd (q : Puncture) (p : Ioi (0 : ℝ) × AddCircle (1 : ℝ)) :
    q.coord (q.cylindricalEnd p) = Complex.UnitDisc.puncturedCylinder p := by
  simp [cylindricalEnd]

/-- The affine coordinate of an end is obtained by applying the inverse puncture chart. -/
theorem coe_cylindricalEnd (q : Puncture) (p : Ioi (0 : ℝ) × AddCircle (1 : ℝ)) :
    ((q.cylindricalEnd p : ThricePuncturedSphere) : ℂ) =
      q.coordInv (Complex.UnitDisc.puncturedCylinder p) := by
  rw [← coord_cylindricalEnd, coordInv_coord]

/-- The negative end at infinity, with `s < 0` and period-one angular coordinate.
Both signs reverse relative to the positive radial coordinate, so its complex lift is
`z ↦ 2 / exp (2πz)` and remains holomorphic. -/
def negativeEnd : Iio (0 : ℝ) × AddCircle (1 : ℝ) ≃ₜ inf.neighborhood :=
  (((Homeomorph.neg ℝ).subtype (fun s ↦ by simp)).prodCongr
    (Homeomorph.neg _)).trans inf.cylindricalEnd

/-- The negative end at infinity is the standard positive radial end with both signs reversed. -/
theorem negativeEnd_apply (s : Iio (0 : ℝ)) (t : AddCircle (1 : ℝ)) :
    negativeEnd (s, t) = inf.cylindricalEnd (⟨-(s : ℝ), neg_pos.mpr s.2⟩, -t) := (rfl)

/-- The complex lifts of the two positive ends and the negative end at infinity.
The lift at infinity is also `2 / exp (2πz)`. -/
def cylindricalEndLift : Puncture → ℂ → ℂ
  | .zero, z => Complex.exp (-(2 * (Real.pi : ℂ)) * z) / 2
  | .one, z => 1 - Complex.exp (-(2 * (Real.pi : ℂ)) * z) / 2
  | .inf, z => 2 * Complex.exp (-(2 * (Real.pi : ℂ)) * z)

/-- The positive end at zero has exponential affine lift. -/
@[simp] theorem cylindricalEndLift_zero : cylindricalEndLift zero =
    fun z ↦ Complex.exp (-(2 * (Real.pi : ℂ)) * z) / 2 := (rfl)

/-- The positive end at one has exponential affine lift. -/
@[simp] theorem cylindricalEndLift_one : cylindricalEndLift one =
    fun z ↦ 1 - Complex.exp (-(2 * (Real.pi : ℂ)) * z) / 2 := (rfl)

/-- The negative end at infinity has exponential affine lift. -/
@[simp] theorem cylindricalEndLift_inf : cylindricalEndLift inf =
    fun z ↦ 2 * Complex.exp (-(2 * (Real.pi : ℂ)) * z) := (rfl)

/-- The negative lift is the inverse infinity chart applied to the positive exponential. -/
theorem cylindricalEndLift_inf_eq (z : ℂ) :
    inf.cylindricalEndLift z = inf.coordInv (Complex.exp (2 * (Real.pi : ℂ) * z)) := by
  rw [cylindricalEndLift_inf, coordInv_inf]
  simp only [neg_mul, Complex.exp_neg, div_eq_mul_inv]

/-- On real angular lifts, the two finite cylindrical ends have their holomorphic lift. -/
theorem coe_cylindricalEnd_apply_mk (q : Puncture) (hq : q ≠ inf)
    (s : Ioi (0 : ℝ)) (t : ℝ) :
    ((q.cylindricalEnd (s, (t : AddCircle (1 : ℝ))) : ThricePuncturedSphere) : ℂ) =
      q.cylindricalEndLift ((s : ℝ) + t * Complex.I) := by
  rw [coe_cylindricalEnd, Complex.UnitDisc.puncturedCylinder_apply_mk]
  cases q <;> simp_all [cylindricalEndLift]

/-- On real angular lifts, the negative cylindrical end has its holomorphic lift. -/
theorem coe_negativeEnd_apply_mk (s : Iio (0 : ℝ)) (t : ℝ) :
    ((negativeEnd (s, (t : AddCircle (1 : ℝ))) : ThricePuncturedSphere) : ℂ) =
      inf.cylindricalEndLift ((s : ℝ) + t * Complex.I) := by
  rw [negativeEnd_apply, coe_cylindricalEnd, ← AddCircle.coe_neg,
    Complex.UnitDisc.puncturedCylinder_apply_mk, coordInv_inf]
  have h : -(2 * (Real.pi : ℂ)) * ((-(s : ℝ) : ℝ) + (-t : ℝ) * Complex.I) =
      -(-(2 * (Real.pi : ℂ)) * ((s : ℝ) + t * Complex.I)) := by
    push_cast
    ring
  rw [h, Complex.exp_neg]
  simp [cylindricalEndLift, div_inv_eq_mul]

/-- Each lifted end map has the explicit nonzero complex derivative of its exponential. -/
theorem hasDerivAt_cylindricalEndLift (q : Puncture) (z : ℂ) :
    HasDerivAt (cylindricalEndLift q)
      (match q with
      | .zero => -(Real.pi : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ)) * z)
      | .one => (Real.pi : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ)) * z)
      | .inf => -(4 * (Real.pi : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ)) * z)) z := by
  have h := ((hasDerivAt_id z).const_mul (-(2 * (Real.pi : ℂ)))).cexp
  simp only [id_eq, mul_one] at h
  cases q
  · rw [cylindricalEndLift_zero]
    convert h.div_const 2 using 1; ring
  · rw [cylindricalEndLift_one]
    convert (h.div_const 2).const_sub 1 using 1; ring
  · rw [cylindricalEndLift_inf]
    convert h.const_mul 2 using 1; ring

/-- All three lifted ends are holomorphic. -/
@[fun_prop] theorem differentiable_cylindricalEndLift (q : Puncture) :
    Differentiable ℂ (cylindricalEndLift q) :=
  fun z ↦ (q.hasDerivAt_cylindricalEndLift z).differentiableAt

/-- The lifted end maps are smooth at every order, also beyond their half-plane domains. -/
@[fun_prop] theorem contDiff_cylindricalEndLift (q : Puncture) (n : WithTop ℕ∞) :
    ContDiff ℂ n (cylindricalEndLift q) := by
  cases q
  · rw [cylindricalEndLift_zero]
    fun_prop
  · rw [cylindricalEndLift_one]
    fun_prop
  · rw [cylindricalEndLift_inf]
    fun_prop

/-- Every lifted end map is periodic with period one in its real angular coordinate. -/
theorem periodic_cylindricalEndLift (q : Puncture) (s : ℝ) :
    Function.Periodic (fun t : ℝ ↦ q.cylindricalEndLift (s + t * Complex.I)) 1 := by
  intro t
  have h : -(2 * (Real.pi : ℂ)) * ((s : ℂ) + (t + 1 : ℝ) * Complex.I) =
      -(2 * (Real.pi : ℂ)) * ((s : ℂ) + t * Complex.I) -
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  have he := Complex.exp_periodic.sub_eq
    (-(2 * (Real.pi : ℂ)) * ((s : ℂ) + t * Complex.I))
  cases q <;> simp only [cylindricalEndLift, h, he]

/-- The holomorphic lifts have no critical points, including at the chosen angular marker. -/
theorem deriv_cylindricalEndLift_ne_zero (q : Puncture) (z : ℂ) :
    deriv (cylindricalEndLift q) z ≠ 0 := by
  rw [(q.hasDerivAt_cylindricalEndLift z).deriv]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  cases q <;> simp [hp, Complex.exp_ne_zero]

/-- Each parameterization fills precisely its standard puncture neighborhood. -/
theorem range_cylindricalEnd (q : Puncture) :
    Set.range (fun p ↦ (q.cylindricalEnd p : ThricePuncturedSphere)) = q.neighborhood := by
  rw [← Function.comp_def, Set.range_comp, q.cylindricalEnd.surjective.range_eq,
    Set.image_univ, Subtype.range_coe]

/-- The negative end fills precisely the standard infinity neighborhood. -/
theorem range_negativeEnd :
    Set.range (fun p ↦ (negativeEnd p : ThricePuncturedSphere)) = inf.neighborhood := by
  rw [← Function.comp_def, Set.range_comp, negativeEnd.surjective.range_eq,
    Set.image_univ, Subtype.range_coe]

/-- End images at distinct punctures are disjoint. -/
theorem disjoint_range_cylindricalEnd {q r : Puncture} (h : q ≠ r) :
    Disjoint (Set.range (fun p ↦ (q.cylindricalEnd p : ThricePuncturedSphere)))
      (Set.range (fun p ↦ (r.cylindricalEnd p : ThricePuncturedSphere))) := by
  rw [range_cylindricalEnd, range_cylindricalEnd]
  exact pairwise_disjoint_neighborhood h

/-- The complement of the two positive end images and the negative end image is compact. -/
theorem isCompact_compl_endImages : IsCompact
    ((Set.range (fun p ↦ (zero.cylindricalEnd p : ThricePuncturedSphere)) ∪
      Set.range (fun p ↦ (one.cylindricalEnd p : ThricePuncturedSphere)) ∪
      Set.range (fun p ↦ (negativeEnd p : ThricePuncturedSphere)))ᶜ) := by
  rw [range_cylindricalEnd, range_cylindricalEnd, range_negativeEnd,
    neighborhood_zero, neighborhood_one, neighborhood_inf, ← compactCore_one_half]
  exact isCompact_compactCore _

end TauCeti.ThricePuncturedSphere.Puncture
