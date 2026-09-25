/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.ReflectionPair
public import TauCeti.Topology.Algebra.CliffordAlgebra.RealForm
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic

/-!
# A local section of the compact Spin sphere action

Let `e` be the last coordinate unit vector. On the unit level of the positive-definite real
Clifford form, away from `-e`, the normalized vector

`u(x) = (sqrt (Q (e + x)))⁻¹ • (e + x)`

has quadratic norm one. The reflection-pair lift `u(x) * e` belongs to `Spin(n + 1)` and sends
`e` to `x`: reflection in `e` first sends `e` to `-e`, and reflection in `e + x` then sends
`-e` to `x`.

This file packages that lift as a function on the unit level, totalized by the identity at the
excluded antipode. The punctured neighborhood is open, the lift is continuous there, and its
action on `e` is the identity map of the neighborhood. These are the local-section data used in
sphere bundle charts for compact Spin groups; no global transitivity or bundle statement is made
here.

## Main declarations

* `TauCeti.realCliffordSpinLastUnitNeighborhood` is the unit level away from the antipode
  of the last coordinate vector.
* `TauCeti.realCliffordSpinLastLocalSectionDirection` is the normalized direction used by
  the lift.
* `TauCeti.realCliffordSpinLastLocalSection` is the normalized reflection-pair lift.
* `TauCeti.realCliffordSpinLastLocalSection_eq_one_of_not_mem` gives its totalized value at the
  excluded antipode.
* `TauCeti.realCliffordSpinLastLocalSection_apply` evaluates the lift on its neighborhood.
* `TauCeti.continuousOn_realCliffordSpinLastLocalSection` proves its continuity on the
  neighborhood.
* `TauCeti.realCliffordSpinLastLocalSection_action` proves that the lift carries the last
  coordinate vector to the prescribed unit vector.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace TauCeti

open CliffordAlgebra

noncomputable section

private abbrev compactForm (n : ℕ) := realCliffordForm (n + 1) 0

private abbrev compactUnitLevel (n : ℕ) :=
  {x : Fin (n + 1) → ℝ // compactForm n x = 1}

private def lastUnitVector (n : ℕ) : Fin (n + 1) → ℝ :=
  Pi.single (Fin.last n) 1

/-- The unit level of `realCliffordForm (n + 1) 0` with the antipode of the last coordinate unit
vector removed. -/
def realCliffordSpinLastUnitNeighborhood (n : ℕ) :
    Set {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1} :=
  {x | x.1 ≠ -(lastUnitVector n)}

/-- Membership in the last-vector neighborhood means being different from the antipode of the last
coordinate unit vector. -/
@[simp]
theorem mem_realCliffordSpinLastUnitNeighborhood {n : ℕ}
    {x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1}} :
    x ∈ realCliffordSpinLastUnitNeighborhood n ↔
      x.1 ≠ -(Pi.single (Fin.last n) 1) :=
  Iff.rfl

/-- The punctured last-vector unit neighborhood is open. -/
theorem isOpen_realCliffordSpinLastUnitNeighborhood (n : ℕ) :
    IsOpen (realCliffordSpinLastUnitNeighborhood n) := by
  rw [realCliffordSpinLastUnitNeighborhood]
  exact isOpen_compl_singleton.preimage continuous_subtype_val

private theorem last_sub_neg_ne_zero {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : x ≠ -(lastUnitVector n)) :
    lastUnitVector n - -x ≠ 0 := by
  intro h
  apply hx
  rw [eq_neg_iff_add_eq_zero]
  simpa only [sub_neg_eq_add, add_comm] using h

private theorem compactForm_last_sub_neg_pos {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : x ≠ -(lastUnitVector n)) :
    0 < compactForm n (lastUnitVector n - -x) :=
  posDef_realCliffordForm_zero (n + 1) _ (last_sub_neg_ne_zero hx)

/-- The unit direction from the antipode of the last coordinate vector toward an ambient vector.
At the excluded antipode it is totalized to zero by the real inverse. -/
noncomputable def realCliffordSpinLastLocalSectionDirection {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  (Real.sqrt (realCliffordForm (n + 1) 0 (Pi.single (Fin.last n) 1 - -x)))⁻¹ •
    (Pi.single (Fin.last n) 1 - -x)

/-- The normalized direction is given by inverse square-root rescaling of the translated input. -/
theorem realCliffordSpinLastLocalSectionDirection_def {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    realCliffordSpinLastLocalSectionDirection x =
      (Real.sqrt (realCliffordForm (n + 1) 0 (Pi.single (Fin.last n) 1 - -x)))⁻¹ •
        (Pi.single (Fin.last n) 1 - -x) := by
  rfl

/-- Away from the last-vector antipode, the local-section direction has quadratic value one. -/
@[simp]
theorem realCliffordSpinLastLocalSectionDirection_form_eq_one {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hx : x ≠ -(Pi.single (Fin.last n) 1)) :
    realCliffordForm (n + 1) 0 (realCliffordSpinLastLocalSectionDirection x) = 1 := by
  have hpos := compactForm_last_sub_neg_pos (by simpa only [lastUnitVector] using hx)
  simpa only [realCliffordSpinLastLocalSectionDirection, compactForm, lastUnitVector] using
    (QuadraticMap.map_inv_sqrt_smul_eq_one hpos)

/-- The normalized direction is zero at the excluded antipode. -/
@[simp]
theorem realCliffordSpinLastLocalSectionDirection_eq_zero {n : ℕ} :
    realCliffordSpinLastLocalSectionDirection (-(Pi.single (Fin.last n) 1)) = 0 := by
  simp [realCliffordSpinLastLocalSectionDirection]

private def localSectionOn {n : ℕ} (x : compactUnitLevel n)
    (hx : x ∈ realCliffordSpinLastUnitNeighborhood n) :
    realCliffordSpinGroupZero (n + 1) :=
  spinReflectionPair (compactForm n) (realCliffordSpinLastLocalSectionDirection x.1)
    (lastUnitVector n) (realCliffordSpinLastLocalSectionDirection_form_eq_one x.1
      (mem_realCliffordSpinLastUnitNeighborhood.mp hx))
    (by simpa only [compactForm, lastUnitVector] using
      realCliffordForm_unitVector (n + 1) (Fin.last n))

/-- A normalized reflection-pair lift on the last-vector unit neighborhood, totalized by the
identity at the excluded antipode. -/
def realCliffordSpinLastLocalSection (n : ℕ)
    (x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1}) :
    realCliffordSpinGroupZero (n + 1) := by
  classical
  exact if hx : x ∈ realCliffordSpinLastUnitNeighborhood n then localSectionOn x hx else 1

/-- At the excluded antipode, the totalized local section is the identity Spin element. -/
@[simp]
theorem realCliffordSpinLastLocalSection_eq_one_of_not_mem {n : ℕ}
    {x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1}}
    (hx : x ∉ realCliffordSpinLastUnitNeighborhood n) :
    realCliffordSpinLastLocalSection n x = 1 := by
  rw [realCliffordSpinLastLocalSection]
  simp only [hx, dite_false]

/-- On the last-vector neighborhood, the local section is the normalized reflection-pair lift. -/
theorem realCliffordSpinLastLocalSection_apply {n : ℕ}
    (x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1})
    (hx : x ∈ realCliffordSpinLastUnitNeighborhood n) :
    realCliffordSpinLastLocalSection n x =
      spinReflectionPair (realCliffordForm (n + 1) 0)
        (realCliffordSpinLastLocalSectionDirection x.1)
        (Pi.single (Fin.last n) 1)
        (realCliffordSpinLastLocalSectionDirection_form_eq_one x.1
          (mem_realCliffordSpinLastUnitNeighborhood.mp hx))
        (realCliffordForm_unitVector (n + 1) (Fin.last n)) := by
  rw [realCliffordSpinLastLocalSection]
  simp only [hx, dite_true, localSectionOn, compactForm, lastUnitVector]

/-- The normalized reflection-pair lift is continuous on the punctured last-vector neighborhood. -/
theorem continuousOn_realCliffordSpinLastLocalSection (n : ℕ) :
    ContinuousOn (realCliffordSpinLastLocalSection n)
      (realCliffordSpinLastUnitNeighborhood n) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_induced_rng.mpr
  have hvector : Continuous (fun x : realCliffordSpinLastUnitNeighborhood n =>
      lastUnitVector n - -x.1.1) := by fun_prop
  have hform : Continuous (fun x : realCliffordSpinLastUnitNeighborhood n =>
      compactForm n (lastUnitVector n - -x.1.1)) := by
    simp only [compactForm, realCliffordForm_apply]
    fun_prop
  have hpos : ∀ x : realCliffordSpinLastUnitNeighborhood n,
      0 < compactForm n (lastUnitVector n - -x.1.1) := fun x =>
    compactForm_last_sub_neg_pos (mem_realCliffordSpinLastUnitNeighborhood.mp x.2)
  have hscalar : Continuous (fun x : realCliffordSpinLastUnitNeighborhood n =>
      (Real.sqrt (compactForm n (lastUnitVector n - -x.1.1)))⁻¹) :=
    hform.sqrt.inv₀ fun x => Real.sqrt_ne_zero'.mpr (hpos x)
  have hdirection : Continuous (fun x : realCliffordSpinLastUnitNeighborhood n =>
      realCliffordSpinLastLocalSectionDirection x.1.1) := by
    convert hscalar.smul hvector using 1
    funext x
    simp only [realCliffordSpinLastLocalSectionDirection, compactForm, lastUnitVector,
      Pi.smul_apply']
  have hvalue : Continuous (fun x : realCliffordSpinLastUnitNeighborhood n =>
      ι (compactForm n) (realCliffordSpinLastLocalSectionDirection x.1.1) *
        ι (compactForm n) (lastUnitVector n)) :=
    ((continuous_ι (compactForm n)).comp hdirection).mul continuous_const
  exact hvalue.congr fun x => by
    -- The induced topology on the Spin subtype reduces continuity to its Clifford-algebra
    -- carrier; expose that carrier to compare with the explicit reflection-pair product.
    change ι (compactForm n) (realCliffordSpinLastLocalSectionDirection x.1.1) *
        ι (compactForm n) (lastUnitVector n) =
      (realCliffordSpinLastLocalSection n x.1 : CliffordAlgebra (compactForm n))
    rw [realCliffordSpinLastLocalSection]
    simp only [x.2, dite_true, localSectionOn, coe_spinReflectionPair]

/-- On the punctured unit neighborhood, the local section sends the last coordinate unit vector
to its input under the Spin vector action. -/
@[simp]
theorem realCliffordSpinLastLocalSection_action {n : ℕ}
    (x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1})
    (hx : x ∈ realCliffordSpinLastUnitNeighborhood n) :
    spinVectorAction (realCliffordForm (n + 1) 0)
        (realCliffordSpinLastLocalSection n x)
        (Pi.single (Fin.last n) 1) = x.1 := by
  let _ : Invertible (compactForm n (realCliffordSpinLastLocalSectionDirection x.1)) :=
    (realCliffordSpinLastLocalSectionDirection_form_eq_one x.1
      (mem_realCliffordSpinLastUnitNeighborhood.mp hx)).symm ▸ invertibleOne
  let _ : Invertible (compactForm n (lastUnitVector n)) :=
    (realCliffordForm_unitVector (n + 1) (Fin.last n)).symm ▸ invertibleOne
  rw [realCliffordSpinLastLocalSection]
  simp only [hx, dite_true]
  rw [← coe_spinToSpecialOrthogonal_apply, localSectionOn]
  rw [coe_spinToSpecialOrthogonal_spinReflectionPair]
  simp only [Subgroup.coe_mul, QuadraticMap.coe_reflectionOrthogonal, LinearEquiv.mul_apply]
  -- The public statement spells out the basis vector, while the dependent reflection instances
  -- above are built from the private abbreviation; align the vector before rewriting the action.
  rw [show Pi.single (Fin.last n) (1 : ℝ) = lastUnitVector n by rfl]
  rw [QuadraticMap.reflection_apply_self, map_neg]
  have hform : compactForm n (lastUnitVector n) = compactForm n (-x.1) := by
    rw [QuadraticMap.map_neg]
    simpa only [compactForm, lastUnitVector] using
      (realCliffordForm_unitVector (n + 1) (Fin.last n)).trans x.2.symm
  have hpos := compactForm_last_sub_neg_pos
    (mem_realCliffordSpinLastUnitNeighborhood.mp hx)
  let _ : Invertible (compactForm n (lastUnitVector n - -x.1)) :=
    (isUnit_iff_ne_zero.mpr hpos.ne').invertible
  have hreflect : QuadraticMap.reflection (compactForm n) (lastUnitVector n - -x.1)
      (lastUnitVector n) = -x.1 :=
    QuadraticMap.reflection_sub_apply_eq_of_map_eq
      (compactForm n) (lastUnitVector n) (-x.1) hform
  have hreflection : QuadraticMap.reflection (compactForm n)
      (realCliffordSpinLastLocalSectionDirection x.1) =
        QuadraticMap.reflection (compactForm n) (lastUnitVector n - -x.1) := by
    have hscale :
        (Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹ ≠ 0 :=
      inv_ne_zero (Real.sqrt_ne_zero'.mpr hpos)
    let _ : Invertible
        ((Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹) :=
      (isUnit_iff_ne_zero.mpr hscale).invertible
    convert QuadraticMap.reflection_smul_eq (compactForm n)
      (lastUnitVector n - -x.1)
      (Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹ using 1
    -- The direction is definitionally this normalized vector; only its proof-irrelevant norm
    -- instance differs from the one constructed for the generic rescaling theorem.
    congr 1
    exact Subsingleton.elim _ _
  rw [hreflection, hreflect, neg_neg]

end

end TauCeti
