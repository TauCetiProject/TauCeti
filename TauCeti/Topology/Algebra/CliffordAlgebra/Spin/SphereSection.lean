/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.ReflectionPair

/-!
# A local section of the compact Spin sphere action

Let `e` be the last coordinate unit vector. On the unit level of the positive-definite real
Clifford form, away from `-e`, the normalized vector

`u(x) = (sqrt (Q (e + x)))⁻¹ • (e + x)`

has quadratic norm one. The reflection-pair lift `u(x) * e` belongs to `Spin(n + 1)` and sends
`e` to `x`: reflection in `e` first sends `e` to `-e`, and reflection in `e + x` then sends
`-e` to `x`.

This file packages that lift as a function on the unit level, totalized by the identity at the
excluded antipode. The punctured chart is open, the lift is continuous there, and its action on
`e` is the identity map of the chart. These are the local-section data used in sphere bundle
charts for compact Spin groups; no global transitivity or bundle statement is made here.

## Main declarations

* `CliffordAlgebra.realCliffordSpinLastUnitChart` is the unit level away from the antipode of the
  last coordinate vector.
* `CliffordAlgebra.realCliffordSpinLastLocalSection` is the normalized reflection-pair lift.
* `CliffordAlgebra.continuousOn_realCliffordSpinLastLocalSection` proves its continuity on the
  chart.
* `CliffordAlgebra.realCliffordSpinLastLocalSection_action` proves that the lift carries the last
  coordinate vector to the prescribed unit vector.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

private abbrev compactForm (n : ℕ) := realCliffordForm (n + 1) 0

private abbrev compactUnitLevel (n : ℕ) :=
  {x : Fin (n + 1) → ℝ // compactForm n x = 1}

private def lastUnitVector (n : ℕ) : Fin (n + 1) → ℝ :=
  Pi.single (Fin.last n) 1

private theorem compactForm_lastUnitVector (n : ℕ) :
    compactForm n (lastUnitVector n) = 1 := by
  classical
  rw [show compactForm n = QuadraticMap.weightedSumSquares ℝ
      (1 : Fin (n + 1) → ℝ) by
    exact realCliffordForm_zero_eq_weightedSumSquares_one (n + 1)]
  rw [QuadraticMap.weightedSumSquares_apply]
  simp only [Pi.one_apply, one_smul, lastUnitVector]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The unit level of `realCliffordForm (n + 1) 0` with the antipode of the last coordinate unit
vector removed. -/
def realCliffordSpinLastUnitChart (n : ℕ) :
    Set {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1} :=
  {x | x.1 ≠ -(lastUnitVector n)}

/-- Membership in the last-vector chart means being different from the antipode of the last
coordinate unit vector. -/
@[simp]
theorem mem_realCliffordSpinLastUnitChart {n : ℕ}
    {x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1}} :
    x ∈ realCliffordSpinLastUnitChart n ↔
      x.1 ≠ -(Pi.single (Fin.last n) 1) :=
  Iff.rfl

/-- The punctured last-vector unit chart is open. -/
theorem isOpen_realCliffordSpinLastUnitChart (n : ℕ) :
    IsOpen (realCliffordSpinLastUnitChart n) := by
  rw [realCliffordSpinLastUnitChart]
  exact isOpen_compl_singleton.preimage continuous_subtype_val

private theorem last_sub_neg_ne_zero {n : ℕ} {x : compactUnitLevel n}
    (hx : x ∈ realCliffordSpinLastUnitChart n) :
    lastUnitVector n - -x.1 ≠ 0 := by
  intro h
  apply hx
  rw [eq_neg_iff_add_eq_zero]
  simpa only [sub_neg_eq_add, add_comm] using h

private theorem compactForm_last_sub_neg_pos {n : ℕ} {x : compactUnitLevel n}
    (hx : x ∈ realCliffordSpinLastUnitChart n) :
    0 < compactForm n (lastUnitVector n - -x.1) :=
  posDef_realCliffordForm_zero (n + 1) _ (last_sub_neg_ne_zero hx)

private def localSectionDirection {n : ℕ} (x : compactUnitLevel n)
    (_hx : x ∈ realCliffordSpinLastUnitChart n) : Fin (n + 1) → ℝ :=
  (Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹ •
    (lastUnitVector n - -x.1)

private theorem compactForm_localSectionDirection {n : ℕ} (x : compactUnitLevel n)
    (hx : x ∈ realCliffordSpinLastUnitChart n) :
    compactForm n (localSectionDirection x hx) = 1 := by
  have hpos := compactForm_last_sub_neg_pos hx
  have hsqrt : Real.sqrt (compactForm n (lastUnitVector n - -x.1)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hpos
  calc
    compactForm n (localSectionDirection x hx) =
        (Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹ *
          (Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹ *
            compactForm n (lastUnitVector n - -x.1) := by
      rw [localSectionDirection, QuadraticMap.map_smul]
      rfl
    _ = 1 := by
      field_simp
      simpa [pow_two] using (Real.sq_sqrt hpos.le).symm

private def localSectionOn {n : ℕ} (x : compactUnitLevel n)
    (hx : x ∈ realCliffordSpinLastUnitChart n) :
    realCliffordSpinGroupZero (n + 1) :=
  spinReflectionPair (compactForm n) (localSectionDirection x hx) (lastUnitVector n)
    (compactForm_localSectionDirection x hx) (compactForm_lastUnitVector n)

/-- A normalized reflection-pair lift on the last-vector unit chart, totalized by the identity at
the excluded antipode. -/
def realCliffordSpinLastLocalSection (n : ℕ)
    (x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1}) :
    realCliffordSpinGroupZero (n + 1) := by
  classical
  exact if hx : x ∈ realCliffordSpinLastUnitChart n then localSectionOn x hx else 1

/-- The normalized reflection-pair lift is continuous on the punctured last-vector chart. -/
theorem continuousOn_realCliffordSpinLastLocalSection (n : ℕ) :
    ContinuousOn (realCliffordSpinLastLocalSection n)
      (realCliffordSpinLastUnitChart n) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_induced_rng.mpr
  have hvector : Continuous (fun x : realCliffordSpinLastUnitChart n =>
      lastUnitVector n - -x.1.1) := by fun_prop
  have hform : Continuous (fun x : realCliffordSpinLastUnitChart n =>
      compactForm n (lastUnitVector n - -x.1.1)) := by
    simp only [compactForm, realCliffordForm_apply]
    fun_prop
  have hpos : ∀ x : realCliffordSpinLastUnitChart n,
      0 < compactForm n (lastUnitVector n - -x.1.1) := fun x =>
    compactForm_last_sub_neg_pos x.2
  have hscalar : Continuous (fun x : realCliffordSpinLastUnitChart n =>
      (Real.sqrt (compactForm n (lastUnitVector n - -x.1.1)))⁻¹) :=
    hform.sqrt.inv₀ fun x => Real.sqrt_ne_zero'.mpr (hpos x)
  have hdirection : Continuous (fun x : realCliffordSpinLastUnitChart n =>
      localSectionDirection x.1 x.2) := by
    convert hscalar.smul hvector using 1
    funext x
    rfl
  have hvalue : Continuous (fun x : realCliffordSpinLastUnitChart n =>
      ι (compactForm n) (localSectionDirection x.1 x.2) *
        ι (compactForm n) (lastUnitVector n)) :=
    ((continuous_ι (compactForm n)).comp hdirection).mul continuous_const
  exact hvalue.congr fun x => by
    change ι (compactForm n) (localSectionDirection x.1 x.2) *
        ι (compactForm n) (lastUnitVector n) =
      (realCliffordSpinLastLocalSection n x.1 : CliffordAlgebra (compactForm n))
    rw [realCliffordSpinLastLocalSection]
    simp only [x.2, dite_true, localSectionOn, coe_spinReflectionPair]

/-- On the punctured unit chart, the local section sends the last coordinate unit vector to its
input under the Spin vector action. -/
theorem realCliffordSpinLastLocalSection_action {n : ℕ}
    (x : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1})
    (hx : x ∈ realCliffordSpinLastUnitChart n) :
    spinVectorAction (realCliffordForm (n + 1) 0)
        (realCliffordSpinLastLocalSection n x)
        (Pi.single (Fin.last n) 1) = x.1 := by
  let _ : Invertible (compactForm n (localSectionDirection x hx)) :=
    (compactForm_localSectionDirection x hx).symm ▸ invertibleOne
  let _ : Invertible (compactForm n (lastUnitVector n)) :=
    (compactForm_lastUnitVector n).symm ▸ invertibleOne
  rw [realCliffordSpinLastLocalSection]
  simp only [hx, dite_true]
  rw [← coe_spinToSpecialOrthogonal_apply, localSectionOn]
  rw [coe_spinToSpecialOrthogonal_spinReflectionPair]
  simp only [Subgroup.coe_mul, QuadraticMap.coe_reflectionOrthogonal, LinearEquiv.mul_apply]
  rw [show Pi.single (Fin.last n) (1 : ℝ) = lastUnitVector n by rfl]
  rw [QuadraticMap.reflection_apply_self, map_neg]
  have hform : compactForm n (lastUnitVector n) = compactForm n (-x.1) := by
    rw [QuadraticMap.map_neg, compactForm_lastUnitVector]
    exact x.2.symm
  have hpos := compactForm_last_sub_neg_pos hx
  let _ : Invertible (compactForm n (lastUnitVector n - -x.1)) :=
    (isUnit_iff_ne_zero.mpr hpos.ne').invertible
  have hreflect : QuadraticMap.reflection (compactForm n) (lastUnitVector n - -x.1)
      (lastUnitVector n) = -x.1 :=
    QuadraticMap.reflection_sub_apply_eq_of_map_eq
      (compactForm n) (lastUnitVector n) (-x.1) hform
  have hscale :
      (Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact Real.sqrt_ne_zero'.mpr hpos
  have hreflection : QuadraticMap.reflection (compactForm n)
      (localSectionDirection x hx) =
        QuadraticMap.reflection (compactForm n) (lastUnitVector n - -x.1) := by
    let _ : Invertible
        ((Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹) :=
      (isUnit_iff_ne_zero.mpr hscale).invertible
    convert QuadraticMap.reflection_smul_eq (compactForm n)
      (lastUnitVector n - -x.1)
      (Real.sqrt (compactForm n (lastUnitVector n - -x.1)))⁻¹ using 1
    congr 1
    exact Subsingleton.elim _ _
  rw [hreflection, hreflect, neg_neg]

end

end CliffordAlgebra
