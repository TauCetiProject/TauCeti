/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Algebra.Central.Defs
public import TauCeti.Algebra.Quaternion.SplittingCriterion
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic.LinearCombination

/-!
# Central simple quaternion symbol algebras

This file proves centrality and simplicity for the general quaternion algebra `ℍ[K,a,b,c]`. For a
field `K` with `2` invertible, simplicity holds when `c * QuadraticAlgebra.discr a b ≠ 0`:
completing the square reduces this case to a symbol with both parameters units, for which the norm
criterion gives either a division algebra or a two-by-two matrix algebra. The two-parameter symbol
`ℍ[K,a,b]` is the specialization used by the Brauer-valued invariants.

Centrality only requires two to be regular: commuting with `i` and `j` forces the imaginary
coordinates to vanish when either the `j`-square or the discriminant is regular. In particular,
this applies over integral domains of characteristic different from two.

## Main results

* `TauCeti.QuaternionAlgebra.isSimpleRing_of_j_sq_mul_discr_ne_zero`: a quaternion algebra with
  nonzero `j`-square and nonzero discriminant is simple.
* `TauCeti.QuaternionAlgebra.instIsSimpleRing`: quaternion symbol algebras with both parameters
  units are simple.
* `TauCeti.QuaternionAlgebra.mem_center_iff` and
  `TauCeti.QuaternionAlgebra.isCentral_of_isLeftRegular_j_sq_or_isLeftRegular_discr`: centrality
  when two is regular and either the `j`-square or the discriminant is regular.
* `TauCeti.QuaternionAlgebra.isCentral_of_j_sq_ne_zero_or_discr_ne_zero`: centrality over a
  domain of characteristic different from two, without requiring two to be invertible.
* `TauCeti.QuaternionAlgebra.center_units_eq_range_unitsMap_algebraMap`: the center of a
  quaternion unit group with unit symbols consists exactly of scalar units, over a base ring
  in which two is left-regular, including the split case.

The split/division dichotomy used here is the norm-equation criterion in
`TauCeti.Algebra.Quaternion.SplittingCriterion`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §1.1.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {K : Type*}

section Field

variable [Field K] [Invertible (2 : K)] (a b : Kˣ)

/-- A quaternion symbol with both parameters units is a simple ring. -/
instance instIsSimpleRing : IsSimpleRing ℍ[K,(a : K),(b : K)] := by
  rcases QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix a b with hdiv | hsplit
  · let divisionRing : DivisionRing ℍ[K,(a : K),(b : K)] :=
      DivisionRing.ofIsUnitOrEqZero (fun x ↦ by
        by_cases hx : x = 0
        · exact Or.inr hx
        · exact Or.inl (hdiv x hx))
    exact @DivisionRing.isSimpleRing _ divisionRing
  · obtain ⟨e⟩ := hsplit
    exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance

/-- A quaternion algebra with nonzero `j`-square and nonzero discriminant is simple. -/
theorem isSimpleRing_of_j_sq_mul_discr_ne_zero {a b c : K}
    (h : c * QuadraticAlgebra.discr a b ≠ 0) : IsSimpleRing ℍ[K,a,b,c] := by
  have ⟨hc, hd⟩ := mul_ne_zero_iff.mp h
  let u : Kˣ := Units.mk0 (QuadraticAlgebra.discr a b) hd
  let v : Kˣ := Units.mk0 c hc
  have htarget : IsSimpleRing ℍ[K,QuadraticAlgebra.discr a b,0,c] := instIsSimpleRing u v
  exact IsSimpleRing.of_ringEquiv (completeSquareEquiv a b c).symm.toRingEquiv htarget

end Field

section Centrality

variable [CommRing K]

private theorem center_coordinates_eq_zero (a b c : K) (h2 : IsLeftRegular (2 : K))
    (h : IsLeftRegular c ∨ IsLeftRegular (QuadraticAlgebra.discr a b)) {x : ℍ[K,a,b,c]}
    (hi : (⟨0, 1, 0, 0⟩ : ℍ[K,a,b,c]) * x = x * (⟨0, 1, 0, 0⟩ : ℍ[K,a,b,c]))
    (hj : (⟨0, 0, 1, 0⟩ : ℍ[K,a,b,c]) * x = x * (⟨0, 0, 1, 0⟩ : ℍ[K,a,b,c])) :
    x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0 := by
  have hiJ := congrArg _root_.QuaternionAlgebra.imJ hi
  have hiK := congrArg _root_.QuaternionAlgebra.imK hi
  have hjI := congrArg _root_.QuaternionAlgebra.imI hj
  have hjK := congrArg _root_.QuaternionAlgebra.imK hj
  simp only [_root_.QuaternionAlgebra.imI_mul, _root_.QuaternionAlgebra.imJ_mul,
    _root_.QuaternionAlgebra.imK_mul] at hiJ hiK hjI hjK
  have hI : (2 : K) * x.imI = 0 := by
    linear_combination -hjK
  have hK : x.imK = 0 := by
    rcases h with hc | hd
    · apply hc.mul_left_eq_zero_iff.mp
      apply h2.mul_left_eq_zero_iff.mp
      linear_combination -hjI
    · apply hd.mul_left_eq_zero_iff.mp
      rw [QuadraticAlgebra.discr_def]
      -- Eliminate `x.imJ` from the two coordinates of the commutator with `i`.
      linear_combination 2 * hiJ + b * hiK
  have hJ : (2 : K) * x.imJ = 0 := by
    rw [hK] at hiK
    linear_combination hiK
  exact ⟨h2.mul_left_eq_zero_iff.mp hI, h2.mul_left_eq_zero_iff.mp hJ, hK⟩

/-- When two is regular and either the `j`-square or the discriminant is regular,
an element of `ℍ[K,a,b,c]` is central iff its three imaginary coordinates vanish. -/
@[simp]
theorem mem_center_iff (a b c : K) (h2 : IsRegular (2 : K))
    (h : IsRegular c ∨ IsRegular (QuadraticAlgebra.discr a b)) {x : ℍ[K,a,b,c]} :
    x ∈ Subalgebra.center K ℍ[K,a,b,c] ↔
      x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0 := by
  constructor
  · intro hx
    exact center_coordinates_eq_zero a b c h2.left (h.imp (·.left) (·.left))
      (Subalgebra.mem_center_iff.mp hx _) (Subalgebra.mem_center_iff.mp hx _)
  · intro hx
    have hx' : x = algebraMap K ℍ[K,a,b,c] x.re := by
      ext <;> simp [hx.1, hx.2.1, hx.2.2]
    rw [hx']
    exact Subalgebra.algebraMap_mem _ _

/-- A quaternion algebra with left-regular `j`-square or left-regular discriminant is central
when two is left-regular. -/
theorem isCentral_of_isLeftRegular_j_sq_or_isLeftRegular_discr {a b c : K}
    (h2 : IsLeftRegular (2 : K))
    (h : IsLeftRegular c ∨ IsLeftRegular (QuadraticAlgebra.discr a b)) :
    Algebra.IsCentral K ℍ[K,a,b,c] :=
  ⟨fun x hx ↦ Algebra.mem_bot.mpr ⟨x.re, by
    obtain ⟨hI, hJ, hK⟩ := (mem_center_iff a b c (isLeftRegular_iff_isRegular.mp h2)
      (h.imp isLeftRegular_iff_isRegular.mp isLeftRegular_iff_isRegular.mp)).mp hx
    ext <;> simp [hI, hJ, hK]⟩⟩

/-- A quaternion symbol whose second parameter `b` is a unit is central over its base ring. -/
instance instIsCentral (a : K) (b : Kˣ) [Invertible (2 : K)] :
    Algebra.IsCentral K ℍ[K,a,(b : K)] :=
  let h2 : IsLeftRegular (2 : K) := (isUnit_of_invertible (2 : K)).isRegular.left
  let hb : IsLeftRegular (b : K) := b.isUnit.isRegular.left
  isCentral_of_isLeftRegular_j_sq_or_isLeftRegular_discr h2 (Or.inl hb)

/-- Over a base ring in which two is left-regular, the center of the unit group of a quaternion
symbol with unit parameters is exactly the scalar units. This includes split quaternion algebras. -/
theorem center_units_eq_range_unitsMap_algebraMap (a b : Kˣ) (h2 : IsLeftRegular (2 : K)) :
    Subgroup.center ℍ[K,(a : K),(b : K)]ˣ =
      (Units.map (algebraMap K ℍ[K,(a : K),(b : K)]).toMonoidHom).range := by
  ext x
  constructor
  · intro hx
    have hi : IsUnit (⟨0, 1, 0, 0⟩ : ℍ[K,(a : K),(b : K)]) :=
      _root_.QuaternionAlgebra.isUnit_iff_normForm_isUnit _ _ _ _ |>.mpr (by
        simp [_root_.QuaternionAlgebra.normForm_apply_coordinates])
    have hj : IsUnit (⟨0, 0, 1, 0⟩ : ℍ[K,(a : K),(b : K)]) :=
      _root_.QuaternionAlgebra.isUnit_iff_normForm_isUnit _ _ _ _ |>.mpr (by
        simp [_root_.QuaternionAlgebra.normForm_apply_coordinates])
    have hxi := congrArg Units.val (Subgroup.mem_center_iff.mp hx hi.unit)
    have hxj := congrArg Units.val (Subgroup.mem_center_iff.mp hx hj.unit)
    have hc := center_coordinates_eq_zero (a : K) 0 (b : K)
      h2 (Or.inl b.isUnit.isRegular.left)
      (by simpa only [Units.val_mul, hi.unit_spec] using hxi)
      (by simpa only [Units.val_mul, hj.unit_spec] using hxj)
    have hs : (x : ℍ[K,(a : K),(b : K)]) = algebraMap K _ x.val.re := by
      ext <;> simp [hc.1, hc.2.1, hc.2.2]
    have hu : IsUnit x.val.re := by
      have hn := (_root_.QuaternionAlgebra.isUnit_iff_normForm_isUnit _ _ _ _).mp x.isUnit
      rw [hs] at hn
      simpa only [_root_.QuaternionAlgebra.coe_algebraMap,
        _root_.QuaternionAlgebra.normForm_coe,
        isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)] using hn
    exact ⟨hu.unit, Units.ext (by simpa using hs.symm)⟩
  · rintro ⟨r, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun y => Units.ext ?_
    exact (Algebra.commutes (r : K) (y : ℍ[K,(a : K),(b : K)])).symm

end Centrality

section DomainCentrality

variable [CommRing K] [NoZeroDivisors K] [NeZero (2 : K)]

/-- Over a domain of characteristic different from two, a quaternion algebra with nonzero
`j`-square or discriminant is central, even when two is not invertible. -/
theorem isCentral_of_j_sq_ne_zero_or_discr_ne_zero {a b c : K}
    (h : c ≠ 0 ∨ QuadraticAlgebra.discr a b ≠ 0) :
    Algebra.IsCentral K ℍ[K,a,b,c] := by
  apply isCentral_of_isLeftRegular_j_sq_or_isLeftRegular_discr
    (IsRegular.of_ne_zero' (NeZero.ne (2 : K))).left
  exact h.imp (fun hc ↦ (IsRegular.of_ne_zero' hc).left)
    (fun hd ↦ (IsRegular.of_ne_zero' hd).left)

end DomainCentrality

end QuaternionAlgebra

end TauCeti
