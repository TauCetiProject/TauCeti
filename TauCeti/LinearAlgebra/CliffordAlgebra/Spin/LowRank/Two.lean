/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.Two
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation

/-!
# The Spin group in dimension two

In dimension two the odd part of a Clifford algebra is exactly the image of its generating space.
If the quadratic form represents a unit, multiply an even Clifford unit by the corresponding
invertible vector. The product is odd, hence is another vector; solving for the original unit
expresses it as a product of two Lipschitz generators. Consequently every even unitary Clifford
unit belongs to the Lipschitz group, and the even unitary carrier is exactly the Spin carrier.

For the sum of two squares on `K²`, write `J = ι e₀ * ι e₁`, so that `J * J = -1`. Every even
element is `ι e₀ * ι w = w₀ + w₁ J`, so the even Clifford algebra is `K[J]`. When `2` is
invertible in `K` and `K` contains a square root `i` of `-1`, the character
`CliffordAlgebra.evenWeightedSumSquaresOneAlgHom`, sending `u + v J ↦ u + i v`, restricts to an
isomorphism from the Spin group, the elements with `u² + v² = 1`, onto `Kˣ`. Its inverse sends `z`
to `u + v J` with `u = (z + z⁻¹) / 2` and `v = i (z⁻¹ - z) / 2`, a product of two vectors of norm
one. Over `ℂ` this is the isomorphism `Spin₂(ℂ) ≅ ℂˣ`.

The argument is the standard low-dimensional Clifford calculation; see H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.

## Main definitions

* `CliffordAlgebra.spinGroupEquivUnitsWeightedSumSquaresOne`: the isomorphism from the Spin group
  of the sum of two squares onto `Kˣ`.

## Main results

* `CliffordAlgebra.mem_lipschitzGroup_of_mem_even_of_finrank_eq_two`: every even Clifford unit is
  Lipschitz when the form represents a unit.
* `CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_eq_two`: the Spin image
  and even unitary carrier coincide.
-/

public section

open Module

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

section Lipschitz

variable [Invertible (2 : K)]

/-- For a two-dimensional quadratic space representing a unit, every even Clifford unit lies in
Mathlib's Lipschitz group. -/
theorem mem_lipschitzGroup_of_mem_even_of_finrank_eq_two (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : finrank K V = 2) (x : (CliffordAlgebra Q)ˣ)
    (hx : (x : CliffordAlgebra Q) ∈ even Q) : x ∈ lipschitzGroup Q := by
  obtain ⟨v, hv⟩ := hQ
  let _ : Invertible (Q v) := hv.invertible
  have hodd : ((x * unitι Q v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 1 := by
    -- Expose the degree-zero characterization of `even` so graded multiplication sees the two
    -- factors, then normalize the unit coercions.
    change (x : CliffordAlgebra Q) ∈ evenOdd Q 0 at hx
    have hprod : (x : CliffordAlgebra Q) * ι Q v ∈ evenOdd Q 1 :=
      zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded hx (ι_mem_evenOdd_one Q v)
    simpa only [Units.val_mul, coe_unitι] using hprod
  rw [← range_ι_eq_evenOdd_one_of_finrank_eq_two Q hV] at hodd
  obtain ⟨w, hw⟩ := hodd
  have hwQ : IsUnit (Q w) :=
    isUnit_of_isUnit_ι Q (hw ▸ (x * unitι Q v).isUnit)
  let _ : Invertible (Q w) := hwQ.invertible
  have hxw : x * unitι Q v = unitι Q w := by
    apply Units.ext
    simpa only [Units.val_mul, coe_unitι] using hw.symm
  have hx_eq : x = unitι Q w * (unitι Q v)⁻¹ :=
    eq_mul_inv_iff_mul_eq.mpr hxw
  rw [hx_eq]
  exact mul_mem (unitι_mem_lipschitzGroup w) (inv_mem (unitι_mem_lipschitzGroup v))

/-- For a two-dimensional quadratic space representing a unit, the even unitary carrier lies in
the Lipschitz group. -/
theorem evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_two (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : finrank K V = 2) :
    evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  intro x hx
  exact mem_lipschitzGroup_of_mem_even_of_finrank_eq_two Q hQ hV x
    (evenUnitaryGroup.mem_even Q hx)

/-- For a two-dimensional quadratic space representing a unit, the Spin group fills the even
unitary carrier inside Clifford units. -/
-- Not `@[simp]`: `range_spinGroup_toUnits` already simplifies the left-hand side.
theorem range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_eq_two
    (Q : QuadraticForm K V) (hQ : ∃ v, IsUnit (Q v)) (hV : finrank K V = 2) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range = evenUnitaryGroup Q := by
  rw [range_spinGroup_toUnits]
  exact inf_eq_right.mpr (evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_two Q hQ hV)

end Lipschitz

/-! ### The sum of two squares when `-1` is a square -/

section SumTwoSquares

open QuadraticMap

variable (i : K) (hi : i * i = -1)

/-- The Spin element `ι e₀ * ι w` of a vector `w` of norm one, here `w = (u, v)` attached to
`z ∈ Kˣ` by `u = (z + z⁻¹) / 2` and `v = i (z⁻¹ - z) / 2`. -/
private theorem ι_mul_ι_mem_spinGroup_weightedSumSquaresOne [Invertible (2 : K)]
    (hi : i * i = -1) (z : Kˣ) :
    ι _ ![1, 0] * ι _ ![((z : K) + z⁻¹) / 2, i * ((z⁻¹ : Kˣ) - z) / 2] ∈
      spinGroup (weightedSumSquares K ![(1 : K), 1]) := by
  refine ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _ ?_
  simp only [weightedSumSquares_fin_two_apply, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hz : (z : K) * (z⁻¹ : Kˣ) = 1 := z.mul_inv
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  field_simp
  linear_combination 4 * hz + (((z⁻¹ : Kˣ) : K) - z) ^ 2 * hi

/-- **The Spin group of the sum of two squares is the multiplicative group** of a field `K` in
which `2` is invertible and which contains a square root `i` of `-1`. The isomorphism is the
character `evenWeightedSumSquaresOneAlgHom`, sending `u + v J` to `u + i v`; its inverse sends `z`
to `u + v J` with `u = (z + z⁻¹) / 2` and `v = i (z⁻¹ - z) / 2`. -/
noncomputable def spinGroupEquivUnitsWeightedSumSquaresOne [Invertible (2 : K)] :
    spinGroup (weightedSumSquares K ![(1 : K), 1]) ≃* Kˣ where
  toFun g := Units.map (evenWeightedSumSquaresOneAlgHom i hi : even _ →* K)
    ((spinGroupToEven _).toHomUnits g)
  invFun z := ⟨_, ι_mul_ι_mem_spinGroup_weightedSumSquaresOne i hi z⟩
  left_inv g := by
    let _ : Invertible (weightedSumSquares K ![(1 : K), 1] ![1, 0]) :=
      invertibleOfNonzero (by simp)
    obtain ⟨y, hy⟩ := (mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two _ (Module.finrank_fin_fun K)
      ![1, 0]).1 (spinGroup.mem_even g.2)
    have hg : spinGroupToEven _ g = (even.ι _).bilin ![1, 0] y := Subtype.ext (by simp [hy])
    have hg' : spinGroupToEven _ g⁻¹ = (even.ι _).bilin y ![1, 0] := Subtype.ext (by
      simp [← spinGroup.star_eq_inv, hy])
    have h2 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero
    apply Subtype.ext
    simp only [Units.coe_map, MonoidHom.coe_toHomUnits, MonoidHom.coe_ofClass,
      ← map_inv, hg, hg', evenWeightedSumSquaresOneAlgHom_ι]
    rw [hy]
    congr 2
    ext j
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination y 0 * h2
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination -(y 1 * 2 * 2⁻¹) * hi + y 1 * h2
  right_inv z := by
    ext
    have h : spinGroupToEven _ ⟨_, ι_mul_ι_mem_spinGroup_weightedSumSquaresOne i hi z⟩ =
        (even.ι _).bilin ![1, 0] ![((z : K) + z⁻¹) / 2, i * ((z⁻¹ : Kˣ) - z) / 2] :=
      Subtype.ext (by simp)
    simp only [Units.coe_map, MonoidHom.coe_toHomUnits, MonoidHom.coe_ofClass, h,
      evenWeightedSumSquaresOneAlgHom_ι]
    have h2 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (((z⁻¹ : Kˣ) : K) - z) / 2 * hi + (z : K) * h2
  map_mul' g h := by simp

variable [Invertible (2 : K)]

/-- The unit attached to a Spin element is the value of the character
`evenWeightedSumSquaresOneAlgHom` on it. -/
@[simp]
theorem coe_spinGroupEquivUnitsWeightedSumSquaresOne_apply
    (g : spinGroup (weightedSumSquares K ![(1 : K), 1])) :
    (spinGroupEquivUnitsWeightedSumSquaresOne i hi g : K) =
      evenWeightedSumSquaresOneAlgHom i hi (spinGroupToEven _ g) :=
  (rfl)

/-- The Spin element attached to a unit `z` is `ι e₀ * ι (u, v)`, that is `u + v J`, with
`u = (z + z⁻¹) / 2` and `v = i (z⁻¹ - z) / 2`. -/
@[simp]
theorem coe_spinGroupEquivUnitsWeightedSumSquaresOne_symm_apply (z : Kˣ) :
    (((spinGroupEquivUnitsWeightedSumSquaresOne i hi).symm z :
        spinGroup (weightedSumSquares K ![(1 : K), 1])) :
          CliffordAlgebra (weightedSumSquares K ![(1 : K), 1])) =
      ι _ ![1, 0] * ι _ ![((z : K) + z⁻¹) / 2, i * ((z⁻¹ : Kˣ) - z) / 2] :=
  (rfl)

end SumTwoSquares

end CliffordAlgebra
