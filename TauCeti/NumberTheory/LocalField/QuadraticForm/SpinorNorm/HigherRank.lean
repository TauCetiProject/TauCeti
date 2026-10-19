/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.NumberTheory.LocalField.SquareClass
import TauCeti.NumberTheory.LocalField.QuadraticForm.Isotropy

/-!
# Surjectivity of local spinor norms in dimension at least three

For a nondegenerate quadratic space of dimension at least three over a nonarchimedean local
field of characteristic different from two, every square class occurs as the spinor norm of a
product of two reflections. Consequently the spinor norm is surjective on both the special
orthogonal and orthogonal groups, including when the space is anisotropic.

The key input is `QuadraticForm.exists_mem_unitValueSet_and_mem_of_five_le_finrank_add`:
`Q` and `a • Q` represent a common nonzero value `b`. Thus `Q` represents both `b` and `b / a`,
and the product of the corresponding reflections has spinor norm `[b² / a] = [a]`.
This uses the local isotropy bound in dimension five, without identifying the Clifford algebra
or choosing an orthogonal basis.

The image of Spin in the special orthogonal group is the spinor-norm kernel. Its index is
therefore the number of square classes: four away from residue characteristic two, and eight
over `ℚ_[2]`. These indices measure the failure of the Spin projection to be surjective on
local points.

The surjectivity theorems are
`TauCeti.QuadraticMap.spinorNorm_surjective_of_three_le_finrank` and
`TauCeti.QuadraticMap.orthogonalSpinorNorm_surjective_of_three_le_finrank`.
After `open TauCeti`, use `Q.spinorNorm_surjective_of_three_le_finrank hQ hV` and
`Q.orthogonalSpinorNorm_surjective_of_three_le_finrank hQ hV` for a form `Q`, its
nondegeneracy proof `hQ`, and a dimension bound `hV : 3 ≤ Module.finrank K V`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §55, especially 55:6.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.2, Theorem 6, for the local isotropy bound.
-/

public section

namespace TauCeti

namespace QuadraticMap

open TauCeti _root_.CliffordAlgebra _root_.QuadraticMap TauCeti.QuadraticMap
open _root_.ValuativeRel

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Every unit square class is the spinor norm of two anisotropic reflections in a regular
local quadratic space of dimension at least three. -/
theorem exists_reflectionPairSpecialOrthogonal_spinorNorm_eq (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : 3 ≤ Module.finrank K V) (a : Kˣ) :
    ∃ (v w : V) (_ : Invertible (Q v)) (_ : Invertible (Q w)),
      spinorNorm Q hQ (reflectionPairSpecialOrthogonal Q v w) = squareClassHom a := by
  have haQ : ((a : K) • Q).Nondegenerate :=
    (QuadraticMap.nondegenerate_smul_iff a.isUnit Q).mpr hQ
  obtain ⟨b, hb, hab⟩ :=
    Q.exists_mem_unitValueSet_and_mem_of_five_le_finrank_add hQ ((a : K) • Q) haQ
      (by omega) (by omega) (by omega)
  obtain ⟨v, hv⟩ := (represents_iff _ _).mp (mem_unitValueSet.mp hb)
  obtain ⟨w, hw⟩ := (represents_iff _ _).mp (mem_unitValueSet.mp hab)
  have hv0 : Q v ≠ 0 := by rw [hv]; exact b.ne_zero
  have hw0 : Q w ≠ 0 := by
    intro hw0
    exact b.ne_zero (by simpa [hw0] using hw.symm)
  let _ : Invertible (Q v) := invertibleOfNonzero hv0
  let _ : Invertible (Q w) := invertibleOfNonzero hw0
  refine ⟨v, w, inferInstance, inferInstance, ?_⟩
  have hb' : b = a * unitOfInvertible (Q w) :=
    Units.ext (by simpa using hw.symm)
  rw [spinorNorm_reflectionPairSpecialOrthogonal]
  have hv' : unitOfInvertible (Q v) = b := Units.ext hv
  rw [hv', hb']
  simp only [squareClassHom_apply]
  apply Multiplicative.ofAdd.injective
  apply (squareClass_eq_iff_isSquare_mul _ _).mpr
  refine ⟨a * unitOfInvertible (Q w), ?_⟩
  ac_rfl

/-- The spinor norm on the special orthogonal group of a regular local quadratic space of
dimension at least three is surjective, whether or not the form is isotropic. -/
theorem spinorNorm_surjective_of_three_le_finrank (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : 3 ≤ Module.finrank K V) :
    Function.Surjective (spinorNorm Q hQ) := by
  intro c
  obtain ⟨a, rfl⟩ := squareClassHom_surjective c
  obtain ⟨v, w, hv, hw, h⟩ := exists_reflectionPairSpecialOrthogonal_spinorNorm_eq Q hQ hV a
  let _ : Invertible (Q v) := hv
  let _ : Invertible (Q w) := hw
  exact ⟨reflectionPairSpecialOrthogonal Q v w, h⟩

/-- The spinor norm on the full orthogonal group of a regular local quadratic space of
dimension at least three is surjective. -/
theorem orthogonalSpinorNorm_surjective_of_three_le_finrank (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : 3 ≤ Module.finrank K V) :
    Function.Surjective (orthogonalSpinorNorm Q hQ) := by
  exact orthogonalSpinorNorm_surjective_of_spinorNorm_surjective Q hQ
    (spinorNorm_surjective_of_three_le_finrank Q hQ hV)

/-- In dimension at least three, the index of the Spin image in the local special orthogonal
group is the number of square classes, `4 · #𝓀[K] ^ v_K(2)`. -/
theorem index_range_spinToSpecialOrthogonal_of_three_le_finrank (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : 3 ≤ Module.finrank K V) :
    (spinToSpecialOrthogonal Q).range.index =
      4 * Nat.card 𝓀[K] ^ natCastValuation K 2 (Invertible.ne_zero (2 : K)) := by
  rw [range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ,
    Subgroup.index_ker (G' := Multiplicative (SquareClassGroup K)),
    MonoidHom.range_eq_top.mpr (spinorNorm_surjective_of_three_le_finrank Q hQ hV),
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd]
  exact natCard_squareClassGroup _

/-- Away from residue characteristic two, the Spin image in a regular local special orthogonal
group of dimension at least three has index four. -/
theorem index_range_spinToSpecialOrthogonal_eq_four_of_three_le_finrank
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : 3 ≤ Module.finrank K V)
    (h2 : IsUnit (2 : 𝒪[K])) : (spinToSpecialOrthogonal Q).range.index = 4 := by
  rw [index_range_spinToSpecialOrthogonal_of_three_le_finrank Q hQ hV,
    natCastValuation_eq_zero_of_isUnit K (Invertible.ne_zero (2 : K)) h2]
  simp

end LocalField

section PadicTwo

variable {V : Type*} [AddCommGroup V] [Module ℚ_[2] V] [FiniteDimensional ℚ_[2] V]

/-- Over `ℚ_[2]`, the Spin image in a regular special orthogonal group of dimension at least
three has index eight. -/
theorem index_range_spinToSpecialOrthogonal_eq_eight_of_three_le_finrank
    (Q : QuadraticForm ℚ_[2] V) (hQ : Q.Nondegenerate) (hV : 3 ≤ Module.finrank ℚ_[2] V) :
    (spinToSpecialOrthogonal Q).range.index = 8 := by
  rw [index_range_spinToSpecialOrthogonal_of_three_le_finrank Q hQ hV,
    ← absoluteRamificationIndex_eq_natCastValuation ℚ_[2] 2,
    absoluteRamificationIndex_padic, Padic.natCard_residueField]
  norm_num

end PadicTwo

end QuadraticMap

end TauCeti
