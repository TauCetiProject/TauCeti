/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Binary
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Isotropic
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Spinor norms of binary forms over a nonarchimedean local field

Let `K` be a nonarchimedean local field in which `2 ≠ 0`, such as `ℚ_[p]` for any prime `p`, and
let `Q ≅ ⟨a, b⟩` be a nondegenerate binary quadratic form over `K`. The image of the spinor norm
on `SO(Q)` is the image in `Kˣ/(Kˣ)²` of the norm group of the discriminant algebra
`E = K(√(-a b))` (`CliffordAlgebra.range_spinorNorm_of_equivalent_binary`). If `Q` is
anisotropic then `-a b` is not a square, so `E` is a quadratic field extension whose norm group has
index two in `Kˣ` (`TauCeti.quadraticNormSubgroup_index_eq_two_of_not_isSquare`). Since that norm
group contains the squares, its image in the square-class group also has index two.

So, in contrast to the isotropic case, the spinor norm of an anisotropic binary form over a local
field is not surjective on `SO(Q)`: for a binary form over `K`, surjectivity of the spinor norm on
`SO(Q)` is equivalent to isotropy. Over a finite field, by contrast, every unit is a norm from the
quadratic extension, so this equivalence is genuinely local.

## Main results

* `CliffordAlgebra.index_range_spinorNorm_of_finrank_eq_two_of_anisotropic`: the image of the
  spinor norm on the special orthogonal group of an anisotropic binary form has index two.
* `CliffordAlgebra.spinorNorm_surjective_iff_not_anisotropic_of_finrank_eq_two`: for a binary form
  the spinor norm on `SO(Q)` is surjective exactly when `Q` is isotropic.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §55 and §63.
-/

public section

namespace CliffordAlgebra

open TauCeti QuadraticMap

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Over a nonarchimedean local field with `2 ≠ 0`, the image of the spinor norm on the special
orthogonal group of an anisotropic binary form has index two in `Kˣ/(Kˣ)²`: it is the image of the
norm group of the discriminant quadratic extension. -/
theorem index_range_spinorNorm_of_finrank_eq_two_of_anisotropic (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 2) (hani : Q.Anisotropic) :
    ((spinorNorm Q hQ).range : Subgroup (Multiplicative (SquareClassGroup K))).index = 2 := by
  -- Diagonalize `Q ≅ ⟨a, b⟩`.
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  rw [weightedSumSquares_units] at hw
  let e : Fin 2 ≃ Fin (Module.finrank K V) := finCongr hV.symm
  have h : Q.Equivalent (weightedSumSquares K ![(w (e 0) : K), (w (e 1) : K)]) :=
    hw.trans (QuadraticForm.equivalent_weightedSumSquares_of_comp_eq e (by
      funext i
      fin_cases i <;> rfl)).symm
  -- An anisotropic binary form has nonsquare discriminant `-a b`: if `-a b = t²`, then
  -- `(t, a)` is an isotropic vector of `⟨a, b⟩`.
  have hsq : ¬IsSquare (-(w (e 0) * w (e 1))) := by
    rintro ⟨t, ht⟩
    have ht' : -((w (e 0) : K) * w (e 1)) = t * t := by
      simpa using congrArg Units.val ht
    have hzero : weightedSumSquares K ![(w (e 0) : K), (w (e 1) : K)]
        ![(t : K), (w (e 0) : K)] = 0 := by
      simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, smul_eq_mul]
      linear_combination (-(w (e 0) : K)) * ht'
    have h1 := congrFun (h.anisotropic_iff.mp hani _ hzero) 1
    simp only [Matrix.cons_val_one, Pi.zero_apply] at h1
    exact (w (e 0)).ne_zero h1
  -- The norm group contains the kernel of the square-class map, so its image has the same index.
  have hker : (squareClassHom (K := K)).ker ≤
      quadraticNormSubgroup (-((w (e 0) : K) * w (e 1))) := fun x hx ↦
    square_le_quadraticNormSubgroup _ (Subgroup.mem_square.mpr (by simpa using hx))
  have hmap := Subgroup.index_map_eq (G' := Multiplicative (SquareClassGroup K)) _
      squareClassHom_surjective hker
  rw [range_spinorNorm_of_equivalent_binary Q hQ h]
  refine hmap.trans ?_
  -- The norm-index theorem is stated for the unit `-(a b) : Kˣ`; push its coercion into `K`.
  simpa using quadraticNormSubgroup_index_eq_two_of_not_isSquare (Invertible.ne_zero (2 : K)) hsq

/-- Over a nonarchimedean local field with `2 ≠ 0`, the spinor norm on the special orthogonal group
of a nondegenerate binary form is surjective exactly when the form is isotropic. -/
theorem spinorNorm_surjective_iff_not_anisotropic_of_finrank_eq_two (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 2) :
    Function.Surjective (spinorNorm Q hQ) ↔ ¬Q.Anisotropic := by
  refine ⟨fun hsurj hani ↦ ?_, spinorNorm_surjective_of_not_anisotropic Q hQ⟩
  have hindex := index_range_spinorNorm_of_finrank_eq_two_of_anisotropic Q hQ hV hani
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.index_top] at hindex
  exact absurd hindex (by decide)

end CliffordAlgebra
