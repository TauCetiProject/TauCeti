/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates

/-!
# Discriminant classes of standard-coordinate Gram-matrix lattices

Let `G` be an integral symmetric matrix presenting the lattice
`ofGramMatrix (Pi.basisFun ℚ ι) G hG` on `ι → ℚ`, and let `M` be an integer matrix with
`G M = d • 1` for some `d ≠ 0`. Then the columns of `M / d` are the dual basis vectors
(`TauCeti.IntegralLattice.mem_ofGramMatrix_basisFun_dualCarrier_of_mul_eq_smul_one`). This file
computes their discriminant classes from `M` alone: two such classes agree exactly when the
corresponding columns of `M` are congruent modulo `d`, and the discriminant quadratic value of the
`i`-th class is `M i i / (2 d)` modulo `1`. It also shows that the whole discriminant group is
killed by `n` when `G M = n • 1`.

## Main results

* `TauCeti.IntegralLattice.discriminantGroup_mk_eq_mk_iff_of_mul_eq_smul_one` and
  `TauCeti.IntegralLattice.discriminantGroup_mk_eq_zero_iff_of_mul_eq_smul_one`: equality of the
  classes of columns of `M / d` is congruence of the columns of `M` modulo `d`.
* `TauCeti.IntegralLattice.discriminantQuadraticMap_mk_of_mul_eq_smul_one`: the discriminant
  quadratic value of the class of the `i`-th column of `M / d` is `M i i / (2 d)`.
* `TauCeti.IntegralLattice.nsmul_discriminantGroup_ofGramMatrix_basisFun_eq_zero`: if
  `G M = n • 1`, the discriminant group is killed by `n`.
-/

public section

namespace TauCeti.IntegralLattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℤ) (hG : G.IsSymm)

/-- If `G M = n • 1` over `ℤ`, the discriminant group of the lattice presented by `G` is killed
by `n`: every dual vector is `M w / n` for the integer vector `w = G x`. -/
theorem nsmul_discriminantGroup_ofGramMatrix_basisFun_eq_zero {M : Matrix ι ι ℤ} {n : ℕ}
    (hM : G * M = (n : ℤ) • 1) (a : (ofGramMatrix (Pi.basisFun ℚ ι) G hG).DiscriminantGroup) :
    n • a = 0 := by
  induction a using Submodule.Quotient.induction_on with | _ x => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · exact zero_smul _ _
  rw [← Submodule.Quotient.mk_smul, discriminantGroup_mk_eq_zero_iff,
    mem_ofGramMatrix_basisFun_carrier_iff]
  choose w hw using (mem_ofGramMatrix_basisFun_dualCarrier_iff G hG x).mp x.property
  intro j
  refine ⟨∑ i, M j i * w i, ?_⟩
  have hx := apply_eq_sum_mul_form_ofGramMatrix_basisFun_div G hG hM (by exact_mod_cast hn)
    (x : ι → ℚ) j
  simp_rw [form_ofGramMatrix_basisFun_right, ← hw] at hx
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [Submodule.coe_smul_of_tower, Pi.smul_apply, hx, nsmul_eq_mul]
  push_cast
  field_simp

section Column

variable {M : Matrix ι ι ℤ} {d : ℤ} (hM : G * M = d • 1) (hd : d ≠ 0)
include hM hd

/-- The classes of the `i`-th and `i'`-th columns of `M / d` agree exactly when the two columns of
`M` are congruent modulo `d`. -/
theorem discriminantGroup_mk_eq_mk_iff_of_mul_eq_smul_one (i i' : ι) :
    (Submodule.Quotient.mk
        ⟨_, mem_ofGramMatrix_basisFun_dualCarrier_of_mul_eq_smul_one G hG hM hd i⟩ :
        (ofGramMatrix (Pi.basisFun ℚ ι) G hG).DiscriminantGroup) =
      Submodule.Quotient.mk
        ⟨_, mem_ofGramMatrix_basisFun_dualCarrier_of_mul_eq_smul_one G hG hM hd i'⟩ ↔
      ∀ j, d ∣ M j i - M j i' := by
  rw [discriminantGroup_mk_eq_iff, mem_ofGramMatrix_basisFun_carrier_iff]
  refine forall_congr' fun j ↦ ?_
  rw [Submodule.coe_sub, Pi.sub_apply, ← Rat.den_div_intCast_eq_one_iff _ _ hd, Int.cast_sub,
    sub_div]
  exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ Rat.den_intCast z, fun h ↦ ⟨_, (Rat.den_eq_one_iff _).mp h⟩⟩

/-- The class of the `i`-th column of `M / d` vanishes exactly when that column of `M` is
divisible by `d`. -/
theorem discriminantGroup_mk_eq_zero_iff_of_mul_eq_smul_one (i : ι) :
    (Submodule.Quotient.mk
        ⟨_, mem_ofGramMatrix_basisFun_dualCarrier_of_mul_eq_smul_one G hG hM hd i⟩ :
        (ofGramMatrix (Pi.basisFun ℚ ι) G hG).DiscriminantGroup) = 0 ↔
      ∀ j, d ∣ M j i := by
  rw [discriminantGroup_mk_eq_zero_iff, mem_ofGramMatrix_basisFun_carrier_iff]
  refine forall_congr' fun j ↦ ?_
  rw [Submodule.coe_mk, ← Rat.den_div_intCast_eq_one_iff _ _ hd]
  exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ Rat.den_intCast z, fun h ↦ ⟨_, (Rat.den_eq_one_iff _).mp h⟩⟩

/-- The discriminant quadratic value of the class of the `i`-th column of `M / d` is
`M i i / (2 d)` modulo `1`. -/
theorem discriminantQuadraticMap_mk_of_mul_eq_smul_one
    (hL : (ofGramMatrix (Pi.basisFun ℚ ι) G hG).IsEven) (i : ι) :
    (ofGramMatrix (Pi.basisFun ℚ ι) G hG).discriminantQuadraticMap hL
        (Submodule.Quotient.mk
          ⟨_, mem_ofGramMatrix_basisFun_dualCarrier_of_mul_eq_smul_one G hG hM hd i⟩) =
      (((M i i : ℚ) / (2 * d) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticMap_mk, form_ofGramMatrix_basisFun_of_mul_eq_smul_one G hG hM hd,
    div_div, mul_comm]

end Column

end TauCeti.IntegralLattice
