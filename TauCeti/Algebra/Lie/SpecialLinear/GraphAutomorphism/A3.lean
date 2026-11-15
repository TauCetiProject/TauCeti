/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Bracket generation of the pinned A₃ fixed algebra

For the pinned reversal of `sl₄`, the fixed matrices have ten independent entries.
`TauCeti.TypeAThreeFixed.coordinates` and `basis` give their coordinates and integral
matrix basis over every commutative ring. The positive root vectors are
`E₀₁ + E₂₃`, `E₁₂`, `E₀₂ - E₁₃`, `E₀₃`; the negative ones are
`E₁₀ + E₃₂`, `E₂₁`, `-E₂₀ + E₃₁`, `E₃₀`.
In signed interval-root notation these are the combinations
`x_a + x_c`, `x_b`, `x_ab - x_bc`, `x_abc` and their negative counterparts.
The other two basis vectors are the orbit sums of simple coroots.

`lieSpan_simple_eq_top` proves generation by the four folded simple root vectors
when two is invertible. The double brackets giving the highest and lowest root
vectors have coefficient `-2`; this factor is retained in the integral equations.
No assertion of generation in characteristic two is made.

The construction uses the native `typeASpecialLinearGraphAutomorphism` and its
fixed Lie subalgebra, not a separately specified involution.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9, for
  diagram folding and the orbit-sum generators.
-/

public section

namespace TauCeti.TypeAThreeFixed

open Matrix LieAlgebra.SpecialLinear

variable (R : Type*) [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The fixed Lie algebra of the pinned reversal of `sl₄`. -/
abbrev Fixed := (typeASpecialLinearGraphAutomorphism 3 R).toLieHom.fixedSubalgebra

/-- Fixed elements are equal when all their matrix entries agree. -/
@[ext]
theorem Fixed.ext {X Y : Fixed R} (h : ∀ i j, X.val.val i j = Y.val.val i j) : X = Y :=
  Subtype.ext (Subtype.ext (Matrix.ext h))

/-- Reconstruct a fixed matrix from its two Cartan and eight root coordinates. -/
private def matrixOf (c : Fin 10 → R) : Matrix (Fin 4) (Fin 4) R :=
  !![c 0, c 2, c 4, c 5;
     c 6, -c 0 + c 1, c 3, -c 4;
     -c 8, c 7, c 0 - c 1, c 2;
     c 9, c 8, c 6, -c 0]

private theorem matrixOf_trace (c : Fin 10 → R) : trace (matrixOf R c) = 0 := by
  simp [matrixOf, trace, Fin.sum_univ_succ]
  ring

private def ofCoordinates (c : Fin 10 → R) : Fixed R :=
  ⟨⟨matrixOf R c, matrixOf_trace R c⟩, by
    apply LieHom.mem_fixedSubalgebra.mpr
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_typeASpecialLinearGraphAutomorphism,
        typeAGraphLieEquiv_apply_apply, matrixOf, pow_succ] <;> ring⟩

/-- The ten coordinates of an actual fixed matrix. The first two are simple-coroot
orbit coordinates; the remaining coordinates follow the positive then negative roots. -/
def coordinates : Fixed R ≃ₗ[R] (Fin 10 → R) where
  toFun X := ![X.val.val 0 0, X.val.val 0 0 + X.val.val 1 1,
    X.val.val 0 1, X.val.val 1 2, X.val.val 0 2, X.val.val 0 3,
    X.val.val 1 0, X.val.val 2 1, -X.val.val 2 0, X.val.val 3 0]
  invFun := ofCoordinates R
  left_inv X := by
    have h (i j : Fin 4) :
        -((-1 : R) ^ i.val * X.val.val j.rev i.rev * (-1 : R) ^ j.val) =
          X.val.val i j := by
      simpa only [LieEquiv.coe_toLieHom, coe_typeASpecialLinearGraphAutomorphism,
        typeAGraphLieEquiv_apply_apply] using
        congrArg (fun Y : sl (Fin 4) R ↦ Y.val i j)
          (LieHom.mem_fixedSubalgebra.mp X.property)
    -- These six fixed-point equations determine the dependent entries at
    -- (1,3), (2,2), (2,3), (3,1), (3,2), (3,3); the other ten are coordinates.
    have h13 := h 1 3
    have h22 := h 2 2
    have h23 := h 2 3
    have h31 := h 3 1
    have h32 := h 3 2
    have h33 := h 3 3
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [ofCoordinates, matrixOf, pow_succ] <;> grind
  right_inv c := by
    funext i
    fin_cases i <;> simp [ofCoordinates, matrixOf]
  map_add' X Y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a X := by
    funext i
    fin_cases i <;> simp [mul_add]

/-- Read the independent entries of a fixed matrix. -/
@[simp]
theorem coordinates_apply (X : Fixed R) :
    coordinates R X = ![X.val.val 0 0, X.val.val 0 0 + X.val.val 1 1,
      X.val.val 0 1, X.val.val 1 2, X.val.val 0 2, X.val.val 0 3,
      X.val.val 1 0, X.val.val 2 1, -X.val.val 2 0, X.val.val 3 0] :=
  (rfl)

/-- The inverse coordinate map is the literal fixed-matrix reconstruction. -/
@[simp]
theorem coordinates_symm_apply_val (c : Fin 10 → R) :
    ((coordinates R).symm c).val.val =
      !![c 0, c 2, c 4, c 5;
         c 6, -c 0 + c 1, c 3, -c 4;
         -c 8, c 7, c 0 - c 1, c 2;
         c 9, c 8, c 6, -c 0] :=
  (rfl)

/-- The two Cartan orbit sums followed by the four positive and four negative root vectors. -/
noncomputable def basis : Module.Basis (Fin 10) R (Fixed R) :=
  Module.Basis.ofEquivFun (coordinates R)

/-- Basis coordinates are the independent fixed-matrix coordinates. -/
@[simp]
theorem basis_repr (X : Fixed R) (i : Fin 10) :
    (basis R).repr X i = coordinates R X i :=
  Module.Basis.ofEquivFun_repr_apply (coordinates R) X i

/-- Each basis matrix is obtained by setting its corresponding independent coordinate to one. -/
theorem basis_apply_val (i : Fin 10) :
    (basis R i).val.val =
      let c : Fin 10 → R := Pi.single i 1
      !![c 0, c 2, c 4, c 5;
         c 6, -c 0 + c 1, c 3, -c 4;
         -c 8, c 7, c 0 - c 1, c 2;
         c 9, c 8, c 6, -c 0] := by
  rw [basis, Module.Basis.coe_ofEquivFun]
  exact coordinates_symm_apply_val R _

/-- The outer simple-coroot orbit sum is `H₀ + H₂`. -/
@[simp]
theorem basis_zero_val :
    (basis R 0).val.val =
      Matrix.single 0 0 1 - Matrix.single 1 1 1 +
        Matrix.single 2 2 1 - Matrix.single 3 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The middle simple coroot is `H₁`. -/
@[simp]
theorem basis_one_val :
    (basis R 1).val.val = Matrix.single 1 1 1 - Matrix.single 2 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The paired simple positive root vector is `E₀₁ + E₂₃`. -/
@[simp]
theorem basis_two_val :
    (basis R 2).val.val = Matrix.single 0 1 1 + Matrix.single 2 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The middle simple positive root vector is `E₁₂`. -/
@[simp]
theorem basis_three_val : (basis R 3).val.val = Matrix.single 1 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The height-two positive root vector is `E₀₂ - E₁₃`. -/
@[simp]
theorem basis_four_val :
    (basis R 4).val.val = Matrix.single 0 2 1 - Matrix.single 1 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The highest positive root vector is `E₀₃`. -/
@[simp]
theorem basis_five_val : (basis R 5).val.val = Matrix.single 0 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The paired simple negative root vector is `E₁₀ + E₃₂`. -/
@[simp]
theorem basis_six_val :
    (basis R 6).val.val = Matrix.single 1 0 1 + Matrix.single 3 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The middle simple negative root vector is `E₂₁`. -/
@[simp]
theorem basis_seven_val : (basis R 7).val.val = Matrix.single 2 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The height-two negative root vector is `-E₂₀ + E₃₁`. -/
@[simp]
theorem basis_eight_val :
    (basis R 8).val.val = -Matrix.single 2 0 1 + Matrix.single 3 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

/-- The lowest negative root vector is `E₃₀`. -/
@[simp]
theorem basis_nine_val : (basis R 9).val.val = Matrix.single 3 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis_apply_val]

-- All bracket identities reduce to the same sixteen entry calculations in sl₄.
local macro "fixed_matrix_bracket" : tactic =>
  `(tactic| (apply Fixed.ext _
             intro i j
             fin_cases i <;> fin_cases j <;>
               simp [LieSubalgebra.coe_bracket, Ring.lie_def, basis_apply_val] <;> ring))

/-- The bracket of the paired simple positive root and the middle root. -/
@[simp]
theorem lie_basis_two_three : ⁅basis R 2, basis R 3⁆ = basis R 4 := by
  fixed_matrix_bracket

/-- The highest root vector occurs with the integral root-string coefficient `-2`. -/
@[simp]
theorem lie_basis_two_four : ⁅basis R 2, basis R 4⁆ = (-2 : R) • basis R 5 := by
  fixed_matrix_bracket

/-- The bracket of the paired simple negative root and the middle negative root. -/
@[simp]
theorem lie_basis_six_seven : ⁅basis R 6, basis R 7⁆ = basis R 8 := by
  fixed_matrix_bracket

/-- The lowest root vector has the same integral root-string coefficient `-2`. -/
@[simp]
theorem lie_basis_six_eight : ⁅basis R 6, basis R 8⁆ = (-2 : R) • basis R 9 := by
  fixed_matrix_bracket

/-- The paired positive and negative simple roots produce the outer Cartan orbit sum. -/
@[simp]
theorem lie_basis_two_six : ⁅basis R 2, basis R 6⁆ = basis R 0 := by
  fixed_matrix_bracket

/-- The middle positive and negative simple roots produce the middle coroot. -/
@[simp]
theorem lie_basis_three_seven : ⁅basis R 3, basis R 7⁆ = basis R 1 := by
  fixed_matrix_bracket

/-- Simple positive and negative root vectors from different orbits commute. -/
@[simp]
theorem lie_basis_two_seven : ⁅basis R 2, basis R 7⁆ = 0 := by
  fixed_matrix_bracket

/-- The middle positive root commutes with the paired simple negative root. -/
@[simp]
theorem lie_basis_three_six : ⁅basis R 3, basis R 6⁆ = 0 := by
  fixed_matrix_bracket

/-- The two simple-coroot orbit sums commute. -/
@[simp]
theorem lie_basis_zero_one : ⁅basis R 0, basis R 1⁆ = 0 := by
  fixed_matrix_bracket

/-- The outer coroot orbit sum acts on its simple positive root with weight two. -/
@[simp]
theorem lie_basis_zero_two : ⁅basis R 0, basis R 2⁆ = (2 : R) • basis R 2 := by
  fixed_matrix_bracket

/-- The outer coroot orbit sum acts on the middle positive root with weight minus two. -/
@[simp]
theorem lie_basis_zero_three : ⁅basis R 0, basis R 3⁆ = (-2 : R) • basis R 3 := by
  fixed_matrix_bracket

/-- The outer coroot orbit sum acts on its simple negative root with weight minus two. -/
@[simp]
theorem lie_basis_zero_six : ⁅basis R 0, basis R 6⁆ = (-2 : R) • basis R 6 := by
  fixed_matrix_bracket

/-- The outer coroot orbit sum acts on the middle negative root with weight two. -/
@[simp]
theorem lie_basis_zero_seven : ⁅basis R 0, basis R 7⁆ = (2 : R) • basis R 7 := by
  fixed_matrix_bracket

/-- The middle coroot acts on the paired simple positive root with weight minus one. -/
@[simp]
theorem lie_basis_one_two : ⁅basis R 1, basis R 2⁆ = -basis R 2 := by
  fixed_matrix_bracket

/-- The middle coroot acts on its simple positive root with weight two. -/
@[simp]
theorem lie_basis_one_three : ⁅basis R 1, basis R 3⁆ = (2 : R) • basis R 3 := by
  fixed_matrix_bracket

/-- The middle coroot acts on the paired simple negative root with weight one. -/
@[simp]
theorem lie_basis_one_six : ⁅basis R 1, basis R 6⁆ = basis R 6 := by
  fixed_matrix_bracket

/-- The middle coroot acts on its simple negative root with weight minus two. -/
@[simp]
theorem lie_basis_one_seven : ⁅basis R 1, basis R 7⁆ = (-2 : R) • basis R 7 := by
  fixed_matrix_bracket

/-- When two is invertible, the folded positive and negative simple root vectors
`E₀₁ + E₂₃`, `E₁₂`, `E₁₀ + E₃₂`, `E₂₁` generate the actual fixed Lie algebra. -/
theorem lieSpan_simple_eq_top [Invertible (2 : R)] :
    LieSubalgebra.lieSpan R (Fixed R) {basis R 2, basis R 3, basis R 6, basis R 7} = ⊤ := by
  let S := LieSubalgebra.lieSpan R (Fixed R) {basis R 2, basis R 3, basis R 6, basis R 7}
  have h2 : basis R 2 ∈ S := LieSubalgebra.subset_lieSpan (by simp)
  have h3 : basis R 3 ∈ S := LieSubalgebra.subset_lieSpan (by simp)
  have h6 : basis R 6 ∈ S := LieSubalgebra.subset_lieSpan (by simp)
  have h7 : basis R 7 ∈ S := LieSubalgebra.subset_lieSpan (by simp)
  have h4 : basis R 4 ∈ S := by simpa using S.lie_mem h2 h3
  have h8 : basis R 8 ∈ S := by simpa using S.lie_mem h6 h7
  have h5 : basis R 5 ∈ S := by
    have h := S.smul_mem (-⅟ (2 : R)) (S.lie_mem h2 h4)
    simpa [smul_smul] using h
  have h9 : basis R 9 ∈ S := by
    have h := S.smul_mem (-⅟ (2 : R)) (S.lie_mem h6 h8)
    simpa [smul_smul] using h
  have hb : ∀ i, basis R i ∈ S := by
    intro i
    fin_cases i
    · simpa using S.lie_mem h2 h6
    · simpa using S.lie_mem h3 h7
    all_goals assumption
  apply top_unique
  intro X _
  rw [← (basis R).sum_repr X]
  exact S.sum_mem fun i _ ↦ S.smul_mem _ (hb i)

end TauCeti.TypeAThreeFixed
