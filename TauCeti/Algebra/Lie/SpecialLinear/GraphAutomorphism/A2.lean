/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.Lie.Subalgebra.Fixed
public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# The integral fixed lattice of the type-A₂ graph involution

The pinned involution of `sl₃` has fixed matrices
`[[h,e,0],[f,0,e],[0,f,-h]]` when two is regular in the coefficient ring.
Their integral basis satisfies `[e,f]=h`, `[h,e]=e`, `[h,f]=-f`.
Consequently the normalized A₁ frame `E=e, F=2f, H=2h` spans an index-four
sublattice, not the whole integral fixed lattice. This distinguishes taking integral
fixed points from choosing a normalized folded Chevalley lattice.

The involution is the existing signed-reversal construction
`TauCeti.typeASpecialLinearGraphAutomorphism`; the index calculation uses
`LinearMap.index_range_eq_natAbs_det_toMatrix`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, §7.9 (folding and normalization).
-/

public section

namespace TauCeti.TypeA2Fixed

open Matrix LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (A : Type*) [CommRing A]

/-- The fixed Lie algebra of the pinned reversal of `sl₃`. -/
abbrev fixedAlgebra := (typeASpecialLinearGraphAutomorphism 2 A).toLieHom.fixedSubalgebra

private def matrixCoordinates : (Fin 3 → A) →ₗ[A] Matrix (Fin 3) (Fin 3) A where
  toFun v := !![v 2, v 0, 0; v 1, 0, v 0; 0, v 1, -v 2]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' a v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The fixed matrix with raising, lowering and Cartan coordinates `v 0`, `v 1`, `v 2`. -/
def ofCoordinates : (Fin 3 → A) →ₗ[A] fixedAlgebra A where
  toFun v := ⟨⟨matrixCoordinates A v, by
    simp [matrixCoordinates, sl, Matrix.trace, Fin.sum_univ_succ]⟩, by
    apply LieHom.mem_fixedSubalgebra.mpr
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixCoordinates, coe_typeASpecialLinearGraphAutomorphism,
        typeAGraphLieEquiv_apply_apply]⟩
  map_add' v w := Subtype.ext (Subtype.ext ((matrixCoordinates A).map_add v w))
  map_smul' a v := Subtype.ext (Subtype.ext ((matrixCoordinates A).map_smul a v))

/-- The underlying matrix of the coordinate parameterization. -/
@[simp] theorem ofCoordinates_val (v : Fin 3 → A) :
    (ofCoordinates A v).val.val =
      !![v 2, v 0, 0; v 1, 0, v 0; 0, v 1, -v 2] := (rfl)

/-- When two is regular, every fixed matrix has the displayed three-coordinate form. -/
@[simp] theorem ofCoordinates_entries (h2 : IsRegular (2 : A)) (X : fixedAlgebra A) :
    ofCoordinates A ![X.val.val 0 1, X.val.val 1 0, X.val.val 0 0] = X := by
  have hx : typeAGraphLieEquiv 2 A X.val.val = X.val.val := by
    simpa [-LieHom.apply_coe_fixedSubalgebra] using congrArg (fun Z : sl (Fin 3) A ↦ Z.val)
      (LieHom.mem_fixedSubalgebra.mp X.property)
  have hentry (i j : Fin 3) := congrFun (congrFun hx i) j
  simp only [typeAGraphLieEquiv_apply_apply] at hentry
  have h02 : X.val.val 0 2 = 0 := by
    apply h2.left
    simpa [two_mul] using (eq_neg_iff_add_eq_zero.mp (hentry 0 2).symm)
  have h20 : X.val.val 2 0 = 0 := by
    apply h2.left
    simpa [two_mul] using (eq_neg_iff_add_eq_zero.mp (hentry 2 0).symm)
  have h11 : X.val.val 1 1 = 0 := by
    apply h2.left
    simpa [two_mul] using (eq_neg_iff_add_eq_zero.mp (hentry 1 1).symm)
  have h12 := hentry 1 2
  have h21 := hentry 2 1
  have h22 := hentry 2 2
  apply Subtype.ext; apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all

/-- Coordinates on the fixed algebra, with inverse the explicit matrix parameterization. -/
def coordinates (h2 : IsRegular (2 : A)) : fixedAlgebra A ≃ₗ[A] (Fin 3 → A) where
  toFun X := ![X.val.val 0 1, X.val.val 1 0, X.val.val 0 0]
  invFun := ofCoordinates A
  left_inv := ofCoordinates_entries A h2
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' X Y := by ext i; fin_cases i <;> rfl
  map_smul' a X := by ext i; fin_cases i <;> rfl

/-- The coordinates are the entries `X₀₁`, `X₁₀`, `X₀₀`, in that order. -/
@[simp] theorem coordinates_apply (h2 : IsRegular (2 : A)) (X : fixedAlgebra A) :
    coordinates A h2 X = ![X.val.val 0 1, X.val.val 1 0, X.val.val 0 0] := (rfl)

/-- The inverse coordinate map gives the explicit fixed matrix. -/
@[simp] theorem coordinates_symm_apply (h2 : IsRegular (2 : A)) (v : Fin 3 → A) :
    (coordinates A h2).symm v = ofCoordinates A v := (rfl)

/-- The fixed basis, ordered as raising vector `e`, lowering vector `f`, Cartan vector `h`. -/
noncomputable def fixedBasis (h2 : IsRegular (2 : A)) :
    Module.Basis (Fin 3) A (fixedAlgebra A) :=
  (Pi.basisFun A (Fin 3)).map (coordinates A h2).symm

/-- The fixed basis vectors are the matrices obtained from the coordinate unit vectors. -/
theorem fixedBasis_apply (h2 : IsRegular (2 : A)) (i : Fin 3) :
    fixedBasis A h2 i = ofCoordinates A (Pi.single i 1) := by
  simp [fixedBasis]

/-- The basis coefficients are the three matrix-entry coordinates. -/
@[simp] theorem fixedBasis_repr (h2 : IsRegular (2 : A)) (X : fixedAlgebra A) (i : Fin 3) :
    (fixedBasis A h2).repr X i = coordinates A h2 X i := by
  simp [fixedBasis, Module.Basis.map_repr]

/-- Brackets in fixed coordinates: the unnormalized Cartan acts with weights `1,-1`. -/
theorem lie_ofCoordinates (v w : Fin 3 → A) :
    ⁅ofCoordinates A v, ofCoordinates A w⁆ =
      ofCoordinates A ![v 2 * w 0 - v 0 * w 2,
        v 1 * w 2 - v 2 * w 1, v 0 * w 1 - v 1 * w 0] := by
  apply Subtype.ext; apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LieSubalgebra.coe_bracket, Ring.lie_def] <;> ring

/-- In the integral fixed basis, `[e,f]=h`. -/
@[simp] theorem lie_fixedBasis_zero_one (h2 : IsRegular (2 : A)) :
    ⁅fixedBasis A h2 0, fixedBasis A h2 1⁆ = fixedBasis A h2 2 := by
  simp only [fixedBasis_apply, lie_ofCoordinates]
  congr 1
  ext i
  fin_cases i <;> simp

/-- In the integral fixed basis, `[h,e]=e`, not `2e`. -/
@[simp] theorem lie_fixedBasis_two_zero (h2 : IsRegular (2 : A)) :
    ⁅fixedBasis A h2 2, fixedBasis A h2 0⁆ = fixedBasis A h2 0 := by
  simp only [fixedBasis_apply, lie_ofCoordinates]
  congr 1
  ext i
  fin_cases i <;> simp

/-- In the integral fixed basis, `[h,f]=-f`, not `-2f`. -/
@[simp] theorem lie_fixedBasis_two_one (h2 : IsRegular (2 : A)) :
    ⁅fixedBasis A h2 2, fixedBasis A h2 1⁆ = -fixedBasis A h2 1 := by
  simp only [fixedBasis_apply, lie_ofCoordinates, ← map_neg]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Rescaling the lowering and Cartan vectors gives the normalized A₁ triple. -/
theorem isSl2Triple_normalized [Nontrivial A] (h2 : IsRegular (2 : A)) :
    IsSl2Triple ((2 : A) • fixedBasis A h2 2) (fixedBasis A h2 0)
      ((2 : A) • fixedBasis A h2 1) where
  h_ne_zero := by
    intro hh
    have hz := congrArg (fun X : fixedAlgebra A ↦ X.val.val 0 0) hh
    have hz' : (2 : A) = 0 := by simpa [fixedBasis_apply] using hz
    exact one_ne_zero (h2.left (by simp [hz']))
  lie_e_f := by rw [lie_smul, lie_fixedBasis_zero_one]
  lie_h_e_nsmul := by
    rw [smul_lie, lie_fixedBasis_two_zero]
    simp only [two_smul]
  lie_h_f_nsmul := by
    rw [smul_lie, lie_smul, lie_fixedBasis_two_one]
    simp only [two_smul, neg_add_rev, smul_neg]

/-- The integral lattice spanned by the normalized frame `E=e`, `F=2f`, `H=2h`. -/
noncomputable def normalizedLattice : Submodule ℤ (fixedAlgebra ℤ) :=
  Submodule.span ℤ (Set.range fun i : Fin 3 ↦
    (![1, 2, 2] i : ℤ) • fixedBasis ℤ (IsRegular.of_ne_zero (by norm_num)) i)

/-- Membership in the normalized lattice means the lowering and Cartan coordinates are even. -/
@[simp] theorem mem_normalizedLattice_iff (X : fixedAlgebra ℤ) :
    X ∈ normalizedLattice ↔ 2 ∣ X.val.val 1 0 ∧ 2 ∣ X.val.val 0 0 := by
  let h2 : IsRegular (2 : ℤ) := IsRegular.of_ne_zero (by norm_num)
  rw [normalizedLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    have hc' := congrArg (coordinates ℤ h2) hc
    have h1 := congrFun hc' 1
    have h2' := congrFun hc' 2
    simp [Fin.sum_univ_succ, fixedBasis_apply] at h1 h2'
    exact ⟨⟨c 1, by omega⟩, ⟨c 2, by omega⟩⟩
  · rintro ⟨⟨f, hf⟩, ⟨h, hh⟩⟩
    refine ⟨![X.val.val 0 1, f, h], ?_⟩
    apply (coordinates ℤ h2).injective
    ext i
    fin_cases i <;> simp [Fin.sum_univ_succ, fixedBasis_apply, hf, hh] <;> omega

/-- The normalized folded lattice has index four in the full integral fixed lattice. -/
theorem normalizedLattice_index : normalizedLattice.toAddSubgroup.index = 4 := by
  let h2 : IsRegular (2 : ℤ) := IsRegular.of_ne_zero (by norm_num)
  let b := fixedBasis ℤ h2
  let f := b.constr ℤ (fun i ↦ (![1, 2, 2] i : ℤ) • b i)
  have hf : Function.Injective f := by
    apply b.injective_constr_of_linearIndependent
    exact b.linearIndependent.smul_of_isRightRegular (fun i ↦ by
      apply (IsRegular.of_ne_zero ?_).right
      fin_cases i <;> norm_num)
  have hrange : LinearMap.range f = normalizedLattice := by
    rw [Module.Basis.constr_range]
    rfl
  rw [← hrange, LinearMap.index_range_eq_natAbs_det_toMatrix b b hf]
  have hm : LinearMap.toMatrix b b f = Matrix.diagonal (![1, 2, 2] : Fin 3 → ℤ) := by
    ext i j
    simp [f, LinearMap.toMatrix_apply, Matrix.diagonal_apply, Finsupp.single_apply,
      eq_comm]
    split_ifs with h <;> simp_all
  rw [hm]
  norm_num [Matrix.det_diagonal, Fin.prod_univ_succ]

end TauCeti.TypeA2Fixed
