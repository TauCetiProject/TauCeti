/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Points
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Unitary

/-!
# The upper root group on the rank-one unitary points

The upper unitriangular unitary group fixes infinity and acts sharply transitively on
its complement in the isotropic points of the three-dimensional signed reversal form.
The orbit coordinates are the actual last column of the root matrix, not an arbitrarily
chosen bijection. This is the affine-orbit input to uniqueness of unipotent coordinates
in the rank-one Bruhat decomposition.
The results hold over any field with an involution, including characteristic two.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti.UnitaryRankOne

section Ring

variable {K : Type*} [CommRing K] {σ : K →+* K}

variable (K σ) in
/-- The upper unitriangular root embedding into the special isometries of the signed
reversal form. -/
def upperRootHom : HeisenbergGroup.unitarySubgroup σ →*
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ :=
  (HeisenbergGroup.toSpecialLinear.comp (HeisenbergGroup.unitarySubgroup σ).subtype).codRestrict
    _ fun a ↦ by
      rw [coe_typeAGraphConjugator_two, Matrix.mem_specialIsometryGroup_iff]
      simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype,
        HeisenbergGroup.coe_toSpecialLinear] using
          HeisenbergGroup.mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq.mp a.property

/-- The upper root embedding retains its Heisenberg matrix. -/
@[simp]
theorem coe_upperRootHom (a : HeisenbergGroup.unitarySubgroup σ) :
    (upperRootHom K σ a : SpecialLinearGroup (Fin 3) K) =
      HeisenbergGroup.toSpecialLinear a := (rfl)

variable (K σ) in
/-- The upper root embedding is faithful. -/
theorem upperRootHom_injective : Function.Injective (upperRootHom K σ) := by
  intro a b h
  exact Subtype.ext (HeisenbergGroup.toSpecialLinear_injective (congrArg Subtype.val h))

end Ring

variable {K : Type*} [Field K] {σ : K →+* K}

/-- Every upper root element fixes the point at infinity. -/
@[simp]
theorem upperRootHom_smul_infinity (a : HeisenbergGroup.unitarySubgroup σ) :
    upperRootHom K σ a • infinity K σ = infinity K σ := by
  apply Subtype.ext
  rw [SubMulAction.val_smul, Subgroup.smul_def, coe_infinity, Projectivization.smul_mk]
  congr 1
  rw [coe_upperRootHom, Matrix.SpecialLinearGroup.smul_def, smul_eq_mulVec,
    HeisenbergGroup.coe_toSpecialLinear, HeisenbergGroup.toMatrix_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

variable (hσ : Function.Involutive σ)

/-- The action on an affine point is given by multiplication by the upper root matrix. -/
theorem upperRootHom_smul_point (a : HeisenbergGroup.unitarySubgroup σ)
    (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    upperRootHom K σ a • point K σ c =
      point K σ ⟨((a : HeisenbergGroup K).z + c.1.1 +
          (a : HeisenbergGroup K).x * c.1.2,
        σ (a : HeisenbergGroup K).x + c.1.2), by
          simp only [map_add, map_mul, hσ _]
          linear_combination HeisenbergGroup.unitarySubgroup.z_add_map_z a + c.2⟩ := by
  apply Subtype.ext
  rw [SubMulAction.val_smul, Subgroup.smul_def, coe_point, Projectivization.smul_mk,
    coe_point]
  congr 1
  rw [coe_upperRootHom, Matrix.SpecialLinearGroup.smul_def, smul_eq_mulVec,
    HeisenbergGroup.coe_toSpecialLinear, HeisenbergGroup.toMatrix_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The orbit of `[0 : 0 : 1]` records the two free root parameters. -/
theorem upperRootHom_smul_zero (a : HeisenbergGroup.unitarySubgroup σ) :
    upperRootHom K σ a • point K σ ⟨(0, 0), by simp⟩ =
      point K σ ⟨((a : HeisenbergGroup K).z, σ (a : HeisenbergGroup K).x), by
        simpa [hσ _, mul_comm] using HeisenbergGroup.unitarySubgroup.z_add_map_z a⟩ := by
  rw [upperRootHom_smul_point hσ]
  congr 1; simp

include hσ

/-- Every affine isotropic point is the image of `[0 : 0 : 1]` under a unique upper
root element. -/
theorem existsUnique_upperRootHom_smul_zero (p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ)
    (hp : p ≠ infinity K σ) :
    ∃! a : HeisenbergGroup.unitarySubgroup σ,
      upperRootHom K σ a • point K σ ⟨(0, 0), by simp⟩ = p := by
  obtain ⟨c, rfl⟩ := exists_point hp
  let a := HeisenbergGroup.unitaryMk σ hσ (σ c.1.2) c.1.1 (by
    simpa [hσ _] using c.2)
  have ha : upperRootHom K σ a • point K σ ⟨(0, 0), by simp⟩ = point K σ c := by
    rw [upperRootHom_smul_zero hσ]
    apply point_inj.mpr
    apply Subtype.ext
    simp [a, hσ _]
  refine ⟨a, ha, ?_⟩
  intro b hb
  rw [upperRootHom_smul_zero hσ, point_inj] at hb
  have hz := congrArg (fun c ↦ c.val.1) hb
  have hx := congrArg (fun c ↦ c.val.2) hb
  apply HeisenbergGroup.unitarySubgroup.ext
  · simpa [a, hσ _] using congrArg σ hx
  · simpa [a] using hz

/-- The upper root group acts sharply transitively on the complement of infinity. -/
theorem existsUnique_upperRootHom_smul_eq (p q :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ)
    (hp : p ≠ infinity K σ) (hq : q ≠ infinity K σ) :
    ∃! a : HeisenbergGroup.unitarySubgroup σ, upperRootHom K σ a • p = q := by
  obtain ⟨b, hb, _⟩ := existsUnique_upperRootHom_smul_zero hσ p hp
  obtain ⟨c, hc, hc_unique⟩ := existsUnique_upperRootHom_smul_zero hσ q hq
  refine ⟨c * b⁻¹, ?_, ?_⟩
  · simpa only [map_mul, map_inv, mul_smul, ← hb, inv_smul_smul] using hc
  · intro a ha
    have hab : a * b = c := hc_unique _ (by simpa only [map_mul, mul_smul, hb] using ha)
    exact eq_mul_inv_iff_mul_eq.mpr hab

/-- Away from infinity no nonidentity upper root element fixes a point. -/
@[simp]
theorem upperRootHom_smul_eq_self_iff (a : HeisenbergGroup.unitarySubgroup σ)
    (p : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ)
    (hp : p ≠ infinity K σ) : upperRootHom K σ a • p = p ↔ a = 1 := by
  constructor
  · intro ha
    obtain ⟨b, _, hb⟩ := existsUnique_upperRootHom_smul_eq hσ p p hp hp
    exact (hb a ha).trans (hb 1 (by simp)).symm
  · rintro rfl
    simp

end TauCeti.UnitaryRankOne
