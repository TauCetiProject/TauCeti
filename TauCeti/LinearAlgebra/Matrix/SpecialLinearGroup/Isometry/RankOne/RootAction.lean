/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Points
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Unitary.Basic

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
  (MulEquiv.subgroupCongr (by rw [coe_typeAGraphConjugator_two])).toMonoidHom.comp
    ((HeisenbergGroup.toSpecialLinear.subgroupComap
      (Matrix.specialIsometryGroup !![0, 0, 1; 0, -1, 0; 1, 0, 0] σ)).comp
        (MulEquiv.subgroupCongr (HeisenbergGroup.unitarySubgroup_eq_comap σ)).toMonoidHom)

/-- The upper root embedding retains its Heisenberg matrix. -/
@[simp]
theorem coe_upperRootHom (a : HeisenbergGroup.unitarySubgroup σ) :
    (upperRootHom K σ a : SpecialLinearGroup (Fin 3) K) =
      HeisenbergGroup.toSpecialLinear a := by
  simp only [upperRootHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_apply]
  exact MonoidHom.subgroupComap_apply_coe _ _ _

variable (K σ) in
/-- The upper root embedding is faithful. -/
theorem upperRootHom_injective : Function.Injective (upperRootHom K σ) := by
  intro a b h
  apply Subtype.ext
  apply HeisenbergGroup.toSpecialLinear_injective
  simpa only [coe_upperRootHom] using congrArg Subtype.val h

/-- An isometry belongs to the upper root group exactly when its matrix is upper
unitriangular. -/
theorem mem_range_upperRootHom_iff
    (g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) :
    g ∈ (upperRootHom K σ).range ↔
      ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsUpperUnitriangular := by
  rw [← HeisenbergGroup.mem_range_toSpecialLinear_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (coe_upperRootHom a).symm⟩
  · rintro ⟨a, ha⟩
    have ha' : a ∈ HeisenbergGroup.unitarySubgroup σ := by
      rw [HeisenbergGroup.unitarySubgroup_eq_comap, Subgroup.mem_comap, ha]
      simpa only [coe_typeAGraphConjugator_two] using g.property
    exact ⟨⟨a, ha'⟩, Subtype.ext ((coe_upperRootHom ⟨a, ha'⟩).trans ha)⟩

/-- The upper root matrix acts on vectors by its three coordinate formulas. -/
theorem upperRootHom_smul_vec (a : HeisenbergGroup.unitarySubgroup σ) (v : Fin 3 → K) :
    upperRootHom K σ a • v =
      ![v 0 + (a : HeisenbergGroup K).x * v 1 + (a : HeisenbergGroup K).z * v 2,
        v 1 + σ (a : HeisenbergGroup K).x * v 2, v 2] := by
  rw [Subgroup.smul_def, coe_upperRootHom, Matrix.SpecialLinearGroup.smul_def,
    smul_eq_mulVec, HeisenbergGroup.coe_toSpecialLinear, HeisenbergGroup.toMatrix_mulVec,
    HeisenbergGroup.unitarySubgroup.y_eq]

end Ring

variable {K : Type*} [Field K] {σ : K →+* K}

private theorem coe_upperRootHom_smul_mk (a : HeisenbergGroup.unitarySubgroup σ)
    (p : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ)
    {v : Fin 3 → K} {hv : v ≠ 0} (hp : (p : ℙ K (Fin 3 → K)) = Projectivization.mk K v hv) :
    ((upperRootHom K σ a • p : _) : ℙ K (Fin 3 → K)) =
      Projectivization.mk K (upperRootHom K σ a • v)
        ((smul_ne_zero_iff_ne _).mpr hv) := by
  simp only [SubMulAction.val_smul, Subgroup.smul_def, hp, Projectivization.smul_mk]

/-- Every upper root element fixes the point at infinity. -/
@[simp]
theorem upperRootHom_smul_infinity (a : HeisenbergGroup.unitarySubgroup σ) :
    upperRootHom K σ a • infinity K σ = infinity K σ := by
  apply Subtype.ext
  rw [coe_upperRootHom_smul_mk a _ (coe_infinity K σ), coe_infinity]
  congr 1
  simp [upperRootHom_smul_vec]

/-- The action on an affine point is given by multiplication by the upper root matrix. -/
@[simp]
theorem upperRootHom_smul_point (a : HeisenbergGroup.unitarySubgroup σ)
    (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    upperRootHom K σ a • point K σ c =
      point K σ ⟨((a : HeisenbergGroup K).z + c.val.1 +
          (a : HeisenbergGroup K).x * c.val.2,
        σ (a : HeisenbergGroup K).x + c.val.2), by
          simp only [map_add, map_mul, HeisenbergGroup.unitarySubgroup.map_map_x]
          linear_combination HeisenbergGroup.unitarySubgroup.z_add_map_z a + c.property⟩ := by
  apply Subtype.ext
  rw [coe_upperRootHom_smul_mk a _ (coe_point c), coe_point]
  congr 1
  rw [upperRootHom_smul_vec]
  ext i
  fin_cases i <;> simp <;> ring

/-- The orbit of `[0 : 0 : 1]` records the two free root parameters. -/
theorem upperRootHom_smul_origin (a : HeisenbergGroup.unitarySubgroup σ) :
    upperRootHom K σ a • origin K σ =
      point K σ ⟨((a : HeisenbergGroup K).z, σ (a : HeisenbergGroup K).x), by
        simpa using HeisenbergGroup.unitarySubgroup.z_add_map_z a⟩ := by
  rw [origin_eq_point, upperRootHom_smul_point]
  congr 1; simp

/-- Away from infinity no nonidentity upper root element fixes a point. -/
@[simp]
theorem upperRootHom_smul_eq_self_iff (a : HeisenbergGroup.unitarySubgroup σ)
    (p : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ)
    (hp : p ≠ infinity K σ) : upperRootHom K σ a • p = p ↔ a = 1 := by
  constructor
  · intro ha
    obtain ⟨c, rfl⟩ := exists_point hp
    rw [upperRootHom_smul_point, point_inj] at ha
    have hx : (a : HeisenbergGroup K).x = 0 := (map_eq_zero σ).mp (by
      simpa using congrArg (fun c ↦ c.val.2) ha)
    have hz : (a : HeisenbergGroup K).z = 0 := by
      simpa [hx] using congrArg (fun c ↦ c.val.1) ha
    apply HeisenbergGroup.unitarySubgroup.ext
    · simpa using hx
    · simpa using hz
  · rintro rfl
    simp

variable (hσ : Function.Involutive σ)

include hσ

/-- Every affine isotropic point is the image of `[0 : 0 : 1]` under a unique upper
root element. -/
theorem existsUnique_upperRootHom_smul_origin (p :
    (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ)
    (hp : p ≠ infinity K σ) :
    ∃! a : HeisenbergGroup.unitarySubgroup σ,
      upperRootHom K σ a • origin K σ = p := by
  obtain ⟨c, rfl⟩ := exists_point hp
  let a := HeisenbergGroup.unitaryMk σ hσ (σ c.val.2) c.val.1 (by
    simpa [hσ _] using c.property)
  have ha : upperRootHom K σ a • origin K σ = point K σ c := by
    rw [upperRootHom_smul_origin]
    apply point_inj.mpr
    apply Subtype.ext
    simp [a, hσ _]
  refine ⟨a, ha, ?_⟩
  intro b hb
  rw [upperRootHom_smul_origin, point_inj] at hb
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
  obtain ⟨b, hb, _⟩ := existsUnique_upperRootHom_smul_origin hσ p hp
  obtain ⟨c, hc, hc_unique⟩ := existsUnique_upperRootHom_smul_origin hσ q hq
  refine ⟨c * b⁻¹, ?_, ?_⟩
  · simpa only [map_mul, map_inv, mul_smul, ← hb, inv_smul_smul] using hc
  · intro a ha
    have hab : a * b = c := hc_unique _ (by simpa only [map_mul, mul_smul, hb] using ha)
    exact eq_mul_inv_iff_mul_eq.mpr hab

end TauCeti.UnitaryRankOne
