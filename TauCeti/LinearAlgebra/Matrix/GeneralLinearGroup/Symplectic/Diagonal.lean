/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi

/-!
# The diagonal torus in the symplectic group

For a family of units `t : Fin m → Rˣ`, the block-diagonal matrix

```text
diag(t₀, …, tₘ₋₁, t₀⁻¹, …, tₘ₋₁⁻¹)
```

preserves the standard alternating form. This file packages these matrices as the homomorphism
`TauCeti.GLSymplecticFin.diagonal` into `Sp₂ₘ(R)` and computes conjugation on every standard
symplectic root subgroup.

The five root characters are `tᵢ²`, `tᵢ⁻²`, `tᵢtⱼ⁻¹`, `tᵢtⱼ`, and
`(tᵢtⱼ)⁻¹` for the roots `2eᵢ`, `-2eᵢ`, `eᵢ-eⱼ`, `eᵢ+eⱼ`, and
`-eᵢ-eⱼ`, respectively. The uniform theorem
`TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv` records the corresponding pinning
equation.

## Main declarations

* `TauCeti.GLSymplecticFin.diagonal`: the diagonal split-torus homomorphism into the symplectic
  matrix group.
* `TauCeti.GLSymplecticFin.RootSubgroupIndex.character`: the character of the diagonal torus
  belonging to a root.
* `TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv`: conjugation scales a root parameter
  by its root character.

## References

* J. S. Milne, *Algebraic Groups* (2017), §23 and §24.6.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.

These conjugation calculations supply the root-action equations used in the standard type-`C`
pinning.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

universe u

variable {m : ℕ} {R : Type u}

section Coordinates

variable [Monoid R]

/-- The diagonal entries of a standard symplectic torus element in `Fin (m + m)` coordinates:
`t i` on the first block and `(t i)⁻¹` on the second. -/
def diagonalCoordinates (t : Fin m → Rˣ) (k : Fin (m + m)) : Rˣ :=
  Sum.elim t (fun i ↦ (t i)⁻¹) (finSumFinEquiv.symm k)

@[simp]
theorem diagonalCoordinates_castAdd (t : Fin m → Rˣ) (i : Fin m) :
    diagonalCoordinates t (Fin.castAdd m i) = t i := by
  rw [← finSumFinEquiv_apply_left, diagonalCoordinates, Equiv.symm_apply_apply]
  rfl

@[simp]
theorem diagonalCoordinates_addNat (t : Fin m → Rˣ) (i : Fin m) :
    diagonalCoordinates t (i.addNat m) = (t i)⁻¹ := by
  rw [← Fin.natAdd_eq_addNat, ← finSumFinEquiv_apply_right, diagonalCoordinates,
    Equiv.symm_apply_apply]
  rfl

end Coordinates

section Matrix

variable [CommRing R]

private theorem finSumFinEquiv_symm_addNat (i : Fin m) :
    finSumFinEquiv.symm (i.addNat m) = Sum.inr i := by
  rw [← Fin.natAdd_eq_addNat, finSumFinEquiv_symm_apply_natAdd]

private theorem diagGL_inv (t : Fin m → Rˣ) :
    (diagGL t)⁻¹ = diagGL (fun i ↦ (t i)⁻¹) := by
  rw [← map_inv]
  apply congrArg diagGL
  funext i
  rfl

/-- **The diagonal split torus in the standard symplectic matrix group.** It sends `t` to the
diagonal matrix with entries `t i` on the first block and `(t i)⁻¹` on the second. -/
noncomputable def diagonal : (Fin m → Rˣ) →* GLSymplecticFin m R :=
  leviHom.comp diagGL

/-- The underlying general-linear matrix of a symplectic diagonal element. -/
@[simp]
theorem coe_diagonal (t : Fin m → Rˣ) :
    ((diagonal t : GLSymplecticFin m R) : GL (Fin (m + m)) R) =
      diagGL (diagonalCoordinates t) := by
  rw [diagonal, MonoidHom.comp_apply]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_leviHom]
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · simp [diagGL_apply, Matrix.diagonal_apply, finSumFinEquiv_symm_apply_castAdd]
    · have h : Fin.castAdd m i ≠ j.addNat m := by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using finSumFinEquiv_inl_ne_inr i j
      simp [diagGL_apply, h, finSumFinEquiv_symm_addNat,
        finSumFinEquiv_symm_apply_castAdd]
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · have h : i.addNat m ≠ Fin.castAdd m j := by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using finSumFinEquiv_inr_ne_inl i j
      simp [diagGL_apply, h, finSumFinEquiv_symm_addNat,
        finSumFinEquiv_symm_apply_castAdd]
    · simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.fromBlocks_apply₂₂]
      rw [diagGL_inv]
      by_cases hij : i = j
      · subst j
        simp [diagGL_apply, diagonalCoordinates, finSumFinEquiv_symm_addNat]
      · have hji : j ≠ i := Ne.symm hij
        simp [diagGL_apply, hij, hji]

/-- The symplectic diagonal homomorphism is injective. -/
theorem diagonal_injective : Function.Injective (diagonal (m := m) (R := R)) := by
  exact leviHom_injective.comp diagGL_injective

/-- The diagonal symplectic matrix commutes with change of coefficient ring. -/
@[simp]
theorem map_diagonal {S : Type*} [CommRing S] (f : R →+* S) (t : Fin m → Rˣ) :
    GLSymplecticFin.map m R f (diagonal t) =
      diagonal (fun i ↦ Units.map f (t i)) := by
  rw [diagonal, diagonal, MonoidHom.comp_apply, MonoidHom.comp_apply, map_leviHom]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.GeneralLinearGroup.map_apply, diagGL_apply]
  · simp [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, hij]

end Matrix

namespace RootSubgroupIndex

variable [CommMonoid R]

/-- The character of the standard symplectic diagonal torus belonging to a root. -/
def character (root : RootSubgroupIndex m) : (Fin m → Rˣ) →* Rˣ :=
  match root with
  | .positiveLong i =>
      { toFun := fun t ↦ t i * t i
        map_one' := by simp
        map_mul' := by intros; simp only [Pi.mul_apply]; ac_rfl }
  | .negativeLong i =>
      { toFun := fun t ↦ (t i * t i)⁻¹
        map_one' := by simp
        map_mul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc] }
  | .difference i j _ =>
      { toFun := fun t ↦ t i * (t j)⁻¹
        map_one' := by simp
        map_mul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc] }
  | .positiveSum i j _ =>
      { toFun := fun t ↦ t i * t j
        map_one' := by simp
        map_mul' := by intros; simp only [Pi.mul_apply]; ac_rfl }
  | .negativeSum i j _ =>
      { toFun := fun t ↦ (t i * t j)⁻¹
        map_one' := by simp
        map_mul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc] }

@[simp]
theorem character_positiveLong (i : Fin m) (t : Fin m → Rˣ) :
    (RootSubgroupIndex.positiveLong i).character t = t i * t i := by
  simp [character]

@[simp]
theorem character_negativeLong (i : Fin m) (t : Fin m → Rˣ) :
    (RootSubgroupIndex.negativeLong i).character t = (t i * t i)⁻¹ := by
  simp [character]

@[simp]
theorem character_difference (i j : Fin m) (hij : i ≠ j) (t : Fin m → Rˣ) :
    (RootSubgroupIndex.difference i j hij).character t = t i * (t j)⁻¹ := by
  simp [character]

@[simp]
theorem character_positiveSum (i j : Fin m) (hij : i < j) (t : Fin m → Rˣ) :
    (RootSubgroupIndex.positiveSum i j hij).character t = t i * t j := by
  simp [character]

@[simp]
theorem character_negativeSum (i j : Fin m) (hij : i < j) (t : Fin m → Rˣ) :
    (RootSubgroupIndex.negativeSum i j hij).character t = (t i * t j)⁻¹ := by
  simp [character]

end RootSubgroupIndex

section Matrix

variable [CommRing R]

/-- **Conjugation by a diagonal symplectic matrix acts on each root subgroup through its root
character.** -/
theorem diagonal_mul_rootSubgroup_mul_inv (root : RootSubgroupIndex m) (t : Fin m → Rˣ)
    (c : Multiplicative R) :
    diagonal t * root.hom c * (diagonal t)⁻¹ =
      root.hom (Multiplicative.ofAdd ((root.character t : R) * c.toAdd)) := by
  apply Subtype.ext
  cases root with
  | positiveLong i =>
      rw [RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.character_positiveLong]
      simp only [positiveLongRootTransvectionHom_apply,
        coe_diagonal, coe_positiveLongRootTransvectionUnit, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [diagGL_mul_transvectionUnit_mul_inv]
      congr 1
      simp
      ring
  | negativeLong i =>
      rw [RootSubgroupIndex.hom_negativeLong, RootSubgroupIndex.character_negativeLong]
      simp only [negativeLongRootTransvectionHom_apply,
        coe_diagonal, coe_negativeLongRootTransvectionUnit, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [diagGL_mul_transvectionUnit_mul_inv]
      congr 1
      simp
      ring
  | difference i j hij =>
      rw [RootSubgroupIndex.hom_difference, RootSubgroupIndex.character_difference]
      simp only [differenceShortRootHom_apply, coe_diagonal,
        coe_differenceShortRootUnit, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← MulAut.conj_apply, map_mul]
      simp only [MulAut.conj_apply]
      rw [diagGL_mul_transvectionUnit_mul_inv,
        diagGL_mul_transvectionUnit_mul_inv]
      congr 1 <;> simp <;> ring_nf
  | positiveSum i j hij =>
      rw [RootSubgroupIndex.hom_positiveSum, RootSubgroupIndex.character_positiveSum]
      simp only [positiveSumShortRootHom_apply, coe_diagonal,
        coe_positiveSumShortRootUnit, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← MulAut.conj_apply, map_mul]
      simp only [MulAut.conj_apply]
      rw [diagGL_mul_transvectionUnit_mul_inv,
        diagGL_mul_transvectionUnit_mul_inv]
      congr 1 <;> simp <;> ring_nf
  | negativeSum i j hij =>
      rw [RootSubgroupIndex.hom_negativeSum, RootSubgroupIndex.character_negativeSum]
      simp only [negativeSumShortRootHom_apply, coe_diagonal,
        coe_negativeSumShortRootUnit, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← MulAut.conj_apply, map_mul]
      simp only [MulAut.conj_apply]
      rw [diagGL_mul_transvectionUnit_mul_inv,
        diagGL_mul_transvectionUnit_mul_inv]
      congr 1 <;> simp <;> ring_nf

end Matrix

end TauCeti.GLSymplecticFin
