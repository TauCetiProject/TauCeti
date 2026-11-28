/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Borel`, its normal form `TauCeti.GL2Borel.mk` and the Weyl element
-- `TauCeti.GL2WeylElement` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
-- `Subgroup.center (GL (Fin 2) R)` occurs in the statements below, and
-- `Matrix.GeneralLinearGroup.center_eq_range_scalar` identifies it with the scalar matrices.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
-- `TauCeti.AffineGroup` occurs in the statements below.
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic

/-!
# The mirabolic subgroup of `GL₂`

The **mirabolic subgroup** `P` of `GL₂(R)` consists of the invertible matrices whose lower row is
`(0, 1)`, that is, the matrices `!![a, b; 0, 1]` with `a` a unit. It is the stabiliser of the
linear form `(x, y) ↦ y`, and `!![a, b; 0, 1]` acts on the column vectors `(x, 1)` by the affine
map `x ↦ a x + b`; this identifies `P` with the affine group `R ⋊ Rˣ` of the line. Over
`R = ℚ_p` it is the group through which Colmez's construction of the `p`-adic local Langlands
correspondence for `GL₂(ℚ_p)` starts: an étale `(φ, Γ)`-module is a module over a submonoid of
`P(ℚ_p)`. Since `P`, the centre `Z` and the Weyl element `w = !![0, 1; 1, 0]` generate `GL₂` over
a field, an action of `GL₂` is determined by its restriction to `P`, `Z` and `w`.

The subgroup, its normal form and its identification with the affine group are set up over an
arbitrary ring; the comparison with the Borel subgroup `B = TauCeti.GL2Borel R` and the centre `Z`
is proved over an arbitrary commutative ring. It only uses that `P` sits inside `B` and that every
element of `B` is a scalar matrix times an element of `P`, which gives `B = Z ⊔ P`; with the
Bruhat-cell generation `TauCeti.GL2Borel.closure_insert_gl2WeylElement_eq_top` this gives the
generation of `GL₂` over a field.

## Main definitions

* `TauCeti.GL2Mirabolic R`: the subgroup of `GL (Fin 2) R` of matrices with lower row `(0, 1)`.
* `TauCeti.GL2Mirabolic.affineGroupMulEquiv`: the isomorphism `R ⋊ Rˣ ≃* P` sending the affine
  map `x ↦ a x + b` to `!![a, b; 0, 1]`.

## Main results

* `TauCeti.GL2Mirabolic.mem_iff`: membership is the two entry conditions `g 1 0 = 0` and
  `g 1 1 = 1`.
* `TauCeti.GL2Mirabolic.mem_iff_exists_mk`: the elements of `P` are exactly the matrices
  `!![a, b; 0, 1]` with `a` a unit.
* `TauCeti.GL2Mirabolic.neg_one_mem_iff`: `-1 ∈ P` only when `-1 = 1`.
* `TauCeti.GL2Mirabolic.map_det`: over a commutative ring the determinant maps `P` onto the units.
* `TauCeti.GL2Mirabolic.le_gl2Borel`: `P` lies in the Borel subgroup.
* `TauCeti.GL2Mirabolic.inf_center_eq_bot`: `P ∩ Z = 1`.
* `TauCeti.GL2Mirabolic.center_sup_eq_gl2Borel`: `Z ⊔ P = B`.
* `TauCeti.GL2Mirabolic.closure_insert_gl2WeylElement_eq_top`: over a field, `GL₂` is generated
  by `P`, `Z` and `w`.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §4 and §III.1.1.
-/

public section

namespace TauCeti

open Matrix

universe u

section Ring

variable (R : Type u) [Ring R]

/-- The **mirabolic subgroup** of `GL₂(R)`: the invertible matrices `!![a, b; 0, 1]` whose lower
row is `(0, 1)`. -/
def GL2Mirabolic : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hh.1, hh.2]
  inv_mem' {g} hg := by
    -- The lower row of `g g⁻¹ = 1` is the lower row of `g⁻¹`, since that of `g` is `(0, 1)`.
    have h := congrFun (congrFun g.mul_inv 1)
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2] using And.intro (h 0) (h 1)

namespace GL2Mirabolic

variable {R}

/-- Membership in the mirabolic subgroup is the pair of entry conditions defining it. -/
theorem mem_iff {g : GL (Fin 2) R} :
    g ∈ GL2Mirabolic R ↔
      (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 :=
  Iff.rfl

/-- The lower-left entry of an element of the mirabolic subgroup vanishes. -/
@[simp]
theorem apply_one_zero (g : GL2Mirabolic R) :
    ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
  (mem_iff.mp g.property).1

/-- The lower-right entry of an element of the mirabolic subgroup is `1`. -/
@[simp]
theorem apply_one_one (g : GL2Mirabolic R) :
    ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 :=
  (mem_iff.mp g.property).2

/-- The upper-triangular matrix `!![a, b; 0, d]` is mirabolic exactly when `d = 1`. -/
@[simp]
theorem mk_mem_iff (a d : Rˣ) (b : R) : GL2Borel.mk a d b ∈ GL2Mirabolic R ↔ d = 1 := by
  simp only [mem_iff, GL2Borel.coe_mk]
  simp [Units.val_eq_one]

variable (R) in
/-- **The mirabolic subgroup is the affine group of the line**: the affine map `x ↦ a x + b`,
the element `(b, a)` of `R ⋊ Rˣ`, corresponds to the matrix `!![a, b; 0, 1]`. -/
def affineGroupMulEquiv : AffineGroup R ≃* GL2Mirabolic R where
  toFun g := ⟨GL2Borel.mk g.right 1 g.left.toAdd, (mk_mem_iff _ 1 _).mpr rfl⟩
  -- The upper-left entries of `g` and `g⁻¹` are inverse to each other, as `g` and `g⁻¹` are
  -- upper triangular.
  invFun g := ⟨Multiplicative.ofAdd (((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1),
    ⟨((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0,
      (((g : GL (Fin 2) R)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0, by
        have h := congrFun (congrFun (g : GL (Fin 2) R).mul_inv 0) 0
        simpa [Matrix.mul_apply, Fin.sum_univ_two, (mem_iff.mp (inv_mem g.property)).1] using h, by
        have h := congrFun (congrFun (g : GL (Fin 2) R).inv_mul 0) 0
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using h⟩⟩
  left_inv g := by
    refine SemidirectProduct.ext ?_ (Units.ext ?_) <;> simp
  right_inv g := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j ↦ ?_))
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j ↦ ?_))
    fin_cases i <;> fin_cases j <;>
      simp [add_comm]

@[simp]
theorem coe_affineGroupMulEquiv_apply (g : AffineGroup R) :
    ((affineGroupMulEquiv R g : GL2Mirabolic R) : GL (Fin 2) R) =
      GL2Borel.mk g.right 1 g.left.toAdd :=
  (rfl)

/-- The translation part of the affine map attached to a mirabolic matrix `!![a, b; 0, 1]` is its
upper-right entry `b`. -/
@[simp]
theorem toAdd_affineGroupMulEquiv_symm_apply_left (g : GL2Mirabolic R) :
    ((affineGroupMulEquiv R).symm g).left.toAdd =
      ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 :=
  (rfl)

/-- The linear part of the affine map attached to a mirabolic matrix `!![a, b; 0, 1]` is its
upper-left entry `a`. -/
@[simp]
theorem coe_affineGroupMulEquiv_symm_apply_right (g : GL2Mirabolic R) :
    (((affineGroupMulEquiv R).symm g).right : R) =
      ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 :=
  (rfl)

/-- **Normal form**: the elements of the mirabolic subgroup are exactly the matrices
`!![a, b; 0, 1]` with `a` a unit. -/
theorem mem_iff_exists_mk {g : GL (Fin 2) R} :
    g ∈ GL2Mirabolic R ↔ ∃ (a : Rˣ) (b : R), g = GL2Borel.mk a 1 b := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · set x := (affineGroupMulEquiv R).symm ⟨g, hg⟩
    exact ⟨x.right, x.left.toAdd, by
      rw [← coe_affineGroupMulEquiv_apply, MulEquiv.apply_symm_apply]⟩
  · rintro ⟨a, b, rfl⟩
    exact (mk_mem_iff a 1 b).mpr rfl

variable (R) in
/-- The upper unipotent matrices `!![1, b; 0, 1]` are mirabolic. -/
theorem upperRightHom_mem (b : R) : GeneralLinearGroup.upperRightHom b ∈ GL2Mirabolic R := by
  simp [mem_iff, GeneralLinearGroup.upperRightHom]

/-- A scalar matrix is mirabolic only when it is the identity. -/
@[simp]
theorem scalar_mem_iff (u : Rˣ) :
    GeneralLinearGroup.scalar (Fin 2) u ∈ GL2Mirabolic R ↔ u = 1 := by
  simp only [mem_iff, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  simp [Units.val_eq_one]

/-- `-1` lies in the mirabolic subgroup exactly when `-1 = 1` in `R`. -/
theorem neg_one_mem_iff : (-1 : GL (Fin 2) R) ∈ GL2Mirabolic R ↔ (-1 : R) = 1 := by
  simp [mem_iff]

end GL2Mirabolic

end Ring

section CommRing

variable (R : Type u) [CommRing R]

namespace GL2Mirabolic

variable {R}

/-- The determinant of a mirabolic matrix `!![a, b; 0, 1]` is its upper-left entry `a`. -/
theorem det_eq {g : GL (Fin 2) R} (hg : g ∈ GL2Mirabolic R) :
    (g : Matrix (Fin 2) (Fin 2) R).det = (g : Matrix (Fin 2) (Fin 2) R) 0 0 := by
  rw [Matrix.det_fin_two, (mem_iff.mp hg).1, (mem_iff.mp hg).2, mul_one, mul_zero, sub_zero]

/-- The determinant maps the mirabolic subgroup onto the units: `!![u, 0; 0, 1]` has determinant
`u`. -/
theorem map_det : (GL2Mirabolic R).map Matrix.GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr fun u _ ↦ ⟨GL2Borel.mk u 1 0, (mk_mem_iff _ _ _).mpr rfl, by simp⟩

variable (R) in
/-- The mirabolic subgroup lies in the Borel subgroup. -/
theorem le_gl2Borel : GL2Mirabolic R ≤ GL2Borel R :=
  fun _ hg ↦ GL2Borel.mem_iff.mpr (mem_iff.mp hg).1

variable (R) in
/-- **`P ∩ Z = 1`**: the only central element of the mirabolic subgroup is the identity. -/
theorem inf_center_eq_bot : GL2Mirabolic R ⊓ Subgroup.center (GL (Fin 2) R) = ⊥ := by
  refine eq_bot_iff.mpr fun g ⟨hP, hZ⟩ ↦ ?_
  rw [GeneralLinearGroup.center_eq_range_scalar] at hZ
  obtain ⟨u, rfl⟩ := hZ
  rw [(scalar_mem_iff u).mp hP, map_one]
  exact Subgroup.one_mem _

variable (R) in
/-- **`B = Z P`**: the Borel subgroup is generated by the centre and the mirabolic subgroup. -/
theorem center_sup_eq_gl2Borel :
    Subgroup.center (GL (Fin 2) R) ⊔ GL2Mirabolic R = GL2Borel R := by
  refine le_antisymm (sup_le ?_ (le_gl2Borel R)) fun g hg ↦ ?_
  · rw [GeneralLinearGroup.center_eq_range_scalar]
    rintro _ ⟨u, rfl⟩
    exact GL2Borel.scalar_mem R u
  · -- Dividing `!![a, b; 0, d]` by the scalar `d` makes its lower-right entry `1`.
    obtain ⟨a, d, b, rfl⟩ := GL2Borel.mem_iff_exists_mk.mp hg
    have hd : GeneralLinearGroup.scalar (Fin 2) d ∈ Subgroup.center (GL (Fin 2) R) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨d, rfl⟩
    have hmk : GL2Borel.mk a d b =
        GeneralLinearGroup.scalar (Fin 2) d * GL2Borel.mk (d⁻¹ * a) 1 ((d⁻¹ : Rˣ) * b) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← mul_assoc]
    rw [hmk]
    exact Subgroup.mul_mem_sup hd ((mk_mem_iff _ 1 _).mpr rfl)

end GL2Mirabolic

end CommRing

namespace GL2Mirabolic

variable (F : Type u) [Field F]

/-- **`P`, `Z` and `w` generate `GL₂` over a field.** The centre and the mirabolic subgroup
generate the Borel subgroup, which together with the Weyl element generates `GL₂` by the Bruhat
decomposition. In particular an action of the mirabolic subgroup extends to at most one action of
`GL₂` with prescribed actions of the centre and of `w`. -/
theorem closure_insert_gl2WeylElement_eq_top :
    Subgroup.closure (insert (GL2WeylElement F)
      ((Subgroup.center (GL (Fin 2) F) : Set (GL (Fin 2) F)) ∪ GL2Mirabolic F)) = ⊤ := by
  rw [eq_top_iff, ← GL2Borel.closure_insert_gl2WeylElement_eq_top, Subgroup.closure_le]
  rintro g (rfl | hg)
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [SetLike.mem_coe, ← center_sup_eq_gl2Borel, Subgroup.sup_eq_closure] at hg
    exact Subgroup.closure_mono (Set.subset_insert _ _) hg

end GL2Mirabolic

end TauCeti
