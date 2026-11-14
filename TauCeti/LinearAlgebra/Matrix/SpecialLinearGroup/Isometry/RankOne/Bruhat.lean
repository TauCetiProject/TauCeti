/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Unitary
public import TauCeti.GroupTheory.TitsSystem.RankOne
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Points
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The Bruhat decomposition and rank-one Tits system of a three-dimensional unitary group

Let `Q` be the three-dimensional signed reversal matrix `!![0, 0, 1; 0, -1, 0; 1, 0, 0]`, realized
as `TauCeti.typeAGraphConjugator 2`, and let `G = Matrix.specialIsometryGroup Q σ` be the special
isometry group of the `σ`-sesquilinear form of Gram matrix `Q`. This file constructs the standard
rank-one root-group, torus, Weyl, and Borel data in `G` and establishes its two-cell Bruhat
decomposition and irreducible Tits system of rank one.

Over a commutative ring `R` with an endomorphism `σ : R →+* R`:

* `TauCeti.UnitaryRankOne.unipotentHom` embeds the unitary Heisenberg subgroup
  `TauCeti.HeisenbergGroup.unitarySubgroup σ` into `G` as its upper-unitriangular subgroup
  `TauCeti.UnitaryRankOne.unipotentSubgroup`, which is nilpotent;
* `TauCeti.UnitaryRankOne.weyl` is the involutive antidiagonal element `Q` in `G`, conjugating
  upper-unitriangular root elements to lower-unitriangular ones;
* when `σ` is involutive, `TauCeti.UnitaryRankOne.torus` embeds `Rˣ` as the diagonal matrices
  `diag(t, t⁻¹ σ(t), σ(t⁻¹))` in `G`, normalizing the unipotent subgroup and inverted up to `σ` by
  the Weyl element.

Over a field `K`, the Borel subgroup `TauCeti.UnitaryRankOne.borelSubgroup` is the stabilizer of
the isotropic point `infinity K σ = [1 : 0 : 0]`. By the affine chart characterization of
`TauCeti.UnitaryRankOne.eq_infinity_iff`, a matrix in `G` stabilizes `infinity K σ` if and only if
its `(2, 0)` entry vanishes. When `σ` is involutive, every Borel element factors into a torus
element times a unipotent element (`TauCeti.UnitaryRankOne.borelSubgroup_eq_sup`), so the Borel
subgroup normalizes the unipotent subgroup. Acting on `infinity K σ` by `u * weyl` sweeps out all
affine isotropic points `point K σ c`, yielding the sharp Bruhat decomposition `G = B ∪ U w B` and
the rank-one Tits system `TauCeti.UnitaryRankOne.titsSystem` without any trace or characteristic
restriction on `(K, σ)`.

## Main definitions

* `TauCeti.UnitaryRankOne.unipotentHom`: the upper-unitriangular root-group embedding into `G`.
* `TauCeti.UnitaryRankOne.unipotentSubgroup`: the upper-unitriangular subgroup `U` of `G`.
* `TauCeti.UnitaryRankOne.weyl`: the involutive Weyl element `w` in `G`.
* `TauCeti.UnitaryRankOne.torus`: the diagonal torus homomorphism `Rˣ →* G` for involutive `σ`.
* `TauCeti.UnitaryRankOne.borelSubgroup`: the stabilizer `B` of `infinity K σ` in `G`.
* `TauCeti.UnitaryRankOne.titsSystem`: the irreducible rank-one Tits system `(B, ⟨w⟩)` on `G`.

## Main results

* `TauCeti.UnitaryRankOne.mem_borelSubgroup_iff`: `g ∈ B` if and only if `g 2 0 = 0`.
* `TauCeti.UnitaryRankOne.borelSubgroup_eq_sup`: `B = H ⊔ U` for involutive `σ`.
* `TauCeti.UnitaryRankOne.borelSubgroup_le_normalizer_unipotentSubgroup`: `B` normalizes `U`.
* `TauCeti.UnitaryRankOne.mem_borelSubgroup_or_mem_doubleCoset`: `G = B ∪ B w B`.
* `TauCeti.UnitaryRankOne.isIrreducible_titsSystem`: the rank-one Tits system on `G` is irreducible.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* J. E. Humphreys, *Linear Algebraic Groups*, Springer (1975), Section 29.1.
* D. E. Taylor, *The Geometry of the Classical Groups*, Heldermann (1992), Chapter 10.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti.UnitaryRankOne

/-! ### Unipotent subgroup, Weyl element, and diagonal torus over a commutative ring -/

section CommRing

variable {R : Type*} [CommRing R] {σ : R →+* R}

variable (R σ) in
/-- The upper-unitriangular root-group homomorphism from `HeisenbergGroup.unitarySubgroup σ` into
the special isometry group of the three-dimensional signed reversal form. -/
def unipotentHom :
    HeisenbergGroup.unitarySubgroup σ →*
      (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ :=
  (HeisenbergGroup.toSpecialLinear.comp (HeisenbergGroup.unitarySubgroup σ).subtype).codRestrict
    ((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ) fun a ↦ by
      have ha := HeisenbergGroup.mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq.mp a.2
      rw [Matrix.mem_specialIsometryGroup_iff, coe_typeAGraphConjugator_two]
      simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype,
        HeisenbergGroup.coe_toSpecialLinear] using ha

/-- The underlying special linear matrix of `unipotentHom` is `HeisenbergGroup.toSpecialLinear`. -/
@[simp]
theorem coe_unipotentHom (a : HeisenbergGroup.unitarySubgroup σ) :
    (unipotentHom R σ a : Matrix.SpecialLinearGroup (Fin 3) R) =
      HeisenbergGroup.toSpecialLinear a := (rfl)

variable (R σ) in
/-- The upper-unitriangular root-group embedding is injective. -/
theorem unipotentHom_injective : Function.Injective (unipotentHom R σ) :=
  fun _ _ h ↦ Subtype.ext (HeisenbergGroup.toSpecialLinear_injective (congrArg Subtype.val h))

variable (R σ) in
/-- The upper-unitriangular unipotent subgroup of the rank-one special isometry group. -/
def unipotentSubgroup :
    Subgroup ((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ) :=
  (unipotentHom R σ).range

variable (R σ) in
/-- The unipotent subgroup is the range of `unipotentHom`. -/
theorem unipotentSubgroup_def : unipotentSubgroup R σ = (unipotentHom R σ).range := (rfl)

/-- Every image of `unipotentHom` lies in `unipotentSubgroup`. -/
@[simp]
theorem unipotentHom_mem_unipotentSubgroup (a : HeisenbergGroup.unitarySubgroup σ) :
    unipotentHom R σ a ∈ unipotentSubgroup R σ :=
  ⟨a, rfl⟩

/-- An element of the rank-one special isometry group lies in `unipotentSubgroup` if and only if
its matrix is upper unitriangular. -/
theorem mem_unipotentSubgroup_iff
    {g : (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ} :
    g ∈ unipotentSubgroup R σ ↔
      ((g : Matrix.SpecialLinearGroup (Fin 3) R) :
        Matrix (Fin 3) (Fin 3) R).IsUpperUnitriangular := by
  rw [unipotentSubgroup_def, MonoidHom.mem_range, ← HeisenbergGroup.mem_range_toSpecialLinear_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    have hg := Matrix.mem_specialIsometryGroup_iff.mp g.2
    rw [← ha, HeisenbergGroup.coe_toSpecialLinear, coe_typeAGraphConjugator_two] at hg
    exact HeisenbergGroup.mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq.mpr hg

/-- The unipotent subgroup is nilpotent, being a homomorphic image of a subgroup of the Heisenberg
group. -/
instance : Group.IsNilpotent (unipotentSubgroup R σ) :=
  Group.nilpotent_of_surjective (unipotentHom R σ).rangeRestrict
    (unipotentHom R σ).rangeRestrict_surjective

private def weylSL (R : Type*) [CommRing R] : Matrix.SpecialLinearGroup (Fin 3) R :=
  ⟨!![0, 0, 1; 0, -1, 0; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

variable (R σ) in
/-- The involutive antidiagonal Weyl element `!![0, 0, 1; 0, -1, 0; 1, 0, 0]` of the rank-one
special isometry group. -/
def weyl : (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ :=
  ⟨weylSL R, by
    rw [Matrix.mem_specialIsometryGroup_iff, coe_typeAGraphConjugator_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylSL, Matrix.mul_apply, Fin.sum_univ_three]⟩

variable (R σ) in
/-- The matrix of the Weyl element is `!![0, 0, 1; 0, -1, 0; 1, 0, 0]`. -/
@[simp]
theorem coe_weyl :
    ((weyl R σ : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      !![0, 0, 1; 0, -1, 0; 1, 0, 0] := (rfl)

variable (R σ) in
/-- The Weyl element has square `1`. -/
@[simp]
theorem weyl_mul_self : weyl R σ * weyl R σ = 1 := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

variable (R σ) in
/-- The Weyl element is equal to its own inverse. -/
@[simp]
theorem weyl_inv : (weyl R σ)⁻¹ = weyl R σ :=
  inv_eq_of_mul_eq_one_right (weyl_mul_self R σ)

/-- Conjugating an upper-unitriangular root element by `weyl` gives the lower-unitriangular matrix
with off-diagonal coordinates `-σ x`, `z`, and `-x`. -/
theorem coe_weyl_mul_unipotentHom_mul_weyl (a : HeisenbergGroup.unitarySubgroup σ) :
    (((weyl R σ * unipotentHom R σ a * weyl R σ :
        (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ) :
        Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      !![1, 0, 0; -σ (a : HeisenbergGroup R).x, 1, 0;
        (a : HeisenbergGroup R).z, -(a : HeisenbergGroup R).x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HeisenbergGroup.toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three]

private def torusSL (R : Type*) [CommRing R] (σ : R →+* R) :
    Rˣ →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun t :=
    ⟨Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R) * σ (t : R), σ ((t⁻¹ : Rˣ) : R)], by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
      calc (t : R) * (((t⁻¹ : Rˣ) : R) * σ (t : R)) * σ ((t⁻¹ : Rˣ) : R)
          = ((t : R) * ((t⁻¹ : Rˣ) : R)) * σ ((t : R) * ((t⁻¹ : Rˣ) : R)) := by
              rw [map_mul]; ring
        _ = 1 := by simp⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) R)
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  map_mul' s t := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · exact Units.val_mul s t
    · dsimp
      rw [_root_.mul_inv_rev, Units.val_mul, map_mul]
      ring
    · dsimp
      rw [_root_.mul_inv_rev, Units.val_mul, map_mul]
      ring

@[simp]
private theorem coe_torusSL (t : Rˣ) :
    (torusSL R σ t : Matrix (Fin 3) (Fin 3) R) =
      Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R) * σ (t : R), σ ((t⁻¹ : Rˣ) : R)] := (rfl)

/-- For an involutive endomorphism `σ`, the diagonal torus homomorphism sending `t : Rˣ` to
`diag(t, t⁻¹ σ(t), σ(t⁻¹))` in the rank-one special isometry group. -/
def torus (R : Type*) [CommRing R] (σ : R →+* R) (hσ : Function.Involutive σ) :
    Rˣ →* (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ :=
  (torusSL R σ).codRestrict
    ((typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ) fun t ↦ by
      have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := t.mul_inv
      have h2 : σ (t : R) * σ ((t⁻¹ : Rˣ) : R) = 1 := by
        rw [← map_mul, h1, map_one]
      rw [Matrix.mem_specialIsometryGroup_iff, coe_typeAGraphConjugator_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, hσ (t : R), hσ ((t⁻¹ : Rˣ) : R)]
      · linear_combination h2
      · linear_combination σ (t : R) * σ ((t⁻¹ : Rˣ) : R) * h1 + h2

/-- The matrix of `torus R σ hσ t` is `diag(t, t⁻¹ σ(t), σ(t⁻¹))`. -/
@[simp]
theorem coe_torus (hσ : Function.Involutive σ) (t : Rˣ) :
    ((torus R σ hσ t : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R) * σ (t : R), σ ((t⁻¹ : Rˣ) : R)] := (rfl)

/-- The diagonal torus embedding is injective. -/
theorem torus_injective (hσ : Function.Involutive σ) : Function.Injective (torus R σ hσ) := by
  intro s t h
  apply Units.ext
  have h00 := congrArg (fun g :
      (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ ↦
    ((g : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 0) h
  simpa using h00

/-- Conjugating `torus R σ hσ t` by `weyl` maps `t` to `(σ t)⁻¹`. -/
@[simp]
theorem weyl_mul_torus_mul_weyl (hσ : Function.Involutive σ) (t : Rˣ) :
    weyl R σ * torus R σ hσ t * weyl R σ =
      torus R σ hσ (Units.map σ.toMonoidHom t)⁻¹ := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weyl, coe_torus,
    Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Units.coe_map_inv, hσ (t : R), hσ ((t⁻¹ : Rˣ) : R), mul_comm]

/-- Conjugating a root element `unitaryMk σ hσ x z hz` by `torus R σ hσ t` rescales `x` by
`t² σ(t⁻¹)` and `z` by `t σ(t)`. -/
theorem torus_mul_unipotentHom_unitaryMk_mul_inv (hσ : Function.Involutive σ) (t : Rˣ)
    (x z : R) (hz : z + σ z = x * σ x) :
    torus R σ hσ t * unipotentHom R σ (HeisenbergGroup.unitaryMk σ hσ x z hz) *
        (torus R σ hσ t)⁻¹ =
      unipotentHom R σ (HeisenbergGroup.unitaryMk σ hσ
        ((t : R) ^ 2 * σ ((t⁻¹ : Rˣ) : R) * x) ((t : R) * σ (t : R) * z) (by
          have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := t.mul_inv
          have h2 : σ (t : R) * σ ((t⁻¹ : Rˣ) : R) = 1 := by
            rw [← map_mul, h1, map_one]
          simp only [map_mul, map_pow, hσ (t : R), hσ ((t⁻¹ : Rˣ) : R)]
          linear_combination (t : R) * σ (t : R) * hz -
            (t : R) * σ (t : R) * x * σ x * h2 -
            (t : R) * (σ (t : R)) ^ 2 * σ ((t⁻¹ : Rˣ) : R) * x * σ x * h1)) := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := t.mul_inv
  have h2 : σ (t : R) * σ ((t⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, h1, map_one]
  rw [← (torus R σ hσ).map_inv t]
  apply Subtype.ext
  change (((torus R σ hσ t * unipotentHom R σ (HeisenbergGroup.unitaryMk σ hσ x z hz) *
      torus R σ hσ t⁻¹ :
      (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R).specialIsometryGroup σ) :
      Matrix.SpecialLinearGroup (Fin 3) R)) =
    (unipotentHom R σ _ : Matrix.SpecialLinearGroup (Fin 3) R)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torus, coe_unipotentHom,
    HeisenbergGroup.coe_toSpecialLinear, HeisenbergGroup.coe_unitaryMk, inv_inv]
  fin_cases i <;> fin_cases j <;>
    simp [HeisenbergGroup.toMatrix_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      hσ ((t⁻¹ : Rˣ) : R)]
  · ring
  · ring
  · linear_combination σ (t : R) * σ ((t⁻¹ : Rˣ) : R) * h1 + h2
  · ring
  · linear_combination h2

/-- The diagonal torus normalizes the unipotent subgroup. -/
theorem torus_range_le_normalizer_unipotentSubgroup (hσ : Function.Involutive σ) :
    (torus R σ hσ).range ≤ Subgroup.normalizer (unipotentSubgroup R σ : Set _) := by
  rintro _ ⟨t, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  rintro u
  simp only [unipotentSubgroup_def, MonoidHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    rw [← HeisenbergGroup.unitaryMk_eta hσ a, torus_mul_unipotentHom_unitaryMk_mul_inv]
    exact ⟨_, rfl⟩
  · rintro ⟨a, ha⟩
    have hconj : (torus R σ hσ t)⁻¹ * (torus R σ hσ t * u * (torus R σ hσ t)⁻¹) *
        ((torus R σ hσ t)⁻¹)⁻¹ = u := by group
    rw [← hconj, ← ha, ← HeisenbergGroup.unitaryMk_eta hσ a, ← map_inv (torus R σ hσ) t,
      torus_mul_unipotentHom_unitaryMk_mul_inv]
    exact ⟨_, rfl⟩

end CommRing

/-! ### Borel subgroup, Bruhat decomposition, and rank-one Tits system over a field -/

section Field

variable {K : Type*} [Field K] {σ : K →+* K}

variable (K σ) in
/-- The Borel subgroup of the rank-one special isometry group: the stabilizer of the distinguished
isotropic point `infinity K σ = [1 : 0 : 0]`. -/
def borelSubgroup :
    Subgroup ((typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) :=
  MulAction.stabilizer _ (infinity K σ)

variable (K σ) in
/-- The Borel subgroup is the stabilizer of `infinity K σ`. -/
theorem borelSubgroup_def : borelSubgroup K σ = MulAction.stabilizer _ (infinity K σ) := (rfl)

/-- Membership in `borelSubgroup` is fixing `infinity K σ`. -/
theorem mem_borelSubgroup_iff_smul_infinity
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ} :
    g ∈ borelSubgroup K σ ↔ g • infinity K σ = infinity K σ :=
  Iff.rfl

/-- An element of the rank-one special isometry group lies in the Borel subgroup if and only if
its `(2, 0)` matrix entry vanishes. -/
theorem mem_borelSubgroup_iff
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ} :
    g ∈ borelSubgroup K σ ↔
      ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  rw [mem_borelSubgroup_iff_smul_infinity, eq_infinity_iff, SubMulAction.val_smul,
    coe_infinity, Subgroup.smul_def, Projectivization.smul_mk,
    Projectivization.mk_mem_affineOpen_iff, not_not, Matrix.SpecialLinearGroup.smul_def,
    smul_eq_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Every element of the Borel subgroup also has vanishing `(1, 0)` entry, by isotropy of the
first column. -/
theorem apply_one_zero_of_mem_borelSubgroup
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∈ borelSubgroup K σ) :
    ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
  have hg20 := mem_borelSubgroup_iff.mp hg
  have hiso := congrFun (congrFun (Matrix.mem_specialIsometryGroup_iff.mp g.2) 0) 0
  have hmul : σ (((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0) *
      ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hg20] using hiso
  exact (mul_eq_zero.mp hmul).elim (map_eq_zero σ).mp id

/-- Every element of the Borel subgroup has nonzero `(0, 0)` entry. -/
theorem apply_zero_zero_ne_zero_of_mem_borelSubgroup
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∈ borelSubgroup K σ) :
    ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
  intro hg00
  have hg10 := apply_one_zero_of_mem_borelSubgroup hg
  have hg20 := mem_borelSubgroup_iff.mp hg
  have hdet := g.1.prop
  rw [Matrix.det_fin_three, hg00, hg10, hg20] at hdet
  simp at hdet

variable (K σ) in
/-- The unipotent subgroup is contained in the Borel subgroup. -/
theorem unipotentSubgroup_le_borelSubgroup : unipotentSubgroup K σ ≤ borelSubgroup K σ := by
  intro g hg
  rw [unipotentSubgroup_def] at hg
  obtain ⟨a, rfl⟩ := hg
  rw [mem_borelSubgroup_iff]
  simp [HeisenbergGroup.toMatrix_apply]

/-- Every diagonal torus element lies in the Borel subgroup. -/
theorem torus_mem_borelSubgroup (hσ : Function.Involutive σ) (t : Kˣ) :
    torus K σ hσ t ∈ borelSubgroup K σ := by
  rw [mem_borelSubgroup_iff]
  simp

/-- The Weyl element does not lie in the Borel subgroup. -/
theorem weyl_notMem_borelSubgroup : weyl K σ ∉ borelSubgroup K σ := by
  rw [mem_borelSubgroup_iff]
  simp

/-- For involutive `σ`, every element of the Borel subgroup factors as a diagonal torus element
multiplied by a unipotent element. -/
theorem exists_torus_mul_unipotent_of_mem_borelSubgroup (hσ : Function.Involutive σ)
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∈ borelSubgroup K σ) :
    ∃ (t : Kˣ) (u : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ),
      u ∈ unipotentSubgroup K σ ∧ torus K σ hσ t * u = g := by
  let t : Kˣ := Units.mk0 _ (apply_zero_zero_ne_zero_of_mem_borelSubgroup hg)
  let u := (torus K σ hσ t)⁻¹ * g
  refine ⟨t, u, mem_unipotentSubgroup_iff.mpr ?_, mul_inv_cancel_left _ _⟩
  have hg10 := apply_one_zero_of_mem_borelSubgroup hg
  have hg20 := mem_borelSubgroup_iff.mp hg
  have hu00 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    simp [u, t, ← map_inv, inv_mul_cancel₀ (apply_zero_zero_ne_zero_of_mem_borelSubgroup hg)]
  have hu10 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    simp [u, ← map_inv, hg10]
  have hu20 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    simp [u, ← map_inv, hg20]
  have hiso := Matrix.mem_specialIsometryGroup_iff.mp u.2
  have hu21 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hu00, hu10, hu20] using
      congrFun (congrFun hiso 0) 1
  have hu22 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hu00, hu10, hu20] using
      congrFun (congrFun hiso 0) 2
  have hu11 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    have hdet := u.1.prop
    rw [Matrix.det_fin_three, hu00, hu10, hu20, hu21, hu22] at hdet
    simpa using hdet
  rw [Matrix.isUpperUnitriangular_def]
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> simp_all

/-- For involutive `σ`, the Borel subgroup is the join of the diagonal torus and the unipotent
subgroup. -/
theorem borelSubgroup_eq_sup (hσ : Function.Involutive σ) :
    borelSubgroup K σ = (torus K σ hσ).range ⊔ unipotentSubgroup K σ := by
  refine le_antisymm (fun g hg ↦ ?_) (sup_le ?_ (unipotentSubgroup_le_borelSubgroup K σ))
  · obtain ⟨t, u, hu, rfl⟩ := exists_torus_mul_unipotent_of_mem_borelSubgroup hσ hg
    exact mul_mem (Subgroup.mem_sup_left ⟨t, rfl⟩) (Subgroup.mem_sup_right hu)
  · rintro _ ⟨t, rfl⟩
    exact torus_mem_borelSubgroup hσ t

/-- For involutive `σ`, the Borel subgroup normalizes the unipotent subgroup. -/
theorem borelSubgroup_le_normalizer_unipotentSubgroup (hσ : Function.Involutive σ) :
    borelSubgroup K σ ≤ Subgroup.normalizer (unipotentSubgroup K σ : Set _) := by
  rw [borelSubgroup_eq_sup hσ]
  exact sup_le (torus_range_le_normalizer_unipotentSubgroup hσ) Subgroup.le_normalizer

/-- Acting on `infinity K σ` by `unipotentHom (unitaryMk σ hσ (σ c.2) c.1 _) * weyl` produces the
affine isotropic point `point K σ c`. -/
theorem unipotentHom_mul_weyl_smul_infinity (hσ : Function.Involutive σ)
    (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    (unipotentHom K σ (HeisenbergGroup.unitaryMk σ hσ (σ c.1.2) c.1.1
        (by simpa [hσ c.1.2] using c.2)) * weyl K σ) • infinity K σ =
      point K σ c := by
  apply Subtype.ext
  rw [SubMulAction.val_smul, coe_infinity, coe_point, Subgroup.smul_def, Projectivization.smul_mk]
  have hvec : ((unipotentHom K σ (HeisenbergGroup.unitaryMk σ hσ (σ c.1.2) c.1.1
        (by simpa [hσ c.1.2] using c.2)) * weyl K σ :
        (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) :
      Matrix.SpecialLinearGroup (Fin 3) K) • ![1, 0, 0] = ![c.1.1, c.1.2, 1] := by
    rw [Matrix.SpecialLinearGroup.smul_def, smul_eq_mulVec]
    ext i
    fin_cases i <;>
      simp [HeisenbergGroup.toMatrix_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_three, hσ c.1.2]
  simp only [hvec]

/-- **Sharp rank-one Bruhat decomposition**: every element outside the Borel subgroup factors as
`u * weyl * b` with `u` unipotent and `b` in the Borel subgroup. -/
theorem exists_unipotent_mul_weyl_mul_borel_of_notMem_borelSubgroup (hσ : Function.Involutive σ)
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∉ borelSubgroup K σ) :
    ∃ u ∈ unipotentSubgroup K σ, ∃ b ∈ borelSubgroup K σ, u * weyl K σ * b = g := by
  obtain ⟨c, hc⟩ := exists_point (mt mem_borelSubgroup_iff_smul_infinity.mpr hg)
  let u := unipotentHom K σ (HeisenbergGroup.unitaryMk σ hσ (σ c.1.2) c.1.1
    (by simpa [hσ c.1.2] using c.2))
  let b := (u * weyl K σ)⁻¹ * g
  have hb : b ∈ borelSubgroup K σ := by
    rw [mem_borelSubgroup_iff_smul_infinity, mul_smul, inv_smul_eq_iff,
      unipotentHom_mul_weyl_smul_infinity, hc]
  exact ⟨u, unipotentHom_mem_unipotentSubgroup _, b, hb, mul_inv_cancel_left _ _⟩

/-- **The rank-one Bruhat decomposition** `G = B ∪ B w B` of the three-dimensional unitary group. -/
theorem mem_borelSubgroup_or_mem_doubleCoset (hσ : Function.Involutive σ)
    (g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) :
    g ∈ borelSubgroup K σ ∨
      g ∈ DoubleCoset.doubleCoset (weyl K σ) (borelSubgroup K σ) (borelSubgroup K σ) := by
  by_cases hg : g ∈ borelSubgroup K σ
  · exact Or.inl hg
  · obtain ⟨u, hu, b, hb, rfl⟩ :=
      exists_unipotent_mul_weyl_mul_borel_of_notMem_borelSubgroup hσ hg
    exact Or.inr (DoubleCoset.mem_doubleCoset.mpr
      ⟨u, unipotentSubgroup_le_borelSubgroup K σ hu, b, hb, rfl⟩)

/-- Over every field `K` and involutive `σ`, some unipotent element is conjugated outside the
Borel subgroup by `weyl`. -/
theorem exists_mem_unipotentSubgroup_weyl_conj_notMem_borelSubgroup (hσ : Function.Involutive σ) :
    ∃ u ∈ unipotentSubgroup K σ, weyl K σ * u * (weyl K σ)⁻¹ ∉ borelSubgroup K σ := by
  by_cases h2 : (2 : K) = 0
  · let a := HeisenbergGroup.unitaryMk σ hσ 0 1 (by simp [← two_mul, h2])
    refine ⟨unipotentHom K σ a, unipotentHom_mem_unipotentSubgroup a, ?_⟩
    rw [weyl_inv, mem_borelSubgroup_iff, coe_weyl_mul_unipotentHom_mul_weyl]
    simp [a]
  · let a := HeisenbergGroup.unitaryMk σ hσ 1 (2 : K)⁻¹
      (by rw [map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ h2]; simp)
    refine ⟨unipotentHom K σ a, unipotentHom_mem_unipotentSubgroup a, ?_⟩
    rw [weyl_inv, mem_borelSubgroup_iff, coe_weyl_mul_unipotentHom_mul_weyl]
    simp [a, h2]

variable (K σ) in
/-- **The rank-one Tits system** `(B, ⟨w⟩)` on the three-dimensional unitary group over any field
`K` with an involutive endomorphism `σ`. -/
def titsSystem (hσ : Function.Involutive σ) :
    TitsSystem ((typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) :=
  TitsSystem.ofRankOne (borelSubgroup K σ) (Subgroup.zpowers (weyl K σ))
    ⟨weyl K σ, Subgroup.mem_zpowers _⟩ (by simp [one_mem])
    (fun _ hx ↦ by
      rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one (by rw [sq, weyl_mul_self])).mp hx
        with rfl | rfl
      · exact Or.inl (one_mem _)
      · exact Or.inr (by simp [one_mem]))
    (by
      obtain ⟨u, hu, hwu⟩ := exists_mem_unipotentSubgroup_weyl_conj_notMem_borelSubgroup hσ
      exact ⟨u, unipotentSubgroup_le_borelSubgroup K σ hu, hwu⟩)
    (mem_borelSubgroup_or_mem_doubleCoset hσ)

/-- The subgroup `B` of the rank-one unitary Tits system is `borelSubgroup K σ`. -/
@[simp]
theorem titsSystem_subgroupB (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).subgroupB = borelSubgroup K σ :=
  TitsSystem.ofRankOne_subgroupB

/-- The subgroup `N` of the rank-one unitary Tits system is generated by `weyl K σ`. -/
@[simp]
theorem titsSystem_subgroupN (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).subgroupN = Subgroup.zpowers (weyl K σ) :=
  TitsSystem.ofRankOne_subgroupN

/-- The unique simple reflection of the rank-one unitary Tits system is the class of `weyl K σ`. -/
@[simp]
theorem titsSystem_simple (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).simple =
      {QuotientGroup.mk ⟨weyl K σ, by rw [titsSystem_subgroupN]; exact Subgroup.mem_zpowers _⟩} :=
  TitsSystem.ofRankOne_simple

/-- **The rank-one unitary Tits system is irreducible.** -/
theorem isIrreducible_titsSystem (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).IsIrreducible :=
  TitsSystem.isIrreducible_ofRankOne

end Field

end TauCeti.UnitaryRankOne
