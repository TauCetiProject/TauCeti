/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Unitary.Basic
public import TauCeti.GroupTheory.TitsSystem.RankOne
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Points
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.UnitaryRankOne
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.DoubleCoset.Orbits

/-!
# The Bruhat decomposition and rank-one Tits system of a three-dimensional unitary group

Let `Q` be the three-dimensional signed reversal matrix `!![0, 0, 1; 0, -1, 0; 1, 0, 0]`, realized
as `TauCeti.typeAGraphConjugator 2`, and let `G = Matrix.specialIsometryGroup Q σ` be the special
isometry group of the `σ`-sesquilinear form of Gram matrix `Q`. Building on the diagonal torus
`TauCeti.UnitaryRankOne.torus` (parametrized by `TauCeti.UnitaryRankOne.torusHom`) and the
involutive Weyl representative `TauCeti.UnitaryRankOne.weyl` from
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.UnitaryRankOne`, this file constructs the
upper-unitriangular root subgroup and Borel data in `G` and establishes its two-cell Bruhat
decomposition and irreducible Tits system of rank one.

Over a commutative ring `R` with an endomorphism `σ : R →+* R`:

* `TauCeti.UnitaryRankOne.unipotentHom` embeds the unitary Heisenberg subgroup
  `TauCeti.HeisenbergGroup.unitarySubgroup σ` into `G` as its upper-unitriangular subgroup
  `TauCeti.UnitaryRankOne.unipotentSubgroup`, which is nilpotent;
* `TauCeti.UnitaryRankOne.weyl` conjugates upper-unitriangular root elements to
  lower-unitriangular ones;
* when `σ` is involutive, `TauCeti.UnitaryRankOne.torusHom` embeds `Rˣ` onto the diagonal
  subgroup `TauCeti.UnitaryRankOne.torus`, which normalizes the unipotent subgroup and intersects it
  trivially.

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
* `TauCeti.UnitaryRankOne.borelSubgroup`: the stabilizer `B` of `infinity K σ` in `G`.
* `TauCeti.UnitaryRankOne.titsSystem`: the irreducible rank-one Tits system `(B, ⟨w⟩)` on `G`.

## Main results

* `TauCeti.UnitaryRankOne.torus_inf_unipotentSubgroup_eq_bot`: `H ⊓ U = ⊥`.
* `TauCeti.UnitaryRankOne.torus_le_normalizer_unipotentSubgroup`: `H` normalizes `U`.
* `TauCeti.UnitaryRankOne.mem_borelSubgroup_iff`: `g ∈ B` if and only if `g 2 0 = 0`.
* `TauCeti.UnitaryRankOne.weyl_mul_unipotentHom_mul_weyl_mem_borelSubgroup_iff`:
  `w u(a) w ∈ B` if and only if `a = 1`.
* `TauCeti.UnitaryRankOne.borelSubgroup_eq_sup`: `B = H ⊔ U` for involutive `σ`.
* `TauCeti.UnitaryRankOne.borelSubgroup_le_normalizer_unipotentSubgroup`: `B` normalizes `U`.
* `TauCeti.UnitaryRankOne.existsUnique_unipotent_mul_weyl_mul_borel_of_notMem_borelSubgroup`:
  every `g ∉ B` factors uniquely as `u * w * b` with `u ∈ U` and `b ∈ B`.
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

/-! ### Unipotent subgroup, Weyl conjugation, and torus normalization over a commutative ring -/

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
      have ha :=
        HeisenbergGroup.mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq.mp a.property
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

/-- Two root elements have the same image under `unipotentHom` if and only if they are equal. -/
@[simp]
theorem unipotentHom_inj {a b : HeisenbergGroup.unitarySubgroup σ} :
    unipotentHom R σ a = unipotentHom R σ b ↔ a = b :=
  (unipotentHom_injective R σ).eq_iff

/-- A root element maps to `1` under `unipotentHom` if and only if it is `1`. -/
@[simp]
theorem unipotentHom_eq_one_iff {a : HeisenbergGroup.unitarySubgroup σ} :
    unipotentHom R σ a = 1 ↔ a = 1 :=
  map_eq_one_iff _ (unipotentHom_injective R σ)

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
    have hg := Matrix.mem_specialIsometryGroup_iff.mp g.property
    rw [← ha, HeisenbergGroup.coe_toSpecialLinear, coe_typeAGraphConjugator_two] at hg
    exact HeisenbergGroup.mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq.mpr hg

/-- The unipotent subgroup is nilpotent, being a homomorphic image of a subgroup of the Heisenberg
group. -/
instance : Group.IsNilpotent (unipotentSubgroup R σ) :=
  Group.nilpotent_of_surjective (unipotentHom R σ).rangeRestrict
    (unipotentHom R σ).rangeRestrict_surjective

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
    simp [coe_typeAGraphConjugator_two, HeisenbergGroup.toMatrix_apply, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- Two units have the same image under `torusHom` if and only if they are equal. -/
@[simp]
theorem torusHom_inj (hσ : Function.Involutive σ) {s t : Rˣ} :
    torusHom R σ hσ s = torusHom R σ hσ t ↔ s = t :=
  (torusHom_injective R σ hσ).eq_iff

/-- A unit maps to `1` under `torusHom` if and only if it is `1`. -/
@[simp]
theorem torusHom_eq_one_iff (hσ : Function.Involutive σ) {t : Rˣ} :
    torusHom R σ hσ t = 1 ↔ t = 1 :=
  map_eq_one_iff _ (torusHom_injective R σ hσ)

/-- The diagonal torus and the unipotent subgroup intersect trivially. -/
theorem torus_inf_unipotentSubgroup_eq_bot :
    torus R σ ⊓ unipotentSubgroup R σ = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgT, hgU⟩
  have hdiag := (mem_torus_iff R σ g).mp hgT
  have htri := mem_unipotentSubgroup_iff.mp hgU
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simpa using htri.apply_diag i
  · simpa [hij] using hdiag hij

/-- Conjugating a root element `unitaryMk σ hσ x z hz` by `torusHom R σ hσ t` rescales `x` by
`t² σ(t⁻¹)` and `z` by `t σ(t)`. -/
@[simp]
theorem torusHom_mul_unipotentHom_unitaryMk_mul_inv (hσ : Function.Involutive σ) (t : Rˣ)
    (x z : R) (hz : z + σ z = x * σ x) :
    torusHom R σ hσ t * unipotentHom R σ (HeisenbergGroup.unitaryMk σ hσ x z hz) *
        (torusHom R σ hσ t)⁻¹ =
      unipotentHom R σ (HeisenbergGroup.unitaryMk σ hσ
        ((t : R) ^ 2 * σ ((t⁻¹ : Rˣ) : R) * x) ((t : R) * σ (t : R) * z) (by
          simp only [map_mul, map_pow, hσ (t : R), hσ ((t⁻¹ : Rˣ) : R)]
          linear_combination (t : R) * σ (t : R) * hz -
            (t : R) * σ (t : R) * x * σ x * map_mul_eq_one σ t.mul_inv -
            (t : R) * (σ (t : R)) ^ 2 * σ ((t⁻¹ : Rˣ) : R) * x * σ x * t.mul_inv)) := by
  rw [← (torusHom R σ hσ).map_inv t]
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torusHom, coe_unipotentHom,
    HeisenbergGroup.coe_toSpecialLinear, HeisenbergGroup.coe_unitaryMk, inv_inv,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [HeisenbergGroup.toMatrix_apply, hσ ((t⁻¹ : Rˣ) : R)]
  · ring
  · ring
  · linear_combination σ (t : R) * σ ((t⁻¹ : Rˣ) : R) * t.mul_inv + map_mul_eq_one σ t.mul_inv
  · ring
  · linear_combination map_mul_eq_one σ t.mul_inv

/-- The diagonal torus normalizes the unipotent subgroup. -/
theorem torus_le_normalizer_unipotentSubgroup (hσ : Function.Involutive σ) :
    torus R σ ≤ Subgroup.normalizer (unipotentSubgroup R σ : Set _) := by
  rw [torus_eq_range_torusHom R σ hσ]
  exact Subgroup.le_normalizer_iff.mpr <| by
    rintro _ ⟨t, rfl⟩ _ ⟨a, rfl⟩
    rw [← HeisenbergGroup.unitaryMk_eta hσ a, torusHom_mul_unipotentHom_unitaryMk_mul_inv]
    exact unipotentHom_mem_unipotentSubgroup _

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

private theorem vec_one_zero_zero_eq_single :
    (![1, 0, 0] : Fin 3 → K) = Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp

/-- An element of the rank-one special isometry group lies in the Borel subgroup if and only if
its `(2, 0)` matrix entry vanishes. -/
theorem mem_borelSubgroup_iff
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ} :
    g ∈ borelSubgroup K σ ↔
      ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  have h2 : ((g : Matrix.SpecialLinearGroup (Fin 3) K) • (![1, 0, 0] : Fin 3 → K)) 2 =
      ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 := by
    rw [Matrix.SpecialLinearGroup.smul_def, smul_eq_mulVec, vec_one_zero_zero_eq_single,
      Matrix.mulVec_single_one, Matrix.col_apply]
  simp [borelSubgroup_def, MulAction.mem_stabilizer_iff, eq_infinity_iff, coe_infinity,
    Subgroup.smul_def, h2]

/-- Every element of the Borel subgroup also has vanishing `(1, 0)` entry, by isotropy of the
first column. -/
theorem apply_one_zero_eq_zero_of_mem_borelSubgroup
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∈ borelSubgroup K σ) :
    ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
  have hg20 := mem_borelSubgroup_iff.mp hg
  have hiso := congrFun (congrFun (Matrix.mem_specialIsometryGroup_iff.mp g.property) 0) 0
  rw [Matrix.mul_mul_apply, dotProduct_typeAGraphConjugator_two_mulVec] at hiso
  have hmul : σ (((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0) *
      ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    neg_eq_zero.mp (by simpa [typeAGraphConjugator_apply, hg20] using hiso)
  exact (mul_eq_zero.mp hmul).elim (map_eq_zero σ).mp id

/-- Every element of the Borel subgroup has nonzero `(0, 0)` entry. -/
theorem apply_zero_zero_ne_zero_of_mem_borelSubgroup
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∈ borelSubgroup K σ) :
    ((g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
  intro hg00
  have hg10 := apply_one_zero_eq_zero_of_mem_borelSubgroup hg
  have hg20 := mem_borelSubgroup_iff.mp hg
  have hdet := g.val.prop
  rw [Matrix.det_eq_zero_of_column_eq_zero 0 fun i ↦ by fin_cases i <;> assumption] at hdet
  exact zero_ne_one hdet

variable (K σ) in
/-- The unipotent subgroup is contained in the Borel subgroup. -/
theorem unipotentSubgroup_le_borelSubgroup : unipotentSubgroup K σ ≤ borelSubgroup K σ := by
  intro g hg
  rw [unipotentSubgroup_def] at hg
  obtain ⟨a, rfl⟩ := hg
  rw [mem_borelSubgroup_iff]
  simp [HeisenbergGroup.toMatrix_apply]

/-- Every image of `unipotentHom` lies in the Borel subgroup. -/
@[simp]
theorem unipotentHom_mem_borelSubgroup (a : HeisenbergGroup.unitarySubgroup σ) :
    unipotentHom K σ a ∈ borelSubgroup K σ :=
  unipotentSubgroup_le_borelSubgroup K σ (unipotentHom_mem_unipotentSubgroup a)

/-- Every diagonal torus element lies in the Borel subgroup. -/
@[simp]
theorem torusHom_mem_borelSubgroup (hσ : Function.Involutive σ) (t : Kˣ) :
    torusHom K σ hσ t ∈ borelSubgroup K σ := by
  rw [mem_borelSubgroup_iff]
  simp

variable (K σ) in
/-- The diagonal torus is contained in the Borel subgroup. -/
theorem torus_le_borelSubgroup : torus K σ ≤ borelSubgroup K σ := by
  intro g hg
  rw [mem_borelSubgroup_iff]
  exact (mem_torus_iff K σ g).mp hg (by decide)

/-- The Weyl element does not lie in the Borel subgroup. -/
@[simp]
theorem weyl_notMem_borelSubgroup : weyl K σ ∉ borelSubgroup K σ := by
  rw [mem_borelSubgroup_iff]
  simp

/-- A `weyl`-conjugated root element lies in the Borel subgroup if and only if the root element is
trivial. -/
@[simp]
theorem weyl_mul_unipotentHom_mul_weyl_mem_borelSubgroup_iff
    (a : HeisenbergGroup.unitarySubgroup σ) :
    weyl K σ * unipotentHom K σ a * weyl K σ ∈ borelSubgroup K σ ↔ a = 1 := by
  constructor
  · intro h
    rw [mem_borelSubgroup_iff, coe_weyl_mul_unipotentHom_mul_weyl] at h
    have hz : (a : HeisenbergGroup K).z = 0 := by simpa using h
    have hx0 : (a : HeisenbergGroup K).x * σ (a : HeisenbergGroup K).x = 0 := by
      have htr := HeisenbergGroup.unitarySubgroup.z_add_map_z a
      rw [hz, map_zero, add_zero] at htr
      exact htr.symm
    have hx : (a : HeisenbergGroup K).x = 0 :=
      (mul_eq_zero.mp hx0).elim id (map_eq_zero σ).mp
    exact HeisenbergGroup.unitarySubgroup.ext hx hz
  · rintro rfl
    simp [one_mem]

/-- For involutive `σ`, every element of the Borel subgroup factors as a diagonal torus element
multiplied by a unipotent element. -/
theorem exists_torusHom_mul_unipotent_of_mem_borelSubgroup (hσ : Function.Involutive σ)
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∈ borelSubgroup K σ) :
    ∃ (t : Kˣ) (u : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ),
      u ∈ unipotentSubgroup K σ ∧ torusHom K σ hσ t * u = g := by
  let t : Kˣ := Units.mk0 _ (apply_zero_zero_ne_zero_of_mem_borelSubgroup hg)
  let u := (torusHom K σ hσ t)⁻¹ * g
  refine ⟨t, u, mem_unipotentSubgroup_iff.mpr ?_, mul_inv_cancel_left _ _⟩
  have hg10 := apply_one_zero_eq_zero_of_mem_borelSubgroup hg
  have hg20 := mem_borelSubgroup_iff.mp hg
  have hu00 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    simp [u, t, ← map_inv, inv_mul_cancel₀ (apply_zero_zero_ne_zero_of_mem_borelSubgroup hg)]
  have hu10 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    simp [u, ← map_inv, hg10]
  have hu20 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    simp [u, ← map_inv, hg20]
  have hiso := Matrix.mem_specialIsometryGroup_iff.mp u.property
  have hu21 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have h01 := congrFun (congrFun hiso 0) 1
    rw [Matrix.mul_mul_apply, dotProduct_typeAGraphConjugator_two_mulVec] at h01
    simpa [typeAGraphConjugator_apply, hu00, hu10, hu20] using h01
  have hu22 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h02 := congrFun (congrFun hiso 0) 2
    rw [Matrix.mul_mul_apply, dotProduct_typeAGraphConjugator_two_mulVec] at h02
    simpa [typeAGraphConjugator_apply, hu00, hu10, hu20] using h02
  have htri :
      ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hu11 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    have hdet := u.val.prop
    rw [Matrix.det_of_isUpperTriangular htri, Fin.prod_univ_three, hu00, hu22] at hdet
    simpa using hdet
  rw [Matrix.isUpperUnitriangular_def]
  exact ⟨htri, fun i ↦ by fin_cases i <;> simp [hu00, hu11, hu22]⟩

/-- For involutive `σ`, the Borel subgroup is the join of the diagonal torus and the unipotent
subgroup. -/
theorem borelSubgroup_eq_sup (hσ : Function.Involutive σ) :
    borelSubgroup K σ = torus K σ ⊔ unipotentSubgroup K σ := by
  refine le_antisymm (fun g hg ↦ ?_)
    (sup_le (torus_le_borelSubgroup K σ) (unipotentSubgroup_le_borelSubgroup K σ))
  obtain ⟨t, u, hu, rfl⟩ := exists_torusHom_mul_unipotent_of_mem_borelSubgroup hσ hg
  exact mul_mem (Subgroup.mem_sup_left (torusHom_mem_torus K σ hσ t)) (Subgroup.mem_sup_right hu)

/-- For involutive `σ`, the Borel subgroup normalizes the unipotent subgroup. -/
theorem borelSubgroup_le_normalizer_unipotentSubgroup (hσ : Function.Involutive σ) :
    borelSubgroup K σ ≤ Subgroup.normalizer (unipotentSubgroup K σ : Set _) := by
  rw [borelSubgroup_eq_sup hσ]
  exact sup_le (torus_le_normalizer_unipotentSubgroup hσ) Subgroup.le_normalizer

/-- Acting on `infinity K σ` by `unipotentHom (unitaryMk σ hσ (σ c.val.2) c.val.1 _) * weyl`
produces the affine isotropic point `point K σ c`. -/
theorem unipotentHom_mul_weyl_smul_infinity (hσ : Function.Involutive σ)
    (c : {c : K × K // c.1 + σ c.1 = σ c.2 * c.2}) :
    (unipotentHom K σ (HeisenbergGroup.unitaryMk σ hσ (σ c.val.2) c.val.1
        (by simpa [hσ c.val.2] using c.property)) * weyl K σ) • infinity K σ =
      point K σ c := by
  apply Subtype.ext
  rw [SubMulAction.val_smul, coe_infinity, coe_point, Subgroup.smul_def, Projectivization.smul_mk]
  have hvec : ((unipotentHom K σ (HeisenbergGroup.unitaryMk σ hσ (σ c.val.2) c.val.1
        (by simpa [hσ c.val.2] using c.property)) * weyl K σ :
        (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) :
      Matrix.SpecialLinearGroup (Fin 3) K) • ![1, 0, 0] = ![c.val.1, c.val.2, 1] := by
    rw [Matrix.SpecialLinearGroup.smul_def, smul_eq_mulVec, vec_one_zero_zero_eq_single,
      Matrix.mulVec_single_one]
    ext i
    fin_cases i <;>
      simp [coe_typeAGraphConjugator_two, HeisenbergGroup.toMatrix_apply, hσ c.val.2]
  simp only [hvec]

/-- The unipotent subgroup meets the Weyl-conjugate of the Borel subgroup trivially. -/
theorem disjoint_unipotentSubgroup_map_conj_weyl_borelSubgroup :
    Disjoint (unipotentSubgroup K σ)
      ((borelSubgroup K σ).map (MulAut.conj (weyl K σ)).toMonoidHom) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨a, rfl⟩ hb
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, weyl_inv,
    weyl_mul_unipotentHom_mul_weyl_mem_borelSubgroup_iff] at hb
  simp [hb]

/-- **Sharp rank-one Bruhat decomposition**: every element outside the Borel subgroup factors as
`u * weyl * b` with `u` unipotent and `b` in the Borel subgroup. -/
theorem exists_unipotent_mul_weyl_mul_borel_of_notMem_borelSubgroup (hσ : Function.Involutive σ)
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∉ borelSubgroup K σ) :
    ∃ u ∈ unipotentSubgroup K σ, ∃ b ∈ borelSubgroup K σ, u * weyl K σ * b = g := by
  have hg' : g • infinity K σ ≠ infinity K σ := by
    simpa [borelSubgroup_def, MulAction.mem_stabilizer_iff] using hg
  obtain ⟨c, hc⟩ := exists_point hg'
  let u : unipotentSubgroup K σ :=
    ⟨unipotentHom K σ (HeisenbergGroup.unitaryMk σ hσ (σ c.val.2) c.val.1
      (by simpa [hσ c.val.2] using c.property)), unipotentHom_mem_unipotentSubgroup _⟩
  have horb : MulAction.orbitRel (unipotentSubgroup K σ) _
      (g • infinity K σ) (weyl K σ • infinity K σ) := by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨u, ?_⟩
    rw [Subgroup.smul_def, smul_smul, unipotentHom_mul_weyl_smul_infinity, hc]
  obtain ⟨u', hu', b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp
    ((orbitRel_smul_iff_mem_doubleCoset_stabilizer (unipotentSubgroup K σ)
      (infinity K σ) g (weyl K σ)).mp horb)
  exact ⟨u', hu', b, by simpa [borelSubgroup_def] using hb, rfl⟩

/-- **Unique sharp rank-one Bruhat decomposition**: every element outside the Borel subgroup
factors uniquely as `u * weyl * b` with `u ∈ unipotentSubgroup` and `b ∈ borelSubgroup`. -/
theorem existsUnique_unipotent_mul_weyl_mul_borel_of_notMem_borelSubgroup
    (hσ : Function.Involutive σ)
    {g : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ}
    (hg : g ∉ borelSubgroup K σ) :
    ∃! p : unipotentSubgroup K σ × borelSubgroup K σ,
      (p.1 : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) *
        weyl K σ * p.2 = g :=
  ((unipotentSubgroup K σ).mul_mul_injective_of_disjoint (borelSubgroup K σ)
    disjoint_unipotentSubgroup_map_conj_weyl_borelSubgroup).existsUnique_iff_exists.mpr <| by
      obtain ⟨u, hu, b, hb, hub⟩ :=
        exists_unipotent_mul_weyl_mul_borel_of_notMem_borelSubgroup hσ hg
      exact ⟨(⟨u, hu⟩, ⟨b, hb⟩), hub⟩

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
    simp [a]
  · let a := HeisenbergGroup.unitaryMk σ hσ 1 (2 : K)⁻¹
      (by rw [map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ h2]; simp)
    refine ⟨unipotentHom K σ a, unipotentHom_mem_unipotentSubgroup a, ?_⟩
    simp [a, h2]

variable (K σ) in
/-- **The rank-one Tits system** `(B, ⟨w⟩)` on the three-dimensional unitary group over any field
`K` with an involutive endomorphism `σ`. -/
def titsSystem (hσ : Function.Involutive σ) :
    TitsSystem ((typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).specialIsometryGroup σ) :=
  TitsSystem.ofRankOneOfSqEqOne (borelSubgroup K σ) (weyl K σ) (by rw [sq, weyl_mul_self])
    (by
      obtain ⟨u, hu, hwu⟩ := exists_mem_unipotentSubgroup_weyl_conj_notMem_borelSubgroup hσ
      exact ⟨u, unipotentSubgroup_le_borelSubgroup K σ hu, hwu⟩)
    (mem_borelSubgroup_or_mem_doubleCoset hσ)

/-- The subgroup `B` of the rank-one unitary Tits system is `borelSubgroup K σ`. -/
@[simp]
theorem titsSystem_subgroupB (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).subgroupB = borelSubgroup K σ :=
  TitsSystem.ofRankOneOfSqEqOne_subgroupB

/-- The subgroup `N` of the rank-one unitary Tits system is generated by `weyl K σ`. -/
@[simp]
theorem titsSystem_subgroupN (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).subgroupN = Subgroup.zpowers (weyl K σ) :=
  TitsSystem.ofRankOneOfSqEqOne_subgroupN

/-- The unique simple reflection of the rank-one unitary Tits system is the class of `weyl K σ`. -/
@[simp]
theorem titsSystem_simple (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).simple =
      {QuotientGroup.mk ⟨weyl K σ, by rw [titsSystem_subgroupN]; exact Subgroup.mem_zpowers _⟩} :=
  TitsSystem.ofRankOneOfSqEqOne_simple

/-- **The rank-one unitary Tits system is irreducible.** -/
theorem isIrreducible_titsSystem (hσ : Function.Involutive σ) :
    (titsSystem K σ hσ).IsIrreducible :=
  TitsSystem.isIrreducible_ofRankOneOfSqEqOne

end Field

end TauCeti.UnitaryRankOne
