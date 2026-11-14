/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.CauchySchwarz

/-!
# Completely bounded maps between C⋆-algebras

For a complex-linear map `φ : A → B` between C⋆-algebras and `n : ℕ`, the amplification
`φₙ : M_n(A) → M_n(B)` applies `φ` entrywise, where `M_n(A) = CStarMatrix (Fin n) (Fin n) A`
carries its C⋆-norm (the operator norm on the Hilbert `A`-module `Aⁿ`), never an entrywise norm.
The map `φ` is **completely bounded** when the amplifications are uniformly bounded, and its
**cb norm** `‖φ‖_cb = sup_n ‖φₙ‖` is the least uniform bound.

This file treats C⋆-algebras only, with the operator-space structure they carry through
`CStarMatrix`; abstract operator spaces are not used.

## Main declarations

* `LinearMap.IsCompletelyBounded`, `LinearMap.cbNorm`: complete boundedness and the cb norm, with
  `LinearMap.norm_map_le_cbNorm_mul` (`‖φₙ x‖ ≤ ‖φ‖_cb ‖x‖`, for matrices over any finite index
  type), `LinearMap.cbNorm_le_iff`, and `LinearMap.norm_apply_le_cbNorm_mul`
  (`‖φ a‖ ≤ ‖φ‖_cb ‖a‖`, the level-one comparison).
* `LinearMap.cbNorm_zero`, `LinearMap.cbNorm_add_le`, `LinearMap.cbNorm_smul`,
  `LinearMap.cbNorm_neg`, `LinearMap.cbNorm_sub_le`, `LinearMap.cbNorm_eq_zero_iff`: the cb norm
  is a norm on the completely bounded maps.
* `LinearMap.IsCompletelyBounded.comp`, `LinearMap.cbNorm_comp_le`: composition, and
  `LinearMap.cbNorm_id`.
* `NonUnitalStarAlgHom.isCompletelyBounded`, `NonUnitalStarAlgHom.cbNorm_le_one`: star
  homomorphisms are complete contractions.
* `CStarMatrix.isCompletelyBounded_transposeₗ`, `CStarMatrix.cbNorm_transposeₗ`: the transpose on
  `M_n(ℂ)` is completely bounded with cb norm `n`.

## Implementation notes

For the transpose on `M_n(ℂ)` with matrix units `E i j`, the upper bound `n` at every level comes
from writing the transpose as `y ↦ ∑ E i j * y * E i j` and applying
`Finset.norm_sum_mul_mul_sq_le`. For `n ≥ 1`, the lower bound comes from level `n`: the
amplification sends the flip unitary `[E l k]_{k l}`, of norm `1`, to `[E k l]_{k l}`, which is
`n` times a rank-one projection.

## References

* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3 and Exercise 3.11.
* G. Pisier, *Introduction to Operator Space Theory*, §1.2.
-/

public section

open scoped ComplexOrder

namespace LinearMap

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A linear map between C⋆-algebras is **completely bounded** when its matrix amplifications
are uniformly bounded, for the C⋆-norms of `CStarMatrix` rather than an entrywise matrix
norm. -/
def IsCompletelyBounded (φ : A →ₗ[ℂ] B) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖

/-- The **cb norm** `‖φ‖_cb = sup_n ‖φₙ‖` of a linear map between C⋆-algebras: the least
uniform bound on the norms of its matrix amplifications. It is `0` when `φ` is not completely
bounded; the results about it assume `IsCompletelyBounded φ` where needed. -/
noncomputable def cbNorm (φ : A →ₗ[ℂ] B) : ℝ :=
  sInf {C | 0 ≤ C ∧ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖}

theorem isCompletelyBounded_def {φ : A →ₗ[ℂ] B} :
    IsCompletelyBounded φ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖ :=
  (Iff.rfl)

theorem cbNorm_def (φ : A →ₗ[ℂ] B) :
    cbNorm φ =
      sInf {C | 0 ≤ C ∧ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖} :=
  (rfl)

/-- The cb norm of a map that is not completely bounded is the junk value `0`. -/
theorem cbNorm_of_not_isCompletelyBounded {φ : A →ₗ[ℂ] B} (hφ : ¬IsCompletelyBounded φ) :
    cbNorm φ = 0 := by
  rw [cbNorm_def]
  exact (congrArg sInf (Set.eq_empty_of_forall_notMem fun C hC => hφ ⟨C, hC⟩)).trans
    Real.sInf_empty

@[simp, grind .]
theorem cbNorm_nonneg (φ : A →ₗ[ℂ] B) : 0 ≤ cbNorm φ :=
  Real.sInf_nonneg fun _ h => h.1

/-- A uniform bound on the amplifications bounds the cb norm. -/
theorem cbNorm_le_of_bound {φ : A →ₗ[ℂ] B} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ c * ‖x‖) : cbNorm φ ≤ c :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hc, h⟩

/-- The cb norm bounds the amplifications of a completely bounded map at the levels `Fin n`. -/
private theorem norm_map_le_cbNorm_mul_fin {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) : ‖x.map φ‖ ≤ cbNorm φ * ‖x‖ := by
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · rw [← hx, norm_eq_zero.mp hx.symm]
    simp [← CStarMatrix.mapₗ_apply]
  rw [← div_le_iff₀ hx]
  obtain ⟨c, hc, hb⟩ := hφ
  exact le_csInf ⟨c, hc, hb⟩ fun d hd => (div_le_iff₀ hx).mpr (hd.2 n x)

/-- The cb norm bounds every amplification of a completely bounded map, for matrices over any
finite index type. -/
theorem norm_map_le_cbNorm_mul {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) {κ : Type*}
    [Fintype κ] (x : CStarMatrix κ κ A) : ‖x.map φ‖ ≤ cbNorm φ * ‖x‖ := by
  classical
  let e := Fintype.equivFin κ
  have hmap : CStarMatrix.reindexₐ ℂ B e (x.map φ) = (CStarMatrix.reindexₐ ℂ A e x).map φ := by
    simpa using CStarMatrix.mapₗ_reindexₐ (M := x) (e := e) φ
  rw [← StarAlgEquiv.norm_map (CStarMatrix.reindexₐ ℂ B e), hmap,
    ← StarAlgEquiv.norm_map (CStarMatrix.reindexₐ ℂ A e) x]
  exact norm_map_le_cbNorm_mul_fin hφ _

/-- For a completely bounded map, the cb norm is at most `c ≥ 0` exactly when `c` bounds every
amplification. -/
theorem cbNorm_le_iff {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) {c : ℝ} (hc : 0 ≤ c) :
    cbNorm φ ≤ c ↔ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ c * ‖x‖ :=
  ⟨fun h n x => (norm_map_le_cbNorm_mul hφ x).trans (by gcongr), cbNorm_le_of_bound hc⟩

/-- Complete boundedness only needs some uniform bound on the amplifications. -/
theorem isCompletelyBounded_iff_exists_bound {φ : A →ₗ[ℂ] B} :
    IsCompletelyBounded φ ↔
      ∃ C : ℝ, ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖ := by
  refine ⟨fun ⟨C, _, h⟩ => ⟨C, h⟩, fun ⟨C, h⟩ => ⟨max C 0, le_max_right _ _, fun n x => ?_⟩⟩
  exact (h n x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- The level-one comparison `‖φ a‖ ≤ ‖φ‖_cb ‖a‖` for a completely bounded map. -/
theorem norm_apply_le_cbNorm_mul {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) (a : A) :
    ‖φ a‖ ≤ cbNorm φ * ‖a‖ := by
  let eA := (CStarMatrix.toOneByOne (Fin 1) ℂ A).toNonUnitalStarAlgHom
  let eB := (CStarMatrix.toOneByOne (Fin 1) ℂ B).toNonUnitalStarAlgHom
  have hmap : eB (φ a) = (eA a).map φ := by
    ext i j
    -- Mathlib's `StarAlgEquiv.toNonUnitalStarAlgHom_apply` does not rewrite here: the
    -- `Add`/`Mul`/`SMul` instances `toOneByOne` is stated with differ syntactically from those
    -- `toNonUnitalStarAlgHom` expects, so we unfold the coercion definitionally.
    change CStarMatrix.toOneByOne (Fin 1) ℂ B (φ a) i j =
      φ (CStarMatrix.toOneByOne (Fin 1) ℂ A a i j)
    simp
  rw [← NonUnitalStarAlgHom.norm_map eB (CStarMatrix.toOneByOne (Fin 1) ℂ B).injective, hmap,
    ← NonUnitalStarAlgHom.norm_map eA (CStarMatrix.toOneByOne (Fin 1) ℂ A).injective a]
  exact norm_map_le_cbNorm_mul hφ _

section Zero

@[simp, grind .]
theorem isCompletelyBounded_zero : IsCompletelyBounded (0 : A →ₗ[ℂ] B) :=
  ⟨0, le_rfl, fun n x => by simp⟩

@[simp, grind =]
theorem cbNorm_zero : cbNorm (0 : A →ₗ[ℂ] B) = 0 :=
  le_antisymm (cbNorm_le_of_bound le_rfl fun n x => by simp) (cbNorm_nonneg _)

/-- A completely bounded map has cb norm `0` exactly when it is zero. -/
@[simp, grind =]
theorem cbNorm_eq_zero_iff {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) :
    cbNorm φ = 0 ↔ φ = 0 := by
  refine ⟨fun h => LinearMap.ext fun a => norm_le_zero_iff.mp ?_, fun h => h ▸ cbNorm_zero⟩
  simpa [h] using norm_apply_le_cbNorm_mul hφ a

end Zero

section Add

private theorem norm_map_add_le {φ ψ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ)
    (hψ : IsCompletelyBounded ψ) {n : ℕ} (x : CStarMatrix (Fin n) (Fin n) A) :
    ‖x.map ⇑(φ + ψ)‖ ≤ (cbNorm φ + cbNorm ψ) * ‖x‖ := by
  rw [CStarMatrix.map_add_linearMap, add_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_map_le_cbNorm_mul hφ x) (norm_map_le_cbNorm_mul hψ x))

@[grind ←]
theorem IsCompletelyBounded.add {φ ψ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ)
    (hψ : IsCompletelyBounded ψ) : IsCompletelyBounded (φ + ψ) :=
  ⟨_, add_nonneg (cbNorm_nonneg φ) (cbNorm_nonneg ψ), fun _ x => norm_map_add_le hφ hψ x⟩

/-- The cb norm satisfies the triangle inequality on completely bounded maps. -/
theorem cbNorm_add_le {φ ψ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ)
    (hψ : IsCompletelyBounded ψ) : cbNorm (φ + ψ) ≤ cbNorm φ + cbNorm ψ :=
  cbNorm_le_of_bound (add_nonneg (cbNorm_nonneg φ) (cbNorm_nonneg ψ)) fun _ x =>
    norm_map_add_le hφ hψ x

end Add

section SMul

@[grind ←]
theorem IsCompletelyBounded.smul {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) (c : ℂ) :
    IsCompletelyBounded (c • φ) :=
  ⟨‖c‖ * cbNorm φ, mul_nonneg (norm_nonneg c) (cbNorm_nonneg φ), fun n x => by
    rw [CStarMatrix.map_smul_linearMap, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_map_le_cbNorm_mul hφ x) (norm_nonneg c)⟩

private theorem cbNorm_smul_le {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) (c : ℂ) :
    cbNorm (c • φ) ≤ ‖c‖ * cbNorm φ :=
  cbNorm_le_of_bound (mul_nonneg (norm_nonneg c) (cbNorm_nonneg φ)) fun n x => by
    rw [CStarMatrix.map_smul_linearMap, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_map_le_cbNorm_mul hφ x) (norm_nonneg c)

/-- The cb norm is absolutely homogeneous. -/
@[simp, grind =]
theorem cbNorm_smul (c : ℂ) (φ : A →ₗ[ℂ] B) : cbNorm (c • φ) = ‖c‖ * cbNorm φ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hinv (ψ : A →ₗ[ℂ] B) : c⁻¹ • c • ψ = ψ := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  by_cases hφ : IsCompletelyBounded φ
  · refine le_antisymm (cbNorm_smul_le hφ c) ?_
    have := cbNorm_smul_le (hφ.smul c) c⁻¹
    rw [hinv, norm_inv, inv_mul_eq_div, le_div_iff₀ (norm_pos_iff.mpr hc), mul_comm] at this
    exact this
  · have hcφ : ¬IsCompletelyBounded (c • φ) := fun h => hφ (hinv φ ▸ h.smul c⁻¹)
    rw [cbNorm_of_not_isCompletelyBounded hφ, cbNorm_of_not_isCompletelyBounded hcφ, mul_zero]

@[simp, grind =]
theorem isCompletelyBounded_neg {φ : A →ₗ[ℂ] B} :
    IsCompletelyBounded (-φ) ↔ IsCompletelyBounded φ :=
  ⟨fun h => by simpa using h.smul (-1), fun h => by simpa using h.smul (-1)⟩

@[simp, grind =]
theorem cbNorm_neg (φ : A →ₗ[ℂ] B) : cbNorm (-φ) = cbNorm φ := by
  simpa using cbNorm_smul (-1) φ

@[grind ←]
theorem IsCompletelyBounded.sub {φ ψ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ)
    (hψ : IsCompletelyBounded ψ) : IsCompletelyBounded (φ - ψ) :=
  sub_eq_add_neg φ ψ ▸ hφ.add (isCompletelyBounded_neg.mpr hψ)

theorem cbNorm_sub_le {φ ψ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ)
    (hψ : IsCompletelyBounded ψ) : cbNorm (φ - ψ) ≤ cbNorm φ + cbNorm ψ := by
  simpa [sub_eq_add_neg] using cbNorm_add_le hφ (isCompletelyBounded_neg.mpr hψ)

end SMul

section Comp

@[simp, grind .]
theorem isCompletelyBounded_id : IsCompletelyBounded (LinearMap.id : A →ₗ[ℂ] A) :=
  ⟨1, zero_le_one, fun n x => by simp⟩

/-- The identity map has cb norm at most `1`. -/
theorem cbNorm_id_le_one : cbNorm (LinearMap.id : A →ₗ[ℂ] A) ≤ 1 :=
  cbNorm_le_of_bound zero_le_one fun n x => by simp

/-- The identity map of a nontrivial C⋆-algebra has cb norm `1`. -/
@[simp, grind =]
theorem cbNorm_id [Nontrivial A] : cbNorm (LinearMap.id : A →ₗ[ℂ] A) = 1 := by
  refine le_antisymm cbNorm_id_le_one ?_
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have := norm_apply_le_cbNorm_mul isCompletelyBounded_id a
  rwa [LinearMap.id_apply, le_mul_iff_one_le_left (norm_pos_iff.mpr ha)] at this

private theorem norm_map_comp_le {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsCompletelyBounded ψ)
    (hφ : IsCompletelyBounded φ) {n : ℕ} (x : CStarMatrix (Fin n) (Fin n) A) :
    ‖x.map (ψ ∘ₗ φ)‖ ≤ cbNorm ψ * cbNorm φ * ‖x‖ := by
  have : x.map (ψ ∘ₗ φ) = (x.map φ).map ψ := by ext; simp
  rw [this, mul_assoc]
  exact (norm_map_le_cbNorm_mul hψ _).trans
    (mul_le_mul_of_nonneg_left (norm_map_le_cbNorm_mul hφ x) (cbNorm_nonneg ψ))

/-- The composite of completely bounded maps is completely bounded. -/
@[grind ←]
theorem IsCompletelyBounded.comp {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsCompletelyBounded ψ)
    (hφ : IsCompletelyBounded φ) : IsCompletelyBounded (ψ ∘ₗ φ) :=
  ⟨_, mul_nonneg (cbNorm_nonneg ψ) (cbNorm_nonneg φ), fun _ x => norm_map_comp_le hψ hφ x⟩

/-- The cb norm is submultiplicative. -/
theorem cbNorm_comp_le {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsCompletelyBounded ψ)
    (hφ : IsCompletelyBounded φ) : cbNorm (ψ ∘ₗ φ) ≤ cbNorm ψ * cbNorm φ :=
  cbNorm_le_of_bound (mul_nonneg (cbNorm_nonneg ψ) (cbNorm_nonneg φ)) fun _ x =>
    norm_map_comp_le hψ hφ x

end Comp

end LinearMap

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

private theorem norm_map_le (π : F) {n : ℕ} (x : CStarMatrix (Fin n) (Fin n) A) :
    ‖x.map (π : A →ₗ[ℂ] B)‖ ≤ 1 * ‖x‖ := by
  simpa using norm_apply_le (CStarMatrix.mapₙₐ (n := Fin n) (ofClass π)) x

/-- A star homomorphism of C⋆-algebras is completely bounded. -/
theorem isCompletelyBounded (π : F) : (π : A →ₗ[ℂ] B).IsCompletelyBounded :=
  ⟨1, zero_le_one, fun _ x => norm_map_le π x⟩

/-- A star homomorphism of C⋆-algebras is a complete contraction. -/
theorem cbNorm_le_one (π : F) : (π : A →ₗ[ℂ] B).cbNorm ≤ 1 :=
  LinearMap.cbNorm_le_of_bound zero_le_one fun _ x => norm_map_le π x

end NonUnitalStarAlgHom

namespace CStarMatrix

section Transpose

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The matrix unit `E i j` of `M_n(ℂ)`. -/
private def matrixUnit [DecidableEq n] (i j : n) : CStarMatrix n n ℂ :=
  ofMatrix (Matrix.single i j 1)

omit [Fintype n] in
private theorem star_matrixUnit [DecidableEq n] (i j : n) :
    star (matrixUnit i j) = matrixUnit j i := by
  ext r s
  simp [matrixUnit, star_apply, Matrix.single_apply, and_comm, apply_ite]

/-- The transpose on `M_n(ℂ)` is `y ↦ ∑ E i j * y * E i j`. -/
private theorem transposeₗ_eq_sum [DecidableEq n] (y : CStarMatrix n n ℂ) :
    transposeₗ ℂ y = ∑ p : n × n, matrixUnit p.1 p.2 * y * matrixUnit p.1 p.2 := by
  ext r s
  simp [sum_apply, mul_apply, matrixUnit, Matrix.single_apply, Fintype.sum_prod_type, ite_and]

/-- The block-diagonal matrix `diag(E i j, …, E i j)` in `M_m(M_n(ℂ))`. -/
private def blockMatrixUnit (m : Type*) [Fintype m] [DecidableEq m] [DecidableEq n] (i j : n) :
    CStarMatrix m m (CStarMatrix n n ℂ) :=
  ofMatrix (Matrix.scalar m (matrixUnit i j))

private theorem blockMatrixUnit_apply [DecidableEq m] [DecidableEq n] (i j : n) (k l : m) :
    blockMatrixUnit m i j k l = if k = l then matrixUnit i j else 0 := by
  simp [blockMatrixUnit, Matrix.diagonal_apply]

private theorem star_blockMatrixUnit [DecidableEq m] [DecidableEq n] (i j : n) :
    star (blockMatrixUnit m i j) = blockMatrixUnit m j i := by
  ext k l : 1
  simp only [star_apply, blockMatrixUnit_apply, eq_comm (a := l)]
  split_ifs <;> simp only [star_matrixUnit, star_zero]

private theorem blockMatrixUnit_apply_apply [DecidableEq m] [DecidableEq n] (i j : n) (k l : m)
    (r s : n) : blockMatrixUnit m i j k l r s = if k = l ∧ i = r ∧ j = s then 1 else 0 := by
  rw [blockMatrixUnit_apply]
  split_ifs <;> simp_all [matrixUnit, zero_apply]

/-- The amplification of the transpose is `x ↦ ∑ diag(E i j) * x * diag(E i j)`. -/
private theorem map_transposeₗ_eq_sum [DecidableEq m] [DecidableEq n]
    (x : CStarMatrix m m (CStarMatrix n n ℂ)) :
    x.map (transposeₗ ℂ) =
      ∑ p : n × n, blockMatrixUnit m p.1 p.2 * x * blockMatrixUnit m p.1 p.2 := by
  ext k l : 2
  rw [sum_apply, map_apply, transposeₗ_eq_sum]
  simp [mul_apply, blockMatrixUnit_apply]

private theorem sum_blockMatrixUnit_mul_star [DecidableEq m] [DecidableEq n] :
    ∑ p : n × n, blockMatrixUnit m p.1 p.2 * star (blockMatrixUnit m p.1 p.2) =
      (Fintype.card n : ℂ) • 1 := by
  ext k l r s
  simp [sum_apply, mul_apply, star_apply, blockMatrixUnit_apply_apply, one_apply,
    Fintype.sum_prod_type, ite_and]
  by_cases hkl : k = l <;> by_cases hrs : r = s <;> simp [hkl, hrs, one_apply, eq_comm]

private theorem sum_star_blockMatrixUnit_mul [DecidableEq m] [DecidableEq n] :
    ∑ p : n × n, star (blockMatrixUnit m p.1 p.2) * blockMatrixUnit m p.1 p.2 =
      (Fintype.card n : ℂ) • 1 := by
  simp_rw [star_blockMatrixUnit]
  rw [← sum_blockMatrixUnit_mul_star (m := m)]
  refine Fintype.sum_equiv (Equiv.prodComm n n) _ _ fun p => ?_
  simp [star_blockMatrixUnit]

/-- Every amplification of the transpose on `M_n(ℂ)` is bounded by `n`. -/
theorem norm_map_transposeₗ_le (x : CStarMatrix m m (CStarMatrix n n ℂ)) :
    ‖x.map (transposeₗ ℂ)‖ ≤ Fintype.card n * ‖x‖ := by
  classical
  have h := Finset.norm_sum_mul_mul_sq_le Finset.univ
    (fun p : n × n => blockMatrixUnit m p.1 p.2) (fun p : n × n => blockMatrixUnit m p.1 p.2) x
  rw [sum_blockMatrixUnit_mul_star, sum_star_blockMatrixUnit_mul, ← map_transposeₗ_eq_sum] at h
  have hn : ‖(Fintype.card n : ℂ) • (1 : CStarMatrix m m (CStarMatrix n n ℂ))‖ ≤
      Fintype.card n := by
    refine (norm_smul_le (Fintype.card n : ℂ) (1 : CStarMatrix m m (CStarMatrix n n ℂ))).trans ?_
    simpa using mul_le_of_le_one_right (Nat.cast_nonneg (Fintype.card n))
      (CStarRing.norm_one_le (E := CStarMatrix m m (CStarMatrix n n ℂ)))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans ?_)
  calc _ ≤ (Fintype.card n : ℝ) * ‖x‖ ^ 2 * Fintype.card n := by gcongr
    _ = (Fintype.card n * ‖x‖) ^ 2 := by ring

/-- The flip unitary `[E l k]_{k l}` in `M_n(M_n(ℂ))`. -/
private def flipMatrix (n : Type*) [DecidableEq n] :
    CStarMatrix n n (CStarMatrix n n ℂ) :=
  ofMatrix (Matrix.of fun k l => matrixUnit l k)

omit [Fintype n] in
private theorem flipMatrix_apply_apply [DecidableEq n] (k l r s : n) :
    flipMatrix n k l r s = if l = r ∧ k = s then 1 else 0 := by
  simp [flipMatrix, matrixUnit, Matrix.single_apply]

private theorem flipMatrix_mem_unitary [DecidableEq n] :
    flipMatrix n ∈ unitary (CStarMatrix n n (CStarMatrix n n ℂ)) := by
  have hstar : star (flipMatrix n) = flipMatrix n := by
    ext k l r s
    simp [star_apply, flipMatrix_apply_apply, and_comm, apply_ite]
  rw [Unitary.mem_iff, hstar, and_self]
  ext k l r s
  simp [sum_apply, mul_apply, flipMatrix_apply_apply, one_apply, ite_and]
  by_cases hkl : k = l <;> by_cases hrs : r = s <;> simp [hkl, hrs, one_apply, eq_comm]

private theorem norm_map_transposeₗ_flipMatrix [DecidableEq n] [Nonempty n] :
    ‖(flipMatrix n).map (transposeₗ ℂ)‖ = Fintype.card n := by
  set P := (flipMatrix n).map (transposeₗ ℂ)
  have hP_apply (k l r s : n) : P k l r s = if k = r ∧ l = s then 1 else 0 := by
    simp [P, flipMatrix_apply_apply, and_comm]
  have hstar : star P = P := by
    ext k l r s
    simp [star_apply, hP_apply, and_comm, apply_ite]
  have hsq : P * P = (Fintype.card n : ℂ) • P := by
    ext k l r s
    simp [sum_apply, mul_apply, hP_apply, ite_and]
    split_ifs <;> simp
  obtain ⟨k₀⟩ := ‹Nonempty n›
  have hP : P ≠ 0 := fun h => by
    simpa [hP_apply, zero_apply] using congr($h k₀ k₀ k₀ k₀)
  have hnorm : ‖P‖ * ‖P‖ = Fintype.card n * ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self, hstar, hsq, norm_smul, Complex.norm_natCast]
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hP) hnorm

/-- The transpose on `M_n(ℂ)` is completely bounded. -/
@[simp, grind .]
theorem isCompletelyBounded_transposeₗ (n : Type*) [Fintype n] :
    (transposeₗ ℂ : CStarMatrix n n ℂ →ₗ[ℂ] _).IsCompletelyBounded :=
  ⟨Fintype.card n, by positivity, fun _ x => norm_map_transposeₗ_le x⟩

/-- **The transpose on `M_n(ℂ)` has cb norm `n`.** -/
@[simp, grind =]
theorem cbNorm_transposeₗ (n : Type*) [Fintype n] :
    (transposeₗ ℂ : CStarMatrix n n ℂ →ₗ[ℂ] _).cbNorm = Fintype.card n := by
  classical
  refine le_antisymm (LinearMap.cbNorm_le_of_bound (by positivity) fun _ x =>
    norm_map_transposeₗ_le x) ?_
  cases isEmpty_or_nonempty n
  · simp
  have hU := CStarRing.norm_of_mem_unitary (flipMatrix_mem_unitary (n := n))
  have := LinearMap.norm_map_le_cbNorm_mul (isCompletelyBounded_transposeₗ n) (flipMatrix n)
  rwa [norm_map_transposeₗ_flipMatrix, hU, mul_one] at this

end Transpose

end CStarMatrix
