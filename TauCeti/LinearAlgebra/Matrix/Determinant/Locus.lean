/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination

/-!
# The determinant locus of square matrices

Let `B` be a commutative ring, `π ∈ B` and `N : ℕ`. The *determinant locus*
`Matrix.detLocus n π N` is the set of square matrices `A` over `B` whose determinant is `π ^ N`
times a unit. The column span of such a matrix contains `π ^ N B ^ n`, and right multiplication
by `GL n B` preserves both the locus and the column span. For `B = W(R)`, the Witt vectors of a
perfect ring of characteristic `p`, and `π = p`, this is the matrix locus `V_N` through which Zhu
presents the bounded piece of type `(N, 0, …, 0)` of the Witt vector affine Grassmannian of `GL_n`,
the lattice of `A` being its column span. Over `W(R)` the locus is cut out by the Witt coordinates
of the determinant: `det₀ = ⋯ = det_{N-1} = 0` with `det_N` a unit
(`WittVector.associated_p_pow_iff`).

The locus is cut out by finitely many jets. Suppose that `π` lies in the Jacobson radical of `B`,
as `p` does in `W(R)`, and let `h > N`. Then

* a matrix `A + π ^ h • C` congruent to `A ∈ detLocus n π N` modulo `π ^ h` is `A * γ` for an
  invertible `γ ≡ 1` modulo `π ^ (h - N)`, so it lies in the locus and has the same column span;
* whether `A` lies in the locus depends only on its image modulo `π ^ h`, and the image of the
  locus modulo `π ^ h` is the determinant locus of `B ⧸ (π ^ h)` for the image of `π`.

The strict inequality `h > N` is needed: modulo `π ^ N` the determinants `π ^ N` and `0` both
vanish, so the truncation cannot see the leading unit of the determinant.

## Main definitions

* `Matrix.detLocus n π N`: the `n × n` matrices whose determinant is associated to `π ^ N`.

## Main results

* `Matrix.mem_detLocus_iff`: `A ∈ detLocus n π N` exactly when `A.det = u * π ^ N` for a unit `u`.
* `Matrix.mul_mem_detLocus`, `Matrix.mul_mem_detLocus_iff_of_isUnit_det`: the locus is
  multiplicative in `N`, and stable under multiplication by invertible matrices on either side.
* `Matrix.map_mem_detLocus`: a ring homomorphism maps the locus for `π` into the locus for its
  image.
* `Matrix.exists_mulVec_eq_pow_smul`, `Matrix.pow_smul_top_le_range_mulVecLin`: the column span of
  a matrix in the locus contains `π ^ N B ^ n`.
* `Matrix.exists_add_pow_smul_eq_mul`: for `h > N` and `π` in the Jacobson radical, a matrix
  congruent modulo `π ^ h` to `A ∈ detLocus n π N` is `A * γ` with `γ` invertible and congruent to
  `1` modulo `π ^ (h - N)`.
* `Matrix.map_mk_mem_detLocus_iff`, `Matrix.image_map_mk_detLocus`: membership in the locus is
  detected modulo `π ^ h`, and the locus surjects onto the locus modulo `π ^ h`.
* `Matrix.range_mulVecLin_eq_of_map_mk_eq`: the column span of a matrix in the locus depends only
  on the matrix modulo `π ^ h`.

## References

* X. Zhu, *Affine Grassmannians and the geometric Satake in mixed characteristic*, Ann. of Math.
  185 (2017), §1.1.
-/

public section

open Ideal Pointwise

namespace Matrix

variable (n : Type*) [Fintype n] [DecidableEq n] {B C : Type*} [CommRing B] [CommRing C]

/-- The *determinant locus* `V_N`: the square matrices over `B` whose determinant is `π ^ N` times
a unit of `B`. -/
def detLocus (π : B) (N : ℕ) : Set (Matrix n n B) :=
  {A | Associated (π ^ N) A.det}

variable {n} {π : B} {N M h : ℕ} {A A' : Matrix n n B}

/-- Membership in the determinant locus unfolds to `π ^ N` being associated to the
determinant. -/
theorem mem_detLocus_iff_associated : A ∈ detLocus n π N ↔ Associated (π ^ N) A.det :=
  Iff.rfl

/-- A matrix lies in the determinant locus exactly when its determinant is `π ^ N` times a
unit. -/
theorem mem_detLocus_iff : A ∈ detLocus n π N ↔ ∃ u : Bˣ, A.det = u * π ^ N := by
  simp only [mem_detLocus_iff_associated, Associated, mul_comm]
  exact exists_congr fun _ ↦ eq_comm

/-- The determinant locus for `N = 0` consists of the matrices with invertible determinant. -/
@[simp]
theorem detLocus_zero : detLocus n π 0 = {A | IsUnit A.det} := by
  ext A
  simp [mem_detLocus_iff_associated, Associated.comm, associated_one_iff_isUnit]

/-- The determinant locus is multiplicative: a product of matrices in the loci for `N` and `M`
lies in the locus for `N + M`. -/
theorem mul_mem_detLocus (hA : A ∈ detLocus n π N) (hA' : A' ∈ detLocus n π M) :
    A * A' ∈ detLocus n π (N + M) := by
  rw [mem_detLocus_iff_associated, det_mul, pow_add]
  exact hA.mul_mul hA'

/-- Right multiplication by a matrix with invertible determinant preserves the determinant
locus. -/
theorem mul_mem_detLocus_iff_of_isUnit_det {g : Matrix n n B} (hg : IsUnit g.det) :
    A * g ∈ detLocus n π N ↔ A ∈ detLocus n π N := by
  simp [mem_detLocus_iff_associated, det_mul, associated_mul_isUnit_right_iff hg]

/-- Left multiplication by a matrix with invertible determinant preserves the determinant
locus. -/
theorem mul_mem_detLocus_iff_of_isUnit_det_left {g : Matrix n n B} (hg : IsUnit g.det) :
    g * A ∈ detLocus n π N ↔ A ∈ detLocus n π N := by
  simp [mem_detLocus_iff_associated, det_mul, associated_isUnit_mul_right_iff hg]

/-- Right multiplication by an element of `GL n B` preserves the determinant locus. -/
@[simp]
theorem mul_coe_mem_detLocus_iff (g : GL n B) :
    A * (g : Matrix n n B) ∈ detLocus n π N ↔ A ∈ detLocus n π N :=
  mul_mem_detLocus_iff_of_isUnit_det (isUnit_det_of_invertible _)

/-- Left multiplication by an element of `GL n B` preserves the determinant locus. -/
@[simp]
theorem coe_mul_mem_detLocus_iff (g : GL n B) :
    (g : Matrix n n B) * A ∈ detLocus n π N ↔ A ∈ detLocus n π N :=
  mul_mem_detLocus_iff_of_isUnit_det_left (isUnit_det_of_invertible _)

/-- A ring homomorphism maps the determinant locus for `π` into the determinant locus for the
image of `π`. -/
theorem map_mem_detLocus (f : B →+* C) (hA : A ∈ detLocus n π N) :
    A.map f ∈ detLocus n (f π) N := by
  obtain ⟨u, hu⟩ := mem_detLocus_iff.mp hA
  exact mem_detLocus_iff.mpr ⟨Units.map f u, by simpa [f.map_det] using congrArg f hu⟩

/-- If `A.det = u * π ^ N` with `u` a unit, then the adjugate of `A` divided by `u` is a right
inverse of `A` up to `π ^ N`. -/
theorem mul_smul_adjugate_eq {u : Bˣ} (hu : A.det = u * π ^ N) :
    A * ((↑u⁻¹ : B) • A.adjugate) = π ^ N • 1 := by
  rw [mul_smul_comm, mul_adjugate, hu, smul_smul, Units.inv_mul_cancel_left]

/-- Every vector times `π ^ N` lies in the column span of a matrix in the determinant locus: the
adjugate divided by the unit part of the determinant is an inverse up to `π ^ N`. -/
theorem exists_mulVec_eq_pow_smul (hA : A ∈ detLocus n π N) (v : n → B) :
    ∃ w, A *ᵥ w = π ^ N • v := by
  obtain ⟨u, hu⟩ := mem_detLocus_iff.mp hA
  exact ⟨((↑u⁻¹ : B) • A.adjugate) *ᵥ v, by
    rw [mulVec_mulVec, mul_smul_adjugate_eq hu, smul_mulVec, one_mulVec]⟩

/-- The column span of a matrix in the determinant locus contains `π ^ N B ^ n`. -/
theorem pow_smul_top_le_range_mulVecLin (hA : A ∈ detLocus n π N) :
    π ^ N • (⊤ : Submodule B (n → B)) ≤ LinearMap.range A.mulVecLin := by
  rintro _ ⟨v, -, rfl⟩
  obtain ⟨w, hw⟩ := exists_mulVec_eq_pow_smul hA v
  exact ⟨w, hw⟩

/-- **Finite jets of the determinant locus.** Let `π` lie in the Jacobson radical and `N < h`. A
matrix congruent modulo `π ^ h` to a matrix `A` of the determinant locus `V_N` is `A * γ` for an
invertible matrix `γ` congruent to `1` modulo `π ^ (h - N)`. -/
theorem exists_add_pow_smul_eq_mul (hπ : π ∈ Ring.jacobson B) (hNh : N < h)
    (hA : A ∈ detLocus n π N) (C : Matrix n n B) :
    ∃ γ : GL n B, A + π ^ h • C = A * γ ∧ ∃ D : Matrix n n B, (γ : Matrix n n B) =
      1 + π ^ (h - N) • D := by
  obtain ⟨u, hu⟩ := mem_detLocus_iff.mp hA
  set D := (↑u⁻¹ : B) • A.adjugate * C
  have hγ : IsUnit (1 + π ^ (h - N) • D).det :=
    isUnit_det_one_add_smul (Ideal.pow_mem_of_mem _ hπ _ (Nat.sub_pos_of_lt hNh)) D
  refine ⟨GeneralLinearGroup.mk'' _ hγ, ?_, D, GeneralLinearGroup.val_mk'' _ hγ⟩
  have hAD : A * D = π ^ N • C := by rw [← mul_assoc, mul_smul_adjugate_eq hu, smul_one_mul]
  simp [mul_add, hAD, smul_smul, pow_sub_mul_pow π hNh.le]

/-- For `π` in the Jacobson radical and `N < h`, a matrix congruent modulo `π ^ h` to a matrix of
the determinant locus `V_N` lies in `V_N`. -/
theorem add_pow_smul_mem_detLocus (hπ : π ∈ Ring.jacobson B) (hNh : N < h)
    (hA : A ∈ detLocus n π N) (C : Matrix n n B) : A + π ^ h • C ∈ detLocus n π N := by
  obtain ⟨γ, hγ, -⟩ := exists_add_pow_smul_eq_mul hπ hNh hA C
  rwa [hγ, mul_coe_mem_detLocus_iff]

/-- For `π` in the Jacobson radical and `N < h`, a matrix congruent modulo `π ^ h` to a matrix of
the determinant locus `V_N` has the same column span. -/
theorem range_mulVecLin_add_pow_smul (hπ : π ∈ Ring.jacobson B) (hNh : N < h)
    (hA : A ∈ detLocus n π N) (C : Matrix n n B) :
    LinearMap.range (A + π ^ h • C).mulVecLin = LinearMap.range A.mulVecLin := by
  obtain ⟨γ, hγ, -⟩ := exists_add_pow_smul_eq_mul hπ hNh hA C
  rw [hγ, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (mulVec_surjective_iff_isUnit.mpr γ.isUnit)

/-- For `π` in the Jacobson radical and `N < h`, a matrix lies in the determinant locus `V_N`
exactly when its reduction modulo `π ^ h` lies in the determinant locus of `B ⧸ (π ^ h)` for the
image of `π`. -/
theorem map_mk_mem_detLocus_iff (hπ : π ∈ Ring.jacobson B) (hNh : N < h) :
    A.map (Ideal.Quotient.mk (span {π ^ h})) ∈
        detLocus n (Ideal.Quotient.mk (span {π ^ h}) π) N ↔ A ∈ detLocus n π N := by
  refine ⟨fun hA ↦ ?_, map_mem_detLocus _⟩
  have hπN : π ^ (h - N) ∈ Ring.jacobson B := pow_mem_of_mem _ hπ _ (Nat.sub_pos_of_lt hNh)
  have : IsLocalHom (Ideal.Quotient.mk (span {π ^ h})) := isLocalHom_of_le_jacobson <|
    (span_singleton_le_iff_mem _).mpr (pow_mem_of_mem _ hπ _ (by omega))
  obtain ⟨u, hu⟩ := mem_detLocus_iff.mp hA
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ span {π ^ h})
  obtain ⟨w, rfl⟩ := (isUnit_map_iff (Ideal.Quotient.mk _) v).mp (hv ▸ u.isUnit)
  have hmem : A.det - w * π ^ N ∈ span {π ^ h} := by
    rw [← Ideal.Quotient.eq]
    simpa [RingHom.map_det, hv] using hu
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  have hdet : A.det = π ^ N * (w * (1 + π ^ (h - N) * (↑w⁻¹ * c))) := by
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, ← pow_sub_mul_pow π hNh.le]
    linear_combination (-(π ^ (h - N) * π ^ N * c)) * w.mul_inv
  rw [mem_detLocus_iff_associated, hdet]
  refine associated_mul_unit_right _ _ (w.isUnit.mul (isUnit_of_sub_one_mem_jacobson _ ?_))
  rw [add_sub_cancel_left]
  exact mul_mem_right _ _ hπN

/-- For `π` in the Jacobson radical and `N < h`, the reduction modulo `π ^ h` of the determinant
locus `V_N` of `B` is the determinant locus of `B ⧸ (π ^ h)` for the image of `π`. -/
theorem image_map_mk_detLocus (hπ : π ∈ Ring.jacobson B) (hNh : N < h) :
    (fun A : Matrix n n B ↦ A.map (Ideal.Quotient.mk (span {π ^ h}))) '' detLocus n π N =
      detLocus n (Ideal.Quotient.mk (span {π ^ h}) π) N := by
  refine Set.Subset.antisymm (Set.image_subset_iff.mpr fun A ↦ map_mem_detLocus _) fun A hA ↦ ?_
  choose c hc using fun i j ↦ Ideal.Quotient.mk_surjective (A i j)
  have hcA : (of c).map (Ideal.Quotient.mk (span {π ^ h})) = A := ext fun i j ↦ by simp [hc]
  exact ⟨of c, (map_mk_mem_detLocus_iff hπ hNh).mp (hcA ▸ hA), hcA⟩

/-- **The column span is determined by a finite jet.** For `π` in the Jacobson radical and
`N < h`, the column span of a matrix in the determinant locus `V_N` depends only on the matrix
modulo `π ^ h`. -/
theorem range_mulVecLin_eq_of_map_mk_eq (hπ : π ∈ Ring.jacobson B) (hNh : N < h)
    (hA : A ∈ detLocus n π N)
    (hAA' : A'.map (Ideal.Quotient.mk (span {π ^ h})) = A.map (Ideal.Quotient.mk (span {π ^ h}))) :
    LinearMap.range A'.mulVecLin = LinearMap.range A.mulVecLin := by
  obtain ⟨C, rfl⟩ := map_mk_eq_map_mk_iff.mp hAA'
  exact range_mulVecLin_add_pow_smul hπ hNh hA C

end Matrix
