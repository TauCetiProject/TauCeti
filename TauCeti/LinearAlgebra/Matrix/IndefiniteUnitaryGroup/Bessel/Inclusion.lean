/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel
import TauCeti.Algebra.Star.SelfAdjoint
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.SiegelTransvection

/-!
# The inclusion of the unitary group of `X₀` in the split unitary group, and frame blocks

Let `R` be a commutative ring with involution and `N ∈ R`. The split form of
`T = diag(1_κ, -N)` (`TauCeti.splitGram ϱ (TauCeti.middleGram N)`) on the basis
`e₀, …, e_{ϱ-1}, x_i (i ∈ κ), z, e*₀, …, e*_{ϱ-1}` is the sum of `ϱ` hyperbolic planes, the
identity form on `X₀ = R^κ` (spanned by the `x_i`) and a line `R z` of norm `-N`. Over `ℂ` with
`N = 1` its unitary group `G` is the real group `G₁` of the second moments of Poincaré series,
of signature `(ϱ + #κ, ϱ + 1)`.

This file embeds the unitary group `U(κ)` of `X₀` in that unitary group and relates it to the
Bessel subgroups of `TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel`. It is the split
model of the graded inclusion `TauCeti.gradedInclusion`, for the reordering of the basis in
`TauCeti.gradedGram_eq_submatrix_splitGram`; the Bessel subgroups `U`, `U⁰` and `H_l` are stated in
the split basis.

* `TauCeti.splitInclusion ϱ N : U(κ) →* G`, written `ι`: `ι(h)` acts by `h` on the
  `x_i` and fixes `e_a`, `z`, `e*_a`. It is injective, and its matrix is unitary for the standard
  form (`TauCeti.coe_splitInclusion_mem_unitaryGroup`), so over `ℝ` or `ℂ` left
  multiplication by `ι(h)` preserves the `ℓ²` operator norm (`CStarRing.norm_mem_unitary_mul`).
* For a unit `N`, the group `H = H_{ϱ+1}` of elements fixing `e_a`, `e*_a` and `z` is exactly
  `ι(U(κ))` (`TauCeti.range_splitInclusion`).
* The unipotent Bessel group `U` meets `ι(U(κ))` only in `1`
  (`TauCeti.splitInclusion_mem_besselU_iff`), hence so does `U⁰ ⊆ U`.
* For a unit `N`, every element fixing the frame `e₀, …, e_{ϱ-1}, z` is `v ι(h)` with `v ∈ U⁰`
  (`TauCeti.exists_mem_besselU0_mul_splitInclusion`); by the previous point the factors
  are unique.
* If `R` has an element `τ` with `τ + star τ = 1` and `N` is a self-adjoint unit, every upper
  unitriangular `(ϱ + 1) × (ϱ + 1)` matrix is the block on the frame of some element of `U`
  (`TauCeti.exists_mem_besselU_submatrix_besselFrame_eq`). The element is the Levi element
  `diag(A, 1, 1, (A⁻¹)ᴴ)` times the Siegel transformation `S(Σ y_a e_a, N⁻¹ z, τ N⁻¹)` of
  `TauCeti.LinearAlgebra.Matrix.UnitaryGroup.SiegelTransvection`, which moves `z` to
  `z + Σ y_a e_a`.

These facts describe the Bessel subgroups of `G₁` through their actions on the frame and on
`X₀`: Bessel functions of a type transform under `U` and under `ι(U(κ))`, and the Haar measures
on `U⁰` and `U` are built from the frame fixers and from the frame blocks.

## References

* W. T. Gan, B. H. Gross and D. Prasad, *Symplectic local root numbers, central critical
  L-values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012), Section 12, for the Bessel subgroups.
* The statements follow the Lean project grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic, PBC), file `src/Lib/DiscreteSeries/Bessel/Basic.lean`,
  declarations `New.toBesselH`, `New.exists_eq_toBesselH`, `New.exists_mem_besselU_frameMatrix_eq`,
  `New.RealPlace.exists_embedH_eq_of_fix_frameCols`, `New.RealPlace.embedH_eq_one_of_mem_besselU0`
  and `New.RealPlace.norm_embedH_mul`. The statements here are over a commutative ring with
  involution and a unit `N` rather than over `ℂ` with `N = 1`, and the proofs are written
  independently.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R] [StarRing R] (ϱ : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The embedding `ι` of the unitary group `U(κ)` of `X₀ = R^κ` into the unitary group of the
split form of `diag(1_κ, -N)`: `ι(h)` acts by `h` on the `x_i` and fixes `e_a`, `z` and `e*_a`. -/
noncomputable def splitInclusion (N : R) :
    unitaryGroup κ R →* unitaryGroupOf (splitGram ϱ (middleGram (κ := κ) N)) :=
  (Unitary.toUnits.comp (UnitaryGroup.sum.comp ((MonoidHom.inr _ _).comp
    (UnitaryGroup.sum.comp ((MonoidHom.inl _ _).comp
      (UnitaryGroup.sum.comp (MonoidHom.inl _ (unitaryGroup Unit R)))))))).codRestrict _
    fun h ↦ by
      have hh (i j : κ) := congrFun₂ (Unitary.coe_star_mul_self h) i j
      simp only [Matrix.mul_apply, star_apply] at hh
      rw [mem_unitaryGroupOf_iff]
      ext (a | (i | ⟨⟩) | a) (b | (j | ⟨⟩) | b) <;>
        simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hh, apply_ite star,
          eq_comm]

variable {ϱ}

/-- The matrix of `ι(h)` is `diag(1, h, 1, 1)` in the blocks `e`, `x`, `z`, `e*`. -/
@[simp]
theorem coe_splitInclusion (N : R) (h : unitaryGroup κ R) :
    ((splitInclusion ϱ N h : GL (BesselIndex ϱ κ) R) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) =
      fromBlocks 1 0 0 (fromBlocks (fromBlocks (h : Matrix κ κ R) 0 0 1) 0 0 1) := by
  simp [splitInclusion]

/-- `ι(h)` fixes every basis vector of floor at most `ϱ`, so it lies in `H = H_{ϱ+1}`. -/
theorem splitInclusion_mem_floorFixingSubgroup (N : R) (h : unitaryGroup κ R) :
    splitInclusion ϱ N h ∈ floorFixingSubgroup ϱ (middleGram N) (ϱ + 1) := by
  rw [mem_floorFixingSubgroup]
  rintro i (b | (j | ⟨⟩) | b) hj
  · rcases i with a | (k | ⟨⟩) | a <;> simp [Matrix.one_apply]
  · simp at hj
  all_goals rcases i with a | (k | ⟨⟩) | a <;> simp [Matrix.one_apply]

/-- `ι` is injective. -/
theorem splitInclusion_injective (N : R) :
    Function.Injective (splitInclusion (κ := κ) ϱ N) := by
  intro h h' hh
  ext i j
  simpa using congrFun₂ (congrArg (fun g : unitaryGroupOf _ ↦
    ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)) hh)
      (.inr (.inl (.inl i))) (.inr (.inl (.inl j)))

variable {N : R}

section Rows

variable {G : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R}
  (hG : star G * splitGram ϱ (middleGram N) * G = splitGram ϱ (middleGram N))
include hG

/-- If an isometry fixes `e_a`, its row at `e*_a` is that of the identity. -/
private theorem row_eStar_of_col_inl {a : Fin ϱ}
    (ha : ∀ i, G i (.inl a) = (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i (.inl a))
    (j : BesselIndex ϱ κ) :
    G (.inr (.inr a)) j = (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inr a)) j := by
  have := congrFun₂ hG (.inl a) j
  rcases j with b | (k | ⟨⟩) | b <;>
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, ha, Matrix.one_apply, apply_ite star,
      eq_comm] using this

/-- If an isometry fixes `e*_a`, its row at `e_a` is that of the identity. -/
private theorem row_inl_of_col_eStar {a : Fin ϱ}
    (ha : ∀ i, G i (.inr (.inr a)) =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i (.inr (.inr a)))
    (j : BesselIndex ϱ κ) :
    G (.inl a) j = (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inl a) j := by
  have := congrFun₂ hG (.inr (.inr a)) j
  rcases j with b | (k | ⟨⟩) | b <;>
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, ha, Matrix.one_apply, apply_ite star,
      eq_comm] using this

/-- If an isometry fixes `z` and `N` is a unit, its row at `z` is that of the identity. -/
private theorem row_z_of_col_z (hN : IsUnit N)
    (hz : ∀ i, G i (BesselIndex.z ϱ κ) =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i (BesselIndex.z ϱ κ))
    (j : BesselIndex ϱ κ) :
    G (BesselIndex.z ϱ κ) j =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (BesselIndex.z ϱ κ) j := by
  have h := congrFun₂ hG (BesselIndex.z ϱ κ) j
  -- Read at `z`, the form gives `-N * G z j = -N * 1 z j`.
  refine hN.neg.mul_left_cancel ?_
  rcases j with b | (k | ⟨⟩) | b
  · simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, apply_ite star] using h
  · simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, apply_ite star] using h
  · simp [hz]
  · simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, apply_ite star] using h

/-- If the rows of an isometry at the `e*_a` and at `z` are those of the identity, its block on
the `x_i` is unitary. -/
private theorem conjTranspose_mul_xBlock
    (hes : ∀ a j, G (.inr (.inr a)) j =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inr a)) j)
    (hz : ∀ j, G (BesselIndex.z ϱ κ) j =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (BesselIndex.z ϱ κ) j) :
    (G.submatrix (fun i : κ ↦ .inr (.inl (.inl i))) fun i ↦ .inr (.inl (.inl i)))ᴴ *
      G.submatrix (fun i : κ ↦ .inr (.inl (.inl i))) (fun i ↦ .inr (.inl (.inl i))) = 1 := by
  ext i j
  have := congrFun₂ hG (.inr (.inl (.inl i))) (.inr (.inl (.inl j)))
  -- `simp` writes the index `z` as `inr (inl (inr ()))`, so unfold the abbreviation.
  simp only [BesselIndex.z] at hz
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, hes, hz, Matrix.one_apply] using this

end Rows

/-- **The fixer of the floors below `ϱ + 1` is the unitary group of `X₀`.** For a unit `N`, the
elements of the unitary group of the split form of `diag(1_κ, -N)` that fix `e_a`, `e*_a` and
`z` are exactly the images `ι(h)` of the unitary matrices `h`. -/
theorem range_splitInclusion (hN : IsUnit N) :
    (splitInclusion ϱ N).range =
      floorFixingSubgroup ϱ (middleGram (κ := κ) N) (ϱ + 1) := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · rintro _ ⟨h, rfl⟩
    exact splitInclusion_mem_floorFixingSubgroup N h
  set G : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R :=
    ((g : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) with hGdef
  have hfix := (mem_floorFixingSubgroup ϱ (middleGram N)).1 hg
  have hG : star G * splitGram ϱ (middleGram N) * G = splitGram ϱ (middleGram N) :=
    mem_unitaryGroupOf_iff.1 g.property
  have he a i := hfix i (.inl a) (by simp)
  have hes' a i := hfix i (.inr (.inr a)) (by simp)
  have hz' i := hfix i (BesselIndex.z ϱ κ) (by simp)
  have hes := fun a ↦ row_eStar_of_col_inl hG (he a)
  have hinl := fun a ↦ row_inl_of_col_eStar hG (hes' a)
  have hz := row_z_of_col_z hG hN hz'
  have hblock := conjTranspose_mul_xBlock hG hes hz
  rw [← star_eq_conjTranspose] at hblock
  refine ⟨⟨_, mem_unitaryGroup_iff'.2 hblock⟩, ?_⟩
  -- `simp` writes the index `z` as `inr (inl (inr ()))`, so unfold the abbreviation.
  simp only [BesselIndex.z] at hz hz'
  ext (a | (i | ⟨⟩) | a) (b | (j | ⟨⟩) | b)
  all_goals simp [← hGdef, he, hes, hes', hinl, hz, hz', Matrix.one_apply]

/-- **The unipotent Bessel group meets `ι(U(κ))` only in `1`**: the diagonal block of an element
of `U` on the `x_i`, which have one level, is the identity. In particular `U⁰ ∩ ι(U(κ)) = 1`. The
high `simp` priority takes precedence over the entrywise expansion `TauCeti.mem_besselU`. -/
@[simp high]
theorem splitInclusion_mem_besselU_iff {a : unitaryGroup κ R} :
    splitInclusion ϱ N a ∈ besselU ϱ (middleGram N) ↔ a = 1 := by
  refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ by rw [h, map_one]; exact one_mem _⟩
  ext i j
  simpa [Matrix.one_apply] using ((mem_besselU ϱ (middleGram N)).1 h).apply_of_eq
    (i := .inr (.inl (.inl i))) (j := .inr (.inl (.inl j))) (by simp)

/-- **Frame fixers in the Bessel unipotent group times the unitary group of `X₀`.** For a unit
`N`, every element `s` of the unitary group of the split form of `diag(1_κ, -N)` that fixes the
frame `e₀, …, e_{ϱ-1}, z` is `v ι(h)` with `v` in `U⁰` (the frame fixers in the unipotent Bessel
group) and `a` a unitary matrix. The factors are unique, by
`TauCeti.splitInclusion_mem_besselU_iff`. -/
theorem exists_mem_besselU0_mul_splitInclusion (hN : IsUnit N)
    {s : unitaryGroupOf (splitGram ϱ (middleGram (κ := κ) N))}
    (hs : s ∈ frameFixingSubgroup ϱ (middleGram N)) :
    ∃ v ∈ besselU0 ϱ (middleGram N), ∃ a, s = v * splitInclusion ϱ N a := by
  set G : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R :=
    ((s : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
  have hfix := (mem_frameFixingSubgroup ϱ (middleGram N)).1 hs
  have hG : star G * splitGram ϱ (middleGram N) * G = splitGram ϱ (middleGram N) :=
    mem_unitaryGroupOf_iff.1 s.property
  have he a i : G i (.inl a) = _ := hfix i (.inl a) ⟨a.castSucc, by simp⟩
  have hz' i : G i (BesselIndex.z ϱ κ) = _ := hfix i _ ⟨Fin.last ϱ, by simp⟩
  have hes := fun a ↦ row_eStar_of_col_inl hG (he a)
  have hz := row_z_of_col_z hG hN hz'
  have hblock := conjTranspose_mul_xBlock hG hes hz
  rw [← star_eq_conjTranspose] at hblock
  set h : unitaryGroup κ R := ⟨_, mem_unitaryGroup_iff'.2 hblock⟩
  refine ⟨s * (splitInclusion ϱ N h)⁻¹, ?_, h, (inv_mul_cancel_right _ _).symm⟩
  -- The matrix of `s ι(h)⁻¹` agrees with `G` outside the columns of the `x_i`, and there it is
  -- `G` times `star h`.
  have hV : ((s * (splitInclusion ϱ N h)⁻¹ : unitaryGroupOf _) :
      GL (BesselIndex ϱ κ) R) =
      (G * fromBlocks 1 0 0 (fromBlocks (fromBlocks (star (h : Matrix κ κ R)) 0 0 1) 0 0 1) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) := by
    rw [← map_inv, ← Unitary.star_eq_inv, Subgroup.coe_mul, Units.val_mul,
      coe_splitInclusion, Unitary.coe_star]
  have hhh : (h : Matrix κ κ R) * star (h : Matrix κ κ R) = 1 := Unitary.coe_mul_star_self h
  -- `simp` writes the index `z` as `inr (inl (inr ()))`, so unfold the abbreviation.
  simp only [BesselIndex.z] at hz hz'
  refine (mem_besselU0 ϱ _).2 ⟨(mem_besselU ϱ (middleGram N)).2
    (blockUnitriangular_of_apply_eq_one_apply_of_not_lt ?_),
    (mem_frameFixingSubgroup ϱ (middleGram N)).2 ?_⟩
  · rw [hV]
    rintro (a | (i | ⟨⟩) | a) (b | (j | ⟨⟩) | b) hlev
    all_goals simp [Matrix.mul_apply, Fintype.sum_sum_type, he, hes, hz, hz', Matrix.one_apply]
      at hlev ⊢
    all_goals try omega
    -- On the `x_i` the matrix is `h * star h = 1`.
    simpa [Matrix.mul_apply, Matrix.one_apply, h] using congrFun₂ hhh i j
  · rw [hV]
    rintro i _ ⟨b, rfl⟩
    induction b using Fin.lastCases <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, he, hz', Matrix.one_apply]

/-- The matrix of `ι(h)` is unitary for the standard hermitian form: `ι(h)` acts by the unitary
matrix `h` on the span of the `x_i` and fixes the other basis vectors. -/
theorem coe_splitInclusion_mem_unitaryGroup (h : unitaryGroup κ R) :
    ((splitInclusion ϱ N h : GL (BesselIndex ϱ κ) R) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) ∈ unitaryGroup (BesselIndex ϱ κ) R := by
  have hh : (h : Matrix κ κ R)ᴴ * h = 1 := Unitary.coe_star_mul_self h
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, coe_splitInclusion]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hh, fromBlocks_one]

section FrameBlock

omit [CommRing R] [StarRing R] [Fintype κ] [DecidableEq κ] in
/-- The split form in blocks, for the decomposition of the basis into the `e_a` and the rest. -/
private theorem splitGram_eq_fromBlocks {R μ : Type*} [Zero R] [One R] (T : Matrix μ μ R) :
    splitGram ϱ T = fromBlocks 0 (fromCols 0 1) (fromRows 0 1) (fromBlocks T 0 0 0) := by
  ext (a | i | a) (b | j | b) <;> simp

omit [StarRing R] in
/-- For a unit `N`, the split form of `diag(1_κ, -N)` is invertible. -/
private theorem isUnit_splitGram_middleGram (hN : IsUnit N) :
    IsUnit (splitGram ϱ (middleGram (κ := κ) N)) := by
  obtain ⟨n, rfl⟩ := hN
  have h : splitGram ϱ (middleGram (κ := κ) (n : R)) *
      splitGram ϱ (middleGram (κ := κ) ((n⁻¹ : Rˣ) : R)) = 1 := by
    ext (a | (i | ⟨⟩) | a) (b | (j | ⟨⟩) | b) <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have := invertibleOfRightInverse _ _ h
  exact isUnit_of_invertible _

/-- The Levi element `diag(A, 1, (A⁻¹)ᴴ)`, acting by `A` on the `e_a` and by `(A⁻¹)ᴴ` on the
`e*_a`. -/
private noncomputable def leviMatrix (A : Matrix (Fin ϱ) (Fin ϱ) R) :
    Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R :=
  fromBlocks A 0 0 (fromBlocks 1 0 0 (A⁻¹)ᴴ)

private theorem leviMatrix_mem {A : Matrix (Fin ϱ) (Fin ϱ) R} (hA : IsUnit A.det) :
    star (leviMatrix (κ := κ) A) * splitGram ϱ (middleGram (κ := κ) N) * leviMatrix A =
      splitGram ϱ (middleGram N) := by
  have h₁ : A⁻¹ * A = 1 := nonsing_inv_mul A hA
  have h₂ : Aᴴ * (A⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h₁, conjTranspose_one]
  rw [star_eq_conjTranspose, splitGram_eq_fromBlocks]
  simp [leviMatrix, fromBlocks_conjTranspose, fromBlocks_multiply, fromCols_mul_fromBlocks,
    fromBlocks_mul_fromRows, h₁, h₂]

omit [Fintype κ] in
/-- The Levi element lies in the unipotent Bessel group when `A` is upper unitriangular. -/
private theorem blockUnitriangular_leviMatrix {A : Matrix (Fin ϱ) (Fin ϱ) R}
    (hA : A.BlockUnitriangular fun a ↦ (a : ℕ)) :
    (leviMatrix (κ := κ) A).BlockUnitriangular splitLevel := by
  have hA' := hA.inv
  refine blockUnitriangular_of_apply_eq_one_apply_of_not_lt ?_
  rintro (a | (i | ⟨⟩) | a) (b | (j | ⟨⟩) | b) hlev
  all_goals simp only [splitLevel_inl, splitLevel_middle, splitLevel_eStar, not_lt] at hlev
  · rcases hlev.lt_or_eq with hlt | heq
    · have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hlt
      simp [leviMatrix, hne, hA.blockTriangular hlt]
    · obtain rfl : b = a := Fin.ext heq
      simp [leviMatrix, hA.apply_of_eq rfl]
  rotate_right
  · have hba : (a : ℕ) ≤ b := by omega
    rcases hba.lt_or_eq with hlt | heq
    · have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hlt
      simp [leviMatrix, hne, hA'.blockTriangular hlt]
    · obtain rfl : a = b := Fin.ext heq
      simp [leviMatrix, hA'.apply_of_eq rfl]
  all_goals simp [leviMatrix, Matrix.one_apply]

/-- The Siegel transformation `S(Σ y_a e_a, n z, c)` is block upper unitriangular for the levels:
it moves `z` by a combination of the `e_a`, and `e*_b` by a combination of `z` and the `e_a`. -/
private theorem blockUnitriangular_siegelTransvection (y : Fin ϱ → R) (n c : R) :
    (Matrix.siegelTransvection (splitGram ϱ (middleGram (κ := κ) N)) (starRingEnd R) 1
      (Sum.elim y 0) (Pi.single (BesselIndex.z ϱ κ) n) c).BlockUnitriangular splitLevel := by
  refine blockUnitriangular_of_apply_eq_one_apply_of_not_lt ?_
  rintro (a | (i | ⟨⟩) | a) (b | (j | ⟨⟩) | b) hlev
  all_goals simp only [splitLevel_inl, splitLevel_middle, splitLevel_eStar, not_lt] at hlev
  all_goals simp [siegelTransvection_def, vecMulVec_apply, vecMul, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply]
  all_goals omega

/-- The conditions under which `S(Σ y_a e_a, N⁻¹ z, τ N⁻¹)` preserves the split form: `Σ y_a e_a`
is isotropic and orthogonal to `z`, and `τ N⁻¹ + star (τ N⁻¹) + ⟨N⁻¹ z, N⁻¹ z⟩ = 0`. -/
private theorem siegelTransvection_conditions {τ : R} (hτ : τ + star τ = 1) (n : Rˣ)
    (hn : star ((n⁻¹ : Rˣ) : R) = (n⁻¹ : Rˣ)) (y : Fin ϱ → R) :
    star (Sum.elim y 0 : BesselIndex ϱ κ → R) ⬝ᵥ
        splitGram ϱ (middleGram (κ := κ) (n : R)) *ᵥ Sum.elim y 0 = 0 ∧
      star (Sum.elim y 0 : BesselIndex ϱ κ → R) ⬝ᵥ splitGram ϱ (middleGram (κ := κ) (n : R)) *ᵥ
        Pi.single (BesselIndex.z ϱ κ) ((n⁻¹ : Rˣ) : R) = 0 ∧
      τ * ((n⁻¹ : Rˣ) : R) + star (τ * ((n⁻¹ : Rˣ) : R)) +
        star (Pi.single (BesselIndex.z ϱ κ) ((n⁻¹ : Rˣ) : R)) ⬝ᵥ
          splitGram ϱ (middleGram (κ := κ) (n : R)) *ᵥ
            Pi.single (BesselIndex.z ϱ κ) ((n⁻¹ : Rˣ) : R) = 0 := by
  refine ⟨by simp [dotProduct, mulVec, Fintype.sum_sum_type],
    by simp [dotProduct, mulVec, Fintype.sum_sum_type], ?_⟩
  simp only [dotProduct, mulVec, Fintype.sum_sum_type]
  simp [hn]
  linear_combination ((n⁻¹ : Rˣ) : R) * hτ

/-- **Every upper unitriangular matrix is the frame block of an element of the unipotent Bessel
group.** Let `R` have an element `τ` with `τ + star τ = 1`, and let `N` be a self-adjoint unit. For
every upper unitriangular `(ϱ + 1) × (ϱ + 1)` matrix `M` there is `u` in the unipotent Bessel
group `U` of the split form of `diag(1_κ, -N)` whose block `(u_{f_a f_b})` on the frame
`f = (e₀, …, e_{ϱ-1}, z)` is `M`. -/
theorem exists_mem_besselU_submatrix_besselFrame_eq {τ : R} (hτ : τ + star τ = 1)
    (hN : IsUnit N) (hNs : star N = N) {M : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) R}
    (hM : M.BlockUnitriangular id) :
    ∃ u ∈ besselU ϱ (middleGram (κ := κ) N),
      ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R).submatrix
        besselFrame besselFrame = M := by
  obtain ⟨n, rfl⟩ := hN
  -- The frame block is `[[A, c], [0, 1]]`; the element is `diag(A, 1, (A⁻¹)ᴴ)` times a Siegel
  -- transformation moving `z` by `Σ y_a e_a`, where `A y = c`.
  set A : Matrix (Fin ϱ) (Fin ϱ) R := M.submatrix Fin.castSucc Fin.castSucc
  set c : Fin ϱ → R := fun a ↦ M a.castSucc (Fin.last ϱ)
  have hA : A.BlockUnitriangular fun a ↦ (a : ℕ) := by
    have h := hM.submatrix (Fin.castSucc_injective ϱ)
    exact blockUnitriangular_iff.2
      ⟨fun i j hij ↦ h.blockTriangular (Fin.castSucc_lt_castSucc_iff.2 hij),
        fun i j hij ↦ h.apply_of_eq (congrArg _ (Fin.ext hij))⟩
  set y : Fin ϱ → R := A⁻¹ *ᵥ c
  have hAy : A *ᵥ y = c := by
    rw [mulVec_mulVec, mul_nonsing_inv A hA.isUnit_det, one_mulVec]
  have hJ : (splitGram ϱ (middleGram (κ := κ) (n : R))).IsHermitian :=
    isHermitian_splitGram (isHermitian_middleGram hNs)
  have hn : star ((n⁻¹ : Rˣ) : R) = (n⁻¹ : Rˣ) :=
    (IsSelfAdjoint.of_mul_eq_one (hNs : IsSelfAdjoint (n : R)) (Units.mul_inv n)).star_eq
  obtain ⟨hx, hxw, hc⟩ := siegelTransvection_conditions (κ := κ) hτ n hn y
  refine ⟨unitaryGroupOf.ofMatrix (isUnit_splitGram_middleGram n.isUnit) (leviMatrix A)
      (leviMatrix_mem hA.isUnit_det) * unitaryGroupOf.siegelTransvection hJ hx hxw hc,
    mul_mem ((mem_besselU ϱ _).2 (by
      rw [unitaryGroupOf.val_ofMatrix]; exact blockUnitriangular_leviMatrix hA))
      ((mem_besselU ϱ _).2 (by
        rw [unitaryGroupOf.val_siegelTransvection]
        exact blockUnitriangular_siegelTransvection _ _ _)), ?_⟩
  have hcancel : (starRingEnd R) ((n⁻¹ : Rˣ) : R) * n = 1 := by
    rw [starRingEnd_apply, hn, Units.inv_mul]
  -- The four blocks of the frame: `A`, the column `A y = c`, and the last row of `1`.
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · simp [leviMatrix, siegelTransvection_def, Matrix.mul_apply, Fintype.sum_sum_type,
      vecMulVec_apply, vecMul, dotProduct, hM.apply_of_eq (rfl : id (Fin.last ϱ) = _)]
  · rename_i b
    have h0 : M (Fin.last ϱ) b.castSucc = 0 := hM.blockTriangular (Fin.castSucc_lt_last b)
    simp [leviMatrix, siegelTransvection_def, Matrix.mul_apply, Fintype.sum_sum_type,
      vecMulVec_apply, vecMul, dotProduct, h0]
  · simpa [leviMatrix, siegelTransvection_def, Matrix.mul_apply, Fintype.sum_sum_type,
      vecMulVec_apply, vecMul, dotProduct, Matrix.one_apply, hcancel, mulVec] using
      congrFun hAy _
  · simp [leviMatrix, siegelTransvection_def, Matrix.mul_apply, Fintype.sum_sum_type,
      vecMulVec_apply, vecMul, dotProduct, Matrix.one_apply, A]

end FrameBlock

end TauCeti
