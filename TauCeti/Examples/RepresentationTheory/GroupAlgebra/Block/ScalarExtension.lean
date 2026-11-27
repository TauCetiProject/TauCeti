/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.PrincipalBlock
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter.ScalarExtension
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.ScalarExtension

/-!
# Blocks of `S₃` and `C₃` in characteristic `2` under scalar extension

The scalar-extension Check of ModularCharactersAndBlocks §6.2, along `𝔽₄ ⊆ 𝔽₂^alg`, where `𝔽₄`
splits `S₃` and all its subgroups.

* **`S₃`.** The blocks `e₀ = 1 + ρ + ρ²` and `e₁ = ρ + ρ²` of `𝔽₂[S₃]` have central characters:
  the augmentation for `e₀`, with values `(1, 0, 1)` on the class sums of `1`, of the `3`-cycles
  and of the transpositions, and for `e₁` the character with values `(1, 1, 0)`, by which the class
  sums act on the line `Z(𝔽₂[S₃]) e₁ = 𝔽₂ e₁`. So over every field `K` of characteristic `2` the
  images of `e₀` and `e₁` in `K[S₃]` are blocks with central characters taking these values, and
  along every field homomorphism `K → K'`, for instance `𝔽₄ → 𝔽₂^alg`, they stay blocks. The class
  sums do not act on `e₀` by scalars: `Z(𝔽₂[S₃]) e₀` is `2`-dimensional.
* **`C₃`.** Over a field `K` of characteristic `2` containing a root `α` of `X² + X + 1`, for
  instance `𝔽₄`, the blocks `1 + r + r²`, `1 + α² r + α r²` and `1 + α r + α² r²` of `K[C₃]` have
  central characters (`r ↦ 1`, `r ↦ α`, `r ↦ α²`), so they stay blocks along every `K → K'`.
* **Against it**, `𝔽₂` splits `S₃` but not `C₃`: the block `r + r²` of `𝔽₂[C₃]` maps to the sum of
  the last two blocks of `𝔽₄[C₃]`
  (`TauCeti.GroupAlgebraBlockExamples.not_isBlockIdempotent_centerMapRingHom_r_add_r_sq`), so
  without the splitting of `H` a block of `k[H]` need not stay a block.
-/

public section

namespace TauCeti.Examples.BlockScalarExtension

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.PrincipalBlockExamples

/-! ### `S₃` -/

/-- The augmentation of a class sum of `𝔽₂[S₃]` is its size mod `2`: `1`, `0`, `1` on the classes
of `1`, of the `3`-cycles and of the transpositions. -/
theorem centerAugmentation_classSumCenter (g : S₃) :
    centerAugmentation (ZMod 2) S₃ (classSumCenter (ConjClasses.mk g)) =
      if g ≠ 1 ∧ g * g * g = 1 then 0 else 1 := by
  rw [centerAugmentation_apply, classSumCenter_coe, classSum_eq_sum, map_sum]
  simp only [of_apply, augmentation_single, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  revert g
  decide +kernel

/-- Each class sum of `𝔽₂[S₃]` acts on the block `ρ + ρ²` by `1`, `1`, `0` on the classes of `1`,
of the `3`-cycles and of the transpositions. -/
theorem blockTwoS₃_mul_classSumCenter (g : S₃) :
    blockTwoS₃ * classSumCenter (ConjClasses.mk g) =
      (if g ≠ 1 ∧ g * g = 1 then 0 else 1 : ZMod 2) • blockTwoS₃ := by
  refine Subtype.ext (ext (Finsupp.ext fun h ↦ ?_))
  rw [Subalgebra.coe_mul, coeff_mul_eq_sum, Subalgebra.coe_smul, coeff_smul, Finsupp.smul_apply,
    coeff_blockTwoS₃, classSumCenter_coe]
  simp only [classSum_coeff, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff, smul_eq_mul]
  revert g h
  decide +kernel

variable {K K' : Type*} [Field K] [Field K']

/-- The value of a character `φ` with `b z = φ(z) b` at an element acting on `b ≠ 0` by `c`. -/
private theorem apply_eq_of_mul_eq_smul {A : Type*} [CommRing A] [Algebra K A] {b z : A}
    (hb : b ≠ 0) {φ : A →ₐ[K] K} (hφ : ∀ z, b * z = φ z • b) {c : K} (hc : b * z = c • b) :
    φ z = c :=
  smul_left_injective K hb ((hφ z).symm.trans hc)

/-- The class sums act on `ρ + ρ²` by scalars. -/
theorem forall_exists_mul_classSumCenter_blockTwoS₃ (C : ConjClasses S₃) :
    ∃ c : ZMod 2, blockTwoS₃ * classSumCenter C = c • blockTwoS₃ := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  exact ⟨_, blockTwoS₃_mul_classSumCenter g⟩

/-- The class sums act on each image of `ρ + ρ²` by scalars. -/
theorem exists_mul_classSumCenter_blockTwoS₃ (f : ZMod 2 →+* K) (C : ConjClasses S₃) :
    ∃ c : K, centerMapRingHom S₃ f blockTwoS₃ * classSumCenter C =
      c • centerMapRingHom S₃ f blockTwoS₃ :=
  exists_mul_classSumCenter_centerMapRingHom f forall_exists_mul_classSumCenter_blockTwoS₃ C

/-- The augmentation is the central character of `1 + ρ + ρ²` over every `K`: it takes the value
`f 1 = 1` at its image. -/
theorem centerAugmentation_blockOneS₃_map (f : ZMod 2 →+* K) :
    centerAugmentation K S₃ (centerMapRingHom S₃ f blockOneS₃) = 1 := by
  rw [centerAugmentation_centerMapRingHom, centerAugmentation_apply, augmentation_blockOneS₃,
    map_one]

/-- Over every field `K` of characteristic `2`, the image of `1 + ρ + ρ²` is a block of `K[S₃]`. -/
theorem isBlockIdempotent_blockOneS₃_map (f : ZMod 2 →+* K) :
    IsBlockIdempotent (centerMapRingHom S₃ f blockOneS₃) :=
  isBlockIdempotent_blockOneS₃.centerMapRingHom f
    (by rw [centerAugmentation_apply, augmentation_blockOneS₃])

/-- Over every field `K` of characteristic `2`, the image of `ρ + ρ²` is a block of `K[S₃]`. -/
theorem isBlockIdempotent_blockTwoS₃_map (f : ZMod 2 →+* K) :
    IsBlockIdempotent (centerMapRingHom S₃ f blockTwoS₃) :=
  isBlockIdempotent_blockTwoS₃.centerMapRingHom_of_forall_exists_mul_classSumCenter f
    forall_exists_mul_classSumCenter_blockTwoS₃

/-- **The central character of `1 + ρ + ρ²` over `K`**, the augmentation, takes the values `1`,
`0`, `1` on the class sums of `1`, of the `3`-cycles and of the transpositions. -/
theorem centerAugmentation_classSumCenter_map (f : ZMod 2 →+* K) (g : S₃) :
    centerAugmentation K S₃ (classSumCenter (ConjClasses.mk g)) =
      if g ≠ 1 ∧ g * g * g = 1 then 0 else 1 := by
  rw [← centerMapRingHom_classSumCenter f, centerAugmentation_centerMapRingHom,
    centerAugmentation_classSumCenter]
  split_ifs <;> simp

/-- **The central character of `ρ + ρ²` over `K`** takes the values `1`, `1`, `0` on the class sums
of `1`, of the `3`-cycles and of the transpositions. -/
theorem exists_centralCharacter_blockTwoS₃ (f : ZMod 2 →+* K) :
    ∃ φ : Subalgebra.center K (MonoidAlgebra K S₃) →ₐ[K] K,
      φ (centerMapRingHom S₃ f blockTwoS₃) = 1 ∧ ∀ g : S₃,
        φ (classSumCenter (ConjClasses.mk g)) = if g ≠ 1 ∧ g * g = 1 then 0 else 1 := by
  have hb := isBlockIdempotent_blockTwoS₃_map f
  obtain ⟨φ, hφ1, hφ⟩ := hb.exists_algHom_of_forall_exists_mul_classSumCenter
    (exists_mul_classSumCenter_blockTwoS₃ f)
  refine ⟨φ, hφ1, fun g ↦ apply_eq_of_mul_eq_smul hb.ne_zero hφ ?_⟩
  have := congrArg (centerMapRingHom S₃ f) (blockTwoS₃_mul_classSumCenter g)
  rw [map_mul, centerMapRingHom_classSumCenter, Algebra.smul_def, map_mul,
    centerMapRingHom_algebraMap, ← Algebra.smul_def] at this
  rw [this]
  split_ifs <;> simp

/-- **The blocks of `K[S₃]` stay blocks.** For fields `K`, `K'` of characteristic `2`, for
instance `𝔽₄ ⊆ 𝔽₂^alg`, the blocks `1 + ρ + ρ²` and `ρ + ρ²` of `K[S₃]` map to blocks of
`K'[S₃]`: the theorem for blocks with a central character, applied over `K` to the augmentation
and to the central character of `ρ + ρ²`. -/
theorem isBlockIdempotent_centerMapRingHom_blockS₃ (f : ZMod 2 →+* K) (f' : K →+* K') :
    IsBlockIdempotent (centerMapRingHom S₃ f' (centerMapRingHom S₃ f blockOneS₃)) ∧
      IsBlockIdempotent (centerMapRingHom S₃ f' (centerMapRingHom S₃ f blockTwoS₃)) :=
  ⟨(isBlockIdempotent_blockOneS₃_map f).centerMapRingHom f' (centerAugmentation_blockOneS₃_map f),
    (isBlockIdempotent_blockTwoS₃_map f).centerMapRingHom_of_forall_exists_mul_classSumCenter f'
      (exists_mul_classSumCenter_blockTwoS₃ f)⟩

/-! ### `C₃` -/

section C₃

variable {α : K}

/-- `1 + r + r²` of `K[C₃]` is fixed by every `r^i`. -/
private theorem one_add_r_add_r_sq_mul_of (g : C₃) :
    (1 + of K C₃ r + of K C₃ (r ^ 2)) * of K C₃ g =
      (1 : K) • (1 + of K C₃ r + of K C₃ (r ^ 2)) := by
  refine ext (Finsupp.ext fun h ↦ ?_)
  fin_cases g <;> fin_cases h <;>
    simp +decide [coeff_mul_single_apply, Finsupp.single_apply, one_def]

/-- Over a field of characteristic `2`, `1 + r + r²` is a block idempotent of `K[C₃]`. -/
theorem isBlockIdempotent_one_add_r_add_r_sq_of_charP [CharP K 2] :
    IsBlockIdempotent (toCenter (1 + of K C₃ r + of K C₃ (r ^ 2))) := by
  refine isBlockIdempotent_of_mul_of_eq_smul (fun _ ↦ 1)
    (by simpa only [coe_toCenter] using one_add_r_add_r_sq_mul_of (K := K))
    (by simp +decide [one_def]) ?_
  rw [sum_c₃]
  simp +decide [one_def]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h2

/-- If every `r^i` acts on a central `b ∈ K[C₃]` by a scalar, so does every class sum. -/
private theorem exists_mul_classSumCenter_of_mul_of {b : MonoidAlgebra K C₃} (c : C₃ → K)
    (hb : ∀ g, b * of K C₃ g = c g • b) (C : ConjClasses C₃) :
    ∃ c : K, toCenter b * classSumCenter C = c • toCenter b := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  exact ⟨c g, Subtype.ext (by simpa using hb g)⟩

/-- **The blocks of `K[C₃]` stay blocks.** Over a field `K` of characteristic `2` containing a
root `α` of `X² + X + 1`, for instance `𝔽₄`, the blocks `1 + r + r²`, `1 + α² r + α r²` and
`1 + α r + α² r²` of `K[C₃]` map to blocks of `K'[C₃]` along every `f : K →+* K'`, for instance
`𝔽₄ → 𝔽₂^alg`: `r` acts on them by `1`, `α`, `α²`, so they have central characters. -/
theorem isBlockIdempotent_centerMapRingHom_blockC₃ [CharP K 2] (hα : α ^ 2 + α + 1 = 0)
    (f : K →+* K') :
    IsBlockIdempotent (centerMapRingHom C₃ f (toCenter (1 + of K C₃ r + of K C₃ (r ^ 2)))) ∧
      IsBlockIdempotent (centerMapRingHom C₃ f (toCenter (eOne α))) ∧
      IsBlockIdempotent (centerMapRingHom C₃ f (toCenter (eTwo α))) :=
  ⟨IsBlockIdempotent.centerMapRingHom_of_forall_exists_mul_classSumCenter f
      isBlockIdempotent_one_add_r_add_r_sq_of_charP
      (exists_mul_classSumCenter_of_mul_of _ one_add_r_add_r_sq_mul_of),
    (isBlockIdempotent_eOne hα).centerMapRingHom_of_forall_exists_mul_classSumCenter f
      (exists_mul_classSumCenter_of_mul_of _ (eOne_mul_of hα)),
    (isBlockIdempotent_eTwo hα).centerMapRingHom_of_forall_exists_mul_classSumCenter f
      (exists_mul_classSumCenter_of_mul_of _ (eTwo_mul_of hα))⟩

end C₃

/-- **`𝔽₄ ⊆ 𝔽₂^alg`.** For a root `α ∈ 𝔽₄` of `X² + X + 1`, the three blocks `1 + r + r²`,
`1 + α² r + α r²` and `1 + α r + α² r²` of `𝔽₄[C₃]` stay blocks of `𝔽₂^alg[C₃]`, and the two
blocks of `𝔽₄[S₃]` stay blocks of `𝔽₂^alg[S₃]`. -/
theorem galoisField_two_two_algebraicClosure :
    ∃ α : GaloisField 2 2, α ^ 2 + α + 1 = 0 ∧
      IsBlockIdempotent (centerMapRingHom C₃ (algebraMap _ (AlgebraicClosure (GaloisField 2 2)))
          (toCenter (1 + of (GaloisField 2 2) C₃ r + of (GaloisField 2 2) C₃ (r ^ 2)))) ∧
      IsBlockIdempotent (centerMapRingHom C₃ (algebraMap _ (AlgebraicClosure (GaloisField 2 2)))
          (toCenter (eOne α))) ∧
      IsBlockIdempotent (centerMapRingHom C₃ (algebraMap _ (AlgebraicClosure (GaloisField 2 2)))
          (toCenter (eTwo α))) ∧
      IsBlockIdempotent (centerMapRingHom S₃ (algebraMap _ (AlgebraicClosure (GaloisField 2 2)))
          (centerMapRingHom S₃ (ZMod.castHom (dvd_refl 2) (GaloisField 2 2)) blockOneS₃)) ∧
      IsBlockIdempotent (centerMapRingHom S₃ (algebraMap _ (AlgebraicClosure (GaloisField 2 2)))
          (centerMapRingHom S₃ (ZMod.castHom (dvd_refl 2) (GaloisField 2 2)) blockTwoS₃)) := by
  obtain ⟨α, hα⟩ := exists_sq_add_self_add_one_eq_zero_galoisField_two_two
  exact ⟨α, hα, isBlockIdempotent_centerMapRingHom_blockC₃ hα _ |>.1,
    isBlockIdempotent_centerMapRingHom_blockC₃ hα _ |>.2.1,
    isBlockIdempotent_centerMapRingHom_blockC₃ hα _ |>.2.2,
    isBlockIdempotent_centerMapRingHom_blockS₃ _ _ |>.1,
    isBlockIdempotent_centerMapRingHom_blockS₃ _ _ |>.2⟩

end TauCeti.Examples.BlockScalarExtension
