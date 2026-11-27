/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.DefectGroup.Principal
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.DefectZero.Splitting
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect.Class
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect.Sylow

/-!
# Defect classes of small blocks

The Checks of defect classes (`TauCeti.IsDefectClass`).

* **Defect classes need a splitting field.** The block `r + r²` of `𝔽₂[C₃]` has no central
  character: an `𝔽₂`-algebra homomorphism `φ` of the centre sends `r` to a cube root of unity of
  `𝔽₂`, that is to `1`, so `φ(r + r²) = 0`. Hence it has no defect class with respect to a central
  character, although its defect group is `1`
  (`TauCeti.DefectZeroSplittingExamples.isDefectGroup_r_add_r_sq_bot`).
* Over a field `K` of characteristic `2` containing a root `α` of `X² + X + 1`, for instance `𝔽₄`,
  which splits `C₃`, every central character `λ` of the block `1 + α² r + α r²` has `λ(r) = α`;
  the coefficient of the block on the class `{r}` is `α²`, and `α² · α = 1 ≠ 0`, so `{r}` is a
  defect class. The Sylow `2`-subgroup `1` of `C_{C₃}(r) = C₃` is the defect group.
* **`𝔽₂[S₃]`**, block `1 + ρ + ρ²` with central character the augmentation: the class `{1}` has
  coefficient `1` and `λ(1) = 1`, so it is a defect class, and the Sylow `2`-subgroups of
  `C_{S₃}(1) = S₃`, of order `2`, are the defect groups. The class of `ρ` has coefficient `1`, but
  its class sum is `ρ + ρ²`, with augmentation `2 = 0`, so it is not a defect class, and the Sylow
  `2`-subgroup `1` of `C_{S₃}(ρ)` is not a defect group.
* **Martínez's theorem on these blocks** (`TauCeti.IsDefectClass.isDefectGroup_iff`): the defect
  groups of `1 + ρ + ρ²` are exactly the Sylow `2`-subgroups of `C_{S₃}(1)`, read off the defect
  class `{1}`; and for every central character `λ` of the block `1 + α² r + α r²` of `k[C₃]`, the
  defect groups are exactly the Sylow `2`-subgroups of `C_{C₃}(r)`, read off the defect class
  `{r}`, so the defect group is `1`.
-/

public section

namespace TauCeti.Examples.DefectClass

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.PrincipalBlockExamples
  TauCeti.PrincipalBlockDefectExamples

/-! ### `C₃` in characteristic `2` -/

section C₃

variable {k : Type*} [Field k]

/-- **No central character without a splitting field.** No `𝔽₂`-algebra homomorphism
`Z(𝔽₂[C₃]) → 𝔽₂` takes the value `1` at the block `r + r²`: it sends `r` to a cube root of unity
in `𝔽₂`, that is to `1`, and so `r + r²` to `1 + 1 = 0`. -/
theorem not_exists_algHom_r_add_r_sq_eq_one :
    ¬ ∃ φ : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) C₃) →ₐ[ZMod 2] ZMod 2,
      φ (toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2))) = 1 := by
  rintro ⟨φ, hφ⟩
  set x := φ (toCenter (of (ZMod 2) C₃ r))
  have hpow (n : ℕ) : φ (toCenter (of (ZMod 2) C₃ (r ^ n))) = x ^ n := by
    rw [map_pow, map_pow, map_pow]
  have h3 : x ^ 3 = 1 := by
    rw [← hpow, show r ^ 3 = 1 by decide, map_one, map_one, map_one]
  rw [map_add, map_add, hpow] at hφ
  have key : ∀ y : ZMod 2, y ^ 3 = 1 → y + y ^ 2 ≠ 1 := by decide
  exact key x h3 hφ

/-- **The block `r + r²` of `𝔽₂[C₃]` has no defect class for a central character**, since no
`𝔽₂`-algebra homomorphism of the centre to `𝔽₂` takes the value `1` at the block. (For the
augmentation, which sends `r + r²` to `0`, the class `{r}` does satisfy `IsDefectClass`, but the
augmentation is not a central character of this block.) Its defect group is `1` all the same
(`TauCeti.DefectZeroSplittingExamples.isDefectGroup_r_add_r_sq_bot`). -/
theorem not_exists_isDefectClass_r_add_r_sq :
    ¬ ∃ (φ : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) C₃) →ₐ[ZMod 2] ZMod 2),
      φ (toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2))) = 1 ∧
        ∃ C, IsDefectClass φ (toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2))) C :=
  fun ⟨φ, hφ, _⟩ => not_exists_algHom_r_add_r_sq_eq_one ⟨φ, hφ⟩

variable {α : k}

/-- A central character `λ` of the block `1 + α² r + α r²` takes the value `α` at `r`, since `r`
acts on the block by `α`. -/
theorem apply_toCenter_of_r (hα : α ^ 2 + α + 1 = 0)
    {φ : Subalgebra.center k (MonoidAlgebra k C₃) →ₐ[k] k} (hφ : φ (toCenter (eOne α)) = 1) :
    φ (toCenter (of k C₃ r)) = α := by
  have h := congrArg (fun x => φ (toCenter x)) (eOne_mul_of hα r)
  simp only [map_mul, map_smul, hφ, one_mul, smul_eq_mul, mul_one] at h
  rw [h]
  simp [show r ≠ 1 by decide]

/-- **A defect class over `𝔽₄`.** For a root `α` of `X² + X + 1`, for instance in `𝔽₄`, the
class `{r}` is a defect class of the block `1 + α² r + α r²` of `k[C₃]` for every central
character `λ`: the coefficient `α²` times `λ(r) = α` is `α³ = 1`. -/
theorem isDefectClass_eOne_r (hα : α ^ 2 + α + 1 = 0)
    {φ : Subalgebra.center k (MonoidAlgebra k C₃) →ₐ[k] k} (hφ : φ (toCenter (eOne α)) = 1) :
    IsDefectClass φ (toCenter (eOne α)) (ConjClasses.mk r) := by
  rw [isDefectClass_mk_iff, classSumCenter_mk_of_commGroup, apply_toCenter_of_r hα hφ, coe_toCenter]
  have hcoeff : (eOne α).coeff r = α ^ 2 := by
    simp +decide [one_def]
  rw [hcoeff, ← pow_succ, show α ^ 3 = 1 by linear_combination (α - 1) * hα]
  exact one_ne_zero

variable [CharP k 2]

/-- The defect group of the block `1 + α² r + α r²` of `k[C₃]` is `1`, the Sylow `2`-subgroup of
`C_{C₃}(r) = C₃`. -/
theorem isDefectGroup_eOne_bot (hα : α ^ 2 + α + 1 = 0) :
    IsDefectGroup k 2 (eOne α) ⊥ := by
  have hne : eOne α ≠ 0 := fun h => (isBlockIdempotent_eOne hα).ne_zero
    (by rw [← map_zero toCenter, h])
  obtain ⟨D, hD⟩ := exists_isDefectGroup 2 hne
  rwa [← DefectZeroSplittingExamples.eq_bot_of_isPGroup_two hD.isPGroup]

/-- **Martínez's theorem on `k[C₃]`.** For every central character `λ` of the block
`1 + α² r + α r²`, the class `{r}` is a defect class, so the defect groups of the block are
exactly the Sylow `2`-subgroups of `C_{C₃}(r)`. -/
theorem isDefectGroup_eOne_iff_sylow_centralizer_r (hα : α ^ 2 + α + 1 = 0)
    {φ : Subalgebra.center k (MonoidAlgebra k C₃) →ₐ[k] k} (hφ : φ (toCenter (eOne α)) = 1)
    {D : Subgroup C₃} :
    IsDefectGroup k 2 (eOne α) D ↔ ∃ S : Sylow 2 (Subgroup.centralizer {r}),
      D = (S : Subgroup (Subgroup.centralizer {r})).map (Subgroup.subtype _) := by
  rw [← coe_toCenter (eOne α),
    (isDefectClass_eOne_r hα hφ).isDefectGroup_iff (isBlockIdempotent_eOne hα) hφ]
  simp only [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq, exists_eq_left]

end C₃

/-! ### `𝔽₂[S₃]` -/

/-- The class sum of the `3`-cycles of `S₃` is the block `ρ + ρ²`. -/
theorem classSumCenter_mk_ρ :
    classSumCenter (k := ZMod 2) (ConjClasses.mk ρ) = blockTwoS₃ := by
  refine Subtype.ext (ext (Finsupp.ext fun g => ?_))
  simp only [classSumCenter_coe, classSum_coeff, coeff_blockTwoS₃,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  revert g
  decide +kernel

/-- **`{1}` is a defect class of `1 + ρ + ρ²`**: coefficient `1` and `λ(1) = 1`. The
augmentation is the central character of this principal block
(`TauCeti.centerAugmentation_principalBlockIdempotent`). -/
theorem isDefectClass_blockOneS₃_one :
    IsDefectClass (centerAugmentation (ZMod 2) S₃) blockOneS₃ (ConjClasses.mk 1) := by
  simp only [isDefectClass_mk_iff, classSumCenter_mk_one, map_one, mul_one, coeff_blockOneS₃]
  decide

/-- **The class of `ρ` is not a defect class of `1 + ρ + ρ²`**: its coefficient is `1`, but its
class sum `ρ + ρ²` has augmentation `2 = 0`. -/
theorem not_isDefectClass_blockOneS₃_ρ :
    ¬ IsDefectClass (centerAugmentation (ZMod 2) S₃) blockOneS₃ (ConjClasses.mk ρ) := by
  rw [isDefectClass_mk_iff, classSumCenter_mk_ρ, centerAugmentation_apply,
    augmentation_blockTwoS₃, mul_zero, not_not]

/-- The Sylow `2`-subgroup `1` of `C_{S₃}(ρ) = ⟨ρ⟩` is not a defect group of `1 + ρ + ρ²`: the
defect groups are the Sylow `2`-subgroups of `S₃ = C_{S₃}(1)`, of order `2`. -/
theorem not_isDefectGroup_blockOneS₃_bot :
    ¬ IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) ⊥ := fun h => by
  obtain ⟨S, hS⟩ := isDefectGroup_blockOneS₃_iff_sylow.1 h
  have hτ := S.maximal_isPGroup.eq_of_le (IsPGroup.of_card card_zpowers_τ) (hS ▸ bot_le)
  have : τ ∈ (⊥ : Subgroup S₃) := hS ▸ hτ ▸ Subgroup.mem_zpowers τ
  exact absurd (Subgroup.mem_bot.1 this) (by decide)

/-- **Martínez's theorem on `𝔽₂[S₃]`.** The class `{1}` is a defect class of `1 + ρ + ρ²` for
its central character, the augmentation, so the defect groups of the block are exactly the Sylow
`2`-subgroups of `C_{S₃}(1)`. -/
theorem isDefectGroup_blockOneS₃_iff_sylow_centralizer_one {D : Subgroup S₃} :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) D ↔
      ∃ S : Sylow 2 (Subgroup.centralizer {(1 : S₃)}),
        D = (S : Subgroup (Subgroup.centralizer {(1 : S₃)})).map (Subgroup.subtype _) := by
  have hφ : centerAugmentation (ZMod 2) S₃ blockOneS₃ = 1 := by
    rw [blockOneS₃_eq_principalBlockIdempotent, centerAugmentation_principalBlockIdempotent]
  rw [isDefectClass_blockOneS₃_one.isDefectGroup_iff isBlockIdempotent_blockOneS₃ hφ]
  simp only [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left, exists_eq_left]

end TauCeti.Examples.DefectClass
