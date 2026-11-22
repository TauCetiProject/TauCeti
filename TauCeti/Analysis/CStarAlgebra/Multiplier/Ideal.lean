/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Annihilator
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic

/-!
# Canonical multiplier homomorphisms for closed two-sided ideals

Canonical homomorphism `TwoSidedIdeal.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` from a C⋆-algebra `A`
into the multiplier algebra of a closed two-sided ideal `I`, with kernel `I.annihilator` and
injectivity / isometry characterizations via essentiality of `I`.

## References

* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.54.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

open scoped MultiplierAlgebra

namespace TwoSidedIdeal

section MultiplierHom

section

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The annihilator of a closed two-sided ideal `I` is the kernel of the canonical homomorphism
from `A` into the multiplier algebra of `I`. -/
theorem ker_multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    ker (I.toNonUnitalStarSubalgebra.multiplierHom I.mul_mem_toNonUnitalStarSubalgebra) =
      I.annihilator :=
  ext fun _ ↦ by
    simp only [mem_ker, NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff,
      mem_toNonUnitalStarSubalgebra, mem_annihilator]

/-- The canonical homomorphism from `A` into the multiplier algebra of a closed two-sided ideal `I`
is injective exactly when `I` is essential. -/
theorem multiplierHom_injective_iff_isEssential (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    Function.Injective (I.toNonUnitalStarSubalgebra.multiplierHom
      I.mul_mem_toNonUnitalStarSubalgebra) ↔ I.IsEssential := by
  rw [← ker_eq_bot, ker_multiplierHom, annihilator_eq_bot_iff_isEssential_of_isClosed]

/-- The canonical contractive `⋆`-homomorphism `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` induced by left and right
multiplication of `A` on a closed two-sided ideal `I`. -/
noncomputable def multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    A →⋆ₙₐ[ℂ] 𝓜(ℂ, I) :=
  (DoubleCentralizer.congr I.toNonUnitalStarSubalgebraEquiv.symm).toNonUnitalStarAlgHom.comp
    (I.toNonUnitalStarSubalgebra.multiplierHom I.mul_mem_toNonUnitalStarSubalgebra)

section

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

@[simp]
theorem multiplierHom_fst_apply (a : A) (x : I) :
    (I.multiplierHom a).fst x = ⟨a * x, I.mul_mem_left a x x.property⟩ := by
  ext
  simp [multiplierHom]

@[simp]
theorem multiplierHom_snd_apply (a : A) (x : I) :
    (I.multiplierHom a).snd x = ⟨x * a, I.mul_mem_right x a x.property⟩ := by
  ext
  simp [multiplierHom]

theorem coe_multiplierHom_fst_apply (a : A) (x : I) :
    (((I.multiplierHom a).fst x : I) : A) = a * x := by
  simp

theorem coe_multiplierHom_snd_apply (a : A) (x : I) :
    (((I.multiplierHom a).snd x : I) : A) = x * a := by
  simp

@[simp]
theorem multiplierHom_coe (x : I) : I.multiplierHom (x : A) = (x : 𝓜(ℂ, I)) :=
  DoubleCentralizer.ext_fst_snd (fun _ => Subtype.ext (by simp)) (fun _ => Subtype.ext (by simp))

@[simp]
theorem multiplierHom_comp_starAlgHom :
    I.multiplierHom.comp I.starAlgHom = DoubleCentralizer.coeHom :=
  NonUnitalStarAlgHom.ext fun x => by simp

theorem norm_multiplierHom_le (a : A) : ‖I.multiplierHom a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le I.multiplierHom a

theorem multiplierHom_eq_zero_iff {a : A} :
    I.multiplierHom a = 0 ↔ a ∈ I.annihilator := by
  let e := DoubleCentralizer.congr I.toNonUnitalStarSubalgebraEquiv.symm
  rw [multiplierHom, NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    map_eq_zero_iff e (EmbeddingLike.injective e),
    NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff, mem_annihilator]
  simp only [mem_toNonUnitalStarSubalgebra]

end

/-- The kernel of `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is the annihilator of `I`. -/
@[simp]
theorem ker_idealMultiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    TwoSidedIdeal.ker I.multiplierHom = I.annihilator := by
  ext a
  rw [mem_ker, multiplierHom_eq_zero_iff]

section

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

theorem multiplierHom_injective_iff_annihilator_eq_bot :
    Function.Injective I.multiplierHom ↔ I.annihilator = ⊥ := by
  rw [← ker_eq_bot, ker_idealMultiplierHom]

/-- For a closed two-sided ideal `I` of a C⋆-algebra `A`, the canonical map `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is
injective if and only if `I` is an essential closed ideal of `A`. -/
theorem multiplierHom_injective_iff_isClosedEssential :
    Function.Injective I.multiplierHom ↔ I.IsClosedEssential := by
  rw [multiplierHom_injective_iff_annihilator_eq_bot,
    isClosedEssential_iff_annihilator_eq_bot]

/-- When `I` is an essential closed ideal of a C⋆-algebra `A`, `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)`
is an isometric embedding. -/
theorem IsClosedEssential.isometry_multiplierHom (hI : I.IsClosedEssential) :
    Isometry I.multiplierHom :=
  NonUnitalStarAlgHom.isometry I.multiplierHom
    (multiplierHom_injective_iff_isClosedEssential.mpr hI)

end

end

/-- In a unital C⋆-algebra, `I.multiplierHom` sends `1` to `1`. -/
@[simp]
theorem multiplierHom_one {A : Type*} [CStarAlgebra A] (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] : I.multiplierHom 1 = 1 :=
  DoubleCentralizer.ext_fst_snd (fun _ => Subtype.ext (by simp)) (fun _ => Subtype.ext (by simp))

end MultiplierHom

end TwoSidedIdeal
