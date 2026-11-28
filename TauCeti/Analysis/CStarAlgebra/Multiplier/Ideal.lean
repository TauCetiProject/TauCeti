/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic
public import TauCeti.Analysis.Normed.Algebra.Multiplier.Ideal
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal.Essential

/-!
# Canonical multiplier homomorphisms for closed two-sided ideals

Canonical homomorphism `TwoSidedIdeal.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` from a C⋆-algebra `A`
into the multiplier algebra of a closed two-sided ideal `I` (defined by specializing
`NonUnitalStarSubalgebra.multiplierHom` to `I.toNonUnitalStarSubalgebra` and transporting along
`I.toNonUnitalStarSubalgebraEquiv.symm`), with kernel `I.annihilator` and injectivity / isometry
characterizations via essentiality of `I`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.7.3.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.54.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

open scoped MultiplierAlgebra

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

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
  simp [multiplierHom]

@[simp]
theorem multiplierHom_snd_apply (a : A) (x : I) :
    (I.multiplierHom a).snd x = ⟨x * a, I.mul_mem_right x a x.property⟩ := by
  simp [multiplierHom]

theorem coe_multiplierHom_fst_apply (a : A) (x : I) :
    (((I.multiplierHom a).fst x : I) : A) = a * x :=
  congrArg Subtype.val (multiplierHom_fst_apply a x)

theorem coe_multiplierHom_snd_apply (a : A) (x : I) :
    (((I.multiplierHom a).snd x : I) : A) = x * a :=
  congrArg Subtype.val (multiplierHom_snd_apply a x)

theorem norm_multiplierHom_le (a : A) : ‖I.multiplierHom a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le I.multiplierHom a

end

/-- The kernel of `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is the annihilator of `I`. -/
@[simp]
theorem ker_multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    TwoSidedIdeal.ker I.multiplierHom = I.annihilator := by
  ext a
  rw [mem_ker, multiplierHom, NonUnitalStarAlgHom.comp_apply,
    StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_eq_zero_iff _ (EquivLike.injective _),
    NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff, mem_annihilator]
  simp only [mem_toNonUnitalStarSubalgebra]

section

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

/-- For a closed two-sided ideal `I` of a C⋆-algebra `A`, the canonical map `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is
injective if and only if `I` is an essential closed ideal of `A`. -/
theorem multiplierHom_injective_iff_isClosedEssential :
    Function.Injective I.multiplierHom ↔ I.IsClosedEssential := by
  rw [← TwoSidedIdeal.ker_eq_bot, ker_multiplierHom, isClosedEssential_iff_annihilator_eq_bot]

/-- When `I` is an essential closed ideal of a C⋆-algebra `A`, `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)`
is an isometric embedding. -/
theorem IsClosedEssential.isometry_multiplierHom (hI : I.IsClosedEssential) :
    Isometry I.multiplierHom :=
  NonUnitalStarAlgHom.isometry I.multiplierHom
    (multiplierHom_injective_iff_isClosedEssential.mpr hI)

end

/-- In a unital C⋆-algebra, `I.multiplierHom` sends `1` to `1`. -/
@[simp]
theorem multiplierHom_one {A : Type*} [CStarAlgebra A] (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] : I.multiplierHom 1 = 1 :=
  DoubleCentralizer.ext_fst fun x => by simp [multiplierHom_fst_apply]

end TwoSidedIdeal
