/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Annihilator
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Idealizer

/-!
# Canonical multiplier homomorphisms for closed two-sided ideals

Canonical homomorphism `TwoSidedIdeal.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` from a C⋆-algebra `A`
into the multiplier algebra of a closed two-sided ideal `I` (defined via
`NonUnitalStarAlgHom.idealToMultiplier` applied to `I.starAlgHom`), with kernel `I.annihilator`
and injectivity / isometry characterizations via essentiality of `I`.

## References

* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.54.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

open scoped MultiplierAlgebra

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

private theorem mul_starAlgHom_mem_range (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (a : A) (x : I) : a * I.starAlgHom x ∈ Set.range I.starAlgHom :=
  ⟨⟨a * x, I.mul_mem_left a x x.property⟩, by simp⟩

/-- The canonical contractive `⋆`-homomorphism `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` induced by left and right
multiplication of `A` on a closed two-sided ideal `I`. -/
noncomputable def multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    A →⋆ₙₐ[ℂ] 𝓜(ℂ, I) :=
  I.starAlgHom.idealToMultiplier I.starAlgHom_injective I.mul_starAlgHom_mem_range

section

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

@[simp]
theorem multiplierHom_fst_apply (a : A) (x : I) :
    (I.multiplierHom a).fst x = ⟨a * x, I.mul_mem_left a x x.property⟩ :=
  Subtype.ext <| by
    simpa only [multiplierHom, starAlgHom_apply] using
      I.starAlgHom.map_idealToMultiplier_fst I.starAlgHom_injective I.mul_starAlgHom_mem_range a x

@[simp]
theorem multiplierHom_snd_apply (a : A) (x : I) :
    (I.multiplierHom a).snd x = ⟨x * a, I.mul_mem_right x a x.property⟩ :=
  Subtype.ext <| by
    simpa only [multiplierHom, starAlgHom_apply] using
      I.starAlgHom.map_idealToMultiplier_snd I.starAlgHom_injective I.mul_starAlgHom_mem_range a x

theorem coe_multiplierHom_fst_apply (a : A) (x : I) :
    (((I.multiplierHom a).fst x : I) : A) = a * x := by
  simp

theorem coe_multiplierHom_snd_apply (a : A) (x : I) :
    (((I.multiplierHom a).snd x : I) : A) = x * a := by
  simp

theorem norm_multiplierHom_le (a : A) : ‖I.multiplierHom a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le I.multiplierHom a

end

/-- The kernel of `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is the annihilator of `I`. -/
@[simp]
theorem ker_multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    TwoSidedIdeal.ker I.multiplierHom = I.annihilator := by
  ext a
  rw [mem_ker, multiplierHom, NonUnitalStarAlgHom.idealToMultiplier_eq_zero_iff, mem_annihilator]
  simp only [starAlgHom_apply]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.property⟩

section

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

/-- For a closed two-sided ideal `I` of a C⋆-algebra `A`, the canonical map `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is
injective if and only if `I` is an essential closed ideal of `A`. -/
theorem multiplierHom_injective_iff_isClosedEssential :
    Function.Injective I.multiplierHom ↔ I.IsClosedEssential := by
  rw [multiplierHom, NonUnitalStarAlgHom.idealToMultiplier_injective_iff,
    isClosedEssential_iff_annihilator_eq_bot, eq_bot_iff]
  simp only [IsConcreteLE.le_iff, mem_annihilator, mem_bot, starAlgHom_apply]
  exact ⟨fun h a ha => h a fun x => ha x x.property,
    fun h a ha => h (x := a) fun _ hx => ha ⟨_, hx⟩⟩

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
