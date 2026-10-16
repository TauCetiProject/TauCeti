/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Algebraic
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.BaseChange

import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm

/-!
# Base change of Hecke characters

For an extension `L / K` of number fields, a Hecke character `χ` of `K` pulls back along the norm
map of idele classes `N_{L/K} : C_L → C_K` to the Hecke character `χ ∘ N_{L/K}` of `L`, its
**base change** to `L`.

At an infinite place `w` of `L` over the place `v` of `K`, the component of `χ ∘ N_{L/K}` is the
component of `χ` at `v` composed with the local norm `N_{L_w/K_v}`. That local norm is the
identity at a real place over a real place, `z ↦ |z|²` at a complex place over a real place, and
the identity or complex conjugation at a complex place over a complex place. So the infinity type
of `χ ∘ N_{L/K}` is the base change of the infinity type of `χ`. Base change of infinity types
preserves algebraicity on the identity component, so the base change of an algebraic Hecke
character is algebraic.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.baseChange`: the base change `χ ↦ χ ∘ N_{L/K}`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.realComponent_baseChange`,
  `TauCeti.GlobalNumberFields.HeckeCharacter.complexComponent_baseChange_of_isReal`,
  `TauCeti.GlobalNumberFields.HeckeCharacter.complexComponent_baseChange_of_comp_eq`,
  `TauCeti.GlobalNumberFields.HeckeCharacter.complexComponent_baseChange_of_conjugate_comp_eq`:
  the archimedean components of the base change.
* `TauCeti.GlobalNumberFields.HeckeCharacter.infinityType_baseChange`: the infinity type of the
  base change is the base change of the infinity type.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic.baseChange`: the base change of an
  algebraic Hecke character is algebraic.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

namespace HeckeCharacter

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (L) in
/-- **The base change of a Hecke character** of `K` to `L`: its pullback `χ ∘ N_{L/K}` along the
norm map of idele classes. -/
def baseChange : HeckeCharacter K →* HeckeCharacter L where
  toFun χ := χ.comp (ideleClassNormMap K L)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The base change of `χ` evaluates `χ` on the norm of an idele class. -/
@[simp]
theorem baseChange_apply (χ : HeckeCharacter K) (c : IdeleClassGroup (𝓞 L) L) :
    baseChange L χ c = χ (ideleClassNormMap K L c) :=
  (rfl)

/-! ### Archimedean components -/

/-- The component of the base change of `χ` at an infinite place `w` of `L` is the component of
`χ` at the place below `w`, composed with the local norm. -/
theorem infiniteComponent_baseChange (χ : HeckeCharacter K) (w : InfinitePlace L)
    (u : w.Completionˣ) :
    (baseChange L χ).infiniteComponent w u =
      χ.infiniteComponent (w.comap (algebraMap K L))
        (Algebra.normUnits (w.comap (algebraMap K L)).Completion u) := by
  rw [infiniteComponent_apply, baseChange_apply,
    ideleClassNormMap_ofCompletion (w.comap (algebraMap K L)) w, infiniteComponent_apply]

/-- At a real place of `L`, the component of the base change of `χ` is the component of `χ` at
the real place below. -/
theorem realComponent_baseChange (χ : HeckeCharacter K) (w : {w : InfinitePlace L // w.IsReal}) :
    (baseChange L χ).realComponent w =
      χ.realComponent ⟨w.1.comap (algebraMap K L), w.2.comap _⟩ := by
  refine ContinuousMonoidHom.ext fun x ↦ ?_
  rw [realComponent_apply, realComponent_apply, infiniteComponent_baseChange]
  congr 1
  rw [ContinuousMulEquiv.eq_symm_apply]
  apply Units.ext
  simp [extensionEmbeddingOfIsReal_norm_of_isReal (w.2.comap (algebraMap K L)) w.2]

/-- At a complex place of `L` over a real place, the component of the base change of `χ` is the
component of `χ` at the real place below, composed with the norm `z ↦ |z|²`. -/
theorem complexComponent_baseChange_of_isReal (χ : HeckeCharacter K)
    (w : {w : InfinitePlace L // w.IsComplex}) (hv : (w.1.comap (algebraMap K L)).IsReal)
    (z : ℂˣ) :
    (baseChange L χ).complexComponent w z =
      χ.realComponent ⟨_, hv⟩ (Units.map (Complex.normSq : ℂ →* ℝ) z) := by
  rw [complexComponent_apply, realComponent_apply, infiniteComponent_baseChange]
  congr 1
  rw [ContinuousMulEquiv.eq_symm_apply]
  apply Units.ext
  simp [extensionEmbeddingOfIsReal_norm_of_isRamified (isRamified_iff.2 ⟨w.2, hv⟩) hv]

/-- At a complex place `w` of `L` over a complex place whose embedding is extended by
`w.embedding`, the component of the base change of `χ` is the component of `χ` below. -/
theorem complexComponent_baseChange_of_comp_eq (χ : HeckeCharacter K)
    (w : {w : InfinitePlace L // w.IsComplex}) (hv : (w.1.comap (algebraMap K L)).IsComplex)
    (he : w.1.embedding.comp (algebraMap K L) = (w.1.comap (algebraMap K L)).embedding) :
    (baseChange L χ).complexComponent w = χ.complexComponent ⟨_, hv⟩ := by
  have : ComplexEmbedding.LiesOver w.1.embedding (w.1.comap (algebraMap K L)).embedding := ⟨he⟩
  refine ContinuousMonoidHom.ext fun z ↦ ?_
  rw [complexComponent_apply, complexComponent_apply, infiniteComponent_baseChange]
  congr 1
  rw [ContinuousMulEquiv.eq_symm_apply]
  apply Units.ext
  simp [extensionEmbedding_norm_of_isUnramified (isUnramified_iff.2 (.inr hv))]

/-- At a complex place `w` of `L` over a complex place whose embedding is extended by the
conjugate of `w.embedding`, the component of the base change of `χ` is the component of `χ`
below, composed with complex conjugation. -/
theorem complexComponent_baseChange_of_conjugate_comp_eq (χ : HeckeCharacter K)
    (w : {w : InfinitePlace L // w.IsComplex}) (hv : (w.1.comap (algebraMap K L)).IsComplex)
    (he : (ComplexEmbedding.conjugate w.1.embedding).comp (algebraMap K L) =
      (w.1.comap (algebraMap K L)).embedding) (z : ℂˣ) :
    (baseChange L χ).complexComponent w z =
      χ.complexComponent ⟨_, hv⟩ (Units.map (starRingEnd ℂ : ℂ →* ℂ) z) := by
  have : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w.1.embedding)
    (w.1.comap (algebraMap K L)).embedding := ⟨he⟩
  rw [complexComponent_apply, complexComponent_apply, infiniteComponent_baseChange]
  congr 1
  rw [ContinuousMulEquiv.eq_symm_apply]
  apply Units.ext
  simp [extensionEmbedding_norm_of_isUnramified_conjugate (isUnramified_iff.2 (.inr hv))]

/-! ### Infinity types -/

/-- **The infinity type of a base change** is the base change of the infinity type. -/
@[simp]
theorem infinityType_baseChange (χ : HeckeCharacter K) :
    (baseChange L χ).infinityType = χ.infinityType.baseChange L := by
  refine infinityType_eq_iff.2 ⟨fun w ↦ ?_, fun w ↦ ?_⟩
  · rw [realComponent_baseChange, realComponent_eq,
      ContinuousInfinityType.baseChange_realExponent, ContinuousInfinityType.baseChange_realParity]
  by_cases hv : (w.1.comap (algebraMap K L)).IsReal
  · refine ContinuousMonoidHom.ext fun z ↦ ?_
    rw [complexComponent_baseChange_of_isReal χ w hv, realComponent_eq,
      realUnitsCharacter_map_normSq,
      ContinuousInfinityType.baseChange_complexExponent_of_isReal _ _ hv,
      ContinuousInfinityType.baseChange_complexAngularFrequency_of_isReal _ _ hv]
  have hv' := not_isReal_iff_isComplex.mp hv
  rw [ContinuousInfinityType.baseChange_complexExponent_of_isComplex _ _ hv']
  rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w.1
    (w.1.comap (algebraMap K L)) with he | he
  · rw [complexComponent_baseChange_of_comp_eq χ w hv' he, complexComponent_eq,
      ContinuousInfinityType.baseChange_complexAngularFrequency_of_comp_eq _ _ hv' he]
  · refine ContinuousMonoidHom.ext fun z ↦ ?_
    rw [complexComponent_baseChange_of_conjugate_comp_eq χ w hv' he, complexComponent_eq,
      complexUnitsCharacter_map_conj,
      ContinuousInfinityType.baseChange_complexAngularFrequency_of_conjugate_comp_eq _ _ hv' he]

/-- **The base change of an algebraic Hecke character is algebraic.** -/
theorem IsAlgebraic.baseChange {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    (baseChange L χ).IsAlgebraic := by
  rw [isAlgebraic_iff, infinityType_baseChange,
    ← ContinuousInfinityType.isAlgebraicOnIdentityComponent_iff]
  exact ((ContinuousInfinityType.isAlgebraicOnIdentityComponent_iff _).2
    (isAlgebraic_iff.1 hχ)).baseChange

end HeckeCharacter

end TauCeti.GlobalNumberFields
