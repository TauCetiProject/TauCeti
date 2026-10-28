/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension

/-!
# The global dimension of a ring

The (left) global dimension of a ring `R` is the supremum of the projective dimensions of all
`R`-modules (Stacks, Definition 10.109.10 (00O6)). It is the invariant through which Serre's
theorem characterizes regular local rings: a Noetherian local ring is regular iff its global
dimension is finite, and then it equals the Krull dimension.

## Main definitions

* `TauCeti.globalDimension R`: the supremum of `CategoryTheory.projectiveDimension M` over all
  `M : ModuleCat.{v} R`, valued in `WithBot ℕ∞`. It is `⊥` exactly for the zero ring.

## Main results

* `TauCeti.globalDimension_le_iff`: `globalDimension R ≤ d` iff every module has projective
  dimension at most `d`, for any `d : WithBot ℕ∞`.
* `TauCeti.globalDimension_le_iff_hasProjectiveDimensionLE`: `globalDimension R ≤ n` iff every
  module has projective dimension at most `n`, in Mathlib's pointwise vocabulary.
* `TauCeti.globalDimension_le_tfae`: it suffices to bound the projective dimensions of the finite
  modules, or only of the cyclic modules `R ⧸ I` (Stacks, Lemma 10.109.12 (065T)).
* `Submonoid.globalDimension_localization_le`: localization does not increase the global dimension
  (Stacks, Lemma 10.109.13 (00O8)).
* `TauCeti.globalDimension_eq_zero_of_isSemisimpleRing`: a nonzero semisimple ring, for instance
  a field, has global dimension zero.

## Implementation notes

The definition follows the supremum form of Nailin Guan's Mathlib pull request
[mathlib4#29558](https://github.com/leanprover-community/mathlib4/pull/29558), including its
universe parameter `v` for the category of modules.

## References

* [Stacks Project, Section 10.109](https://stacks.math.columbia.edu/tag/00O6), Projective
  dimension: Definition 10.109.10 (00O6) and Lemmas 10.109.12 (065T) and 10.109.13 (00O8).
-/

public section

universe v u

open CategoryTheory

namespace TauCeti

section Ring

variable (R : Type u) [Ring R]

/-- The **global dimension** of a ring `R`: the supremum of the projective dimensions of all
`R`-modules in `ModuleCat.{v} R`. Stacks, Definition 10.109.10 (00O6). -/
@[stacks 00O6]
noncomputable def globalDimension : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{v} R, projectiveDimension M

/-- Unfolds `globalDimension` as the supremum of the projective dimensions of all modules. -/
theorem globalDimension_def :
    globalDimension.{v} R = ⨆ M : ModuleCat.{v} R, projectiveDimension M := by
  rw [globalDimension]

variable {R} in
/-- The projective dimension of every module is at most the global dimension of the ring. -/
theorem _root_.ModuleCat.projectiveDimension_le_globalDimension (M : ModuleCat.{v} R) :
    projectiveDimension M ≤ globalDimension.{v} R :=
  le_iSup (fun M : ModuleCat.{v} R ↦ projectiveDimension M) M

/-- The global dimension is at most `d` iff every module has projective dimension at most `d`. -/
theorem globalDimension_le_iff (d : WithBot ℕ∞) :
    globalDimension.{v} R ≤ d ↔ ∀ M : ModuleCat.{v} R, projectiveDimension M ≤ d :=
  iSup_le_iff

/-- The global dimension is at most `n` iff every module has projective dimension at most `n`. -/
theorem globalDimension_le_iff_hasProjectiveDimensionLE (n : ℕ) :
    globalDimension.{v} R ≤ n ↔ ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n := by
  simp [globalDimension, projectiveDimension_le_iff]

/-- Only the zero ring has global dimension `⊥`. -/
@[simp]
theorem globalDimension_eq_bot_iff [Small.{v} R] :
    globalDimension.{v} R = ⊥ ↔ Subsingleton R := by
  simp only [globalDimension, iSup_eq_bot, projectiveDimension_eq_bot_iff,
    ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun h ↦ (equivShrink.{v} R).subsingleton_congr.mpr (h (ModuleCat.of R (Shrink.{v} R))),
    fun _ M ↦ Module.subsingleton R M⟩

/-- **The global dimension is detected on finite and on cyclic modules.** For a natural number
`n`, the following are equivalent: the global dimension of `R` is at most `n`; every finite
`R`-module has projective dimension at most `n`; every cyclic module `R ⧸ I` has projective
dimension at most `n`. Stacks, Lemma 10.109.12 (065T). -/
@[stacks 065T]
theorem globalDimension_le_tfae [Small.{v} R] (n : ℕ) :
    [globalDimension.{v} R ≤ n,
      ∀ M : ModuleCat.{v} R, Module.Finite R M → HasProjectiveDimensionLE M n,
      ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ I))) n].TFAE := by
  tfae_have 1 → 2 := fun h M _ ↦ (globalDimension_le_iff_hasProjectiveDimensionLE R n).mp h M
  tfae_have 2 → 3 := fun h I ↦
    h _ (Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm)
  tfae_have 3 → 1 := fun h ↦ (globalDimension_le_iff_hasProjectiveDimensionLE R n).mpr
    (ModuleCat.hasProjectiveDimensionLE_of_quotients n h)
  tfae_finish

/-- A nonzero semisimple ring, for instance a field or a division ring, has global dimension
zero: every module over it is projective. -/
theorem globalDimension_eq_zero_of_isSemisimpleRing [IsSemisimpleRing R] [Nontrivial R]
    [Small.{v} R] : globalDimension.{v} R = 0 := by
  refine le_antisymm (iSup_le fun M ↦ ?_) ?_
  · have := Module.projective_of_isSemisimpleRing R M
    exact Projective.projectiveDimension_le_zero M
  · have hR : ¬ Limits.IsZero (ModuleCat.of R (Shrink.{v} R)) := by
      rw [ModuleCat.isZero_iff_subsingleton, ← (equivShrink.{v} R).subsingleton_congr]
      exact not_subsingleton R
    exact ((projectiveDimension_ge_zero_iff _).mpr hR).trans
      (ModuleCat.projectiveDimension_le_globalDimension _)

end Ring

section CommRing

variable {R : Type u} [CommRing R]

/-- **Localization does not increase the global dimension.** For a submonoid `S` of `R`, the
global dimension of `S⁻¹R` is at most that of `R`. Stacks, Lemma 10.109.13 (00O8). -/
@[stacks 00O8]
theorem _root_.Submonoid.globalDimension_localization_le [Small.{v} R] (S : Submonoid R) :
    globalDimension.{v} (Localization S) ≤ globalDimension.{v} R := by
  refine iSup_le fun N ↦ ?_
  let : Module R N := Module.compHom N (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := isLocalizedModule_id S N (Localization S)
  let M : ModuleCat.{v} R := ModuleCat.of R N
  let e : M.localizedModule S ≅ N := LinearEquiv.toModuleIso
    ((IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S)
      (LinearMap.id : N →ₗ[R] N)).extendScalarsOfIsLocalization S (Localization S))
  rw [← projectiveDimension_eq_of_iso e]
  exact (ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule S M).trans
    (ModuleCat.projectiveDimension_le_globalDimension M)

end CommRing

end TauCeti
