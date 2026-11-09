/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.Algebra.Module.PseudoCoherent.FaithfullyFlat
import TauCeti.RingTheory.Regular.ProjectiveDimension

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
* `TauCeti.globalDimension_eq_iSup_cyclic`, `TauCeti.globalDimension_eq_iSup_finite`:
  **Auslander's theorem**, the global dimension is the supremum of the projective dimensions of
  the cyclic modules `R ⧸ I`, and also of the finite modules.
* `Submonoid.globalDimension_localization_le`: localization does not increase the global dimension
  (Stacks, Lemma 10.109.13 (00O8)).
* `TauCeti.globalDimension_le_of_faithfullyFlat`: a noetherian ring has global dimension at most
  that of any faithfully flat algebra over it.
* `TauCeti.globalDimension_eq_zero_of_isSemisimpleRing`: a nonzero semisimple ring, for instance
  a field, has global dimension zero.
* `TauCeti.globalDimension_eq_one_of_isPrincipalIdealRing`: a principal ideal domain that is not
  a field, for instance `ℤ`, has global dimension one.
* `TauCeti.globalDimension_eq_globalDimension`: the global dimension does not depend on the
  universe of the modules.

## Implementation notes

The definition follows the supremum form of Nailin Guan's Mathlib pull request
[mathlib4#29558](https://github.com/leanprover-community/mathlib4/pull/29558), including its
universe parameter `v` for the category of modules.

## References

* [Stacks Project, Section 10.109](https://stacks.math.columbia.edu/tag/00O6), Projective
  dimension: Definition 10.109.10 (00O6) and Lemmas 10.109.12 (065T) and 10.109.13 (00O8).
* M. Auslander, *On the dimension of modules and algebras III. Global dimension*, Nagoya Math. J.
  9 (1955), 67–77, Theorem 1.
-/

public section

universe v v' u

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

/-- **Auslander's theorem: the global dimension is the supremum over cyclic modules.** The global
dimension of `R` is the supremum of the projective dimensions of the cyclic modules `R ⧸ I`, for
`I` a left ideal. M. Auslander, *On the dimension of modules and algebras III*, Theorem 1. -/
theorem globalDimension_eq_iSup_cyclic [Small.{v} R] :
    globalDimension.{v} R =
      ⨆ I : Ideal R, projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ I))) := by
  refine le_antisymm ?_ (iSup_le fun I ↦ ModuleCat.projectiveDimension_le_globalDimension _)
  induction h : ⨆ I : Ideal R, projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    using WithBot.recBotCoe with
  | bot =>
    -- The module `R ⧸ ⊥ ≃ R` is zero, so `R` is the zero ring.
    have hR : Limits.IsZero (ModuleCat.of R (Shrink.{v} (R ⧸ (⊥ : Ideal R)))) :=
      (projectiveDimension_eq_bot_iff _).mp (iSup_eq_bot.mp h ⊥)
    rw [ModuleCat.isZero_iff_subsingleton] at hR
    have : Subsingleton R := ((Shrink.linearEquiv R _).trans
      (Submodule.quotEquivOfEqBot ⊥ rfl)).toEquiv.symm.subsingleton
    exact ((globalDimension_eq_bot_iff R).mpr this).le
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      exact ((globalDimension_le_tfae.{v} R n).out 3 1).mp fun I ↦
        (projectiveDimension_le_iff _ n).mp (h ▸ le_iSup _ I)

/-- **The global dimension is the supremum over finite modules.** The global dimension of `R` is
the supremum of the projective dimensions of the finite `R`-modules: this supremum lies between the
one over the cyclic modules (`TauCeti.globalDimension_eq_iSup_cyclic`) and the one over all
modules. -/
theorem globalDimension_eq_iSup_finite [Small.{v} R] :
    globalDimension.{v} R =
      ⨆ (M : ModuleCat.{v} R) (_ : Module.Finite R M), projectiveDimension M := by
  refine le_antisymm ?_ (iSup₂_le fun M _ ↦ M.projectiveDimension_le_globalDimension)
  rw [globalDimension_eq_iSup_cyclic]
  exact iSup_le fun I ↦ le_iSup₂_of_le (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    (Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm) le_rfl

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

/-- One inequality of `TauCeti.globalDimension_eq_globalDimension`: both sides are detected on
the cyclic modules `R ⧸ I`, whose projective dimension does not depend on the universe. -/
private theorem globalDimension_le_globalDimension [Small.{v} R] [Small.{v'} R] :
    globalDimension.{v} R ≤ globalDimension.{v'} R := by
  induction h : globalDimension.{v'} R using WithBot.recBotCoe with
  | bot =>
    exact ((globalDimension_eq_bot_iff.{v} R).mpr ((globalDimension_eq_bot_iff.{v'} R).mp h)).le
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      refine ((globalDimension_le_tfae.{v} R n).out 3 1).mp fun I ↦ ?_
      let M := ModuleCat.of R (Shrink.{v'} (R ⧸ I))
      have := (globalDimension_le_iff_hasProjectiveDimensionLE.{v'} R n).mp h.le M
      exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv.{v', v} (M := M)
        ((Shrink.linearEquiv.{v'} R (R ⧸ I)).trans (Shrink.linearEquiv.{v} R (R ⧸ I)).symm) n

/-- **The global dimension does not depend on the universe of the modules**, as long as the ring
is small in both universes. -/
theorem globalDimension_eq_globalDimension [Small.{v} R] [Small.{v'} R] :
    globalDimension.{v} R = globalDimension.{v'} R :=
  le_antisymm (globalDimension_le_globalDimension.{v, v'} R)
    (globalDimension_le_globalDimension.{v', v} R)

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

/-- **Global dimension descends along faithfully flat algebras.** A noetherian ring `R` has global
dimension at most that of any faithfully flat `R`-algebra `S`: the projective dimension of a
finite `R`-module equals that of its base change to `S`
(`ModuleCat.hasProjectiveDimensionLE_baseChange_iff`), and finite modules detect the global
dimension. -/
theorem globalDimension_le_of_faithfullyFlat {S : Type u} [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.FaithfullyFlat R S] :
    globalDimension.{u} R ≤ globalDimension.{u} S := by
  induction h : globalDimension.{u} S using WithBot.recBotCoe with
  | bot =>
    -- `S` is zero, and `R` embeds into `S`.
    have : Subsingleton S := (globalDimension_eq_bot_iff S).mp h
    have : Subsingleton R := (FaithfulSMul.algebraMap_injective R S).subsingleton
    exact ((globalDimension_eq_bot_iff R).mpr this).le
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      refine ((globalDimension_le_tfae.{u} R n).out 2 1).mp ?_
      intro M _
      exact (ModuleCat.hasProjectiveDimensionLE_baseChange_iff .of_isNoetherianRing).mp
        ((globalDimension_le_iff_hasProjectiveDimensionLE S n).mp h.le _)

/-- **A principal ideal domain that is not a field has global dimension one.** Every module has
projective dimension at most one, and a cyclic module `R ⧸ (a)` with `a` a nonzero nonunit has
projective dimension exactly one
(`ModuleCat.projectiveDimension_quotient_span_singleton_eq_one`). -/
theorem globalDimension_eq_one_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    [Small.{v} R] (hR : ¬ IsField R) : globalDimension.{v} R = 1 := by
  refine le_antisymm ((globalDimension_le_iff_hasProjectiveDimensionLE R 1).mpr inferInstance) ?_
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp hR
  obtain ⟨a, rfl⟩ := IsPrincipalIdealRing.principal I
  have ha : a ≠ 0 := by rintro rfl; simp at hbot
  have ha' : ¬ IsUnit a := fun h ↦ htop.ne (Ideal.span_singleton_eq_top.mpr h)
  exact (ModuleCat.projectiveDimension_quotient_span_singleton_eq_one
    (mem_nonZeroDivisors_of_ne_zero ha) ha').symm.le.trans
    (ModuleCat.projectiveDimension_le_globalDimension _)

end CommRing

end TauCeti
