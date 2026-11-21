/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace
public import TauCeti.Analysis.Variational.DirectMethod
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Compact operators and perturbations in the direct method

In infinite dimensions, compact operators and nonlinear lower-order terms `g ∘ J` need not be
globally weakly continuous, and compactly defined constraint sets such as `{u ∈ S | J u ∈ C}` (for
example, Rayleigh normalization spheres `{u | ‖J u‖ = 1}`) need not be weakly closed in general.
Nevertheless, once an energy controls norm sublevels (`TauCeti.HasBoundedSublevelsOn`), every
variational argument localizes to closed norm balls, which are weakly closed over `ℝ` or `ℂ`
(`TauCeti.isClosed_toWeakSpace_closedBall`) and on which a compact operator `J` is weak-to-norm
continuous (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`).

This file specializes the general bounded-ball localization theorems of
`TauCeti.Analysis.Variational.DirectMethod` to compact perturbations and compact constraints:

1. **Compact perturbations of weakly lower semicontinuous energies.** If `E₀` is weakly lower
   semicontinuous on `S`, `J : V →L[𝕜] F` is compact, `g : F → β` is lower semicontinuous on
   `J '' S`, and the perturbed functional `u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then
   `u ↦ E₀ u + g (J u)` is globally weakly lower semicontinuous on `S`
   (`IsCompactOperator.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn`),
   attains its minimum on any nonempty `S` whose intersections with closed norm balls are weakly
   closed (`IsCompactOperator.exists_isMinOn_add_comp_of_isClosed_toWeakSpace_inter_closedBall`,
   and `IsCompactOperator.exists_isMinOn_add_comp` for weakly closed `S`), and has a weakly compact
   set of minimizers.

2. **The direct method under non-weakly-closed compact constraints.** For a weakly closed set `S`, a
   compact operator `J : V →L[𝕜] F`, and a closed set `C ⊆ F`, every intersection
   `(S ∩ J ⁻¹' C) ∩ closedBall 0 R` is weakly closed
   (`IsCompactOperator.isClosed_toWeakSpace_inter_preimage_inter_closedBall`). Therefore every
   norm-bounded sublevel `{u ∈ S ∩ J ⁻¹' C | E u ≤ b}` of an energy `E` that is weakly lower
   semicontinuous on `S ∩ J ⁻¹' C` is weakly closed
   (`IsCompactOperator.isClosed_toWeakSpace_sublevel_inter_preimage`) and, in a reflexive space,
   weakly compact (`IsCompactOperator.isCompact_toWeakSpace_sublevel_inter_preimage`). Consequently,
   `E` attains its minimum on `S ∩ J ⁻¹' C` and its set of minimizers is weakly compact
   (`IsCompactOperator.exists_isMinOn_inter_preimage`,
   `IsCompactOperator.isCompact_toWeakSpace_minimizers_inter_preimage`), including for compactly
   perturbed energies `u ↦ E₀ u + g (J₂ u)` under an independent compact constraint `J₁ ⁻¹' C`
   (`IsCompactOperator.exists_isMinOn_add_comp_inter_preimage`,
   `IsCompactOperator.isCompact_toWeakSpace_minimizers_add_comp_inter_preimage`).

## References

* M. Struwe, *Variational Methods*, 4th ed., Springer, 2008, Theorem I.1.2 and Section I.2.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications, III: Variational Methods and
  Optimization*, Springer, 1985, §38.3 and §38.7.
-/

public section

open Bornology Filter Function Metric NormedSpace Set Topology

namespace IsCompactOperator

section CompactPerturbation

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
  {J : V →L[𝕜] F}

/-- **Global weak lower semicontinuity of a compact perturbation under bounded sublevels.** Over
`ℝ` or `ℂ`, if `E₀` is weakly lower semicontinuous on `S`, `J : V →L[𝕜] F` is compact, `g : F → β`
is lower semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then
`u ↦ E₀ u + g (J u)` is globally weakly lower semicontinuous on `S`. -/
theorem lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn
    (hJ : IsCompactOperator J) {S : Set V} {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦
        E₀ ((toWeakSpace 𝕜 V).symm w) + g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' S) :=
  TauCeti.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hb fun _ hBS hB ↦
    hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm hB
      (hE₀.mono (image_mono hBS)) (hg.mono (image_mono hBS))

/-- **Direct method for compactly perturbed energies with bounded-ball weak closedness.** In a
reflexive seminormed space over `ℝ` or `ℂ`, if `S` is nonempty, `S ∩ closedBall 0 R` is weakly
closed for every `R : ℝ`, `E₀` is weakly lower semicontinuous on `S`, `J` is compact, `g` is lower
semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then
`u ↦ E₀ u + g (J u)` attains its minimum on `S`. -/
theorem exists_isMinOn_add_comp_of_isClosed_toWeakSpace_inter_closedBall
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J) {S : Set V}
    (hne : S.Nonempty) (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)))
    {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    ∃ u ∈ S, IsMinOn (fun v ↦ E₀ v + g (J v)) S u := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall hV hne hS
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, if `S ∩ closedBall 0 R` is weakly closed for
every `R : ℝ`, `E₀` is weakly lower semicontinuous on `S`, `J` is compact, `g` is lower
semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then the set of
minimizers of `u ↦ E₀ u + g (J u)` on `S` is weakly compact, including when `S` is empty. -/
theorem isCompact_toWeakSpace_minimizers_add_comp_of_isClosed_toWeakSpace_inter_closedBall
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J) {S : Set V}
    (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R))) {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn (fun v ↦ E₀ v + g (J v)) S u}) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall hV hS
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

/-- **Direct method for compactly perturbed energies.** In a reflexive seminormed space over `ℝ` or
`ℂ`, if `S` is nonempty and weakly closed, `E₀` is weakly lower semicontinuous on `S`, `J` is
compact, `g` is lower semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on
`S`, then `u ↦ E₀ u + g (J u)` attains its minimum on `S`. -/
theorem exists_isMinOn_add_comp (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J) {S : Set V} (hne : S.Nonempty)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    ∃ u ∈ S, IsMinOn (fun v ↦ E₀ v + g (J v)) S u := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.exists_isMinOn_of_weak_closed hV hne hS
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, if `S` is weakly closed, `E₀` is weakly lower
semicontinuous on `S`, `J` is compact, `g` is lower semicontinuous on `J '' S`, and
`u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then the set of minimizers of
`u ↦ E₀ u + g (J u)` on `S` is weakly compact, including when `S` is empty. -/
theorem isCompact_toWeakSpace_minimizers_add_comp (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J) {S : Set V} (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn (fun v ↦ E₀ v + g (J v)) S u}) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.isCompact_toWeakSpace_minimizers hV hS
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

end CompactPerturbation

section CompactConstraint

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)]
  [LinearOrder β] {J : V →L[𝕜] F} {S : Set V} {C : Set F} {E : V → β}

/-- **Weak closedness of bounded sublevels on compactly constrained sets.** Over `ℝ` or `ℂ`, even
though `S ∩ J ⁻¹' C` need not be weakly closed, if `S` is weakly closed, `J` is compact, `C ⊆ F` is
closed, and `E` is weakly lower semicontinuous on `S ∩ J ⁻¹' C`, then every norm-bounded sublevel
`{u ∈ S ∩ J ⁻¹' C | E u ≤ b}` is closed in the weak topology. -/
theorem isClosed_toWeakSpace_sublevel_inter_preimage (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (b : β) (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) :
    IsClosed (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) :=
  TauCeti.isClosed_toWeakSpace_sublevel_of_isClosed_toWeakSpace_inter_closedBall
    (hJ.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE b hb

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, if `S` is weakly closed, `J` is compact,
`C ⊆ F` is closed, and `E` is weakly lower semicontinuous on `S ∩ J ⁻¹' C`, then every norm-bounded
sublevel `{u ∈ S ∩ J ⁻¹' C | E u ≤ b}` is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_inter_preimage
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (b : β) (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.isCompact_toWeakSpace_sublevel_of_isClosed_toWeakSpace_inter_closedBall hV
    (hJ.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE b hb

/-- **Single-sublevel direct method under a compact constraint.** In a reflexive seminormed space
over `ℝ` or `ℂ`, if `S` is weakly closed, `J` is compact, `C ⊆ F` is closed, and `E` is weakly
lower semicontinuous on `S ∩ J ⁻¹' C`, then a single nonempty norm-bounded sublevel
`{u ∈ S ∩ J ⁻¹' C | E u ≤ b}` suffices for `E` to attain its minimum on `S ∩ J ⁻¹' C`, without
requiring `S ∩ J ⁻¹' C` itself to be weakly closed. -/
theorem exists_isMinOn_inter_preimage_of_isBounded_sublevel
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    {b : β} (hne : {u ∈ S ∩ J ⁻¹' C | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) :
    ∃ u ∈ S ∩ J ⁻¹' C, IsMinOn E (S ∩ J ⁻¹' C) u := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall_of_isBounded_sublevel hV
    (hJ.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE hne hb

/-- **The direct method under a compact constraint.** In a reflexive seminormed space over `ℝ` or
`ℂ`, if `S` is weakly closed, `J` is compact, `C ⊆ F` is closed, `S ∩ J ⁻¹' C` is nonempty, and `E`
is weakly lower semicontinuous with norm-bounded sublevels on `S ∩ J ⁻¹' C`, then `E` attains its
minimum on `S ∩ J ⁻¹' C`. -/
theorem exists_isMinOn_inter_preimage
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hne : (S ∩ J ⁻¹' C).Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn E (S ∩ J ⁻¹' C)) :
    ∃ u ∈ S ∩ J ⁻¹' C, IsMinOn E (S ∩ J ⁻¹' C) u := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall hV hne
    (hJ.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE hb

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, if `S` is weakly closed, `J` is compact,
`C ⊆ F` is closed, `E` is weakly lower semicontinuous on `S ∩ J ⁻¹' C`, and the set of minimizers of
`E` on `S ∩ J ⁻¹' C` is norm-bounded, then that set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_inter_preimage_of_isBounded
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | IsMinOn E (S ∩ J ⁻¹' C) u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | IsMinOn E (S ∩ J ⁻¹' C) u}) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact
    TauCeti.isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall_of_isBounded
      hV (hJ.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE hb

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, for an energy `E` that is weakly lower
semicontinuous and has norm-bounded sublevels on `S ∩ J ⁻¹' C` (with `S` weakly closed, `J` compact,
and `C` closed), the set of minimizers of `E` on `S ∩ J ⁻¹' C` is weakly compact, including when
`S ∩ J ⁻¹' C` is empty. -/
theorem isCompact_toWeakSpace_minimizers_inter_preimage
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn E (S ∩ J ⁻¹' C)) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | IsMinOn E (S ∩ J ⁻¹' C) u}) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall hV
    (hJ.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE hb

/-- **Direct method for compactly perturbed energies under a compact constraint.** In a reflexive
seminormed space over `ℝ` or `ℂ`, if `S` is weakly closed, `J₁ : V →L[𝕜] F` and `J₂ : V →L[𝕜] F₂`
are compact, `C ⊆ F` is closed, `S ∩ J₁ ⁻¹' C` is nonempty, `E₀` is weakly lower semicontinuous on
`S ∩ J₁ ⁻¹' C`, `g` is lower semicontinuous on `J₂ '' (S ∩ J₁ ⁻¹' C)`, and `u ↦ E₀ u + g (J₂ u)`
has bounded sublevels on `S ∩ J₁ ⁻¹' C`, then `u ↦ E₀ u + g (J₂ u)` attains its minimum on
`S ∩ J₁ ⁻¹' C`. -/
theorem exists_isMinOn_add_comp_inter_preimage
    {F₂ γ : Type*} [TopologicalSpace F₂] [AddCommMonoid F₂] [Module 𝕜 F₂]
    [ContinuousConstSMul 𝕜 F₂] [T2Space (WeakSpace 𝕜 F₂)]
    [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
    [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ]
    {J₁ : V →L[𝕜] F} {J₂ : V →L[𝕜] F₂}
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ₁ : IsCompactOperator J₁) (hJ₂ : IsCompactOperator J₂)
    (hne : (S ∩ J₁ ⁻¹' C).Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    {E₀ : V → γ} {g : F₂ → γ}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J₁ ⁻¹' C)))
    (hg : LowerSemicontinuousOn g (J₂ '' (S ∩ J₁ ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J₂ u)) (S ∩ J₁ ⁻¹' C)) :
    ∃ u ∈ S ∩ J₁ ⁻¹' C, IsMinOn (fun v ↦ E₀ v + g (J₂ v)) (S ∩ J₁ ⁻¹' C) u :=
  hJ₂.exists_isMinOn_add_comp_of_isClosed_toWeakSpace_inter_closedBall hV hne
    (hJ₁.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE₀ hg hb

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, if `S` is weakly closed, `J₁ : V →L[𝕜] F` and
`J₂ : V →L[𝕜] F₂` are compact, `C ⊆ F` is closed, `E₀` is weakly lower semicontinuous on
`S ∩ J₁ ⁻¹' C`, `g` is lower semicontinuous on `J₂ '' (S ∩ J₁ ⁻¹' C)`, and `u ↦ E₀ u + g (J₂ u)`
has bounded sublevels on `S ∩ J₁ ⁻¹' C`, then the set of minimizers of `u ↦ E₀ u + g (J₂ u)` on
`S ∩ J₁ ⁻¹' C` is weakly compact, including when `S ∩ J₁ ⁻¹' C` is empty. -/
theorem isCompact_toWeakSpace_minimizers_add_comp_inter_preimage
    {F₂ γ : Type*} [TopologicalSpace F₂] [AddCommMonoid F₂] [Module 𝕜 F₂]
    [ContinuousConstSMul 𝕜 F₂] [T2Space (WeakSpace 𝕜 F₂)]
    [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
    [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ]
    {J₁ : V →L[𝕜] F} {J₂ : V →L[𝕜] F₂}
    (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ₁ : IsCompactOperator J₁) (hJ₂ : IsCompactOperator J₂)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    {E₀ : V → γ} {g : F₂ → γ}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J₁ ⁻¹' C)))
    (hg : LowerSemicontinuousOn g (J₂ '' (S ∩ J₁ ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J₂ u)) (S ∩ J₁ ⁻¹' C)) :
    IsCompact (toWeakSpace 𝕜 V ''
      {u ∈ S ∩ J₁ ⁻¹' C | IsMinOn (fun v ↦ E₀ v + g (J₂ v)) (S ∩ J₁ ⁻¹' C) u}) :=
  hJ₂.isCompact_toWeakSpace_minimizers_add_comp_of_isClosed_toWeakSpace_inter_closedBall hV
    (hJ₁.isClosed_toWeakSpace_inter_preimage_inter_closedBall hS hC 0) hE₀ hg hb

end CompactConstraint

end IsCompactOperator
