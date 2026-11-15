/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.InductiveDimension.Classes

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Piecewise

/-!
# Continuous extension from a compact subset of a zero-dimensional space

Let `X` be a zero-dimensional space — one with a basis of clopen sets, such as a profinite space —
and let `Y` be a discrete space. This file proves that a continuous map into `Y` defined on a
*compact* subset `s ⊆ X` extends to a continuous map on all of `X`, as soon as one of `s` and `Y`
is nonempty; equivalently, that restriction `C(X, Y) → C(s, Y)` is surjective for every compact
`s ⊆ X` when `Y` is nonempty.

This is the zero-dimensional analogue of the Tietze extension theorem. Nothing can be averaged
here, since `Y` is a bare discrete space; instead each point of `s` has a clopen neighbourhood on
whose trace on `s` the map is constant, finitely many of these cover `s` by compactness, and the
extension is glued from the constant values on these clopens.

## Main results

* `TauCeti.exists_continuous_eqOn_range_subset_image`: for a nonempty compact `s`, a map
  continuous on `s` extends to a continuous map on `X` whose range is still contained in the
  image of `s`.
* `TauCeti.exists_continuous_eqOn`: an ambient function continuous on an arbitrary compact `s`
  agrees there with a continuous function on `X`, without a nonemptiness assumption.
* `ContinuousMap.exists_restrict_eq_of_discrete` and
  `ContinuousMap.restrict_surjective_of_discrete`: the bundled form, for a compact set.
* `ContinuousMap.exists_extension_of_discrete`: the bundled form, for an embedding of a compact
  space.

## Implementation notes

The statements come both for a bare function together with `ContinuousOn` and for bundled
`ContinuousMap`s. The unbundled form is the one continuous cochains are written in, and the bundled
form mirrors Mathlib's Tietze API; it lives in the root `ContinuousMap` namespace, so that dot
notation on a `C(s, Y)` reaches it, and carries an `_of_discrete` suffix to distinguish it from
Mathlib's `TietzeExtension` form of the same statement.

The bundled forms need a nonemptiness hypothesis. If `s` is empty and `Y` is empty while `X` is not,
there is a continuous map on `s` and none on `X`, so one of `s` and `Y` has to be assumed nonempty.
In the unbundled form, the ambient function `f : X → Y` already rules out this obstruction.

Zero-dimensionality of `X` is not decoration either. On the compact Hausdorff space
`[0, 1] ⊆ ℝ` no map into a discrete space separates the two points of the compact subset
`{0, 1}`, so a map taking two distinct values there has no continuous extension; this is spelled
out as an example in `TauCeti/Topology/LocallyConstant/Preconnected.lean`, where the
preconnectedness that drives it lives. Compactness of `s` is what makes finitely many clopens
suffice, and discreteness of `Y` is what makes the map locally constant on `s`.
-/

public section

open Set Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [ZeroDimensionalSpace X] [DiscreteTopology Y] {s : Set X}

/-- **Continuous extension from a compact subset of a zero-dimensional space.** A map continuous
on a nonempty compact subset `s` of a zero-dimensional space, with values in a discrete space,
extends to a continuous map on the whole space, and the extension can be chosen to take no value
that is not already taken on `s`.

That last clause is what lets a consumer keep the extension inside a subgroup, a submodule, or any
other set the original values lie in. -/
theorem exists_continuous_eqOn_range_subset_image {f : X → Y} (hs : IsCompact s)
    (hsne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ g : X → Y, Continuous g ∧ EqOn g f s ∧ range g ⊆ f '' s := by
  classical
  -- Each point `x` of `s` has a clopen neighbourhood `U x` on whose trace on `s` the map `f` is
  -- constant, and finitely many of these cover `s`.
  choose U hU hUf using fun x : s ↦ ((nhdsWithin_hasBasis (nhds_basis_isClopen (x : X)) s).mem_iff.1
    ((hf x x.2).preimage_mem_nhdsWithin ((isOpen_discrete {f x}).mem_nhds rfl)))
  obtain ⟨t, ht⟩ := hs.elim_nhds_subcover' (fun x hx ↦ U ⟨x, hx⟩)
    fun x hx ↦ (hU ⟨x, hx⟩).1.isOpen.mem_nhds (hU ⟨x, hx⟩).2
  -- Glue the constant values of `f` on the clopens `U x`, `x ∈ t`, one clopen at a time.
  suffices ∀ t : Finset s, ∃ g : X → Y, Continuous g ∧ EqOn g f (s ∩ ⋃ x ∈ t, U x) ∧
      range g ⊆ f '' s by
    obtain ⟨g, hg, hgf, hgs⟩ := this t
    exact ⟨g, hg, fun x hx ↦ hgf ⟨hx, ht hx⟩, hgs⟩
  intro t
  induction t using Finset.induction_on with
  | empty =>
    obtain ⟨x, hx⟩ := hsne
    exact ⟨fun _ ↦ f x, continuous_const, by simp, range_subset_iff.2 fun _ ↦ mem_image_of_mem f hx⟩
  | insert a t _ ih =>
    obtain ⟨g, hg, hgf, hgs⟩ := ih
    refine ⟨(U a).piecewise (fun _ ↦ f a) g,
      continuous_const.piecewise (by simp [(hU a).1.frontier_eq]) hg, ?_, ?_⟩
    · rintro x ⟨hxs, hx⟩
      by_cases hxa : x ∈ U a
      · simpa [hxa, eq_comm] using hUf a ⟨hxa, hxs⟩
      · simpa [hxa] using hgf ⟨hxs, by simpa [hxa] using hx⟩
    · rintro _ ⟨x, rfl⟩
      by_cases hxa : x ∈ U a
      · simpa [hxa] using mem_image_of_mem f a.2
      · simpa [hxa] using hgs (mem_range_self x)

/-- **Continuous extension from a compact subset of a zero-dimensional space**, for an ambient
function continuous on an arbitrary compact subset. No nonemptiness hypothesis is needed. -/
theorem exists_continuous_eqOn {f : X → Y} (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ g : X → Y, Continuous g ∧ EqOn g f s := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨f, continuous_of_discreteTopology, fun _ _ ↦ rfl⟩
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨fun _ ↦ f (Classical.arbitrary X), continuous_const, by simp⟩
  · obtain ⟨g, hg, hgf, -⟩ := exists_continuous_eqOn_range_subset_image hs hsne hf
    exact ⟨g, hg, hgf⟩

end TauCeti

/-! ### The bundled form

These live in the root `ContinuousMap` namespace, next to Mathlib's Tietze extension theorems and
within reach of dot notation on a `C(s, Y)`. -/

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [ZeroDimensionalSpace X] [DiscreteTopology Y] {s : Set X}

/-- **Continuous extension from a compact subset of a zero-dimensional space**, bundled: a
continuous map on a compact subset of a zero-dimensional space, with values in a nonempty discrete
space, is the restriction of a continuous map on the whole space.

This is the zero-dimensional counterpart of Mathlib's `ContinuousMap.exists_restrict_eq`, whose
`TietzeExtension` hypothesis on the target no discrete space with more than one point
satisfies. -/
theorem exists_restrict_eq_of_discrete [Nonempty Y] (hs : IsCompact s) (f : C(s, Y)) :
    ∃ g : C(X, Y), g.restrict s = f := by
  classical
  -- Spread `f` out to a map on `X` by an arbitrary value off `s`; only its continuity on `s`
  -- matters.
  have hF (x : s) :
      Function.extend Subtype.val f (fun _ ↦ Classical.arbitrary Y) (x : X) = f x :=
    Subtype.val_injective.extend_apply _ _ x
  obtain ⟨g, hg, hgf⟩ :=
    TauCeti.exists_continuous_eqOn
      (f := Function.extend Subtype.val f fun _ ↦ Classical.arbitrary Y)
      hs (continuousOn_iff_continuous_domRestrict.2 (f.continuous.congr fun x ↦ (hF x).symm))
  exact ⟨⟨g, hg⟩, ext fun x ↦ (hgf x.2).trans (hF x)⟩

/-- Restriction of continuous maps to a compact subset of a zero-dimensional space is surjective,
when the target is discrete and nonempty. -/
theorem restrict_surjective_of_discrete [Nonempty Y] (hs : IsCompact s) :
    Function.Surjective fun g : C(X, Y) ↦ g.restrict s :=
  fun f ↦ exists_restrict_eq_of_discrete hs f

/-- **Continuous extension along an embedding of a compact space into a zero-dimensional space.**

The statement and the deduction of this form from the subset form follow Mathlib's
`ContinuousMap.exists_extension` in `Mathlib/Topology/TietzeExtension.lean`. -/
theorem exists_extension_of_discrete [Nonempty Y] {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {e : Z → X} (he : IsEmbedding e) (f : C(Z, Y)) :
    ∃ g : C(X, Y), g.comp ⟨e, he.continuous⟩ = f := by
  -- `he.toHomeomorph : Z ≃ₜ range e` identifies `Z` with the compact subset `range e`, so `f`
  -- transports to a continuous map on `range e`.
  obtain ⟨g, hg⟩ := exists_restrict_eq_of_discrete (isCompact_range he.continuous)
    (f.comp ⟨he.toHomeomorph.symm, he.toHomeomorph.symm.continuous⟩)
  refine ⟨g, ext fun x ↦ ?_⟩
  simpa [he.toHomeomorph_symm_apply] using congr($(hg) ⟨e x, x, rfl⟩)

end ContinuousMap
