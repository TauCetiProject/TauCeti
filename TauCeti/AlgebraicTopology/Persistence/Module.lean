/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Persistence modules, rank invariants and `q`-tameness

A real-indexed persistence module over a ring `R` is a functor `ℝ ⥤ ModuleCat R`, with `ℝ` the
preorder category of Mathlib (`Preorder.smallCategory`): a family of modules `V_t` with maps
`V_s → V_t` for `s ≤ t`, compatible with composition (Chazal–de Silva–Glisse–Oudot, *The
Structure and Stability of Persistence Modules*, §2.1, p. 17). Its rank invariant
`rankInv V s t` is the rank of `V_s → V_t` as an element of `ℕ∞` when `s ≤ t`, with infinite
ranks sent to `⊤`, and is `0` when `t < s`. The module is `q`-tame when every structure map across
a positive gap has finite rank.

## Main definitions

* `TauCeti.PersistenceModule R`: the functor category `ℝ ⥤ ModuleCat.{0} R`.
* `TauCeti.IsPFD V`: every `V_t` is a finite `R`-module (pointwise finite generation; over a
  field this is pointwise finite-dimensionality).
* `TauCeti.rankInv V s t`: the rank invariant.
* `TauCeti.IsQTame V`: `rankInv V s t < ⊤` whenever `s < t`.

## Main results

* `TauCeti.rankInv_le_rankInv`: ranks are monotone, `rankInv V s' t' ≤ rankInv V s t` for
  `s' ≤ s ≤ t ≤ t'`, since the long map factors through the short one; the one-sided forms are
  `TauCeti.rankInv_le_rankInv_left` and `TauCeti.rankInv_le_rankInv_right`.
* `TauCeti.rankInv_self`: on the diagonal the rank invariant is the rank of `V_t`.
* `CategoryTheory.Iso.rankInv_congr`, `CategoryTheory.Iso.isPFD_congr`,
  `CategoryTheory.Iso.isQTame_congr`: the three notions are invariant under isomorphism of
  persistence modules.
* `TauCeti.IsPFD.isQTame`: over a ring with the strong rank condition (for instance a field),
  every pointwise finitely generated module is `q`-tame.

The definitions are stated over any ring; the usual setting is a field, which is a special case.
Over a field `𝕜`, `IsPFD` says that every `V_t` is finite-dimensional, and `rankInv V s t` is the
dimension of the image of `V_s → V_t`, with infinite dimensions collapsed to `⊤`: it counts the
features present at `s` that survive to `t`, and persistence diagrams are built from it. For
field-valued modules, `q`-tameness is the finiteness condition under which
Chazal–de Silva–Glisse–Oudot define the persistence diagram.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

variable (R : Type u) [Ring R]

/-- A real-indexed persistence module over `R`: a functor from the real line, as a preorder
category, to modules over `R`. -/
abbrev PersistenceModule := ℝ ⥤ ModuleCat.{0} R

variable {R}

/-- A persistence module is pointwise finitely generated when every `V_t` is a finite `R`-module.
Over a field this says that every `V_t` is finite-dimensional (pointwise finite-dimensional). -/
def IsPFD (V : PersistenceModule R) : Prop :=
  ∀ t, Module.Finite R (V.obj t)

/-- The rank invariant: `rankInv V s t` is the rank of the structure map `V_s → V_t` in `ℕ∞`
(an infinite rank is `⊤`) when `s ≤ t`, and `0` when `t < s`. -/
def rankInv (V : PersistenceModule R) (s t : ℝ) : ℕ∞ :=
  if h : s ≤ t then Cardinal.toENat (V.map (homOfLE h)).hom.rank else 0

/-- A persistence module is `q`-tame when every structure map across a positive gap has finite
rank. -/
def IsQTame (V : PersistenceModule R) : Prop :=
  ∀ s t, s < t → rankInv V s t < ⊤

variable {V W : PersistenceModule R} {s s' t t' : ℝ}

/-- Unfolding `IsPFD`. -/
theorem isPFD_iff : IsPFD V ↔ ∀ t, Module.Finite R (V.obj t) := Iff.rfl

/-- Unfolding `rankInv`. -/
theorem rankInv_def (V : PersistenceModule R) (s t : ℝ) :
    rankInv V s t =
      if h : s ≤ t then Cardinal.toENat (V.map (homOfLE h)).hom.rank else 0 := (rfl)

/-- Unfolding `IsQTame`. -/
theorem isQTame_iff : IsQTame V ↔ ∀ s t, s < t → rankInv V s t < ⊤ := Iff.rfl

/-- For `s ≤ t`, the rank invariant is the rank of the structure map `V_s → V_t`. -/
theorem rankInv_of_le (V : PersistenceModule R) (h : s ≤ t) :
    rankInv V s t = Cardinal.toENat (V.map (homOfLE h)).hom.rank := by
  simp [rankInv_def, h]

/-- The rank invariant vanishes below the diagonal. -/
@[simp]
theorem rankInv_eq_zero_of_gt (V : PersistenceModule R) (h : t < s) : rankInv V s t = 0 := by
  simp [rankInv_def, h.not_ge]

/-- On the diagonal, the rank invariant is the rank of `V_t`. -/
@[simp]
theorem rankInv_self (V : PersistenceModule R) (t : ℝ) :
    rankInv V t t = Cardinal.toENat (Module.rank R (V.obj t)) :=
  -- the structure map `V_t → V_t` is the identity, so its range is all of `V_t`
  (rankInv_of_le V le_rfl).trans <| congrArg _ <|
    rank_range_of_surjective _ fun x => ⟨x, by simp⟩

/-- The rank invariant is at most the rank of the source module. -/
theorem rankInv_le_rank_obj_left (V : PersistenceModule R) (s t : ℝ) :
    rankInv V s t ≤ Cardinal.toENat (Module.rank R (V.obj s)) := by
  rw [rankInv_def]
  split_ifs
  · exact OrderHomClass.mono _ (LinearMap.rank_le_domain _)
  · exact zero_le

/-- The rank invariant is at most the rank of the target module. -/
theorem rankInv_le_rank_obj_right (V : PersistenceModule R) (s t : ℝ) :
    rankInv V s t ≤ Cardinal.toENat (Module.rank R (V.obj t)) := by
  rw [rankInv_def]
  split_ifs
  · exact OrderHomClass.mono _ (LinearMap.rank_le_range _)
  · exact zero_le

/-- The structure map across `r ≤ s ≤ t` is the composite of the two shorter structure maps,
as linear maps. -/
private theorem hom_map_homOfLE_trans (V : PersistenceModule R) {r : ℝ} (hrs : r ≤ s)
    (hst : s ≤ t) :
    (V.map (homOfLE (hrs.trans hst))).hom =
      (V.map (homOfLE hst)).hom ∘ₗ (V.map (homOfLE hrs)).hom := by
  simp [← ModuleCat.hom_comp, ← V.map_comp]

/-- Lowering the first index can only lower the rank invariant: for `s' ≤ s ≤ t`, the map
`V_{s'} → V_t` factors through `V_s → V_t`. -/
theorem rankInv_le_rankInv_left (V : PersistenceModule R) (hs : s' ≤ s) (hst : s ≤ t) :
    rankInv V s' t ≤ rankInv V s t := by
  rw [rankInv_of_le V (hs.trans hst), rankInv_of_le V hst, hom_map_homOfLE_trans V hs hst]
  exact OrderHomClass.mono _ (LinearMap.rank_comp_le_left _ _)

/-- Raising the second index can only lower the rank invariant: for `s ≤ t ≤ t'`, the map
`V_s → V_{t'}` factors through `V_s → V_t`. -/
theorem rankInv_le_rankInv_right (V : PersistenceModule R) (hst : s ≤ t) (ht : t ≤ t') :
    rankInv V s t' ≤ rankInv V s t := by
  rw [rankInv_of_le V (hst.trans ht), rankInv_of_le V hst, hom_map_homOfLE_trans V hst ht]
  exact OrderHomClass.mono _ (LinearMap.rank_comp_le_right _ _)

/-- Ranks are monotone: `rankInv V s' t' ≤ rankInv V s t` for `s' ≤ s ≤ t ≤ t'`, since the map
`V_{s'} → V_{t'}` factors through `V_s → V_t`. -/
theorem rankInv_le_rankInv (V : PersistenceModule R) (hs : s' ≤ s) (hst : s ≤ t)
    (ht : t ≤ t') : rankInv V s' t' ≤ rankInv V s t :=
  (rankInv_le_rankInv_left V hs (hst.trans ht)).trans (rankInv_le_rankInv_right V hst ht)

/-- Over a ring with the strong rank condition, every rank invariant of a pointwise finitely
generated module is finite, on and off the diagonal. -/
theorem IsPFD.rankInv_lt_top [StrongRankCondition R] (hV : IsPFD V) (s t : ℝ) :
    rankInv V s t < ⊤ := by
  have := hV s
  exact (rankInv_le_rank_obj_left V s t).trans_lt
    (Cardinal.toENat_lt_top.2 (Module.rank_lt_aleph0 R (V.obj s)))

/-- Over a ring with the strong rank condition (for instance a field), every pointwise finitely
generated persistence module is `q`-tame. -/
theorem IsPFD.isQTame [StrongRankCondition R] (hV : IsPFD V) : IsQTame V :=
  fun s t _ => hV.rankInv_lt_top s t

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

variable {R : Type*} [Ring R] {V W : PersistenceModule R}

/-- Isomorphic persistence modules have the same rank invariant. -/
theorem rankInv_congr (e : V ≅ W) (s t : ℝ) : rankInv V s t = rankInv W s t := by
  -- each structure map of `W` is a structure map of `V` composed with isomorphisms
  suffices key : ∀ {V W : PersistenceModule R}, (V ≅ W) → rankInv W s t ≤ rankInv V s t from
    le_antisymm (key e.symm) (key e)
  intro V W e
  rw [rankInv_def, rankInv_def]
  split_ifs with h
  · have hW : (W.map (homOfLE h)).hom =
        ((e.hom.app t).hom ∘ₗ (V.map (homOfLE h)).hom) ∘ₗ (e.inv.app s).hom := by
      simp [← ModuleCat.hom_comp]
    rw [hW]
    exact OrderHomClass.mono _ ((LinearMap.rank_comp_le_left _ _).trans
      (LinearMap.rank_comp_le_right _ _))
  · exact le_rfl

/-- Pointwise finite generation (`IsPFD`) is invariant under isomorphism. -/
theorem isPFD_congr (e : V ≅ W) : IsPFD V ↔ IsPFD W :=
  ⟨fun hV t => (hV t).equiv (e.app t).toLinearEquiv,
    fun hW t => (hW t).equiv (e.app t).symm.toLinearEquiv⟩

/-- `q`-tameness is invariant under isomorphism. -/
theorem isQTame_congr (e : V ≅ W) : IsQTame V ↔ IsQTame W := by
  simp only [isQTame_iff, e.rankInv_congr]

end CategoryTheory.Iso
