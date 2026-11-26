/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop

/-!
# Reparametrizing a free Moore loop by its time maps

Let `γ` be a free Moore loop of duration `L`. A *time map* of duration `L` is a path
`g : C(I, ℝ)` on the unit interval with `g 0 = 0` and `g 1 = L`
(`TauCeti.MooreFreeLoopSpace.timeMaps L`). The **reparametrization** of `γ` by `g` is the free
Moore loop of duration `L` which at time `L s` is at `γ (g s)`, reading `γ` as constant at its base
point at negative times (`TauCeti.MooreFreeLoopSpace.reparam`). It depends continuously on `g`, and
`γ` is its own reparametrization by the time map `s ↦ L s`
(`TauCeti.MooreFreeLoopSpace.reparam_mulTimeMap`).

The time maps of a duration form a convex set, which is therefore simply connected. So two paths of
reparametrizations of `γ`, read through paths of time maps with common end points, are homotopic
(`TauCeti.MooreFreeLoopSpace.homotopic_map_reparam`). This is how two deformations of a loop which
only move along the loop are compared, for instance in the comparison of the deformations of a
closed broken geodesic into the broken geodesics through its samples.

## Main definitions

* `TauCeti.MooreFreeLoopSpace.timeMaps`: the time maps of a duration.
* `TauCeti.MooreFreeLoopSpace.reparam`: the reparametrization of a free Moore loop by a time map.

## Main results

* `TauCeti.MooreFreeLoopSpace.toUnitPath_reparam`: the reparametrization by `g`, read on the unit
  interval, is `γ ∘ g`.
* `TauCeti.MooreFreeLoopSpace.reparam_mulTimeMap`: a loop is its reparametrization by `s ↦ L s`.
* `TauCeti.MooreFreeLoopSpace.homotopic_map_reparam`: paths of reparametrizations along paths of
  time maps with the same end points are homotopic.
-/

public section

noncomputable section

open scoped NNReal unitInterval
open Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

namespace MooreFreeLoopSpace

/-- The **time maps** of duration `L`: the paths `g` on the unit interval in `ℝ` from `g 0 = 0` to
`g 1 = L`. -/
def timeMaps (L : ℝ≥0) : Set C(I, ℝ) :=
  {g | g 0 = 0 ∧ g 1 = L}

@[simp]
theorem mem_timeMaps {L : ℝ≥0} {g : C(I, ℝ)} : g ∈ timeMaps L ↔ g 0 = 0 ∧ g 1 = L :=
  Iff.rfl

/-- The time maps of a duration form a convex set. -/
theorem convex_timeMaps (L : ℝ≥0) : Convex ℝ (timeMaps L) := by
  intro g hg h hh a b _ _ hab
  refine ⟨?_, ?_⟩
  · simp [hg.1, hh.1]
  · simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, hg.2, hh.2]
    rw [← add_mul, hab, one_mul]

/-- The time map `s ↦ L s` of duration `L`. -/
def mulTimeMap (L : ℝ≥0) : timeMaps L :=
  ⟨⟨fun s ↦ L * s, by fun_prop⟩, by simp, by simp⟩

@[simp]
theorem coe_mulTimeMap_apply (L : ℝ≥0) (s : I) : (mulTimeMap L : C(I, ℝ)) s = L * s :=
  (rfl)

instance (L : ℝ≥0) : SimplyConnectedSpace (timeMaps L) :=
  have := (convex_timeMaps L).contractibleSpace ⟨_, (mulTimeMap L).property⟩
  inferInstance

variable (γ : MooreFreeLoopSpace X)

/-- On a loop of duration zero, rescaling to its duration gives the constant path of length zero. -/
private theorem rescale_of_length_eq_zero (h : γ.length = 0) (P : MoorePath X) :
    P.rescale γ.length = MoorePath.refl P.source := by
  rw [h, MoorePath.rescale_zero]

/-- The reparametrization of `γ` by a time map, as a Moore path. -/
private def reparamPath (g : timeMaps γ.length) : MoorePath X :=
  (MoorePath.ofUnitPath (γ.toMoorePath.extend.comp g)).rescale γ.length

private theorem reparamPath_target_eq_source (g : timeMaps γ.length) :
    (reparamPath γ g).target = (reparamPath γ g).source := by
  rw [reparamPath, MoorePath.source_rescale, MoorePath.source_ofUnitPath,
    ContinuousMap.comp_apply, g.property.1]
  rcases eq_or_ne γ.length 0 with h | h
  · rw [rescale_of_length_eq_zero γ h, MoorePath.target_refl, MoorePath.source_ofUnitPath,
      ContinuousMap.comp_apply, g.property.1]
  · rw [MoorePath.target_rescale _ h, MoorePath.target_ofUnitPath, ContinuousMap.comp_apply,
      g.property.2, MoorePath.extend_coe, MoorePath.extend_apply, Real.toNNReal_zero,
      ← length_toMoorePath, ← MoorePath.target_def, ← MoorePath.source_def, γ.target_eq_source]

/-- The **reparametrization** of a free Moore loop `γ` of duration `L` by a time map `g`: the free
Moore loop of duration `L` which is at `γ (g s)` at time `L s`. -/
def reparam : C(timeMaps γ.length, MooreFreeLoopSpace X) where
  toFun g := ⟨reparamPath γ g, reparamPath_target_eq_source γ g⟩
  continuous_toFun := by
    refine isEmbedding_toMoorePath.continuous_iff.2 ?_
    refine (MoorePath.continuous_ofUnitPath.comp ((ContinuousMap.continuous_postcomp _).comp
      continuous_subtypeVal)).moorePath_rescale_of_forall_eq_source continuous_const
      fun g hg t ↦ ?_
    simp only [Function.comp_apply, MoorePath.ofUnitPath_apply, MoorePath.source_ofUnitPath,
      ContinuousMap.comp_apply, extend_eq_basepoint_of_length_eq_zero hg]

theorem toMoorePath_reparam (g : timeMaps γ.length) :
    (γ.reparam g).toMoorePath =
      (MoorePath.ofUnitPath (γ.toMoorePath.extend.comp g)).rescale γ.length :=
  (rfl)

@[simp]
theorem length_reparam (g : timeMaps γ.length) : (γ.reparam g).length = γ.length := by
  rw [← length_toMoorePath, toMoorePath_reparam, MoorePath.length_rescale]

/-- The reparametrization of `γ` by `g`, read on the unit interval, is `γ ∘ g`. -/
@[simp]
theorem toUnitPath_reparam (g : timeMaps γ.length) :
    (γ.reparam g).toMoorePath.toUnitPath = γ.toMoorePath.extend.comp g := by
  rw [toMoorePath_reparam]
  rcases eq_or_ne γ.length 0 with h | h
  · ext s
    rw [rescale_of_length_eq_zero γ h, MoorePath.toUnitPath_refl, ContinuousMap.const_apply,
      MoorePath.source_ofUnitPath, ContinuousMap.comp_apply, ContinuousMap.comp_apply,
      extend_eq_basepoint_of_length_eq_zero h, extend_eq_basepoint_of_length_eq_zero h]
  · rw [MoorePath.toUnitPath_rescale _ h, MoorePath.toUnitPath_ofUnitPath]

/-- **A free Moore loop is its reparametrization by the time map `s ↦ L s`.** -/
@[simp]
theorem reparam_mulTimeMap : γ.reparam (mulTimeMap γ.length) = γ := by
  ext1
  rw [toMoorePath_reparam]
  conv_rhs => rw [← MoorePath.ofUnitPath_toUnitPath_rescale_length γ.toMoorePath]
  rw [length_toMoorePath]
  congr 2
  ext s
  rw [ContinuousMap.comp_apply, coe_mulTimeMap_apply, MoorePath.toUnitPath_apply,
    MoorePath.extend_apply, length_toMoorePath]
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (mul_nonneg γ.length.coe_nonneg s.property.1), NNReal.coe_mul,
    unitInterval.coe_toNNReal]

/-- **Paths of reparametrizations along time maps with the same end points are homotopic**: the
time maps of a duration form a convex, hence simply connected, set. -/
theorem homotopic_map_reparam {g₀ g₁ : timeMaps γ.length} (p q : Path g₀ g₁) :
    (p.map γ.reparam.continuous).Homotopic (q.map γ.reparam.continuous) :=
  (SimplyConnectedSpace.paths_homotopic p q).map _

end MooreFreeLoopSpace

end TauCeti
