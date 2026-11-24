/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Diffeology.ContMDiffMap

/-!
# Smooth multiplication, Lie groups, and diffeological translation families

This file bridges Mathlib's smooth monoids (`ContMDiffMul`) and Lie groups (`LieGroup`) with
diffeological spaces and functional diffeologies:

* On a diffeological space `G` compatible with a manifold structure modelled on `𝓘(ℝ, E)` with
  `ContMDiffMul 𝓘(ℝ, E) ∞ G`, multiplication is diffeologically smooth (`TauCeti.dSmooth_mul`),
  and on a `LieGroup 𝓘(ℝ, E) ∞ G`, inversion is diffeologically smooth (`TauCeti.dSmooth_inv`),
  together with their additive counterparts `TauCeti.dSmooth_add` and `TauCeti.dSmooth_neg`.
* Converting Mathlib's bundled left and right translations `smoothLeftMul 𝓘(ℝ, E) g` and
  `smoothRightMul 𝓘(ℝ, E) g` to `TauCeti.Diffeology.DSmoothMap G G` agrees with
  `TauCeti.Diffeology.DSmoothMap.mulLeft` and `TauCeti.Diffeology.DSmoothMap.mulRight`
  (`TauCeti.toDSmoothMap_smoothLeftMul`, `TauCeti.toDSmoothMap_smoothRightMul`), so the left- and
  right-translation families `G → DSmoothMap G G` are smooth for the functional diffeology
  (`TauCeti.dSmooth_toDSmoothMap_smoothLeftMul`, `TauCeti.dSmooth_toDSmoothMap_smoothRightMul`).

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapters 1 and 7, for diffeological groups and functional
  diffeologies of translation maps.
-/

public noncomputable section

open Diffeology
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G]
  [DiffeologicalSpace G] [IsContMDiffCompatible E G]

/-- Multiplication on a manifold-compatible space with smooth multiplication is diffeologically
smooth. -/
@[to_additive
/-- Addition on a manifold-compatible space with smooth addition is diffeologically smooth. -/]
theorem dSmooth_mul [Mul G] [ContMDiffMul 𝓘(ℝ, E) ∞ G] :
    DSmooth (fun p : G × G ↦ p.1 * p.2) :=
  (contMDiff_mul 𝓘(ℝ, E) ∞).dSmooth_prod_dom

/-- Inversion on a manifold-compatible Lie group is diffeologically smooth. -/
@[to_additive
/-- Negation on a manifold-compatible additive Lie group is diffeologically smooth. -/]
theorem dSmooth_inv [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] :
    DSmooth (Inv.inv : G → G) :=
  (contMDiff_inv 𝓘(ℝ, E) ∞).dSmooth

/-- Converting `smoothLeftMul 𝓘(ℝ, E) g` to `DSmoothMap` gives `DSmoothMap.mulLeft`. -/
@[simp]
theorem toDSmoothMap_smoothLeftMul [Mul G] [ContMDiffMul 𝓘(ℝ, E) ∞ G] (g : G) :
    (smoothLeftMul 𝓘(ℝ, E) g).toDSmoothMap = Diffeology.DSmoothMap.mulLeft dSmooth_mul g :=
  Diffeology.DSmoothMap.ext fun _ ↦ by simp

/-- Converting `smoothRightMul 𝓘(ℝ, E) g` to `DSmoothMap` gives `DSmoothMap.mulRight`. -/
@[simp]
theorem toDSmoothMap_smoothRightMul [Mul G] [ContMDiffMul 𝓘(ℝ, E) ∞ G] (g : G) :
    (smoothRightMul 𝓘(ℝ, E) g).toDSmoothMap = Diffeology.DSmoothMap.mulRight dSmooth_mul g :=
  Diffeology.DSmoothMap.ext fun _ ↦ by simp

/-- Left translation `g ↦ (smoothLeftMul 𝓘(ℝ, E) g).toDSmoothMap` on a manifold-compatible space
with smooth multiplication is smooth into the functional diffeology `DSmoothMap G G`. -/
@[fun_prop]
theorem dSmooth_toDSmoothMap_smoothLeftMul [Mul G] [ContMDiffMul 𝓘(ℝ, E) ∞ G] :
    DSmooth (fun g : G ↦ (smoothLeftMul 𝓘(ℝ, E) g).toDSmoothMap) := by
  simp_rw [toDSmoothMap_smoothLeftMul]
  exact Diffeology.DSmoothMap.dSmooth_mulLeft dSmooth_mul

/-- Right translation `g ↦ (smoothRightMul 𝓘(ℝ, E) g).toDSmoothMap` on a manifold-compatible space
with smooth multiplication is smooth into the functional diffeology `DSmoothMap G G`. -/
@[fun_prop]
theorem dSmooth_toDSmoothMap_smoothRightMul [Mul G] [ContMDiffMul 𝓘(ℝ, E) ∞ G] :
    DSmooth (fun g : G ↦ (smoothRightMul 𝓘(ℝ, E) g).toDSmoothMap) := by
  simp_rw [toDSmoothMap_smoothRightMul]
  exact Diffeology.DSmoothMap.dSmooth_mulRight dSmooth_mul

end TauCeti
