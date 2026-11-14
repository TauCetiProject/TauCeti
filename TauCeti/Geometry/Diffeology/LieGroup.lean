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

* On a manifold-compatible diffeological space `G` with `ContMDiffMul I ∞ G`, multiplication is
  diffeologically smooth (`TauCeti.dSmooth_mul`), and on a `LieGroup I ∞ G`, inversion is
  diffeologically smooth (`TauCeti.dSmooth_inv`), together with their additive counterparts
  `TauCeti.dSmooth_add` and `TauCeti.dSmooth_neg`.
* Converting Mathlib's bundled left and right translations `smoothLeftMul I g` and
  `smoothRightMul I g` to `TauCeti.Diffeology.DSmoothMap G G` agrees with
  `TauCeti.Diffeology.DSmoothMap.mulLeft` and `TauCeti.Diffeology.DSmoothMap.mulRight`
  (`TauCeti.toDSmoothMap_smoothLeftMul`, `TauCeti.toDSmoothMap_smoothRightMul`), so the left- and
  right-translation families `G → DSmoothMap G G` are smooth for the functional diffeology
  (`TauCeti.dSmooth_smoothLeftMul_toDSmoothMap`, `TauCeti.dSmooth_smoothRightMul_toDSmoothMap`).

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  [DiffeologicalSpace G] [IsContMDiffCompatible I G]

variable (I) in
/-- Multiplication on a manifold-compatible space with smooth multiplication is diffeologically
smooth. As in Mathlib's `continuousMul_of_contMDiffMul`, the model `I` is an explicit argument
because a single diffeological space (such as `E × F`) can be compatible with distinct manifold
models (`𝓘(ℝ, E × F)` and `𝓘(ℝ, E).prod 𝓘(ℝ, F)`). -/
@[to_additive
/-- Addition on a manifold-compatible space with smooth addition is diffeologically smooth. As in
Mathlib's `continuousAdd_of_contMDiffAdd`, the model `I` is an explicit argument because a single
diffeological space can be compatible with distinct manifold models. -/]
theorem dSmooth_mul [Mul G] [ContMDiffMul I ∞ G] :
    DSmooth (fun p : G × G ↦ p.1 * p.2) :=
  (contMDiff_mul I ∞).dSmooth

variable (I) in
/-- Inversion on a manifold-compatible Lie group is diffeologically smooth. -/
@[to_additive
/-- Negation on a manifold-compatible additive Lie group is diffeologically smooth. -/]
theorem dSmooth_inv [Group G] [LieGroup I ∞ G] :
    DSmooth (Inv.inv : G → G) :=
  (contMDiff_inv I ∞).dSmooth

/-- Converting `smoothLeftMul I g` to `DSmoothMap` gives `DSmoothMap.mulLeft`. -/
@[simp]
theorem toDSmoothMap_smoothLeftMul [Mul G] [ContMDiffMul I ∞ G] (g : G) :
    (smoothLeftMul I g).toDSmoothMap = Diffeology.DSmoothMap.mulLeft (dSmooth_mul I) g :=
  Diffeology.DSmoothMap.ext fun _ ↦ by simp

/-- Converting `smoothRightMul I g` to `DSmoothMap` gives `DSmoothMap.mulRight`. -/
@[simp]
theorem toDSmoothMap_smoothRightMul [Mul G] [ContMDiffMul I ∞ G] (g : G) :
    (smoothRightMul I g).toDSmoothMap = Diffeology.DSmoothMap.mulRight (dSmooth_mul I) g :=
  Diffeology.DSmoothMap.ext fun _ ↦ by simp

/-- Left translation `g ↦ (smoothLeftMul I g).toDSmoothMap` on a manifold-compatible space with
smooth multiplication is smooth into the functional diffeology `DSmoothMap G G`. -/
@[fun_prop]
theorem dSmooth_smoothLeftMul_toDSmoothMap [Mul G] [ContMDiffMul I ∞ G] :
    DSmooth (fun g : G ↦ (smoothLeftMul I g).toDSmoothMap) := by
  simp_rw [toDSmoothMap_smoothLeftMul]
  exact Diffeology.DSmoothMap.dSmooth_mulLeft (dSmooth_mul I)

/-- Right translation `g ↦ (smoothRightMul I g).toDSmoothMap` on a manifold-compatible space with
smooth multiplication is smooth into the functional diffeology `DSmoothMap G G`. -/
@[fun_prop]
theorem dSmooth_smoothRightMul_toDSmoothMap [Mul G] [ContMDiffMul I ∞ G] :
    DSmooth (fun g : G ↦ (smoothRightMul I g).toDSmoothMap) := by
  simp_rw [toDSmoothMap_smoothRightMul]
  exact Diffeology.DSmoothMap.dSmooth_mulRight (dSmooth_mul I)

end TauCeti
