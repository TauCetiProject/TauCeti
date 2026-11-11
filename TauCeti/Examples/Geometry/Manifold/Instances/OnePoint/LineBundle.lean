/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# Examples: the holomorphic line bundles `𝒪(k)` on the Riemann sphere

On the Riemann sphere `OnePoint ℂ`, the line bundle `𝒪(k)` glued along the transition function
`z ↦ z⁻ᵏ` is a holomorphic line bundle in the sense of Mathlib's mixin
`ContMDiffVectorBundle ∞ ℂ _ 𝓘(ℂ)`, with no further input:

* `𝒪(0)` is the trivial line bundle: its transitions are `1`, and the section `1` is
  holomorphic and vanishes nowhere, so it has a global holomorphic trivialization;
* the section `z` of `𝒪(1)` is holomorphic on the whole sphere with exactly one zero, at `0`;
* the transitions of `𝒪(k + l)` and `𝒪(-k)` are the products and inverses of those of
  `𝒪(k)` and `𝒪(l)`.
-/

open Bundle Set
open scoped Manifold ContDiff

-- `𝒪(k)` is a holomorphic line bundle on the Riemann sphere.
example (k : ℤ) : ContMDiffVectorBundle ∞ ℂ (OnePoint.twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℂ) :=
  inferInstance

-- `𝒪(0)` has trivial transitions.
example (x y p : OnePoint ℂ) : OnePoint.twistTransition 0 x y p = 1 :=
  OnePoint.twistTransition_zero x y p

-- `𝒪(0)` has a global holomorphic trivialization.
example : ∃ (e : Trivialization ℂ (π ℂ (OnePoint.twistCore (𝕜 := ℂ) 0).Fiber)) (_ : e.IsLinear ℂ),
    e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear (OnePoint ℂ) ℂ 𝓘(ℂ) ∞).maximalAtlas
        (TotalSpace ℂ (OnePoint.twistCore (𝕜 := ℂ) 0).Fiber) ∧ e.baseSet = univ :=
  (ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero
    (Module.finrank_self ℂ)).2
    ⟨OnePoint.monomialSection 0 0, (OnePoint.contMDiff_monomialSection le_rfl).of_le le_top,
      OnePoint.monomialSection_zero_zero_ne_zero⟩

-- The section `z` of `𝒪(1)` is holomorphic on the whole Riemann sphere.
example : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞
    (fun p ↦ TotalSpace.mk' ℂ (E := (OnePoint.twistCore (1 : ℤ)).Fiber) p
      (OnePoint.identitySection (𝕜 := ℂ) p)) :=
  OnePoint.contMDiff_identitySection.of_le le_top

-- It vanishes exactly at `0`, and in particular not at `∞`.
example (p : OnePoint ℂ) : OnePoint.identitySection p = 0 ↔ p = ((0 : ℂ) : OnePoint ℂ) :=
  OnePoint.identitySection_eq_zero_iff

-- Tensor and dual laws for the transition functions.
example (k l : ℤ) {x y p : OnePoint ℂ} (hx : p ∈ (chartAt ℂ x).source)
    (hy : p ∈ (chartAt ℂ y).source) :
    OnePoint.twistTransition (k + l) x y p =
      OnePoint.twistTransition k x y p * OnePoint.twistTransition l x y p :=
  OnePoint.twistTransition_add k l hx hy

example (k : ℤ) (x y p : OnePoint ℂ) :
    OnePoint.twistTransition (-k) x y p = (OnePoint.twistTransition k x y p)⁻¹ :=
  OnePoint.twistTransition_neg k x y p
