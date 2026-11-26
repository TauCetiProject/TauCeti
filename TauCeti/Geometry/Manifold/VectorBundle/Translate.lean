/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# Smooth fibrewise translation of vector bundles

A `C^n` section `s` of a vector bundle `V` over `B` translates the fibres by a `C^n`
diffeomorphism `p ↦ p + s (π p)` of the total space, with inverse the translation by `-s`
(`TauCeti.vectorBundleTranslateDiffeomorph`). Its smoothness is the sum of the identity and
`s ∘ π`, both sections of `V` along the projection (`ContMDiff.add_sectionAlong`). Like the
fibrewise rescaling `TauCeti.vectorBundleScalarDiffeomorph`, it preserves the projection and
needs no global trivialization. For the cotangent bundle, translation by a one-form is the basic
example of a fibre-preserving map whose effect on the canonical forms is computed by the
one-form.
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 B F EB HB : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] {n : WithTop ℕ∞}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

namespace TauCeti

/-- Translation by a `C^n` section `σ` is `C^n` on the total space. -/
private theorem contMDiff_translate {σ : ∀ y, V y}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      fun p : TotalSpace F V ↦ TotalSpace.mk' F p.proj (p.snd + σ p.proj) := by
  -- The identity, written as the section `p ↦ ⟨p.proj, p.snd⟩` along the projection (structure
  -- eta), so that `add_sectionAlong` can add `σ ∘ π` to it.
  have hid : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      fun p : TotalSpace F V ↦ TotalSpace.mk' F (E := V) p.proj p.snd :=
    contMDiff_id
  exact hid.add_sectionAlong (hσ.comp (contMDiff_proj V))

/-- A `C^n` section `σ` of a vector bundle translates the fibres by a `C^n` diffeomorphism
`p ↦ p + σ (π p)` of the total space. Its inverse is the translation by `-σ`. -/
def vectorBundleTranslateDiffeomorph (σ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) :
    TotalSpace F V ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, F)⟯ TotalSpace F V where
  toFun p := ⟨p.proj, p.snd + σ p.proj⟩
  invFun p := ⟨p.proj, p.snd + (-σ) p.proj⟩
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_translate hσ
  contMDiff_invFun := contMDiff_translate hσ.neg_section

/-- Fibrewise translation by `σ` adds the value of `σ` at the base point. -/
@[simp]
theorem vectorBundleTranslateDiffeomorph_apply (σ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) (p : TotalSpace F V) :
    vectorBundleTranslateDiffeomorph σ hσ p = ⟨p.proj, p.snd + σ p.proj⟩ :=
  (rfl)

/-- The inverse of the translation by `σ` is the translation by `-σ`. -/
@[simp]
theorem vectorBundleTranslateDiffeomorph_symm (σ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) :
    (vectorBundleTranslateDiffeomorph σ hσ).symm =
      vectorBundleTranslateDiffeomorph (-σ) hσ.neg_section :=
  Diffeomorph.ext fun p ↦ (vectorBundleTranslateDiffeomorph σ hσ).injective <| by simp

/-- Translation by the zero section is the identity diffeomorphism. -/
@[simp]
theorem vectorBundleTranslateDiffeomorph_zero :
    vectorBundleTranslateDiffeomorph (0 : ∀ y, V y)
        (Bundle.contMDiff_zeroSection 𝕜 V : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n _) =
      Diffeomorph.refl (IB.prod 𝓘(𝕜, F)) (TotalSpace F V) n :=
  -- The `_apply` lemma is applied by hand: the proof argument above has type
  -- `ContMDiff … (zeroSection F V)`, so `rw` and `simp` do not match it syntactically.
  Diffeomorph.ext fun p ↦ (vectorBundleTranslateDiffeomorph_apply 0 _ p).trans (by simp)

/-- Successive fibre translations add the sections. -/
@[simp]
theorem vectorBundleTranslateDiffeomorph_trans (σ τ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y))
    (hτ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (τ y)) :
    (vectorBundleTranslateDiffeomorph σ hσ).trans (vectorBundleTranslateDiffeomorph τ hτ) =
      vectorBundleTranslateDiffeomorph (σ + τ) (hσ.add_section hτ) :=
  Diffeomorph.ext fun p ↦ by simp [add_assoc]

end TauCeti
