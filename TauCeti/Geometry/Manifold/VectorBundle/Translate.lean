/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth fibrewise translation of vector bundles

Let `V` be a vector bundle over `B` and `b : X → B` a map. A family `s x ∈ V (b x)` is a section
of `V` along `b`, and its total-space map is `x ↦ ⟨b x, s x⟩`. Fibrewise sums of `C^n` sections
along the same map are `C^n` (`ContMDiff.add_sectionAlong`); for `b = id` this is Mathlib's
`ContMDiff.add_section`. The general form applies to maps defined on the total space itself, which
are sections along the projection.

Consequently a `C^n` section `s` of `V` translates the fibres by a `C^n` diffeomorphism
`p ↦ p + s (π p)` of the total space, with inverse the translation by `-s`
(`TauCeti.vectorBundleTranslateDiffeomorph`). Like the fibrewise rescaling
`TauCeti.vectorBundleScalarDiffeomorph`, it preserves the projection and needs no global
trivialization. For the cotangent bundle, translation by a one-form is the basic example of a
fibre-preserving map whose effect on the canonical forms is computed by the one-form.
-/

public section

open Bundle Set Filter
open scoped Manifold Topology

variable {𝕜 B X F EB HB EX HX : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX}
  [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] {n : WithTop ℕ∞}

section AddCommMonoid

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  {b : X → B} {s t : ∀ x, V (b x)} {u : Set X} {x₀ : X}

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n`. -/
theorem ContMDiffWithinAt.add_sectionAlong
    (hs : ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) u x₀)
    (ht : ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) u x₀) :
    ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) u x₀ := by
  rw [contMDiffWithinAt_totalSpace] at hs ht ⊢
  let e := trivializationAt F V (b x₀)
  -- Near `x₀` the base point stays in the base set of `e`, where `e` is linear on the fibres.
  have he : ∀ᶠ x in 𝓝[u] x₀, b x ∈ e.baseSet :=
    hs.1.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (b x₀)))
  refine ⟨hs.1, (hs.2.add ht.2).congr_of_eventuallyEq ?_ ?_⟩
  · filter_upwards [he] with x hx
    exact (e.linear 𝕜 hx).map_add (s x) (t x)
  · exact (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' (b x₀))).map_add (s x₀) (t x₀)

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n`. -/
theorem ContMDiffAt.add_sectionAlong
    (hs : ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) x₀)
    (ht : ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) x₀) :
    ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) x₀ :=
  ContMDiffWithinAt.add_sectionAlong hs ht

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n`. -/
theorem ContMDiffOn.add_sectionAlong
    (hs : ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) u)
    (ht : ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) u) :
    ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) u :=
  fun x hx ↦ (hs x hx).add_sectionAlong (ht x hx)

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n`. -/
theorem ContMDiff.add_sectionAlong
    (hs : ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)))
    (ht : ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x))) :
    ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) :=
  fun x ↦ (hs x).add_sectionAlong (ht x)

end AddCommMonoid

namespace TauCeti

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- Translation by a `C^n` section `σ` is `C^n` on the total space. -/
private theorem contMDiff_translate {σ : ∀ y, V y}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      fun p : TotalSpace F V ↦ TotalSpace.mk' F p.proj (p.2 + σ p.proj) := by
  have hid : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      fun p : TotalSpace F V ↦ TotalSpace.mk' F (E := V) p.proj p.2 :=
    contMDiff_id
  exact hid.add_sectionAlong (hσ.comp (contMDiff_proj V))

/-- A `C^n` section `σ` of a vector bundle translates the fibres by a `C^n` diffeomorphism
`p ↦ p + σ (π p)` of the total space. Its inverse is the translation by `-σ`. -/
def vectorBundleTranslateDiffeomorph (σ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) :
    TotalSpace F V ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, F)⟯ TotalSpace F V where
  toFun p := ⟨p.proj, p.2 + σ p.proj⟩
  invFun p := ⟨p.proj, p.2 + (-σ) p.proj⟩
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_translate hσ
  contMDiff_invFun := contMDiff_translate hσ.neg_section

/-- Fibrewise translation by `σ` adds the value of `σ` at the base point. -/
@[simp]
theorem vectorBundleTranslateDiffeomorph_apply (σ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) (p : TotalSpace F V) :
    vectorBundleTranslateDiffeomorph σ hσ p = ⟨p.proj, p.2 + σ p.proj⟩ :=
  (rfl)

/-- The inverse of the translation by `σ` is the translation by `-σ`. -/
@[simp]
theorem vectorBundleTranslateDiffeomorph_symm (σ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y)) :
    (vectorBundleTranslateDiffeomorph σ hσ).symm =
      vectorBundleTranslateDiffeomorph (-σ) hσ.neg_section :=
  Diffeomorph.ext fun _ ↦ rfl

/-- Translation by the zero section is the identity diffeomorphism. -/
@[simp]
theorem vectorBundleTranslateDiffeomorph_zero :
    vectorBundleTranslateDiffeomorph (0 : ∀ y, V y)
        (Bundle.contMDiff_zeroSection 𝕜 V : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n _) =
      Diffeomorph.refl (IB.prod 𝓘(𝕜, F)) (TotalSpace F V) n :=
  Diffeomorph.ext fun p ↦ congrArg (TotalSpace.mk' F p.proj) (add_zero p.2)

/-- Successive fibre translations add the sections. -/
theorem vectorBundleTranslateDiffeomorph_trans (σ τ : ∀ y, V y)
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (σ y))
    (hτ : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n fun y ↦ TotalSpace.mk' F y (τ y)) :
    (vectorBundleTranslateDiffeomorph σ hσ).trans (vectorBundleTranslateDiffeomorph τ hτ) =
      vectorBundleTranslateDiffeomorph (σ + τ) (hσ.add_section hτ) :=
  Diffeomorph.ext fun p ↦ congrArg (TotalSpace.mk' F p.proj) (add_assoc p.2 (σ p.proj) (τ p.proj))

end TauCeti
