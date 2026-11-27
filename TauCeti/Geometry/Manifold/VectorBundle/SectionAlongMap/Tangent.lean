/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Transport of tangent fields along maps by a differential

For a map `f : M → N` and a tangent field `V` along a map `γ : P → M`, the differential of `f`
gives the tangent field `p ↦ df_{γ p} (V p)` along `f ∘ γ`. When `f` is `C^n` at `γ t`, with
`2 ≤ n`, this transport preserves differentiability at `t`, both as a map into the tangent bundle
and in local coordinates.

## Main results

* `ContMDiffAt.mdifferentiableWithinAt_totalSpace_mfderiv`: the transported field is
  differentiable within a set as a map into the tangent bundle.
* `ContMDiffAt.mdifferentiableAt_totalSpace_mfderiv`: the unrestricted form.
* `ContMDiffAt.mdifferentiableAt_sectionCoord_mfderiv`: the transported field has a
  differentiable coordinate reading.
* `ContMDiffAt.mdifferentiableAt_sectionCoord_mfderiv_of_mdifferentiableAt`: the field
  `y ↦ df_y (Y y)` along `f`, for a vector field `Y` on `M` differentiable at `x`, has a
  differentiable coordinate reading at `x`.
-/

public section

open Bundle
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {HP : Type*} [TopologicalSpace HP] {K : ModelWithCorners 𝕜 G HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold I 2 M] [IsManifold J 2 N] {f : M → N} {n : WithTop ℕ∞}
  {γ : P → M} {V : ∀ p, TangentSpace I (γ p)}

/-- The differential of a map `f` which is `C^n` at `γ t`, with `2 ≤ n`, carries a tangent field
along `γ` which is differentiable within `s` at `t` as a map into the tangent bundle to a tangent
field along `f ∘ γ` with the same property. -/
theorem _root_.ContMDiffAt.mdifferentiableWithinAt_totalSpace_mfderiv {s : Set P} {t : P}
    (hf : ContMDiffAt I J n f (γ t)) (hn : 2 ≤ n)
    (hV : MDifferentiableWithinAt K I.tangent (fun p ↦ TotalSpace.mk' E (γ p) (V p)) s t) :
    MDifferentiableWithinAt K J.tangent
      (fun p ↦ TotalSpace.mk' F (f (γ p)) (mfderiv I J f (γ p) (V p))) s t := by
  have htangent : MDifferentiableAt I.tangent J.tangent (tangentMap I J f)
      (TotalSpace.mk' E (γ t) (V t)) :=
    (hf.contMDiffAt_tangentMap (X := TotalSpace.mk' E (γ t) (V t)) (m := 1)
      (by rwa [one_add_one_eq_two])).mdifferentiableAt one_ne_zero
  have hmap : tangentMap I J f ∘ (fun p ↦ TotalSpace.mk' E (γ p) (V p)) =
      fun p ↦ TotalSpace.mk' F (f (γ p)) (mfderiv I J f (γ p) (V p)) := by
    funext p
    exact TotalSpace.ext tangentMap_proj (heq_of_eq tangentMap_snd)
  simpa only [hmap] using htangent.comp_mdifferentiableWithinAt t hV

/-- The unrestricted form of `ContMDiffAt.mdifferentiableWithinAt_totalSpace_mfderiv`. -/
theorem _root_.ContMDiffAt.mdifferentiableAt_totalSpace_mfderiv {t : P}
    (hf : ContMDiffAt I J n f (γ t)) (hn : 2 ≤ n)
    (hV : MDifferentiableAt K I.tangent (fun p ↦ TotalSpace.mk' E (γ p) (V p)) t) :
    MDifferentiableAt K J.tangent
      (fun p ↦ TotalSpace.mk' F (f (γ p)) (mfderiv I J f (γ p) (V p))) t := by
  rw [← mdifferentiableWithinAt_univ] at hV ⊢
  exact hf.mdifferentiableWithinAt_totalSpace_mfderiv hn hV

/-- The differential of a map `f` which is `C^n` at `γ t`, with `2 ≤ n`, carries a tangent field
along `γ` whose coordinate reading is differentiable at `t` to a tangent field along `f ∘ γ` whose
coordinate reading is differentiable at `t`. -/
theorem _root_.ContMDiffAt.mdifferentiableAt_sectionCoord_mfderiv {t : P}
    (hf : ContMDiffAt I J n f (γ t)) (hn : 2 ≤ n) (hγ : MDifferentiableAt K I γ t)
    (hV : MDifferentiableAt K 𝓘(𝕜, E) (sectionCoord 𝕜 (F := E) γ V (γ t)) t) :
    MDifferentiableAt K 𝓘(𝕜, F)
      (sectionCoord 𝕜 (F := F) (f ∘ γ) (fun p ↦ mfderiv I J f (γ p) (V p)) (f (γ t))) t :=
  mdifferentiableAt_sectionCoord (f ∘ γ) (fun p ↦ mfderiv I J f (γ p) (V p))
    (hf.mdifferentiableAt_totalSpace_mfderiv hn
      ((mdifferentiableAt_sectionCoord_iff γ V hγ
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))).1 hV))
    (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t)))

/-- For a map `f` which is `C^n` at `x`, with `2 ≤ n`, and a vector field `Y` on `M`
differentiable at `x`, the field `y ↦ df_y (Y y)` along `f` has a coordinate reading which is
differentiable at `x`. -/
theorem _root_.ContMDiffAt.mdifferentiableAt_sectionCoord_mfderiv_of_mdifferentiableAt {x : M}
    (hf : ContMDiffAt I J n f x) (hn : 2 ≤ n) {Y : Π y : M, TangentSpace I y}
    (hY : MDiffAt (T% Y) x) :
    MDifferentiableAt I 𝓘(𝕜, F)
      (sectionCoord 𝕜 (F := F) f (fun y ↦ mfderiv I J f y (Y y)) (f x)) x :=
  mdifferentiableAt_sectionCoord f (fun y ↦ mfderiv I J f y (Y y))
    (hf.mdifferentiableAt_totalSpace_mfderiv (γ := id) (V := Y) hn hY)
    (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f x))

end TauCeti.Manifold
