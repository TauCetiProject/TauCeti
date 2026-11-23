/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Pullback.Basic
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Continuity of Hom-bundle sections over pullback bundles

This module characterizes continuity of families of continuous linear maps between pulled-back
vector bundles as sections of Mathlib's Hom bundle (`TauCeti.continuousAt_hom_bundle_pullback_iff`,
`TauCeti.continuous_hom_bundle_pullback_iff`), compares continuity in ambient and pulled-back Hom
bundles (`TauCeti.continuousAt_hom_bundle_comp_iff`, `TauCeti.continuous_hom_bundle_comp_iff`,
`TauCeti.continuous_hom_bundle_pullback_comp_iff`,
`TauCeti.continuous_hom_bundle_pullback_left_comp_iff`), and proves continuity under base-preserving
reindexing (`TauCeti.continuous_hom_bundle_pullback_comp_of_eq`).
-/

public section

open Bundle

namespace TauCeti

section HomBundle

open ContinuousLinearMap

variable {𝕜 B C M X F G H K L : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace M] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V : B → Type*} {W : C → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ c, AddCommGroup (W c)] [∀ c, Module 𝕜 (W c)] [∀ c, TopologicalSpace (W c)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [FunLike K X B] [ContinuousMapClass K X B]
  [FunLike L X C] [ContinuousMapClass L X C]
  [∀ c, IsTopologicalAddGroup (W c)] [∀ c, ContinuousSMul 𝕜 (W c)]

/-- A family of Hom maps between pullbacks by `f` and `g` is continuous at `m₀` as a Hom-bundle
section exactly when its coordinate expression in the original bundles is continuous at `m₀`. -/
theorem continuousAt_hom_bundle_pullback_iff
    {K' L' : Type*} [FunLike K' M B] [ContinuousMapClass K' M B]
    [FunLike L' M C] [ContinuousMapClass L' M C]
    (f : K') (g : L') (ϕ : ∀ m, V (f m) →L[𝕜] W (g m)) {m₀ : M} :
    ContinuousAt (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun y ↦ ((f : M → B) *ᵖ V) y →L[𝕜] ((g : M → C) *ᵖ W) y) m (ϕ m)) m₀ ↔
      ContinuousAt (fun m ↦ inCoordinates F V G W (f m₀) (f m) (g m₀) (g m) (ϕ m)) m₀ := by
  rw [continuousAt_hom_bundle]
  exact (and_iff_right continuousAt_id).trans
    (continuousAt_inCoordinates_pullback_iff f g continuousAt_id continuousAt_id ϕ)

/-- A family of Hom maps between pullbacks by `f` and `g` is continuous as a Hom-bundle section
exactly when its coordinate expression in the original bundles is continuous at every point. -/
theorem continuous_hom_bundle_pullback_iff
    {K' L' : Type*} [FunLike K' M B] [ContinuousMapClass K' M B]
    [FunLike L' M C] [ContinuousMapClass L' M C]
    (f : K') (g : L') (ϕ : ∀ m, V (f m) →L[𝕜] W (g m)) :
    Continuous (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun y ↦ ((f : M → B) *ᵖ V) y →L[𝕜] ((g : M → C) *ᵖ W) y) m (ϕ m)) ↔
      ∀ m₀, ContinuousAt (fun m ↦ inCoordinates F V G W (f m₀) (f m) (g m₀) (g m) (ϕ m)) m₀ := by
  simp only [continuous_iff_continuousAt, continuousAt_hom_bundle_pullback_iff]

/-- A Hom family over a continuous base map `b` is continuous at `m₀` into the ambient Hom bundle
exactly when it is continuous at `m₀` as a section of the pulled-back Hom bundle. -/
theorem continuousAt_hom_bundle_comp_iff
    {V' W' : X → Type*}
    [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x, TopologicalSpace (V' x)]
    [∀ x, AddCommGroup (W' x)] [∀ x, Module 𝕜 (W' x)] [∀ x, TopologicalSpace (W' x)]
    [∀ x, IsTopologicalAddGroup (W' x)] [∀ x, ContinuousSMul 𝕜 (W' x)]
    [TopologicalSpace (TotalSpace F V')] [FiberBundle F V'] [VectorBundle 𝕜 F V']
    [TopologicalSpace (TotalSpace G W')] [FiberBundle G W'] [VectorBundle 𝕜 G W']
    [FunLike H M X] [ContinuousMapClass H M X]
    (b : H) (ϕ : ∀ m, V' (b m) →L[𝕜] W' (b m)) {m₀ : M} :
    ContinuousAt (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x ↦ V' x →L[𝕜] W' x) (b m) (ϕ m)) m₀ ↔
      ContinuousAt (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun y ↦ ((b : M → X) *ᵖ V') y →L[𝕜] ((b : M → X) *ᵖ W') y) m (ϕ m)) m₀ := by
  rw [continuousAt_hom_bundle, continuousAt_hom_bundle_pullback_iff]
  exact and_iff_right (map_continuous b).continuousAt

/-- A Hom family over a continuous base map `b` is continuous into the ambient Hom bundle exactly
when it is continuous as a section of the pulled-back Hom bundle. -/
theorem continuous_hom_bundle_comp_iff
    {V' W' : X → Type*}
    [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x, TopologicalSpace (V' x)]
    [∀ x, AddCommGroup (W' x)] [∀ x, Module 𝕜 (W' x)] [∀ x, TopologicalSpace (W' x)]
    [∀ x, IsTopologicalAddGroup (W' x)] [∀ x, ContinuousSMul 𝕜 (W' x)]
    [TopologicalSpace (TotalSpace F V')] [FiberBundle F V'] [VectorBundle 𝕜 F V']
    [TopologicalSpace (TotalSpace G W')] [FiberBundle G W'] [VectorBundle 𝕜 G W']
    [FunLike H M X] [ContinuousMapClass H M X]
    (b : H) (ϕ : ∀ m, V' (b m) →L[𝕜] W' (b m)) :
    Continuous (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x ↦ V' x →L[𝕜] W' x) (b m) (ϕ m)) ↔
      Continuous (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun y ↦ ((b : M → X) *ᵖ V') y →L[𝕜] ((b : M → X) *ᵖ W') y) m (ϕ m)) := by
  simp only [continuous_iff_continuousAt, continuousAt_hom_bundle_comp_iff]

/-- A Hom family over a continuous map `b` into the Hom bundle between pullbacks `f *ᵖ V` and
`g *ᵖ W` is continuous at `m₀` exactly when its coordinate expression in `V` and `W` is continuous
at `m₀`. -/
theorem continuousAt_hom_bundle_over_pullback_iff
    [FunLike H M X] [ContinuousMapClass H M X]
    (f : K) (g : L) (b : H) (ϕ : ∀ m, V (f (b m)) →L[𝕜] W (g (b m))) {m₀ : M} :
    ContinuousAt (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((g : X → C) *ᵖ W) x) (b m) (ϕ m)) m₀ ↔
      ContinuousAt (fun m ↦ inCoordinates F V G W
        (f (b m₀)) (f (b m)) (g (b m₀)) (g (b m)) (ϕ m)) m₀ := by
  rw [continuousAt_hom_bundle]
  exact (and_iff_right (map_continuous b).continuousAt).trans
    (continuousAt_inCoordinates_pullback_iff f g (map_continuous b).continuousAt
      (map_continuous b).continuousAt ϕ)

/-- A Hom family over a continuous map `b` into the Hom bundle between pullbacks `f *ᵖ V` and
`g *ᵖ W` is continuous exactly when it is continuous as a section of the composite pullback Hom
bundle `(f.comp b) *ᵖ V →L (g.comp b) *ᵖ W`. -/
theorem continuous_hom_bundle_pullback_comp_iff
    (f : C(X, B)) (g : C(X, C)) (b : C(M, X)) (ϕ : ∀ m, V (f (b m)) →L[𝕜] W (g (b m))) :
    Continuous (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((g : X → C) *ᵖ W) x) (b m) (ϕ m)) ↔
      Continuous (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun y ↦ ((f.comp b : M → B) *ᵖ V) y →L[𝕜] ((g.comp b : M → C) *ᵖ W) y)
        m (ϕ m)) := by
  simp only [continuous_iff_continuousAt]
  refine forall_congr' fun m₀ ↦ (continuousAt_hom_bundle_over_pullback_iff f g b ϕ).trans ?_
  exact (continuousAt_hom_bundle_pullback_iff (f.comp b) (g.comp b) ϕ).symm

/-- A Hom family over a continuous map `b` into the Hom bundle from `f *ᵖ V` to `W'` is
continuous at `m₀` exactly when its coordinate expression in `V` and `W'` is continuous at `m₀`.
-/
theorem continuousAt_hom_bundle_over_pullback_left_iff
    {W' : X → Type*} [∀ x, AddCommGroup (W' x)] [∀ x, Module 𝕜 (W' x)]
    [∀ x, TopologicalSpace (W' x)] [∀ x, IsTopologicalAddGroup (W' x)]
    [∀ x, ContinuousSMul 𝕜 (W' x)] [TopologicalSpace (TotalSpace G W')]
    [FiberBundle G W'] [VectorBundle 𝕜 G W']
    [FunLike H M X] [ContinuousMapClass H M X]
    (f : K) (b : H) (ϕ : ∀ m, V (f (b m)) →L[𝕜] W' (b m)) {m₀ : M} :
    ContinuousAt (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] W' x) (b m) (ϕ m)) m₀ ↔
      ContinuousAt (fun m ↦ inCoordinates F V G W'
        (f (b m₀)) (f (b m)) (b m₀) (b m) (ϕ m)) m₀ := by
  rw [continuousAt_hom_bundle]
  exact (and_iff_right (map_continuous b).continuousAt).trans
    (continuousAt_inCoordinates_pullback_iff f (ContinuousMap.id X)
      (map_continuous b).continuousAt (map_continuous b).continuousAt ϕ)

/-- A Hom family over `b : C(M, X)` into `(f *ᵖ V) →L W'` is continuous exactly when it is
continuous as a section of `(f.comp b) *ᵖ V →L b *ᵖ W'`. -/
theorem continuous_hom_bundle_pullback_left_comp_iff
    {W' : X → Type*} [∀ x, AddCommGroup (W' x)] [∀ x, Module 𝕜 (W' x)]
    [∀ x, TopologicalSpace (W' x)] [∀ x, IsTopologicalAddGroup (W' x)]
    [∀ x, ContinuousSMul 𝕜 (W' x)] [TopologicalSpace (TotalSpace G W')]
    [FiberBundle G W'] [VectorBundle 𝕜 G W']
    (f : C(X, B)) (b : C(M, X)) (ϕ : ∀ m, V (f (b m)) →L[𝕜] W' (b m)) :
    Continuous (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] W' x) (b m) (ϕ m)) ↔
      Continuous (fun m ↦ TotalSpace.mk' (F →L[𝕜] G)
        (E := fun y ↦ ((f.comp b : M → B) *ᵖ V) y →L[𝕜] ((b : M → X) *ᵖ W') y) m (ϕ m)) := by
  simp only [continuous_iff_continuousAt]
  refine forall_congr' fun m₀ ↦ (continuousAt_hom_bundle_over_pullback_left_iff f b ϕ).trans ?_
  exact (continuousAt_hom_bundle_pullback_iff (f.comp b) b ϕ).symm

/-- Reindexing a continuous Hom-bundle section between pullbacks along `p` by a continuous map `r`
satisfying `p (r x) = p x` yields a continuous Hom-bundle section. -/
theorem continuous_hom_bundle_pullback_comp_of_eq
    {W' : B → Type*} [∀ b, AddCommGroup (W' b)] [∀ b, Module 𝕜 (W' b)]
    [∀ b, TopologicalSpace (W' b)] [∀ b, IsTopologicalAddGroup (W' b)]
    [∀ b, ContinuousSMul 𝕜 (W' b)] [TopologicalSpace (TotalSpace G W')]
    [FiberBundle G W'] [VectorBundle 𝕜 G W']
    (p : K) {β : ∀ x, ((p : X → B) *ᵖ V) x →L[𝕜] ((p : X → B) *ᵖ W') x}
    (hβ : Continuous fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
      (E := fun z ↦ ((p : X → B) *ᵖ V) z →L[𝕜] ((p : X → B) *ᵖ W') z) x (β x))
    {r : X → X} (hr : Continuous r) (hp : ∀ x, p (r x) = p x) :
    Continuous fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
      (E := fun z ↦ ((p : X → B) *ᵖ V) z →L[𝕜] ((p : X → B) *ᵖ W') z) x
      (show V (p x) →L[𝕜] W' (p x) from hp x ▸ β (r x)) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [continuousAt_hom_bundle_pullback_iff p p]
  have hc := ((continuousAt_hom_bundle_pullback_iff p p β).1
    (hβ.continuousAt (x := r x₀))).comp hr.continuousAt
  refine hc.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  let βrx : V (p (r x)) →L[𝕜] W' (p (r x)) := β (r x)
  have htr {a b : B} (h : a = b) (T : V a →L[𝕜] W' a) :
      (let f {c d : B} (hc : a = c) (hd : a = d) : V c →L[𝕜] W' d := hc ▸ hd ▸ T
       f h h) = (show V b →L[𝕜] W' b from h ▸ T) := by
    cases h
    rfl
  exact (inCoordinates_transport_eq (hp x₀) (hp x) (hp x₀) (hp x) βrx).trans
    (congrArg _ (htr (hp x) βrx))

end HomBundle

end TauCeti
