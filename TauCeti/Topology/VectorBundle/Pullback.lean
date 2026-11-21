/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom

/-!
# Fibres and linear charts of pullback bundles

The fibres of `f *ᵖ E` inherit their additive group, topological module, normed and inner product
structures and their scalar towers from `E (f x)`. Mathlib supplies the additive monoid and module
structures. The topological group structures let fibrewise linear equivalences between pullbacks,
such as the pullback `x ↦ e (f x)` of a family of fibrewise linear equivalences `e`, induce maps of
total spaces with continuous inverses. The normed instances allow the orthonormal frame bundle of a
pullback to use exactly the original fibre metrics, with no transport or renorming. A pulled-back
linear trivialization also induces the original fibre equivalence at the image point
(`Bundle.Trivialization.linearEquivAt_pullback`,
`Bundle.Trivialization.continuousLinearEquivAt_pullback` and
`Bundle.Trivialization.continuousLinearMapAt_pullback`), and reads coordinates back into the fibre
as the original one does (`Bundle.Trivialization.symm_pullback`). Hom coordinates between
pullbacks by two different base maps agree with the original source and target coordinates
(`ContinuousLinearMap.inCoordinates_pullback_of_mem`), yielding continuity comparisons between Hom
families over base maps, sections of pulled-back Hom bundles, and compositions and reindexings of
pullbacks (`TauCeti.continuous_hom_bundle_pullback_iff`, `TauCeti.continuous_hom_bundle_comp_iff`,
`TauCeti.continuous_hom_bundle_pullback_comp_iff`,
`TauCeti.continuous_hom_bundle_pullback_comp_of_eq`).
-/

public section

open Bundle

namespace Bundle.Pullback

variable {B B' : Type*} {E : B → Type*} (f : B' → B)

/-- A pullback fibre carries the additive group structure of the original fibre. -/
instance instAddCommGroup [∀ b, AddCommGroup (E b)] (x : B') : AddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (AddCommGroup (E (f x)))

/-- Addition and negation on a pullback fibre are continuous when they are on the original
fibre. -/
instance instIsTopologicalAddGroup [∀ b, AddCommGroup (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, IsTopologicalAddGroup (E b)] (x : B') : IsTopologicalAddGroup ((f *ᵖ E) x) :=
  inferInstanceAs (IsTopologicalAddGroup (E (f x)))

/-- Scalar multiplication on a pullback fibre is continuous when it is on the original fibre. -/
instance instContinuousSMul {R : Type*} [Semiring R] [TopologicalSpace R]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, ContinuousSMul R (E b)] (x : B') : ContinuousSMul R ((f *ᵖ E) x) :=
  inferInstanceAs (ContinuousSMul R (E (f x)))

/-- Scalar multiplications on a pullback fibre form a tower when they do on the original fibre,
for instance the real and complex scalar multiplications of a complex vector bundle. -/
instance instIsScalarTower {R S : Type*} [Semiring R] [Semiring S] [SMul R S]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)] [∀ b, Module S (E b)]
    [∀ b, IsScalarTower R S (E b)] (x : B') : IsScalarTower R S ((f *ᵖ E) x) :=
  inferInstanceAs (IsScalarTower R S (E (f x)))

/-- A pullback fibre carries the normed additive group structure of the original fibre. -/
instance instNormedAddCommGroup [∀ b, NormedAddCommGroup (E b)] (x : B') :
    NormedAddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (NormedAddCommGroup (E (f x)))

/-- Scalar multiplication on a normed pullback fibre has the original norm bound. -/
instance instNormedSpace {𝕜 : Type*} [NormedField 𝕜]
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)] (x : B') :
    NormedSpace 𝕜 ((f *ᵖ E) x) :=
  inferInstanceAs (NormedSpace 𝕜 (E (f x)))

/-- The inner product on a pullback fibre is the original fibre inner product. -/
instance instInnerProductSpace {𝕜 : Type*} [RCLike 𝕜]
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)] (x : B') :
    InnerProductSpace 𝕜 ((f *ᵖ E) x) :=
  inferInstanceAs (InnerProductSpace 𝕜 (E (f x)))

end Bundle.Pullback

namespace Bundle.Trivialization

variable {𝕜 B B' F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace B'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- A pulled-back linear chart gives the original fibre equivalence at the image point. -/
@[simp]
theorem linearEquivAt_pullback (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (f : K) (b : B') (hb : b ∈ (e.pullback f).baseSet) :
    (e.pullback f).linearEquivAt 𝕜 b hb =
      e.linearEquivAt 𝕜 (f b) (by simpa only [pullback_baseSet, Set.mem_preimage] using hb) := by
  apply LinearEquiv.ext
  intro v
  exact congrArg Prod.snd (e.pullback_apply f ⟨b, v⟩)

/-- A pulled-back chart reads coordinates back into the fibre as the original chart does at the
image point. -/
theorem symm_pullback (e : Trivialization F (π F E)) (f : K) {b : B'}
    (hb : f b ∈ e.baseSet) (y : F) :
    (e.pullback f).symm b y = e.symm (f b) y := by
  simpa only [pullback_apply, Pullback.lift_mk, apply_mk_symm e hb] using
    (e.pullback f).symm_apply_apply_mk hb (e.symm (f b) y)

end Bundle.Trivialization

namespace Bundle.Trivialization

variable {𝕜 B B' F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace B'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- A pulled-back continuous linear fibre chart is the original chart at the image point. -/
@[simp]
theorem continuousLinearEquivAt_pullback (e : Trivialization F (π F V)) [e.IsLinear 𝕜]
    (f : K) (x : B') (hx : x ∈ (e.pullback f).baseSet) :
    (e.pullback f).continuousLinearEquivAt 𝕜 x hx =
      e.continuousLinearEquivAt 𝕜 (f x)
        (by simpa only [pullback_baseSet, Set.mem_preimage] using hx) := by
  ext v
  rfl

/-- A pulled-back continuous linear fibre chart, extended by zero off the base set, is the original
one at the image point. -/
@[simp]
theorem continuousLinearMapAt_pullback (e : Trivialization F (π F V)) [e.IsLinear 𝕜]
    (f : K) (x : B') :
    (e.pullback f).continuousLinearMapAt 𝕜 x = e.continuousLinearMapAt 𝕜 (f x) := by
  ext v
  -- Both sides are the chart at `f x` on the base set and zero off it. Here `v : (f *ᵖ V) x`,
  -- which is `V (f x)` only after unfolding, so `rw`/`simp` cannot rewrite the right side; its
  -- `continuousLinearMapAt_apply` unfolding is applied as a term at type `V (f x)` instead.
  simp only [continuousLinearMapAt_apply, linearMapAt_apply, pullback_baseSet, Set.mem_preimage,
    pullback_apply]
  exact ((congrFun (e.continuousLinearMapAt_apply 𝕜 (f x)) v).trans (e.linearMapAt_apply v)).symm

end Bundle.Trivialization

namespace Bundle.Trivialization

variable {B B' F : Type*} {V : B → Type*} [TopologicalSpace B] [TopologicalSpace B']
  [TopologicalSpace F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, Nonempty (V x)] [FiberBundle F V]

/-- Pulling back an atlas trivialization gives an atlas trivialization of the native pullback
bundle. -/
instance memTrivializationAtlas_pullback (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (f : C(B', B)) : MemTrivializationAtlas (e.pullback f) :=
  ⟨e, inferInstance, rfl⟩

end Bundle.Trivialization

namespace ContinuousLinearMap

variable {𝕜 B C X F G K L : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V : B → Type*} {W : C → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ c, AddCommGroup (W c)] [∀ c, Module 𝕜 (W c)] [∀ c, TopologicalSpace (W c)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [FunLike K X B] [ContinuousMapClass K X B]
  [FunLike L X C] [ContinuousMapClass L X C]

/-- The hom-bundle coordinates between two pullbacks are the original source and target
coordinates at their image points, on the common chart domain. -/
theorem inCoordinates_pullback_of_mem (f : K) (g : L) (x₀ x : X)
    (A : V (f x) →L[𝕜] W (g x))
    (hV : f x ∈ (trivializationAt F V (f x₀)).baseSet)
    (hW : g x ∈ (trivializationAt G W (g x₀)).baseSet) :
    inCoordinates F ((f : X → B) *ᵖ V) G ((g : X → C) *ᵖ W) x₀ x x₀ x A =
      inCoordinates F V G W (f x₀) (f x) (g x₀) (g x) A := by
  have hV' : x ∈ (trivializationAt F ((f : X → B) *ᵖ V) x₀).baseSet := hV
  have hW' : x ∈ (trivializationAt G ((g : X → C) *ᵖ W) x₀).baseSet := hW
  -- The pullback fibres inherit the original module instances; `erw` resolves these synonyms.
  erw [inCoordinates_eq hV' hW', inCoordinates_eq hV hW]
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.continuousLinearEquivAt_pullback]
  rfl

private theorem inCoordinates_pullback_of_mem_two (f : K) (g : L) (x₀ x y₀ y : X)
    (A : V (f x) →L[𝕜] W (g y))
    (hV : f x ∈ (trivializationAt F V (f x₀)).baseSet)
    (hW : g y ∈ (trivializationAt G W (g y₀)).baseSet) :
    inCoordinates F ((f : X → B) *ᵖ V) G ((g : X → C) *ᵖ W) x₀ x y₀ y A =
      inCoordinates F V G W (f x₀) (f x) (g y₀) (g y) A := by
  have hV' : x ∈ (trivializationAt F ((f : X → B) *ᵖ V) x₀).baseSet := hV
  have hW' : y ∈ (trivializationAt G ((g : X → C) *ᵖ W) y₀).baseSet := hW
  -- The pullback fibres inherit the original module instances; `erw` resolves these synonyms.
  erw [inCoordinates_eq hV' hW', inCoordinates_eq hV hW]
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.continuousLinearEquivAt_pullback]
  rfl

private theorem inCoordinates_transport_eq {b₀' b₀ b' b : B}
    (hb₀ : b₀' = b₀) (hb : b' = b) {W' : B → Type*}
    [∀ c, AddCommGroup (W' c)] [∀ c, Module 𝕜 (W' c)] [∀ c, TopologicalSpace (W' c)]
    [TopologicalSpace (TotalSpace G W')] [FiberBundle G W'] [VectorBundle 𝕜 G W']
    (A : V b' →L[𝕜] W' b') :
    inCoordinates F V G W' b₀' b' b₀' b' A =
      inCoordinates F V G W' b₀ b b₀ b (show V b →L[𝕜] W' b from hb ▸ A) := by
  cases hb₀
  cases hb
  rfl

end ContinuousLinearMap

namespace TauCeti

section HomPullback

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

/-- At `m₀`, coordinate continuity of a Hom family between pulled-back bundles agrees with
coordinate continuity in the original bundles along the composed base maps. -/
theorem continuousAt_inCoordinates_pullback_iff {m₀ : M}
    (f : K) (g : L) {a b : M → X} (ha : ContinuousAt a m₀) (hb : ContinuousAt b m₀)
    (ϕ : ∀ m, V (f (a m)) →L[𝕜] W (g (b m))) :
    ContinuousAt (fun m ↦ inCoordinates F ((f : X → B) *ᵖ V) G ((g : X → C) *ᵖ W)
        (a m₀) (a m) (b m₀) (b m) (ϕ m)) m₀ ↔
      ContinuousAt (fun m ↦ inCoordinates F V G W
        (f (a m₀)) (f (a m)) (g (b m₀)) (g (b m)) (ϕ m)) m₀ := by
  refine continuousAt_congr ?_
  filter_upwards
    [((map_continuous f).continuousAt.comp ha).preimage_mem_nhds
      ((trivializationAt F V (f (a m₀))).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V (f (a m₀)))),
     ((map_continuous g).continuousAt.comp hb).preimage_mem_nhds
      ((trivializationAt G W (g (b m₀))).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt G W (g (b m₀))))] with m hV hW
  exact inCoordinates_pullback_of_mem_two f g (a m₀) (a m) (b m₀) (b m) (ϕ m) hV hW

section HomBundle

variable [∀ c, IsTopologicalAddGroup (W c)] [∀ c, ContinuousSMul 𝕜 (W c)]

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
  exact inCoordinates_transport_eq (hp x₀) (hp x) (β (r x))

end HomBundle

end HomPullback

end TauCeti
