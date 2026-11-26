/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Fibres and linear charts of pullback bundles

The fibres of `f *ᵖ E` inherit their additive group, topological module, normed and inner product
structures and their scalar towers from `E (f x)`. Mathlib supplies the additive monoid and module
structures. The topological group structures let fibrewise linear equivalences between pullbacks,
such as the pullback `x ↦ e (f x)` of a family of fibrewise linear equivalences `e`, induce maps of
total spaces with continuous inverses. The normed instances allow the orthonormal frame bundle of a
pullback to use exactly the original fibre metrics, with no transport or renorming. The topology of
the fibre norm is Mathlib's pullback fibre topology itself, not merely equal to it after unfolding,
so Mathlib's `FiberBundle.pullback` and `VectorBundle.pullback` apply to statements that take the
fibre topology from the norm, such as those about smooth sections with fibre inner products over an
open subset. A pulled-back
linear trivialization also induces the original fibre equivalence at the image point
(`Bundle.Trivialization.linearEquivAt_pullback`,
`Bundle.Trivialization.continuousLinearEquivAt_pullback` and
`Bundle.Trivialization.continuousLinearMapAt_pullback`), and reads coordinates back into the fibre
as the original one does (`Bundle.Trivialization.symm_pullback`,
`Bundle.Trivialization.pullback_symmL_apply`). Restricting a chart whose source lies in the base
set of a trivialization to an open subset gives a chart whose source lies in the base set of the
trivialization pulled back along the inclusion
(`Bundle.Trivialization.subtypeRestr_source_subset_pullback_baseSet`). Hom coordinates between
pullbacks by two different base maps agree with the original source and target coordinates
(`ContinuousLinearMap.inCoordinates_pullback`), yielding continuity comparisons in
coordinates (`TauCeti.continuousAt_inCoordinates_pullback_iff`); Hom-bundle continuity statements
live in `TauCeti.Topology.VectorBundle.Pullback.Hom`.
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

/-- A pullback fibre carries the normed additive group structure of the original fibre. Its
topology is Mathlib's pullback fibre topology `instTopologicalSpacePullback`, the one in which
`FiberBundle.pullback` is stated, so that the pullback of a bundle with normed fibres is a fibre
bundle for the topology of the fibre norms. -/
instance instNormedAddCommGroup [∀ b, NormedAddCommGroup (E b)] (x : B') :
    NormedAddCommGroup ((f *ᵖ E) x) :=
  letI : NormedAddCommGroup ((f *ᵖ E) x) := inferInstanceAs (NormedAddCommGroup (E (f x)))
  { this with
    toMetricSpace := @MetricSpace.replaceTopology _ (instTopologicalSpacePullback E f x)
      this.toMetricSpace rfl
    dist_eq := this.dist_eq }

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

/-- A pulled-back continuous linear fibre chart inverse, extended by zero off the base set, is
the original one at the image point. -/
@[simp]
theorem symmL_pullback (e : Trivialization F (π F V)) [e.IsLinear 𝕜]
    (f : K) (x : B') :
    (e.pullback f).symmL 𝕜 x = e.symmL 𝕜 (f x) := by
  ext y
  by_cases hx : x ∈ (e.pullback f).baseSet
  · have hx' : f x ∈ e.baseSet := by simpa only [pullback_baseSet, Set.mem_preimage] using hx
    rw [symmL_apply _ hx, symm_pullback e f hx']
    exact (symmL_apply e hx' y).symm
  · have hx' : f x ∉ e.baseSet := by simpa only [pullback_baseSet, Set.mem_preimage] using hx
    rw [symmL_apply_of_notMem _ hx]
    exact (symmL_apply_of_notMem e hx' y).symm

/-- The inverse of a pulled-back continuous linear fibre chart, extended by zero off the base set,
is the inverse of the original one at the image point, applied to a fibre vector. -/
theorem pullback_symmL_apply (e : Trivialization F (π F V)) [e.IsLinear 𝕜] (f : K) (x : B')
    (w : F) : (e.pullback f).symmL 𝕜 x w = e.symmL 𝕜 (f x) w :=
  congrFun (congrArg DFunLike.coe (symmL_pullback e f x)) w

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

namespace Bundle.Trivialization

/-- If the source of a chart `c` lies in the base set of a frame `t`, the source of its
restriction `c|_U` lies in the base set of the pullback of `t` along the inclusion `U → M`. -/
theorem subtypeRestr_source_subset_pullback_baseSet {E M F : Type*} [TopologicalSpace E]
    [TopologicalSpace M] [TopologicalSpace F]
    {V : M → Type*} [∀ x, Nonempty (V x)] [TopologicalSpace (TotalSpace F V)]
    (t : Trivialization F (π F V)) {c : OpenPartialHomeomorph M E} {U : TopologicalSpace.Opens M}
    (hU : Nonempty U) (hct : c.source ⊆ t.baseSet) :
    (c.subtypeRestr hU).source ⊆
      (t.pullback (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))).baseSet := by
  rw [OpenPartialHomeomorph.subtypeRestr_source, pullback_baseSet]
  exact Set.preimage_mono hct

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
coordinates at their image points. -/
@[simp]
theorem inCoordinates_pullback (f : K) (g : L) (x₀ x y₀ y : X)
    (A : V (f x) →L[𝕜] W (g y)) :
    inCoordinates F ((f : X → B) *ᵖ V) G ((g : X → C) *ᵖ W) x₀ x y₀ y A =
      inCoordinates F V G W (f x₀) (f x) (g y₀) (g y) A := by
  ext v
  have h1 : (trivializationAt G ((g : X → C) *ᵖ W) y₀).continuousLinearMapAt 𝕜 y =
      (trivializationAt G W (g y₀)).continuousLinearMapAt 𝕜 (g y) := by
    simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
      Trivialization.continuousLinearMapAt_pullback]
    -- `(g *ᵖ W) y` is definitionally `W (g y)` with `Bundle.Pullback` instance synonyms.
    rfl
  have h2 : (trivializationAt F ((f : X → B) *ᵖ V) x₀).symmL 𝕜 x =
      (trivializationAt F V (f x₀)).symmL 𝕜 (f x) := by
    simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
      Trivialization.symmL_pullback]
    -- `(f *ᵖ V) x` is definitionally `V (f x)` with `Bundle.Pullback` instance synonyms.
    rfl
  -- The pullback fibres inherit `Bundle.Pullback` module/topology instances that are synonyms
  -- of the original fibre instances on `V (f x)` and `W (g y)`; `erw` resolves these synonyms.
  erw [inCoordinates, inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  exact (congrFun (congrArg DFunLike.coe h1) _).trans
    (congrArg ((trivializationAt G W (g y₀)).continuousLinearMapAt 𝕜 (g y))
      (congrArg A (congrFun (congrArg DFunLike.coe h2) v)))

end ContinuousLinearMap

namespace TauCeti

open ContinuousLinearMap

variable {𝕜 B C M X F G K L : Type*} [NontriviallyNormedField 𝕜]
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
    (f : K) (g : L) (a b : M → X)
    (ϕ : ∀ m, V (f (a m)) →L[𝕜] W (g (b m))) :
    ContinuousAt (fun m ↦ inCoordinates F ((f : X → B) *ᵖ V) G ((g : X → C) *ᵖ W)
        (a m₀) (a m) (b m₀) (b m) (ϕ m)) m₀ ↔
      ContinuousAt (fun m ↦ inCoordinates F V G W
        (f (a m₀)) (f (a m)) (g (b m₀)) (g (b m)) (ϕ m)) m₀ := by
  simp only [inCoordinates_pullback]

end TauCeti
