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
pullback to use exactly the original fibre metrics, with no transport or renorming. A pulled-back
linear trivialization also induces the original fibre equivalence at the image point
(`Bundle.Trivialization.linearEquivAt_pullback` and
`Bundle.Trivialization.continuousLinearEquivAt_pullback`). Hom coordinates between pullbacks by two
different base maps agree with the original source and target coordinates
(`ContinuousLinearMap.inCoordinates_pullback_of_mem`).
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

end ContinuousLinearMap
