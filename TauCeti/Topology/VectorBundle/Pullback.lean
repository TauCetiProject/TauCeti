/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Topology.FiberBundle.Pullback

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

A family of fibrewise isomorphisms `Φ z : E (f z) ≃L[𝕜] E x`, continuous on total spaces together
with its inverse, identifies the pullback `f *ᵖ E` with the trivial bundle with fibre `E x`
(`TauCeti.IsPullbackTrivialization`). Such identifications pull back along continuous maps, and
their coordinate expressions in the trivialization of `E` at `x` are continuous.
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

namespace TauCeti

section PullbackTrivialization

variable {𝕜 : Type*} [Semiring 𝕜] {X : Type*} {Z : Type*} [TopologicalSpace Z] {F : Type*}
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)]

variable (F) in
/-- `Φ` identifies the pullback `f *ᵖ E` of `E` along `f : Z → X` with the trivial bundle over `Z`
whose fibre is the fibre `E x` over a fixed point `x`: the fibrewise isomorphisms
`Φ z : E (f z) ≃L[𝕜] E x` are continuous on total spaces, and so are their inverses. -/
structure IsPullbackTrivialization (f : Z → X) (x : X) (Φ : ∀ z, E (f z) ≃L[𝕜] E x) : Prop where
  /-- The isomorphisms `Φ z` are continuous on total spaces. -/
  continuous_apply : Continuous (fun v : TotalSpace F (f *ᵖ E) ↦
    TotalSpace.mk' F (E := (fun _ : Z ↦ x) *ᵖ E) v.proj (Φ v.proj v.2))
  /-- The inverses `(Φ z)⁻¹` are continuous on total spaces. -/
  continuous_symm_apply : Continuous (fun v : TotalSpace F ((fun _ : Z ↦ x) *ᵖ E) ↦
    TotalSpace.mk' F (E := f *ᵖ E) v.proj ((Φ v.proj).symm v.2))

/-- A pullback trivialization pulls back along continuous maps. -/
theorem IsPullbackTrivialization.comp {Z' : Type*} [TopologicalSpace Z'] {f : Z → X} {x : X}
    {Φ : ∀ z, E (f z) ≃L[𝕜] E x} (hΦ : IsPullbackTrivialization F f x Φ) {g : Z' → Z}
    (hg : Continuous g) : IsPullbackTrivialization F (f ∘ g) x (fun z ↦ Φ (g z)) := by
  have hι : Continuous fun v : TotalSpace F ((f ∘ g) *ᵖ E) ↦
      TotalSpace.mk' F (E := f *ᵖ E) (g v.proj) v.2 :=
    Pullback.continuous_iff.2 ⟨hg.comp (Pullback.continuous_proj F E _),
      Pullback.continuous_lift F E _⟩
  have hι' : Continuous fun v : TotalSpace F ((fun _ : Z' ↦ x) *ᵖ E) ↦
      TotalSpace.mk' F (E := (fun _ : Z ↦ x) *ᵖ E) (g v.proj) v.2 :=
    Pullback.continuous_iff.2 ⟨hg.comp (Pullback.continuous_proj F E _),
      Pullback.continuous_lift F E _⟩
  refine ⟨Pullback.continuous_iff.2 ⟨Pullback.continuous_proj F E _, ?_⟩,
    Pullback.continuous_iff.2 ⟨Pullback.continuous_proj F E _, ?_⟩⟩
  · -- Both maps send a vector to the same point of the total space of `E`.
    have h := (Pullback.continuous_lift F E _).comp (hΦ.continuous_apply.comp hι)
    simp only [Function.comp_def, Pullback.lift_mk] at h ⊢
    exact h
  · have h := (Pullback.continuous_lift F E _).comp (hΦ.continuous_symm_apply.comp hι')
    simp only [Function.comp_def, Pullback.lift_mk] at h ⊢
    exact h

end PullbackTrivialization

section Coordinates

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [TopologicalSpace X] {Z : Type*} [TopologicalSpace Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] {f : Z → X} {x : X}

/-- The coordinate expression `e ∘ Ψ z ∘ (Φ z)⁻¹ ∘ e⁻¹` of the transition between two pullback
trivializations, in the trivialization `e` of `E` at `x`, depends continuously on `z`. -/
theorem IsPullbackTrivialization.continuous_coord_trans {Φ Ψ : ∀ z, E (f z) ≃L[𝕜] E x}
    (hΦ : IsPullbackTrivialization F f x Φ) (hΨ : IsPullbackTrivialization F f x Ψ) :
    Continuous fun z ↦ (trivializationAt F E x).continuousLinearMapAt 𝕜 x ∘L
      (Ψ z : E (f z) →L[𝕜] E x) ∘L ((Φ z).symm : E x →L[𝕜] E (f z)) ∘L
      (trivializationAt F E x).symmL 𝕜 x := by
  set e := trivializationAt F E x
  refine continuous_clm_apply.2 fun w ↦ ?_
  have h₀ : Continuous fun z : Z ↦
      TotalSpace.mk' F (E := (fun _ : Z ↦ x) *ᵖ E) z (e.symmL 𝕜 x w) :=
    Pullback.continuous_iff.2 ⟨continuous_id, by
      simp only [TotalSpace.mk', Pullback.lift_mk]
      exact continuous_const⟩
  have h := (Pullback.continuous_lift F E _).comp
    (hΨ.continuous_apply.comp (hΦ.continuous_symm_apply.comp h₀))
  have h' := (e.continuousOn.comp_continuous h fun z ↦
    e.mem_source.2 (FiberBundle.mem_baseSet_trivializationAt' x)).snd
  refine h'.congr fun z ↦ ?_
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Pullback.lift_mk, TotalSpace.mk']
  exact (e.continuousLinearMapAt_apply_of_mem 𝕜
    (FiberBundle.mem_baseSet_trivializationAt' x) _).symm

/-- The coordinate expression `e ∘ Φ z ∘ e⁻¹` of a pullback trivialization, read in the
trivialization `e` of `E` at `x` on both sides, depends continuously on `z` wherever `f z` lies in
the base set of `e`. -/
theorem IsPullbackTrivialization.continuousOn_coord {Φ : ∀ z, E (f z) ≃L[𝕜] E x}
    (hΦ : IsPullbackTrivialization F f x Φ) (hf : Continuous f) :
    ContinuousOn (fun z ↦ (trivializationAt F E x).continuousLinearMapAt 𝕜 x ∘L
      (Φ z : E (f z) →L[𝕜] E x) ∘L (trivializationAt F E x).symmL 𝕜 (f z))
      (f ⁻¹' (trivializationAt F E x).baseSet) := by
  set e := trivializationAt F E x
  refine continuousOn_clm_apply.2 fun w ↦ ?_
  have h₀ : ContinuousOn (fun z : Z ↦ TotalSpace.mk' F (E := f *ᵖ E) z (e.symmL 𝕜 (f z) w))
      (f ⁻¹' e.baseSet) := by
    refine (inducing_pullbackTotalSpaceEmbedding F E f).continuousOn_iff.2 ?_
    refine continuousOn_id.prodMk ?_
    refine (e.continuousOn_symm.comp (hf.prodMk continuous_const).continuousOn
      fun z hz ↦ Set.mk_mem_prod hz (Set.mem_univ w)).congr fun z hz ↦ ?_
    simp [e.symmL_apply hz]
  have h := (Pullback.continuous_lift F E _).comp_continuousOn
    (hΦ.continuous_apply.comp_continuousOn h₀)
  have h' := (e.continuousOn.comp h fun z _ ↦
    e.mem_source.2 (FiberBundle.mem_baseSet_trivializationAt' x)).snd
  refine h'.congr fun z _ ↦ ?_
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Pullback.lift_mk, TotalSpace.mk']
  exact (e.continuousLinearMapAt_apply_of_mem 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x) _)

end Coordinates

end TauCeti
