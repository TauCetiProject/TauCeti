/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Pullbacks of fibre bundles

Three facts about Mathlib's pullback bundle `f *ᵖ E`, whose fibre over `x` is the fibre of `E` over
`f x`, needed to pull back bundles with extra structure on their fibres or on their atlas.

* The fibres of `f *ᵖ E` carry the actions of a monoid on the fibres of `E`
  (`Bundle.Pullback.instMulAction`), as Mathlib already does for module structures. This is what
  makes the pullback of a principal bundle again carry a right action on its fibres.
* The coordinate change between the pullbacks `e.pullback f` and `e'.pullback f` of two
  trivializations, over a point `x` with `f x` in the base set of `e`, is the coordinate change
  between `e` and `e'` over `f x` (`Bundle.Trivialization.coordChange_pullback`). This transfers
  regularity of the coordinate changes of `E` to those of `f *ᵖ E`.
* The canonical lift `Bundle.Pullback.lift f : TotalSpace F (f *ᵖ E) → TotalSpace F E` has range
  `(π F E) ⁻¹' Set.range f` and inherits injectivity, inducingness, and topological (or open /
  closed) embedding properties from `f` (`Bundle.Pullback.isEmbedding_lift`).
-/

public section

open Bundle Set Topology

variable {B B' : Type*}

/-- The fibres of a pullback bundle `f *ᵖ E` carry the actions on the fibres of `E`: the fibre over
`x` is the fibre of `E` over `f x`. -/
instance Bundle.Pullback.instMulAction {M : Type*} [Monoid M] {E : B → Type*}
    [i : ∀ b, MulAction M (E b)] (f : B' → B) (x : B') : MulAction M ((f *ᵖ E) x) :=
  i (f x)

section Lift

variable {F : Type*} {E : B → Type*}

/-- The canonical lift from the pullback total space `f *ᵖ E` to `E` has image equal to the
part of `E` lying over the range of `f`. -/
@[simp]
theorem Bundle.Pullback.range_lift (f : B' → B) :
    range (Pullback.lift (F := F) (E := E) f) = π F E ⁻¹' range f := by
  ext w
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.proj, rfl⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · exact cast (congrArg E hx.symm) w.2
    · cases w with | mk b v => cases hx; rfl

/-- If `f` is injective, the canonical lift `Pullback.lift f` on total spaces is injective. -/
theorem Bundle.Pullback.lift_injective {f : B' → B} (hf : Function.Injective f) :
    Function.Injective (Pullback.lift (F := F) (E := E) f) := by
  rintro ⟨x₁, v₁⟩ ⟨x₂, v₂⟩ h
  obtain rfl : x₁ = x₂ := hf (congrArg (π F E) h)
  exact TotalSpace.ext rfl (TotalSpace.ext_iff.mp h).2

variable [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]

/-- If `f` is a topological inducing map and the projection `π F E` is continuous, then
`Pullback.lift f` is a topological inducing map. -/
theorem Bundle.Pullback.isInducing_lift_of_continuous_proj {f : B' → B} (hf : IsInducing f)
    (hπ : Continuous (π F E)) :
    IsInducing (Pullback.lift (F := F) (E := E) f) :=
  IsInducing.of_comp (Pullback.continuous_lift F E f) (hπ.prodMk continuous_id)
    ((hf.prodMap .id).comp (inducing_pullbackTotalSpaceEmbedding F E f))

variable [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- Along a topological inducing map `f`, the canonical lift `Pullback.lift f` of a fibre bundle
is a topological inducing map. -/
theorem Bundle.Pullback.isInducing_lift {f : B' → B} (hf : IsInducing f) :
    IsInducing (Pullback.lift (F := F) (E := E) f) :=
  isInducing_lift_of_continuous_proj hf (FiberBundle.continuous_proj F E)

/-- Along a topological embedding `f`, the canonical lift `Pullback.lift f` of a fibre bundle is a
topological embedding. -/
theorem Bundle.Pullback.isEmbedding_lift {f : B' → B} (hf : IsEmbedding f) :
    IsEmbedding (Pullback.lift (F := F) (E := E) f) :=
  ⟨isInducing_lift hf.isInducing, lift_injective hf.injective⟩

/-- Along a closed embedding `f`, the canonical lift `Pullback.lift f` of a fibre bundle is a
closed embedding. -/
theorem Bundle.Pullback.isClosedEmbedding_lift {f : B' → B} (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (Pullback.lift (F := F) (E := E) f) :=
  ⟨isEmbedding_lift hf.isEmbedding,
    (range_lift (F := F) (E := E) f).symm ▸
      hf.isClosed_range.preimage (FiberBundle.continuous_proj F E)⟩

/-- Along an open embedding `f`, the canonical lift `Pullback.lift f` of a fibre bundle is an open
embedding. -/
theorem Bundle.Pullback.isOpenEmbedding_lift {f : B' → B} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (Pullback.lift (F := F) (E := E) f) :=
  ⟨isEmbedding_lift hf.isEmbedding,
    (range_lift (F := F) (E := E) f).symm ▸
      hf.isOpen_range.preimage (FiberBundle.continuous_proj F E)⟩

end Lift

variable {F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, Nonempty (E b)] {K : Type*} [FunLike K B' B]
  [ContinuousMapClass K B' B]

/-- The coordinate change between the pullbacks of two trivializations, over a point `x` whose
image `f x` lies in the base set of the first, is the coordinate change between the
trivializations over `f x`. -/
theorem Bundle.Trivialization.coordChange_pullback (e e' : Trivialization F (π F E)) (f : K)
    {x : B'} (hx : f x ∈ e.baseSet) (v : F) :
    (e.pullback f).coordChange (e'.pullback f) x v = e.coordChange e' (f x) v := by
  rw [Trivialization.coordChange, Trivialization.coordChange, Trivialization.pullback_apply,
    ← e.mk_symm hx]
  -- By construction, the inverse of `e.pullback f` sends `(x, v)` to the point `e.symm (f x) v` of
  -- the fibre over `x`, and `Pullback.lift f` sends that point to `⟨f x, e.symm (f x) v⟩`.
  rfl
