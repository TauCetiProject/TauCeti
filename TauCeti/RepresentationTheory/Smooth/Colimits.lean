/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.RepresentationTheory.Smooth.Abelian

/-!
# Colimits of smooth representations

Let `A` be a ring and `G` a topological group with separately continuous multiplication. A
representation whose underlying module is spanned by the images of intertwining maps out of smooth
representations is smooth: the smooth vectors form a submodule, and an intertwining map sends
smooth vectors to smooth vectors. The legs of a colimit cocone in `Rep A G` jointly span its point,
because the forgetful functor to `ModuleCat A` preserves colimits. So the property "smooth" on
`Rep A G` is closed under colimits of every shape, in particular under arbitrary direct sums and
filtered colimits. Hence `SmoothRep A G` has all colimits, computed in `Rep A G`, and the
inclusion `SmoothRep A G ⥤ Rep A G` preserves them. Together with the preservation of kernels and
finite products, the inclusion is exact.

## Main results

* `Representation.isSmooth_of_iSup_range_eq_top`: a representation spanned by the images of
  intertwining maps out of smooth representations is smooth.
* `TauCeti.SmoothRep.isClosedUnderColimitsOfShape`: smoothness is closed under colimits in
  `Rep A G`.
* `TauCeti.SmoothRep.hasColimitsOfSize`: `SmoothRep A G` has all colimits.
* `TauCeti.SmoothRep.preservesColimitsOfSize_ι`: the inclusion into `Rep A G` preserves all
  colimits.
* `TauCeti.SmoothRep.preservesFiniteLimits_ι`, `TauCeti.SmoothRep.preservesFiniteColimits_ι`:
  the inclusion into `Rep A G` is exact.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1 and §2.
-/

@[expose] public section

open CategoryTheory Limits Representation

universe w u v

namespace Representation

variable {A G : Type*} [Ring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  {W : Type*} [AddCommGroup W] [Module A W] {σ : Representation A G W}

/-- **A representation spanned by smooth images is smooth.** If the ranges of a family of
intertwining maps out of smooth representations span `W`, then `W` is smooth. -/
theorem isSmooth_of_iSup_range_eq_top {κ : Type*} {V : κ → Type*} [∀ k, AddCommGroup (V k)]
    [∀ k, Module A (V k)] {ρ : ∀ k, Representation A G (V k)} [∀ k, IsSmooth (ρ k)]
    (f : ∀ k, (ρ k).IntertwiningMap σ)
    (hf : ⨆ k, LinearMap.range (f k).toLinearMap = ⊤) : IsSmooth σ := by
  refine isSmooth_iff_forall_mem_smoothVectors.2 fun w ↦ ?_
  have hle : ⨆ k, LinearMap.range (f k).toLinearMap ≤ σ.smoothVectors.toSubmodule :=
    iSup_le fun k ↦ by
      rintro _ ⟨v, rfl⟩
      exact (f k).apply_mem_smoothVectors (IsSmooth.mem_smoothVectors v)
  exact hle (hf ▸ Submodule.mem_top)

end Representation

namespace TauCeti

namespace SmoothRep

variable (A : Type u) [Ring A] (G : Type v) [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

/-- **Smoothness passes to colimits**: the point of a colimit cocone in `Rep A G` over a diagram
of smooth representations is smooth, since the images of the legs span it. -/
instance isClosedUnderColimitsOfShape (J : Type w) [Category.{w} J] :
    (isSmoothProperty.{w} A G).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    have : ∀ j, IsSmooth (p.diag.obj j).ρ := p.prop_diag_obj
    exact isSmooth_of_iSup_range_eq_top (fun j ↦ (p.ι.app j).hom)
      (ModuleCat.iSup_range_eq_top_of_isColimit
        (isColimitOfPreserves (forget₂ (Rep.{w} A G) (ModuleCat A)) p.isColimit))

/-- The category of smooth representations has all colimits, computed in `Rep A G`. -/
instance hasColimitsOfSize : HasColimitsOfSize.{w, w} (SmoothRep.{w} A G) where
  has_colimits_of_shape _ _ := inferInstance

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves all colimits. -/
instance preservesColimitsOfSize_ι : PreservesColimitsOfSize.{w, w} (ι.{w} A G) where
  preservesColimitsOfShape := inferInstance

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves finite colimits. -/
instance preservesFiniteColimits_ι : PreservesFiniteColimits (ι.{w} A G) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves finite limits: it preserves kernels, and
finite products are computed in `Rep A G`. -/
instance preservesFiniteLimits_ι : PreservesFiniteLimits (ι.{w} A G) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

end SmoothRep

end TauCeti
