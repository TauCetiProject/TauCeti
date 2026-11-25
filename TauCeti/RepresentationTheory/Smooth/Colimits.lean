/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Abelian

/-!
# Colimits of smooth representations

Let `A` be a ring and `G` a topological group with separately continuous multiplication. A
representation whose underlying module is spanned by the images of intertwining maps out of smooth
representations is smooth (`Representation.isSmooth_of_iSup_range_eq_top`): the smooth vectors
form a submodule, and an intertwining map sends smooth vectors to smooth vectors. The legs of a
colimit cocone in `Rep A G` jointly span its point, because the projection onto the quotient by
the span of their images vanishes on every leg. So the property "smooth" on `Rep A G` is closed
under colimits of every shape, in any universe, in particular under arbitrary direct sums and
filtered colimits. Hence `SmoothRep A G` has all colimits, computed in `Rep A G`, and the
inclusion `SmoothRep A G ⥤ Rep A G` preserves them. (That it preserves finite limits and finite
colimits, so is exact, is the general `CategoryTheory.ObjectProperty.preservesFiniteLimits_ι` and
`CategoryTheory.ObjectProperty.preservesFiniteColimits_ι`.)

## Main results

* `TauCeti.SmoothRep.isClosedUnderColimitsOfShape`: smoothness is closed under colimits in
  `Rep A G`.
* `TauCeti.SmoothRep.hasColimitsOfSize`: `SmoothRep A G` has all colimits.
* `TauCeti.SmoothRep.preservesColimitsOfSize_ι`: the inclusion into `Rep A G` preserves all
  colimits.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1 and §2.
-/

@[expose] public section

open CategoryTheory Limits Representation

universe w u v

namespace TauCeti

namespace SmoothRep

variable (A : Type u) [Ring A] (G : Type v) [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

/-- **Smoothness passes to colimits**: the point of a colimit cocone in `Rep A G` over a diagram
of smooth representations is smooth, since the images of the legs span it. -/
instance isClosedUnderColimitsOfShape (J : Type*) [Category* J] :
    (isSmoothProperty.{w} A G).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    have : ∀ j, IsSmooth (p.diag.obj j).ρ := p.prop_diag_obj
    let f (j : J) : (p.diag.obj j).ρ.IntertwiningMap X.ρ := (p.ι.app j).hom
    set T := ⨆ j, LinearMap.range (f j).toLinearMap
    have hT (g : G) : T ≤ T.comap (X.ρ g) := iSup_le fun j ↦ by
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_iSup_of_mem j ⟨_, Rep.hom_comm_apply (p.ι.app j) g v⟩
    -- The projection onto `X ⧸ T` vanishes on every leg, hence is zero.
    have h : Rep.mkQ X T hT = 0 := p.isColimit.hom_ext fun j ↦ by
      ext v
      simpa [Submodule.Quotient.mk_eq_zero] using
        Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self (f j).toLinearMap v)
    refine isSmooth_of_iSup_range_eq_top f (eq_top_iff.2 fun x _ ↦ ?_)
    simpa [Submodule.Quotient.mk_eq_zero] using congr((Rep.Hom.hom $h) x)

/-- The category of smooth representations has all colimits, computed in `Rep A G`. -/
instance hasColimitsOfSize : HasColimitsOfSize.{w, w} (SmoothRep.{w} A G) where
  has_colimits_of_shape _ _ := inferInstance

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves all colimits. -/
instance preservesColimitsOfSize_ι : PreservesColimitsOfSize.{w, w} (ι.{w} A G) where
  preservesColimitsOfShape := inferInstance

end SmoothRep

end TauCeti
