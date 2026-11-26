/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# The legs of a colimit of representations span its point

The ranges of the legs of a colimit cocone in `Rep A G` span its point: the images of the legs
span a subrepresentation, and the projection `Rep.mkQ` onto the quotient by it vanishes on every
leg, so is zero. This is the `Rep` analogue of `TauCeti.ModuleCat.iSup_range_eq_top_of_isColimit`.
It is proved inside `Rep A G`, so it holds for diagrams of every shape, in any universe, without
asking the forgetful functor to `ModuleCat A` to preserve the colimit.

## Main results

* `TauCeti.Rep.iSup_range_eq_top_of_isColimit`: the ranges of the legs of a colimit cocone in
  `Rep A G` span its point.
-/

@[expose] public section

open CategoryTheory Limits

universe w u v

namespace TauCeti

namespace Rep

variable {A : Type u} [Ring A] {G : Type v} [Monoid G]

-- The codomain `c.pt` is named because the leg `c.ι.app j` is typed with codomain
-- `((Functor.const J).obj c.pt).obj j`, which depends on `j` until it is unfolded.
/-- The ranges of the legs of a colimit cocone in `Rep A G` span its point. -/
theorem iSup_range_eq_top_of_isColimit {J : Type*} [Category* J] {F : J ⥤ _root_.Rep.{w} A G}
    {c : Cocone F} (hc : IsColimit c) :
    ⨆ j, LinearMap.range (_root_.Rep.Hom.hom (B := c.pt) (c.ι.app j)).toLinearMap = ⊤ := by
  set T := ⨆ j, LinearMap.range (_root_.Rep.Hom.hom (B := c.pt) (c.ι.app j)).toLinearMap
  have hT (g : G) : T ≤ T.comap (c.pt.ρ g) := iSup_le fun j ↦ by
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem j ⟨_, _root_.Rep.hom_comm_apply (c.ι.app j) g v⟩
  -- The projection onto `c.pt ⧸ T` vanishes on every leg, hence is zero.
  have h : _root_.Rep.mkQ c.pt T hT = 0 := hc.hom_ext fun j ↦ by
    ext v
    simpa [Submodule.Quotient.mk_eq_zero] using
      Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ v)
  exact eq_top_iff.2 fun x _ ↦ by
    simpa [Submodule.Quotient.mk_eq_zero] using congr((_root_.Rep.Hom.hom $h) x)

end Rep

end TauCeti
