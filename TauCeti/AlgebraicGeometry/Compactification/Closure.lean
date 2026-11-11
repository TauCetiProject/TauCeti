/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Scheme-theoretic closures of quasi-compact immersions as compactifications

Let `i : X ⟶ Y` be a quasi-compact immersion and `q : Y ⟶ S` a proper morphism. Then `X` is a
quasi-compact open subscheme of the scheme-theoretic image of `i`, and that image is proper over
`S` as a closed subscheme of `Y`. So the scheme-theoretic closure of `X` in `Y` is a dense
compactification of `i ≫ q` (`TauCeti.DenseCompactification.ofImmersion`). It keeps the full
scheme structure of `X`, including nilpotents. Every dense compactification whose ambient scheme
maps to `Y` compatibly with `i` and `q` maps to it
(`TauCeti.DenseCompactification.ofImmersionLift`), and such a map is unique because dense
compactifications form a thin category.

This construction is shared by the dense replacement of a compactification `C` (the case
`i = C.j`, `q = C.p`), the common refinement of two compactifications (the immersion of `X` into
the fibre product of their ambient schemes) and the compactifications induced along quasi-compact
immersions.

## Main declarations

* `TauCeti.DenseCompactification.ofImmersion`: the scheme-theoretic image of a quasi-compact
  immersion into a proper `S`-scheme, as a dense compactification.
* `TauCeti.DenseCompactification.ofImmersionLift`: its universal property.

## References

* The Stacks Project, Section 29.6, *Scheme theoretic image* (tag 01R5), and Section 29.7,
  *Scheme theoretic closure and density* (tag 01RB).
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X Y S : Scheme.{u}} {f : X ⟶ S}

namespace DenseCompactification

noncomputable section

variable (i : X ⟶ Y) [IsImmersion i] [QuasiCompact i] (q : Y ⟶ S) [IsProper q] (w : i ≫ q = f)

/-- The scheme-theoretic image of a quasi-compact immersion `i : X ⟶ Y` into a proper `S`-scheme
`q : Y ⟶ S`, as a dense compactification of `f = i ≫ q`. -/
-- Exposure and implicit reducibility keep the projection formulas of the ambient scheme and its
-- maps usable for dependent morphism equations in importing modules.
@[expose, implicit_reducible] def ofImmersion : DenseCompactification f :=
  ⟨Compactification.ofHom i.toImage (i.imageι ≫ q) (by simp [w]),
    (denseCompactificationProperty_iff f _).mpr inferInstance⟩

@[simp]
theorem ofImmersion_obj_Xbar : (ofImmersion i q w).obj.Xbar = i.image :=
  (rfl)

@[simp]
theorem ofImmersion_obj_j : (ofImmersion i q w).obj.j = i.toImage :=
  (rfl)

@[simp]
theorem ofImmersion_obj_p : (ofImmersion i q w).obj.p = i.imageι ≫ q :=
  (rfl)

variable {i q w}

/-- A dense compactification `E` of `f` maps to the scheme-theoretic closure of `i`, given a map
`h` from its ambient scheme to `Y` which restricts to `i` on `X` and lies over `S`. Its interior is
scheme-theoretically dense, so `h` factors through the closed subscheme. -/
def ofImmersionLift (E : DenseCompactification f) (h : E.obj.Xbar ⟶ Y) (hj : E.obj.j ≫ h = i)
    (hp : h ≫ q = E.obj.p) : E ⟶ ofImmersion i q w :=
  have H : i.imageι.ker ≤ h.ker := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι, ← hj,
      E.obj.j.ker_comp_of_isSchemeTheoreticallyDominant]
  ObjectProperty.homMk <| ObjectProperty.homMk
    { h := IsClosedImmersion.lift i.imageι h H
      ι_h := by
        rw [← cancel_mono i.imageι, Category.assoc, IsClosedImmersion.lift_fac, hj]
        exact i.toImage_imageι.symm
      h_π := by
        simp only [ofImmersion_obj_p]
        rw [IsClosedImmersion.lift_fac_assoc, hp] }

/-- On ambient schemes, the map to the closure of `i` followed by the closed immersion into `Y`
is the given map. -/
@[reassoc (attr := simp)]
theorem ofImmersionLift_hom_hom_h_imageι (E : DenseCompactification f) (h : E.obj.Xbar ⟶ Y)
    (hj : E.obj.j ≫ h = i) (hp : h ≫ q = E.obj.p) :
    (ofImmersionLift (w := w) E h hj hp).hom.hom.h ≫ i.imageι = h :=
  IsClosedImmersion.lift_fac _ _ _

end

end DenseCompactification

end TauCeti
