/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.Compactification.BaseChange
public import TauCeti.AlgebraicGeometry.Compactification.Uniqueness
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Compactifications induced along quasi-compact immersions

Let `i : X ⟶ Y` be a quasi-compact immersion and `q : Y ⟶ S` a proper morphism. Then `X` is a
quasi-compact open subscheme of the scheme-theoretic image of `i`, and that image is proper over
`S` as a closed subscheme of `Y`. So the scheme-theoretic closure of `X` in `Y` is a dense
compactification of `i ≫ q` (`TauCeti.DenseCompactification.ofImmersion`). It keeps the full
scheme structure of `X`, including nilpotents. Every dense compactification whose ambient scheme
maps to `Y` compatibly with `i` and `q` maps to it
(`TauCeti.DenseCompactification.ofImmersionLift`), and such a map is unique because dense
compactifications form a thin category. The dense replacement of a compactification `C`
(`TauCeti.Compactification.denseReplacement`) is the case `i = C.j`, `q = C.p`.

Applied to the ambient scheme of a compactification `C` of `f' : X' ⟶ S`, this shows that a
compactification passes to every quasi-compact immersion `i : X ⟶ X'` over `S`, for instance a
closed subscheme of `X'`: the closure of `X` in `C.Xbar` is a dense compactification of
`i ≫ f'` (`TauCeti.Compactification.immersionClosure`). The construction is functorial in refinement
maps of `C` (`TauCeti.Compactification.immersionClosureFunctor`). When `i` is a closed immersion,
the closure meets the open subscheme `X'` of `C.Xbar` exactly in `X`, as schemes: the square formed
by the two interiors, `i` and the closed immersion of ambient schemes is cartesian
(`TauCeti.Compactification.isPullback_immersionClosure`). So the boundary of the induced
compactification lies over the boundary of `C`.

In particular, if `X` is a closed subscheme of a base change `X₀ ×_{S₀} S` of a compactifiable
morphism `X₀ ⟶ S₀`, then `X ⟶ S` has a dense compactification
(`TauCeti.nonempty_denseCompactification_of_isImmersion_pullback`). This is how Nagata's
compactification theorem over a quasi-compact quasi-separated base is deduced from the Noetherian
case: `X` is a closed subscheme of a finitely presented `S`-scheme, which descends to a Noetherian
base. Nothing beyond the embedding is assumed of `X ⟶ S`; in particular it need not be of finite
presentation.

## Main declarations

* `TauCeti.DenseCompactification.ofImmersion`: the scheme-theoretic image of a quasi-compact
  immersion into a proper `S`-scheme, as a dense compactification.
* `TauCeti.DenseCompactification.ofImmersionLift`: its universal property.
* `TauCeti.Compactification.immersionClosure`: the compactification induced along a quasi-compact
  immersion, and `TauCeti.Compactification.immersionClosureFunctor`, its functoriality.
* `TauCeti.Compactification.isPullback_immersionClosure`: for a closed immersion, the induced
  compactification restricts to `X` over the interior of the original one.
* `TauCeti.nonempty_denseCompactification_of_isImmersion` and
  `TauCeti.nonempty_denseCompactification_of_isImmersion_pullback`: existence of dense
  compactifications along quasi-compact immersions.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT), and Section 38.33,
  *Nagata compactification* (tag 0F41).
* The Stacks Project, Section 29.6, *Scheme theoretic image* (tag 01R5), and Section 29.7,
  *Scheme theoretic closure and density* (tag 01RB).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X X' Y S : Scheme.{u}} {f : X ⟶ S}

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

namespace Compactification

noncomputable section

variable {f' : X' ⟶ S} (i : X ⟶ X') [IsImmersion i] [QuasiCompact i] (w : i ≫ f' = f)

/-- The compactification of `f` induced by a compactification `C` of `f'` along a quasi-compact
immersion `i` with `i ≫ f' = f`: the scheme-theoretic closure of `X` in `C.Xbar`. -/
abbrev immersionClosure (C : Compactification f') : DenseCompactification f :=
  DenseCompactification.ofImmersion (i ≫ C.j) C.p (by rw [Category.assoc, C.obj.ι_π, w])

variable {i w}

/-- A refinement map of compactifications of `f'` induces a refinement map of the
compactifications of `f` induced along `i`. -/
def immersionClosureMap {C D : Compactification f'} (φ : C ⟶ D) :
    immersionClosure i w C ⟶ immersionClosure i w D :=
  DenseCompactification.ofImmersionLift _ ((i ≫ C.j).imageι ≫ φ.hom.h)
    (by simp [φ.hom.ι_h]) (by simp [φ.hom.h_π])

/-- On ambient schemes, the induced refinement map is the restriction of the original one. -/
@[reassoc (attr := simp)]
theorem immersionClosureMap_hom_hom_h_imageι {C D : Compactification f'} (φ : C ⟶ D) :
    (immersionClosureMap φ (w := w)).hom.hom.h ≫ (i ≫ D.j).imageι =
      (i ≫ C.j).imageι ≫ φ.hom.h :=
  DenseCompactification.ofImmersionLift_hom_hom_h_imageι _ _ _ _

variable (i w)

/-- Compactifications induced along a quasi-compact immersion `i` with `i ≫ f' = f`, as a
functor from compactifications of `f'` to dense compactifications of `f`. Its functor laws hold
because dense compactifications form a thin category. -/
-- The object equations must remain available when elaborating dependent morphism formulas.
@[expose, implicit_reducible, simps obj map]
def immersionClosureFunctor : Compactification f' ⥤ DenseCompactification f where
  obj := immersionClosure i w
  map := immersionClosureMap
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Along a closed immersion `i`, the compactification induced by `C` meets the interior of `C`
exactly in `X`: the square formed by `i`, the two open immersions and the closed immersion of
ambient schemes is cartesian. -/
theorem isPullback_immersionClosure (i : X ⟶ X') [IsClosedImmersion i] (w : i ≫ f' = f)
    (C : Compactification f') :
    IsPullback i (immersionClosure i w C).obj.j C.j (i ≫ C.j).imageι := by
  refine isPullback_of_isClosedImmersion _ _ _ _ (i ≫ C.j).toImage_imageι.symm ?_
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι,
    ← Scheme.IdealSheafData.ker_eq_comap_of_isPullback_of_isOpenImmersion C.j
      (IsPullback.of_vert_isIso_mono (fst := i) (snd := 𝟙 X) ⟨by simp⟩)]

end

end Compactification

/-- If `f` factors through a quasi-compact immersion into a compactifiable `S`-scheme, for
instance as a closed subscheme of it, then `f` has a dense compactification. -/
theorem nonempty_denseCompactification_of_isImmersion {f' : X' ⟶ S} (i : X ⟶ X')
    [IsImmersion i] [QuasiCompact i] (w : i ≫ f' = f) (h : Nonempty (Compactification f')) :
    Nonempty (DenseCompactification f) :=
  h.map (Compactification.immersionClosure i w)

/-- If `X` is embedded by a quasi-compact immersion, for instance as a closed subscheme, in the
base change `X₀ ×_{S₀} S` of a compactifiable morphism `f₀ : X₀ ⟶ S₀`, then `X ⟶ S` has a dense
compactification. -/
theorem nonempty_denseCompactification_of_isImmersion_pullback {X₀ S₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ S₀} (g : S ⟶ S₀) (h : Nonempty (Compactification f₀)) (i : X ⟶ pullback f₀ g)
    [IsImmersion i] [QuasiCompact i] (w : i ≫ pullback.snd f₀ g = f) :
    Nonempty (DenseCompactification f) :=
  nonempty_denseCompactification_of_isImmersion i w (h.map (·.baseChange g))

end TauCeti
