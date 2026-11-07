/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import TauCeti.AlgebraicGeometry.BaseChangeSection

/-!
# The scheme of tuples of sections

Let `g : Z ⟶ S` be a morphism of schemes and `ι` a finite type. The `ι`-fold fibre power
`Z ×_S ⋯ ×_S Z` (`sectionTupleScheme g ι`) is the scheme of `ι`-tuples of sections of `g`: its
`T`-points over `S` are the families `x : ι → (T ⟶ Z)` of `T`-points of `Z` over `S`, that is,
the families of sections of `Z_T ⟶ T`. Over it lives the universal family of sections
(`universalSection`) of the base change of `Z`.

## Main definitions

* `TauCeti.AlgebraicGeometry.sectionTupleScheme g ι`: the scheme of `ι`-tuples of sections of
  `g`, the fibre power of `Z` over `S`.
* `TauCeti.AlgebraicGeometry.universalSection g ι i`: the universal `i`-th section over it.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {Z S : Scheme.{u}} (g : Z ⟶ S) (ι : Type) [Fintype ι]

/-- The **scheme of `ι`-tuples of sections** of `g : Z ⟶ S`: the `ι`-fold fibre power
`Z ×_S ⋯ ×_S Z`. Its `T`-points over `S` are the families of `T`-points of `Z` over `S`
(`WidePullback.lift`), that is, the families of sections of the base change `Z_T ⟶ T`. -/
noncomputable abbrev sectionTupleScheme : Scheme.{u} :=
  widePullback S (fun _ : ι ↦ Z) fun _ ↦ g

/-- The **universal `i`-th section** over the scheme of tuples of sections: the section of the
base change of `Z` to `sectionTupleScheme g ι` given by the `i`-th projection. -/
noncomputable def universalSection (i : ι) :
    sectionTupleScheme g ι ⟶ pullback (WidePullback.base fun _ : ι ↦ g) g :=
  graphSection (T := Over.mk (WidePullback.base _)) (Over.homMk (WidePullback.π _ i))

/-- The universal section is a section of the base change of `g`. -/
@[reassoc (attr := simp)]
theorem universalSection_fst (i : ι) :
    universalSection g ι i ≫ pullback.fst _ g = 𝟙 _ :=
  graphSection_fst _

/-- The universal `i`-th section followed by the projection to `Z` is the `i`-th projection. -/
@[reassoc (attr := simp)]
theorem universalSection_snd (i : ι) :
    universalSection g ι i ≫ pullback.snd _ g = WidePullback.π _ i :=
  graphSection_snd _

end TauCeti.AlgebraicGeometry
