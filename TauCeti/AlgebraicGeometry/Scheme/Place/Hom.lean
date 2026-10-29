/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Scheme.Place.Basic

/-!
# Dominant morphisms and the places of points

Let `f : X ⟶ Y` be a dominant morphism from an integral scheme over a field `k` to an irreducible
scheme, and let `x` be a point of `X` whose local ring is a discrete valuation ring, with place
`X.toPlace x` of the function field `k(X)`. A rational function on `Y` that is regular at `f x`
pulls back to a rational function on `X` that is regular at `x`: it is the germ of a section over
an open neighbourhood `U` of `f x`, and its pullback is the germ of the pulled-back section over
`f⁻¹ U`, which contains `x`. So the pullback of rational functions `f^* : k(Y) → k(X)` carries
the local ring of `Y` at `f x` into the valuation ring of the place of `x`.

When `k(X)` is algebraic over `f^* k(Y)`, this is what identifies the place of `f x` with the
restriction of the place of `x` to `k(Y)`. It also shows that `f x` is not the generic point of
`Y` as soon as some rational function on `Y` pulls back to one with a pole at `x`: at the generic
point every rational function is regular.

## Main results

* `AlgebraicGeometry.Scheme.Hom.functionFieldMap_germToFunctionField_mem_toPlace_integers`: the
  pullback of the germ of a section over an open neighbourhood of `f x` is regular at `x`.
* `AlgebraicGeometry.Scheme.Hom.functionFieldMap_algebraMap_mem_toPlace_integers`: the pullback of
  a rational function regular at `f x` is regular at `x`.
* `AlgebraicGeometry.Scheme.Hom.ne_genericPoint_of_functionFieldMap_notMem_toPlace_integers`: if
  some rational function pulls back to one with a pole at `x`, then `f x` is not the generic
  point.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IrreducibleSpace Y]
  [X.Over (Spec (.of k))]

/-- **The pullback of a section regular near `f x` is regular at `x`**: for a dominant morphism
`f : X ⟶ Y` from an integral scheme to an irreducible one, the pullback of the germ of a section
of `𝒪_Y` over an open `U` containing `f x` lies in the valuation ring of the place of `x`. -/
theorem functionFieldMap_germToFunctionField_mem_toPlace_integers (f : X ⟶ Y) [IsDominant f]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] {U : Y.Opens} [Nonempty U]
    (hx : f x ∈ U) (s : Γ(Y, U)) :
    f.functionFieldMap (Y.germToFunctionField U s) ∈ (X.toPlace (k := k) x).integers := by
  have hpull := congr($(f.germToFunctionField_functionFieldMap U) s)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hpull
  rw [hpull, ← X.algebraMap_germ_eq_germToFunctionField (show x ∈ f ⁻¹ᵁ U from hx)]
  exact X.algebraMap_stalk_mem_toPlace_integers x _

/-- **The pullback of a rational function regular at `f x` is regular at `x`**: for a dominant
morphism `f : X ⟶ Y` from an integral scheme to an irreducible one, the pullback of rational
functions carries the local ring of `Y` at `f x` into the valuation ring of the place of `x`. -/
theorem functionFieldMap_algebraMap_mem_toPlace_integers (f : X ⟶ Y) [IsDominant f] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (a : Y.presheaf.stalk (f x)) :
    f.functionFieldMap (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) ∈
      (X.toPlace (k := k) x).integers := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf a
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact functionFieldMap_germToFunctionField_mem_toPlace_integers f x hU s

/-- **A point where some pulled-back rational function has a pole does not map to the generic
point**: if `f^* z` is not regular at `x` for some rational function `z` on `Y`, then `f x` is not
the generic point of `Y`, at which every rational function is regular. -/
theorem ne_genericPoint_of_functionFieldMap_notMem_toPlace_integers (f : X ⟶ Y) [IsDominant f]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] {z : Y.functionField}
    (hz : f.functionFieldMap z ∉ (X.toPlace (k := k) x).integers) : f x ≠ genericPoint Y := by
  intro hfx
  -- The function field is the stalk at the generic point, so `z` is the germ there of a section.
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf z
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  exact hz (functionFieldMap_germToFunctionField_mem_toPlace_integers f x (hfx ▸ hU) s)

end AlgebraicGeometry.Scheme.Hom
