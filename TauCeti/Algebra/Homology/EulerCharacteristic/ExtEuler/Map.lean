/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent

/-!
# Naturality of the Ext-Euler characteristic under exact functors

Let `F : C ⥤ D` be an exact `k`-linear functor between `k`-linear abelian categories. It induces
`k`-linear maps `Extⁿ(X, Y) → Extⁿ(F X, F Y)` (Mathlib's `CategoryTheory.Functor.mapExtAddHom`
and `CategoryTheory.Functor.mapExtLinearMap`). This file proves that the finiteness data behind
the Ext-Euler characteristic, and the characteristic itself, are carried along `F` whenever these
maps are bijective:

```text
χ(F X, F Y) = χ(X, Y).
```

The two finiteness conditions travel in opposite directions under the weaker one-sided
hypotheses: injectivity of the maps on `Ext` reflects `Ext`-finiteness and vanishing from `D` back
to `C`, while surjectivity carries them from `C` to `D`.

At the level of Grothendieck groups, if `F` carries the extension-closed properties `P` and `Q`
of `C` into extension-closed properties `P'` and `Q'` of `D`, it restricts to conflation-exact
functors between the full subcategories and so induces maps of exact `K₀`. When `F` is bijective
on the `Ext` groups of every pair in `P × Q`, these maps intertwine the two Ext-Euler pairings
(`TauCeti.extEulerPairing_map_map`).

Mathlib supplies the bijectivity hypothesis for a fully faithful exact functor out of a category
with enough projectives which preserves projective objects
(`CategoryTheory.Functor.mapExt_bijective_of_preservesProjectiveObjects`), and dually with enough
injectives (`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`). For the
forward functor of an additive equivalence it is `CategoryTheory.Equivalence.extAddEquiv`, whose
underlying map is `Ext.mapExactFunctor` by `CategoryTheory.Equivalence.extAddEquiv_apply`.

## Main results

* `TauCeti.IsEulerAdmissible.map` and `TauCeti.IsEulerAdmissible.of_map`: Euler-admissibility is
  carried along `F`, respectively reflected by it, under surjectivity, respectively injectivity,
  of the maps on `Ext`; `TauCeti.IsEulerAdmissibleOn.of_map` is the version for object properties.
* `TauCeti.extEuler_map`: `χ(F X, F Y) = χ(X, Y)` when `F` is bijective on `Ext`.
* `TauCeti.extEulerPairing_map_map`: the induced maps of exact `K₀` intertwine the Ext-Euler
  pairings.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4--2.7, for `Ext`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w w' v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {k : Type t} [Field k] [Linear k C] [Linear k D] [HasExt.{w} C] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [F.Linear k] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C}

/-! ### Transporting the finiteness conditions -/

/-- `Ext`-finiteness is reflected by an exact functor which is injective on `Ext`. -/
theorem IsExtFinite.of_map (h : IsExtFinite.{w'} k (F.obj X) (F.obj Y))
    (hF : ∀ n, Function.Injective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsExtFinite.{w} k X Y :=
  ⟨fun n ↦ haveI := h.finiteDimensional n
    FiniteDimensional.of_injective (F.mapExtLinearMap k X Y n) (hF n)⟩

/-- `Ext`-finiteness is carried along an exact functor which is surjective on `Ext`. -/
theorem IsExtFinite.map (h : IsExtFinite.{w} k X Y)
    (hF : ∀ n, Function.Surjective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsExtFinite.{w'} k (F.obj X) (F.obj Y) :=
  ⟨fun n ↦ haveI := h.finiteDimensional n
    Module.Finite.of_surjective (F.mapExtLinearMap k X Y n) (hF n)⟩

/-- A vanishing bound is reflected by an exact functor which is injective on `Ext` from that
degree on. -/
theorem IsExtBoundedBy.of_map {N : ℕ} (h : IsExtBoundedBy.{w'} (F.obj X) (F.obj Y) N)
    (hF : ∀ ⦃n⦄, N ≤ n → Function.Injective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsExtBoundedBy.{w} X Y N :=
  ⟨fun _ hn ↦ haveI := h.subsingleton hn
    (hF hn).subsingleton⟩

/-- A vanishing bound is carried along an exact functor which is surjective on `Ext` from that
degree on. -/
theorem IsExtBoundedBy.map {N : ℕ} (h : IsExtBoundedBy.{w} X Y N)
    (hF : ∀ ⦃n⦄, N ≤ n → Function.Surjective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsExtBoundedBy.{w'} (F.obj X) (F.obj Y) N :=
  ⟨fun _ hn ↦ haveI := h.subsingleton hn
    (hF hn).subsingleton⟩

/-- Eventual `Ext`-vanishing is reflected by an exact functor which is injective on `Ext`. -/
theorem IsExtBounded.of_map (h : IsExtBounded.{w'} (F.obj X) (F.obj Y))
    (hF : ∀ n, Function.Injective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsExtBounded.{w} X Y :=
  (h.exists_bound.choose_spec.of_map F fun n _ ↦ hF n).isExtBounded

/-- Eventual `Ext`-vanishing is carried along an exact functor which is surjective on `Ext`. -/
theorem IsExtBounded.map (h : IsExtBounded.{w} X Y)
    (hF : ∀ n, Function.Surjective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsExtBounded.{w'} (F.obj X) (F.obj Y) :=
  (h.exists_bound.choose_spec.map F fun n _ ↦ hF n).isExtBounded

/-- Euler-admissibility is reflected by an exact functor which is injective on `Ext`. -/
theorem IsEulerAdmissible.of_map (h : IsEulerAdmissible.{w'} k (F.obj X) (F.obj Y))
    (hF : ∀ n, Function.Injective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsEulerAdmissible.{w} k X Y :=
  ⟨h.isExtFinite.of_map F hF, h.isExtBounded.of_map F hF⟩

/-- Euler-admissibility is carried along an exact functor which is surjective on `Ext`. -/
theorem IsEulerAdmissible.map (h : IsEulerAdmissible.{w} k X Y)
    (hF : ∀ n, Function.Surjective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsEulerAdmissible.{w'} k (F.obj X) (F.obj Y) :=
  ⟨h.isExtFinite.map F hF, h.isExtBounded.map F hF⟩

/-- Euler-admissibility on a pair of object properties is reflected by an exact functor carrying
them into Euler-admissible properties and injective on the `Ext` groups between them. -/
theorem IsEulerAdmissibleOn.of_map {P Q : ObjectProperty C} {P' Q' : ObjectProperty D}
    (h : IsEulerAdmissibleOn.{w'} k P' Q') (hFP : ∀ ⦃X⦄, P X → P' (F.obj X))
    (hFQ : ∀ ⦃Y⦄, Q Y → Q' (F.obj Y))
    (hF : ∀ ⦃X Y⦄, P X → Q Y → ∀ n, Function.Injective (F.mapExtAddHom.{w, w'} X Y n)) :
    IsEulerAdmissibleOn.{w} k P Q :=
  ⟨fun _ _ hX hY ↦ (h.isEulerAdmissible (hFP hX) (hFQ hY)).of_map F (hF hX hY)⟩

/-! ### Naturality of the Ext-Euler characteristic -/

/-- **Naturality of the Ext-Euler characteristic**: an exact functor which is bijective on `Ext`
preserves it, `χ(F X, F Y) = χ(X, Y)`. -/
theorem extEuler_map (hF : ∀ n, Function.Bijective (F.mapExtAddHom.{w, w'} X Y n))
    (h : IsEulerAdmissible.{w} k X Y) (h' : IsEulerAdmissible.{w'} k (F.obj X) (F.obj Y)) :
    extEuler.{w'} k h' = extEuler.{w} k h :=
  extEuler_congr k
    (fun n ↦ LinearEquiv.ofBijective (F.mapExtLinearMap k X Y n) (hF n)) h h'

/-! ### Naturality of the Ext-Euler pairing -/

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]
  {P' Q' : ObjectProperty D} [LocallySmall.{w'} D]
  [ObjectProperty.EssentiallySmall.{w'} P'] [ObjectProperty.EssentiallySmall.{w'} Q']
  [P'.ContainsZero] [P'.IsClosedUnderBinaryProducts]
  [Q'.ContainsZero] [Q'.IsClosedUnderBinaryProducts]

/-- **Naturality of the Ext-Euler pairing.** Let `F` carry the extension-closed properties `P`
and `Q` of `C` into the extension-closed properties `P'` and `Q'` of `D`, and be bijective on the
`Ext` groups of every pair in `P × Q`. Then the maps of exact `K₀` induced by the restrictions of
`F` to the full subcategories intertwine the two Ext-Euler pairings.

The admissibility witness `h` on `C` can always be obtained from `h'` by
`TauCeti.IsEulerAdmissibleOn.of_map`; any witness may be supplied. -/
theorem extEulerPairing_map_map
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q)
    (hP' : (ExactStructure.abelian D).IsExtensionClosed P')
    (hQ' : (ExactStructure.abelian D).IsExtensionClosed Q')
    (h' : IsEulerAdmissibleOn.{w'} k P' Q')
    (hFP : ∀ ⦃X⦄, P X → P' (F.obj X)) (hFQ : ∀ ⦃Y⦄, Q Y → Q' (F.obj Y))
    (hF : ∀ ⦃X Y⦄, P X → Q Y → ∀ n, Function.Bijective (F.mapExtAddHom.{w, w'} X Y n))
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerPairing hP' hQ' h'
        (ExactK0.map (P'.lift (P.ι ⋙ F) fun X ↦ hFP X.property)
          ((ExactStructure.abelian C).isConflationExact_lift hP hP' F
            (ExactStructure.isConflationExact_abelian F) fun X ↦ hFP X.property) x)
        (ExactK0.map (Q'.lift (Q.ι ⋙ F) fun Y ↦ hFQ Y.property)
          ((ExactStructure.abelian C).isConflationExact_lift hQ hQ' F
            (ExactStructure.isConflationExact_abelian F) fun Y ↦ hFQ Y.property) y) =
      extEulerPairing hP hQ h x y := by
  let mapP := ExactK0.map (P'.lift (P.ι ⋙ F) fun X ↦ hFP X.property)
    ((ExactStructure.abelian C).isConflationExact_lift hP hP' F
      (ExactStructure.isConflationExact_abelian F) fun X ↦ hFP X.property)
  let mapQ := ExactK0.map (Q'.lift (Q.ι ⋙ F) fun Y ↦ hFQ Y.property)
    ((ExactStructure.abelian C).isConflationExact_lift hQ hQ' F
      (ExactStructure.isConflationExact_abelian F) fun Y ↦ hFQ Y.property)
  let b := (AddMonoidHom.compHom' mapQ).comp ((extEulerPairing hP' hQ' h').comp mapP)
  exact DFunLike.congr_fun (DFunLike.congr_fun
    (extEulerPairing_unique hP hQ h b fun X Y ↦ by
      simpa [b, mapP, mapQ] using extEuler_map F (hF X.property Y.property)
        (h.isEulerAdmissible X.property Y.property)
        (h'.isEulerAdmissible (hFP X.property) (hFQ Y.property))) x) y

end TauCeti
