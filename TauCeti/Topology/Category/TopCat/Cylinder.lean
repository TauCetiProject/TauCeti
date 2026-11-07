/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Homotopies out of a pushout in `TopCat`

Homotopies on the two sides of a pushout square in `TopCat` which agree on its source glue to a
homotopy on its corner `B'`: since the unit interval `I` is locally compact, maps out of `I × B'`
are maps from `B'` to the path space `C(I, Q)`, and those are glued along the square. So
homotopies `L` on `I × B` and `C` on `I × A'` which agree on `I × A` glue to a homotopy
`TauCeti.TopCat.cylinderDesc` on `I × B'`, restricting to `L` and `C` along the two legs.

This is how homotopies of adjunction spaces, such as spaces obtained by attaching cells, are
built from homotopies on the pieces.

## Main definitions

* `TauCeti.TopCat.cylinderDesc`: the homotopy on the cylinder of the corner of a pushout square
  glued from homotopies on the cylinders of the two sides.

## Main results

* `TauCeti.TopCat.cylinderDesc_inl`, `TauCeti.TopCat.cylinderDesc_inr`: it restricts to the given
  homotopies along the two legs.
* `TauCeti.TopCat.cylinderDesc_apply_eq`: at each time, it is the only function on the corner
  restricting to the given homotopies at that time.
-/

public section

noncomputable section

open CategoryTheory Limits ContinuousMap unitInterval

universe u

namespace TauCeti.TopCat

variable {A A' B B' : TopCat.{u}} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
  {Q : Type u} [TopologicalSpace Q]

/-- The map from the corner of a pushout square to the path space glued from the curried
homotopies `L` and `C`. -/
private def curryDesc (sq : IsPushout g f f' g') (L : C(I × B, Q)) (C : C(I × A', Q))
    (hLC : ∀ t x, L (t, g.hom x) = C (t, f.hom x)) : B' ⟶ _root_.TopCat.of C(I, Q) :=
  sq.desc (_root_.TopCat.ofHom (L.comp prodSwap).curry)
    (_root_.TopCat.ofHom (C.comp prodSwap).curry) (by
      ext x t
      exact hLC t x)

/-- Homotopies `L` on `I × B` and `C` on `I × A'` which agree on `I × A` glue to a homotopy on
the cylinder `I × B'` of the corner of a pushout square in `TopCat`. Since `I` is locally
compact, this is the uncurried form of the map from `B'` to the path space `C(I, Q)` glued from
the curried homotopies. -/
def cylinderDesc (sq : IsPushout g f f' g') (L : C(I × B, Q)) (C : C(I × A', Q))
    (hLC : ∀ t x, L (t, g.hom x) = C (t, f.hom x)) : C(I × B', Q) :=
  ⟨fun p ↦ curryDesc sq L C hLC p.2 p.1,
    continuous_eval.comp
      (((curryDesc sq L C hLC).hom.continuous.comp continuous_snd).prodMk continuous_fst)⟩

/-- The glued homotopy restricts to `L` along `f'`. -/
@[simp]
theorem cylinderDesc_inl (sq : IsPushout g f f' g') (L : C(I × B, Q)) (C : C(I × A', Q))
    (hLC : ∀ t x, L (t, g.hom x) = C (t, f.hom x)) (t : I) (y : B) :
    cylinderDesc sq L C hLC (t, f'.hom y) = L (t, y) := by
  have h : f' ≫ curryDesc sq L C hLC = _root_.TopCat.ofHom (L.comp prodSwap).curry :=
    sq.inl_desc _ _ _
  simpa [cylinderDesc] using congrArg (fun φ : B ⟶ _root_.TopCat.of C(I, Q) ↦ φ y t) h

/-- The glued homotopy restricts to `C` along `g'`. -/
@[simp]
theorem cylinderDesc_inr (sq : IsPushout g f f' g') (L : C(I × B, Q)) (C : C(I × A', Q))
    (hLC : ∀ t x, L (t, g.hom x) = C (t, f.hom x)) (t : I) (y : A') :
    cylinderDesc sq L C hLC (t, g'.hom y) = C (t, y) := by
  have h : g' ≫ curryDesc sq L C hLC = _root_.TopCat.ofHom (C.comp prodSwap).curry :=
    sq.inr_desc _ _ _
  simpa [cylinderDesc] using congrArg (fun φ : A' ⟶ _root_.TopCat.of C(I, Q) ↦ φ y t) h

/-- At each time `t`, the glued homotopy is any function on the corner which agrees with `L` and
`C` at time `t` along the two legs. -/
theorem cylinderDesc_apply_eq (sq : IsPushout g f f' g') (L : C(I × B, Q)) (C : C(I × A', Q))
    (hLC : ∀ t x, L (t, g.hom x) = C (t, f.hom x)) {t : I} {φ : B' → Q}
    (hφl : ∀ y, φ (f'.hom y) = L (t, y)) (hφr : ∀ y, φ (g'.hom y) = C (t, y)) (p : B') :
    cylinderDesc sq L C hLC (t, p) = φ p := by
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := Types.eq_or_eq_of_isPushout ((forget _).map_isPushout sq) p
  · exact (cylinderDesc_inl sq L C hLC t y).trans (hφl y).symm
  · exact (cylinderDesc_inr sq L C hLC t y).trans (hφr y).symm

end TauCeti.TopCat
