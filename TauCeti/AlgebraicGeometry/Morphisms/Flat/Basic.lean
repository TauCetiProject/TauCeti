/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.FunctionField
public import TauCeti.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.Flat.Tower

/-!
# Flat morphisms: restrictions, stalkwise descent and generic points

Flatness on an open subset of the target is equivalent to flatness of the original stalk
maps at all points lying over that open subset. On affine opens, flatness of a stalk map is
flatness over the base of the localization at the corresponding prime.

Flatness of stalk maps descends along morphisms with flat stalk maps, since a flat local
homomorphism of local rings is faithfully flat. Hence if `g` is flat and surjective and `g ≫ f` is
flat, then `f` is flat.

A flat morphism of schemes is generalizing: every generization of the image of a point lifts to
a generization of that point. Between irreducible schemes this forces the generic point of the
source to map to the generic point of the target, since the generic point of the target
generizes the image of the generic point of the source, and the generic point of the source has no
proper generization. This is the dominance of a flat morphism between irreducible schemes, for
instance of a flat model of a curve over a discrete valuation ring, whose generic point lies in
the generic fibre.

## Main results

* `AlgebraicGeometry.Scheme.Hom.flat_restrict_iff`: the stalk criterion for flatness of a
  restriction.
* `AlgebraicGeometry.flat_stalkMap_iff`: on affine opens `x ∈ V ⊆ f⁻¹ U`, the stalk map at `x` is
  flat iff the localization of `Γ(X, V)` at the prime of `x` is flat over `Γ(Y, U)`.
* `AlgebraicGeometry.flat_stalkMap_specMap_iff`: the stalk map of `Spec S ⟶ Spec R` at `q` is flat
  iff `S_q` is flat over `R`.
* `AlgebraicGeometry.Scheme.Hom.flat_stalkMap_of_comp`: flatness of stalk maps descends along
  morphisms with flat stalk maps.
* `AlgebraicGeometry.Flat.of_comp_surjective`: if `g` is flat and surjective and `g ≫ f` is flat,
  then `f` is flat.
* `AlgebraicGeometry.Scheme.Hom.genericPoint_eq_of_flat`: a flat morphism between irreducible
  schemes sends the generic point to the generic point.

## References

* [The Stacks Project, Lemma 29.25.9](https://stacks.math.columbia.edu/tag/01U1), flat
  morphisms are generalizing.
-/

public section

open AlgebraicGeometry

namespace TauCeti

universe u

/-- A flat morphism between irreducible schemes sends the generic point to the generic point. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.genericPoint_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IrreducibleSpace X] [IrreducibleSpace Y] : f (genericPoint X) = genericPoint Y := by
  -- Flat morphisms are generalizing, so the generic point of `Y` lifts to a generization of the
  -- generic point of `X`, which can only be that generic point itself.
  obtain ⟨η, hη, hfη⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  rw [← hfη, (hη.antisymm (genericPoint_specializes η)).eq]

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

/-- Flatness of a restriction is equivalent to flatness of the original stalk maps
at all points lying above the chosen open subset of the target. -/
theorem flat_restrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Flat (f ∣_ U) ↔ ∀ x : X, f x ∈ U → (f.stalkMap x).hom.Flat := by
  rw [Flat.iff_flat_stalkMap]
  constructor
  · intro h x hx
    exact (CommRingCat.flat.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U ⟨x, hx⟩)).mp (h ⟨x, hx⟩)
  · intro h x
    exact (CommRingCat.flat.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U x)).mpr (h x.1 x.2)

/-- Flatness of stalk maps descends along flat morphisms: if `g` has flat stalk map at `x'` and
`g ≫ f` has flat stalk map at `x'`, then `f` has flat stalk map at `g x'`. -/
theorem flat_stalkMap_of_comp {X X' Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (x' : X')
    (hg : (g.stalkMap x').hom.Flat) (h : ((g ≫ f).stalkMap x').hom.Flat) :
    (f.stalkMap (g x')).hom.Flat := by
  have h' : ((g.stalkMap x').hom.comp (f.stalkMap (g x')).hom).Flat := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    -- The stalks at `(g ≫ f) x'` and `f (g x')` agree definitionally, but not reducibly.
    exact h
  algebraize [(f.stalkMap (g x')).hom, (g.stalkMap x').hom,
    (g.stalkMap x').hom.comp (f.stalkMap (g x')).hom]
  -- The algebra structure is that of the stalk map, which is a local homomorphism.
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g x')) (X'.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x').hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (g x')) (X'.presheaf.stalk x') :=
    .of_flat_of_isLocalHom
  exact Module.Flat.of_faithfullyFlat_of_flat _ _ (X'.presheaf.stalk x')

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y : Scheme.{u}}

/-- On affine opens `x ∈ V ⊆ f⁻¹ U`, the stalk map of `f` at `x` is flat iff the localization of
`Γ(X, V)` at the prime of `x` is flat over `Γ(Y, U)`. -/
theorem flat_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.Flat ↔
      Module.Flat Γ(Y, U) (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  algebraize [(f.appLE U V hVU).hom]
  rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)]
  exact Localization.flat_localRingHom_iff _ _
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm

/-- The stalk map of `Spec S ⟶ Spec R` at `q` is flat iff `S_q` is flat over `R`. -/
theorem flat_stalkMap_specMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q).hom.Flat ↔
      Module.Flat R (Localization.AtPrime q.asIdeal) := by
  have h := RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)
  simp only [CommRingCat.hom_ofHom] at h
  exact h.trans (Localization.flat_localRingHom_iff _ _ _)

/-- **Flatness descends along flat surjections.** If `g` is flat and surjective and `g ≫ f` is
flat, then `f` is flat. -/
theorem Flat.of_comp_surjective {X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) [Flat g]
    [Surjective g] [Flat (g ≫ f)] : Flat f :=
  Flat.of_stalkMap f fun x ↦ by
    obtain ⟨x', rfl⟩ := g.surjective x
    exact g.flat_stalkMap_of_comp f x' (Flat.stalkMap g x') (Flat.stalkMap (g ≫ f) x')

end AlgebraicGeometry
