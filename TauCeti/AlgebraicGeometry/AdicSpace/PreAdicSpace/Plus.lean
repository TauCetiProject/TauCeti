/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.PresentationLimit
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Plus.Basic

/-!
# The integral sections `𝒪_X⁺` of a pre-adic space

Every point `x` of a pre-adic space `X` carries the stalk valuation `v_x` on `𝒪_{X,x}`. Following
Wedhorn, the *integral sections* over an open `U ⊆ X` are

```text
𝒪_X⁺(U) = { f ∈ 𝒪_X(U) : v_x(f_x) ≤ 1 for every x ∈ U },
```

where `f_x` is the germ of `f` at `x`. This file defines `𝒪_X⁺(U)` as a subring of `𝒪_X(U)` and
shows that it is functorial in the category `𝒱^pre` of pre-adic spaces: restriction maps carry
`𝒪_X⁺(U)` into `𝒪_X⁺(V)` for `V ⊆ U`, and for a morphism `f : X ⟶ Y` the map on sections
`𝒪_Y(V) → 𝒪_X(f⁻¹V)` carries `𝒪_Y⁺(V)` into `𝒪_X⁺(f⁻¹V)`. Over an open `V` contained in the image
of `f` the preimage of `𝒪_X⁺(f⁻¹V)` is exactly `𝒪_Y⁺(V)`; this applies to every isomorphism and
to every open immersion over its image. So the plus subrings are determined by the stalk
valuations, and a morphism of `𝒱^pre` which is an isomorphism, or an open immersion, identifies
them.

For the pre-adic space `Spa(A, A⁺)` of a Huber pair, `𝒪_X⁺(U)` is the plus subring
`TauCeti.ValuationSpectrum.presentationLimitPlusSubring`, which on a rational open `R(T/s)` is the
plus ring `A_U⁺` of the coordinate ring `A⟨T/s⟩` (Wedhorn, Proposition 8.16).

## Main definitions

* `TauCeti.PreAdicSpace.plusSubring`: the subring `𝒪_X⁺(U)` of `𝒪_X(U)`.

## Main results

* `TauCeti.PreAdicSpace.mem_plusSubring_iff`: a section lies in `𝒪_X⁺(U)` exactly when its germ at
  every point of `U` is sub-unit for the stalk valuation.
* `TauCeti.PreAdicSpace.plusSubring_le_comap`: restriction preserves integral sections.
* `TauCeti.PreAdicSpace.Hom.plusSubring_le_comap`: morphisms of pre-adic spaces preserve integral
  sections.
* `TauCeti.PreAdicSpace.Hom.comap_plusSubring_of_subset_range`: over an open in the image of a
  morphism, a section is integral exactly when its pullback is; the isomorphism case is
  `TauCeti.PreAdicSpace.Hom.comap_plusSubring_of_isIso`.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace_plusSubring`: on `Spa(A, A⁺)` the
  integral sections are `presentationLimitPlusSubring`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.16.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti

universe u

namespace PreAdicSpace

variable (X : PreAdicSpace.{u})

/-- **The integral sections `𝒪_X⁺(U)`** of a pre-adic space over an open `U`: the sections whose
germ at every point `x ∈ U` is sub-unit for the stalk valuation `v_x`. It is the intersection over
`x ∈ U` of the preimages, under the germ maps, of the valuation rings of the stalk valuations. -/
noncomputable def plusSubring (U : Opens X) :
    Subring (X.toRingPresheafedSpace.presheaf.obj (op U)) :=
  ⨅ x : U, (X.stalkValuation x.1).valuation.integer.comap
    (X.toRingPresheafedSpace.presheaf.germ U x.1 x.2).hom

variable {X}

/-- **Membership in `𝒪_X⁺(U)`**: a section over `U` is integral exactly when its germ at every
point `x ∈ U` is sub-unit for the stalk valuation at `x`. -/
@[simp]
theorem mem_plusSubring_iff {U : Opens X} {f : X.toRingPresheafedSpace.presheaf.obj (op U)} :
    f ∈ X.plusSubring U ↔ ∀ (x : X) (hx : x ∈ U),
      (X.stalkValuation x).toValuativeRel.vle
        (X.toRingPresheafedSpace.presheaf.germ U x hx f) 1 := by
  rw [plusSubring, Subring.mem_iInf]
  refine Subtype.forall.trans (forall_congr' fun x ↦ forall_congr' fun hx ↦ ?_)
  rw [Subring.mem_comap, Valuation.mem_integer_iff, ← map_one (X.stalkValuation x).valuation,
    ValuationSpectrum.valuation_le_iff]

/-- **Restriction preserves integral sections**: for opens `V ⊆ U`, the restriction map
`𝒪_X(U) → 𝒪_X(V)` carries `𝒪_X⁺(U)` into `𝒪_X⁺(V)`. -/
theorem plusSubring_le_comap {U V : Opens X} (i : V ⟶ U) :
    X.plusSubring U ≤ (X.plusSubring V).comap (X.toRingPresheafedSpace.presheaf.map i.op).hom := by
  intro f hf
  refine Subring.mem_comap.mpr (mem_plusSubring_iff.mpr fun x hx ↦ ?_)
  -- `rw` cannot rewrite the germ here: the points of `X` and of its presheafed space of rings
  -- are identified only after unfolding `Functor.mapPresheaf`, so the rewritten goal is not
  -- type correct at the transparency `rw` checks it with; the equation is transported along
  -- `congrArg` instead
  exact (congrArg (fun g ↦ (X.stalkValuation x).toValuativeRel.vle g 1)
    (TopCat.Presheaf.germ_res_apply X.toRingPresheafedSpace.presheaf i x hx f)).mpr
      (mem_plusSubring_iff.mp hf x (i.le hx))

namespace Hom

variable {Y : PreAdicSpace.{u}} (f : X ⟶ Y)

/-- The germ at `x` of the pullback of a section `s` of `𝒪_Y` over `V` is the image under the stalk
map of the germ of `s` at `f x`. -/
private theorem germ_c_app_apply (V : Opens Y) (x : X) (hx : f.base x ∈ V)
    (s : Y.toRingPresheafedSpace.presheaf.obj (op V)) :
    X.toRingPresheafedSpace.presheaf.germ ((Opens.map f.base).obj V) x hx
        ((toRingPresheafedSpaceHom f.toHom).c.app (op V) s) =
      f.stalkMap x (Y.toRingPresheafedSpace.presheaf.germ V (f.base x) hx s) := by
  rw [Hom.stalkMap_def]
  exact (congrArg (fun φ ↦ φ.hom s)
    (PresheafedSpace.stalkMap_germ (toRingPresheafedSpaceHom f.toHom) V x hx)).symm

/-- At a point `x` over `V`, the pullback of a section `s` of `𝒪_Y` over `V` is sub-unit at `x`
exactly when `s` is sub-unit at `f x`: the stalk valuation at `f x` is the pullback of the one at
`x` along the stalk map. -/
private theorem vle_germ_c_app_iff (V : Opens Y) (x : X) (hx : f.base x ∈ V)
    (s : Y.toRingPresheafedSpace.presheaf.obj (op V)) :
    (X.stalkValuation x).toValuativeRel.vle
        (X.toRingPresheafedSpace.presheaf.germ ((Opens.map f.base).obj V) x hx
          ((toRingPresheafedSpaceHom f.toHom).c.app (op V) s)) 1 ↔
      (Y.stalkValuation (f.base x)).toValuativeRel.vle
        (Y.toRingPresheafedSpace.presheaf.germ V (f.base x) hx s) 1 := by
  rw [germ_c_app_apply, f.stalkValuation_eq_comap x, ValuationSpectrum.comap_vle, map_one]

/-- **Morphisms preserve integral sections**: for a morphism `f : X ⟶ Y` of pre-adic spaces and an
open `V ⊆ Y`, the map on sections `𝒪_Y(V) → 𝒪_X(f⁻¹V)` carries `𝒪_Y⁺(V)` into `𝒪_X⁺(f⁻¹V)`. -/
theorem plusSubring_le_comap (V : Opens Y) :
    Y.plusSubring V ≤ (X.plusSubring ((Opens.map f.base).obj V)).comap
      ((toRingPresheafedSpaceHom f.toHom).c.app (op V)).hom := by
  intro s hs
  exact Subring.mem_comap.mpr (mem_plusSubring_iff.mpr fun x hx ↦
    (f.vle_germ_c_app_iff V x hx s).mpr (mem_plusSubring_iff.mp hs (f.base x) hx))

/-- **Over the image of a morphism, integrality is detected after pullback**: if the open `V ⊆ Y`
lies in the image of `f : X ⟶ Y`, a section of `𝒪_Y` over `V` is integral exactly when its pullback
to `f⁻¹V` is. This applies to an isomorphism, and to an open immersion over an open of its
image. -/
theorem comap_plusSubring_of_subset_range {V : Opens Y} (hV : (V : Set Y) ⊆ Set.range f.base) :
    (X.plusSubring ((Opens.map f.base).obj V)).comap
        ((toRingPresheafedSpaceHom f.toHom).c.app (op V)).hom = Y.plusSubring V := by
  refine le_antisymm (fun s hs ↦ mem_plusSubring_iff.mpr fun y hy ↦ ?_) (f.plusSubring_le_comap V)
  obtain ⟨x, rfl⟩ := hV hy
  exact (f.vle_germ_c_app_iff V x hy s).mp (mem_plusSubring_iff.mp (Subring.mem_comap.mp hs) x hy)

/-- **Isomorphisms identify integral sections**: for an isomorphism `f : X ⟶ Y` of pre-adic spaces
and every open `V ⊆ Y`, a section of `𝒪_Y` over `V` is integral exactly when its pullback to
`f⁻¹V` is. -/
theorem comap_plusSubring_of_isIso [IsIso f] (V : Opens Y) :
    (X.plusSubring ((Opens.map f.base).obj V)).comap
        ((toRingPresheafedSpaceHom f.toHom).c.app (op V)).hom = Y.plusSubring V :=
  f.comap_plusSubring_of_subset_range fun y _ ↦
    (TopCat.homeoOfIso (forgetToTop.mapIso (asIso f))).surjective y

end Hom

end PreAdicSpace

namespace ValuationSpectrum

/-- **The integral sections of `Spa(A, A⁺)`** are the plus subrings `presentationLimitPlusSubring`
of the presentation-limit presheaf. On a rational open `R(T/s)` these are the plus ring `A_U⁺` of
`A⟨T/s⟩`, by `map_completedPlusSubring_eq_presentationLimitPlusSubring`. -/
theorem presentationLimitPreAdicSpace_plusSubring {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : Huber.PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → Huber.IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)
    (V : Opens ↥(spa Aplus)) :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).plusSubring V =
      presentationLimitPlusSubring hAplus hP V := by
  -- the stalks and germ maps of the two presheaves agree, and so do the stalk valuations
  refine Subring.ext fun f ↦ PreAdicSpace.mem_plusSubring_iff.trans
    (Iff.trans ?_ (mem_presentationLimitPlusSubring_iff hAplus hP).symm)
  exact forall_congr' fun x ↦ forall_congr' fun hx ↦ Iff.of_eq
    (congrArg (fun w ↦ w.toValuativeRel.vle
      ((presentationLimitPresheafInCommRingCat P Aplus).germ V x hx f) 1)
        (presentationLimitPreAdicSpace_stalkValuation P Aplus hAplus hP x))

end ValuationSpectrum

end TauCeti

end
