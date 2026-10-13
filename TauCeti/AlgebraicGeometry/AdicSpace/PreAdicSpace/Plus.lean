/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom

import Mathlib.RingTheory.Valuation.Integers

/-!
# The integral sections `𝒪_X⁺` of a pre-adic space

Every point `x` of a pre-adic space `X` carries the stalk valuation `v_x` on `𝒪_{X,x}`. Following
Wedhorn, the *integral sections* over an open `U ⊆ X` are

```text
𝒪_X⁺(U) = { f ∈ 𝒪_X(U) : v_x(f_x) ≤ 1 for every x ∈ U },
```

where `f_x` is the germ of `f` at `x`. This file defines `𝒪_X⁺(U)` as a subring of `𝒪_X(U)` and
shows that it is functorial in the category `𝒱^pre` of pre-adic spaces: restriction maps carry
`𝒪_X⁺(U)` into `𝒪_X⁺(V)` for `V ⊆ U`, which packages `𝒪_X⁺` as a presheaf of commutative rings
with a monomorphism `𝒪_X⁺ ⟶ 𝒪_X`, and for a morphism `f : X ⟶ Y` the map on sections
`𝒪_Y(V) → 𝒪_X(f⁻¹V)` carries `𝒪_Y⁺(V)` into `𝒪_X⁺(f⁻¹V)`. Over an open `V` contained in the image
of `f` the preimage of `𝒪_X⁺(f⁻¹V)` is exactly `𝒪_Y⁺(V)`; this applies to every isomorphism and
to every open immersion over its image. So the plus subrings are determined by the stalk
valuations, and a morphism of `𝒱^pre` which is an isomorphism, or an open immersion, identifies
them.

For the pre-adic space `Spa(A, A⁺)` of a Huber pair, `𝒪_X⁺(U)` is the plus subring
`TauCeti.ValuationSpectrum.presentationLimitPlusSubring`
(`Spa/StructurePresheaf/Plus/PreAdicSpace.lean`).

## Main definitions

* `TauCeti.PreAdicSpace.plusSubring`: the subring `𝒪_X⁺(U)` of `𝒪_X(U)`.
* `TauCeti.PreAdicSpace.plusPresheaf`: `𝒪_X⁺` as a presheaf of commutative rings on `X`.
* `TauCeti.PreAdicSpace.plusPresheafι`: the inclusion `𝒪_X⁺ ⟶ 𝒪_X`, a monomorphism.

## Main results

* `TauCeti.PreAdicSpace.mem_plusSubring_iff`: a section lies in `𝒪_X⁺(U)` exactly when its germ at
  every point of `U` is sub-unit for the stalk valuation.
* `TauCeti.PreAdicSpace.plusSubring_le_comap`: restriction preserves integral sections.
* `TauCeti.PreAdicSpace.Hom.plusSubring_le_comap`: morphisms of pre-adic spaces preserve integral
  sections.
* `TauCeti.PreAdicSpace.Hom.comap_plusSubring_of_subset_range`: over an open in the image of a
  morphism, a section is integral exactly when its pullback is.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
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

/-! ### The presheaf of integral sections -/

variable (X) in
/-- **The presheaf of integral sections `𝒪_X⁺`** of a pre-adic space: the presheaf of commutative
rings whose sections over `U` are the subring `𝒪_X⁺(U)` of `𝒪_X(U)`, with the restriction maps of
`𝒪_X`. -/
noncomputable def plusPresheaf : X.toTopCat.Presheaf CommRingCat.{u} where
  obj U := CommRingCat.of (X.plusSubring U.unop)
  map i := CommRingCat.ofHom
    ((X.toRingPresheafedSpace.presheaf.map i.unop.op).hom.restrict _ _
      fun _ hf ↦ plusSubring_le_comap i.unop hf)
  -- On underlying elements the restricted maps are the restriction maps of `𝒪_X`
  -- (`RingHom.coe_restrict_apply` is `rfl`), so both laws are those of `𝒪_X`.
  map_id U := CommRingCat.hom_ext <| RingHom.ext fun f ↦ Subtype.ext <|
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (X.toRingPresheafedSpace.presheaf.map_id U)) f.1
  map_comp i j := CommRingCat.hom_ext <| RingHom.ext fun f ↦ Subtype.ext <|
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (X.toRingPresheafedSpace.presheaf.map_comp i j)) f.1

/-- The sections of `𝒪_X⁺` over `U` are the subring `𝒪_X⁺(U)`. -/
@[simp]
theorem plusPresheaf_obj (U : (Opens X)ᵒᵖ) :
    X.plusPresheaf.obj U = CommRingCat.of (X.plusSubring U.unop) := by
  rfl

/-- The restriction maps of `𝒪_X⁺` are those of `𝒪_X`, restricted to the integral sections. The
equality transports account for the evaluation theorem `plusPresheaf_obj`. -/
@[simp]
theorem plusPresheaf_map {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.plusPresheaf.map i ≫ eqToHom (plusPresheaf_obj V) =
      eqToHom (plusPresheaf_obj U) ≫ CommRingCat.ofHom (S := X.plusSubring V.unop)
        ((X.toRingPresheafedSpace.presheaf.map i.unop.op).hom.restrict _ _
          fun _ hf ↦ plusSubring_le_comap i.unop hf) := by
  rfl

variable (X) in
/-- **The inclusion `𝒪_X⁺ ⟶ 𝒪_X`** of the integral sections into the sections. -/
noncomputable def plusPresheafι : X.plusPresheaf ⟶ X.toRingPresheafedSpace.presheaf where
  app U := CommRingCat.ofHom (X.plusSubring U.unop).subtype
  naturality _ _ _ := CommRingCat.hom_ext <| RingHom.ext fun _ ↦ rfl

/-- The inclusion `𝒪_X⁺ ⟶ 𝒪_X` is, over each open `U`, the inclusion of the subring `𝒪_X⁺(U)`.
The equality transport accounts for the evaluation theorem `plusPresheaf_obj`. -/
@[simp]
theorem plusPresheafι_app (U : (Opens X)ᵒᵖ) :
    X.plusPresheafι.app U =
      eqToHom (plusPresheaf_obj U) ≫ CommRingCat.ofHom (X.plusSubring U.unop).subtype := by
  rfl

/-- The inclusion `𝒪_X⁺ ⟶ 𝒪_X` is a monomorphism: `𝒪_X⁺` is a sub-presheaf of `𝒪_X`. -/
instance : Mono X.plusPresheafι :=
  haveI : ∀ U, Mono (X.plusPresheafι.app U) := fun U ↦
    ConcreteCategory.mono_of_injective _ (Subring.subtype_injective (X.plusSubring U.unop))
  NatTrans.mono_of_mono_app _

namespace Hom

variable {Y : PreAdicSpace.{u}} (f : X ⟶ Y)

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
  rw [f.stalkValuation_eq_comap x, ValuationSpectrum.comap_vle, map_one, Hom.stalkMap_def]
  convert Iff.rfl using 2
  exact PresheafedSpace.stalkMap_germ_apply (toRingPresheafedSpaceHom f.toHom) V x hx s

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

end Hom

end PreAdicSpace

end TauCeti

end
