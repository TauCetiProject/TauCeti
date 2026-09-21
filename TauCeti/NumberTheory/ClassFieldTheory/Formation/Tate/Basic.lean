/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality

/-!
# Range comparisons for finite-layer Tate cohomology

For a restriction of finite normal layers `K/E` inside `K/F`, the Galois group of `K/E` is
identified with the image of its inclusion into the Galois group of `K/F`. This file transports
Tate cohomology of the smaller layer along that identification, both with formation coefficients
(`LayerRestriction.tateRangeIso`) and with trivial integral coefficients
(`LayerRestriction.trivialTateRangeIso`). These comparisons are shared by Tate restriction and
Tate corestriction between finite layers.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction.tateRangeIso`: Tate cohomology of the smaller layer
  as Tate cohomology of the image subgroup.
* `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateRangeIso`: the same comparison with
  trivial integral coefficients.

## Main results

* `TauCeti.ClassFieldTheory.LayerRestriction.tateRangeIso_inv_H0π`: in degree zero, the inverse
  comparison sends the class of an invariant element to the class of the same element.
-/

public noncomputable section

open CategoryTheory Rep Representation

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

/-- The range of the inclusion between finite layer Galois groups is finite. -/
noncomputable local instance instFintypeRange (T : LayerRestriction small big) :
    Fintype T.galHom.range :=
  Fintype.ofFinite _

/-- The identification of coefficient modules intertwines the Galois action of the smaller layer
with the action of the image of its Galois group in the larger one. This is the compatible pair
along which `tateRangeIso` transports Tate cohomology. -/
theorem isIntertwiningMap_repIso_range (T : LayerRestriction small big) (F : Formation G) :
    (small.rep F).ρ.IsIntertwiningMap
      ((Rep.res T.galHom.range.subtype (big.rep F)).ρ.comp
        (MonoidHom.ofInjective T.galHom_injective : small.Gal ≃* T.galHom.range))
      (Representation.equivOfIso (T.repIso F)).toLinearEquiv := by
  refine ⟨fun g x ↦ ?_⟩
  exact Rep.hom_comm_apply (T.repIso F).hom g x

/-- Tate cohomology of the smaller layer, identified with Tate cohomology of the image of its
Galois group in the larger one. The coefficient identification is `repIso`. -/
def tateRangeIso (T : LayerRestriction small big) (F : Formation G) (r : ℤ) :
    small.TateH F r ≅
      tateCohomology (Rep.res T.galHom.range.subtype (big.rep F)) r :=
  TauCeti.TateCohomology.mapIso
    (M := small.rep F)
    (N := Rep.res T.galHom.range.subtype (big.rep F))
    (e := MonoidHom.ofInjective T.galHom_injective)
    (e' := (Representation.equivOfIso (T.repIso F)).toLinearEquiv)
    (isIntertwiningMap_repIso_range T F) r

/-- The range comparison is the Tate map attached to the compatible pair
`isIntertwiningMap_repIso_range`. -/
theorem tateRangeIso_hom (T : LayerRestriction small big) (F : Formation G) (r : ℤ) :
    (T.tateRangeIso F r).hom =
      TauCeti.TateCohomology.map (T.isIntertwiningMap_repIso_range F) r := by
  rw [tateRangeIso, TauCeti.TateCohomology.mapIso_hom]

/-- In degree zero, the inverse range comparison sends the class of an invariant of the image
subgroup to the class of the same element, read through `repIso`, in the smaller layer. -/
theorem tateRangeIso_inv_H0π (T : LayerRestriction small big) (F : Formation G)
    (x : (Rep.res T.galHom.range.subtype (big.rep F)).ρ.invariants) :
    (T.tateRangeIso F 0).inv (TauCeti.TateCohomology.H0π _ x) =
      TauCeti.TateCohomology.H0π (small.rep F)
        ⟨(T.repIso F).inv.hom x, fun g ↦ by
          rw [← Rep.hom_comm_apply]
          exact congrArg (T.repIso F).inv.hom (x.2 ⟨T.galHom g, g, rfl⟩)⟩ := by
  rw [tateRangeIso, TauCeti.TateCohomology.mapIso_inv,
    TauCeti.TateCohomology.H0π_comp_map_apply]
  congr 1
  ext
  rw [TauCeti.TateCohomology.mapInvariants_apply_coe]
  simp

/-! ### Trivial coefficients -/

private theorem trivial_isIntertwiningRange (T : LayerRestriction small big) :
    Representation.IsIntertwiningMap (Rep.trivial ℤ small.Gal ℤ).ρ
      ((Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)).ρ.comp
        (MonoidHom.ofInjective T.galHom_injective : small.Gal ≃* T.galHom.range))
      (LinearEquiv.refl ℤ ℤ) :=
  ⟨fun _ _ ↦ rfl⟩

/-- Tate cohomology with trivial integral coefficients on the smaller Galois group, identified
with the restriction of the trivial representation on the larger Galois group to the image of
the inclusion. -/
def trivialTateRangeIso (T : LayerRestriction small big) (r : ℤ) :
    small.TrivialTateH r ≅
      tateCohomology (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) r :=
  TauCeti.TateCohomology.mapIso
    (M := Rep.trivial ℤ small.Gal ℤ)
    (N := Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))
    (e := MonoidHom.ofInjective T.galHom_injective)
    (e' := LinearEquiv.refl ℤ ℤ)
    (trivial_isIntertwiningRange T) r

end TauCeti.ClassFieldTheory.LayerRestriction
