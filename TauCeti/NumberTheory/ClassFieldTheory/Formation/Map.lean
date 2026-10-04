/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.LayerEquiv
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units

/-!
# Transporting finite normal layers along open embeddings

An injective open homomorphism of profinite groups carries every finite normal layer in its
source to a finite normal layer in its target.  If a formation on the source is identified with
the restriction of a formation on the target, the two layers are canonically isomorphic in the
sense of `LayerEquiv`.

The motivating example is the open embedding `G_L → G_K` attached to a finite extension of
fields.  Together with `localFormationRestrict`, the construction in this file identifies a
finite layer of the units formation over `L` with its image in the units formation over `K`.
This is the layer comparison needed to apply `ClassFormation.artinMap_layerEquiv` in the proof of
the norm compatibility of the local Artin map.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.map`: the image of a normal layer under an open
  homomorphism.
* `TauCeti.ClassFieldTheory.NormalLayer.mapGalEquiv`: the canonical isomorphism between the
  Galois group of a layer and that of its image under an injective homomorphism.
* `TauCeti.ClassFieldTheory.NormalLayer.mapLayerEquiv`: the resulting layer isomorphism when the
  coefficient formations agree after restriction.
* `TauCeti.ClassFieldTheory.localFormationLayerEquiv`: the specialization to the units
  formations of a finite extension of fields.
-/

public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [TotallyDisconnectedSpace G']

namespace NormalLayer

variable (L : NormalLayer G) (f : G →* G')

/-- The image of a finite normal layer under an open group homomorphism.  Openness is used only
to make the two image subgroups open; normality inside the image of the ground subgroup is
preserved by every homomorphism. -/
def map (hf : IsOpenMap f) : NormalLayer G' where
  ground := ⟨L.ground.toSubgroup.map f, hf _ L.ground.isOpen⟩
  top := ⟨L.top.toSubgroup.map f, hf _ L.top.isOpen⟩
  top_le_ground := Subgroup.map_mono L.top_le_ground
  normal := by
    constructor
    intro v hv u
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    rcases hv with ⟨v', hv', hv⟩
    rcases u.property with ⟨u', hu', hu⟩
    refine ⟨u' * v' * u'⁻¹, L.conj_mem_top hu' hv', ?_⟩
    simp only [map_mul, map_inv]
    rw [hv, hu]
    rfl

/-- The ground subgroup of the mapped layer is the image of the original ground subgroup. -/
@[simp]
theorem map_ground_toSubgroup (hf : IsOpenMap f) :
    (L.map f hf).ground.toSubgroup = L.ground.toSubgroup.map f :=
  by simp [map]

/-- The top subgroup of the mapped layer is the image of the original top subgroup. -/
@[simp]
theorem map_top_toSubgroup (hf : IsOpenMap f) :
    (L.map f hf).top.toSubgroup = L.top.toSubgroup.map f :=
  by simp [map]

/-- An injective homomorphism identifies the ground subgroup of a layer with the ground subgroup
of its image. -/
def mapGroundEquiv (hf : IsOpenMap f) (hfi : Function.Injective f) :
    L.ground ≃* (L.map f hf).ground :=
  L.ground.toSubgroup.equivMapOfInjective f hfi

/-- On underlying group elements, `mapGroundEquiv` is the original homomorphism. -/
@[simp]
theorem mapGroundEquiv_apply_coe (hf : IsOpenMap f) (hfi : Function.Injective f)
    (u : L.ground) :
    ((L.mapGroundEquiv f hf hfi u : (L.map f hf).ground) : G') = f u :=
  Subgroup.coe_equivMapOfInjective_apply _ _ _ _

/-- The ground-subgroup equivalence carries the relative top subgroup onto the relative top
subgroup of the mapped layer. -/
theorem map_relativeTop_mapGroundEquiv (hf : IsOpenMap f) (hfi : Function.Injective f) :
    L.relativeTop.map (L.mapGroundEquiv f hf hfi) = (L.map f hf).relativeTop := by
  ext v
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ⟨u, Subgroup.mem_subgroupOf.1 hu, rfl⟩
  · intro hv
    rcases Subgroup.mem_subgroupOf.1 hv with ⟨u, hu, huv⟩
    let u' : L.ground := ⟨u, L.top_le_ground hu⟩
    refine ⟨u', Subgroup.mem_subgroupOf.2 hu, ?_⟩
    apply Subtype.ext
    exact huv

/-- The canonical isomorphism from the Galois group of a layer to the Galois group of its image
under an injective open homomorphism. -/
def mapGalEquiv (hf : IsOpenMap f) (hfi : Function.Injective f) :
    L.Gal ≃* (L.map f hf).Gal :=
  QuotientGroup.congr _ _ (L.mapGroundEquiv f hf hfi)
    (L.map_relativeTop_mapGroundEquiv f hf hfi)

/-- `mapGalEquiv` sends the class of a representative to the class of its image. -/
@[simp]
theorem mapGalEquiv_mk (hf : IsOpenMap f) (hfi : Function.Injective f) (u : L.ground) :
    L.mapGalEquiv f hf hfi (QuotientGroup.mk u) =
      QuotientGroup.mk (L.mapGroundEquiv f hf hfi u) :=
  QuotientGroup.congr_mk _ _ _ _ u

variable {F : Formation G} {F' : Formation G'}

/-- An isomorphism between a formation and the restriction of another formation identifies the
top levels of a layer and its image.  The direction of `e` follows `TopRep.res`: its inverse sends
coefficients of `F` to coefficients of `F'`. -/
def mapCoeffEquiv (hf : IsOpenMap f)
    (e : TopRep.res f F'.module ≅ F.module) :
    F.level L.top ≃ₗ[ℤ] F'.level (L.map f hf).top where
  toFun x := ⟨e.inv.hom x.1, by
    rw [Formation.mem_level]
    intro g hg
    rcases hg with ⟨g, hg, rfl⟩
    rw [F'.toRep_ρ_apply]
    calc
      _ = e.inv.hom (F.module.ρ g x.1) := (TopRep.hom_comm_apply e.inv g x.1).symm
      _ = e.inv.hom x.1 := congrArg e.inv.hom (F.mem_level.1 x.property g hg)⟩
  invFun x := ⟨e.hom.hom x.1, by
    rw [Formation.mem_level]
    intro g hg
    have hx := F'.mem_level.1 x.property (f g) ⟨g, hg, rfl⟩
    rw [F.toRep_ρ_apply]
    calc
      _ = e.hom.hom (F'.module.ρ (f g) x.1) :=
        (TopRep.hom_comm_apply e.hom g x.1).symm
      _ = e.hom.hom x.1 := congrArg e.hom.hom hx⟩
  left_inv x := Subtype.ext (e.inv_hom_id_apply x.1)
  right_inv x := Subtype.ext (e.hom_inv_id_apply x.1)
  map_add' x y := Subtype.ext (map_add e.inv.hom x.1 y.1)
  map_smul' c x := Subtype.ext (map_zsmul e.inv.hom c x.1)

/-- On underlying coefficient modules, `mapCoeffEquiv` is the inverse of the chosen restriction
isomorphism. -/
@[simp]
theorem mapCoeffEquiv_apply_coe (hf : IsOpenMap f)
    (e : TopRep.res f F'.module ≅ F.module) (x : F.level L.top) :
    (dsimp% only ((L.mapCoeffEquiv f hf e x : F'.level (L.map f hf).top) : F'.toRep.V)) =
      e.inv x :=
  by simp [mapCoeffEquiv]

/-- The coefficient equivalence intertwines the action of a ground-subgroup representative with
the action of its image. -/
theorem mapCoeffEquiv_rep_mk (hf : IsOpenMap f) (hfi : Function.Injective f)
    (e : TopRep.res f F'.module ≅ F.module) (u : L.ground) (x : F.level L.top) :
    L.mapCoeffEquiv f hf e ((L.rep F).ρ (QuotientGroup.mk u) x) =
      ((L.map f hf).rep F').ρ
        (QuotientGroup.mk (L.mapGroundEquiv f hf hfi u)) (L.mapCoeffEquiv f hf e x) := by
  apply Subtype.ext
  rw [mapCoeffEquiv_apply_coe, NormalLayer.rep_ρ_mk_apply_coe,
    NormalLayer.rep_ρ_mk_apply_coe, mapCoeffEquiv_apply_coe, mapGroundEquiv_apply_coe]
  exact TopRep.hom_comm_apply e.inv u x.1

/-- Transporting a normal layer along an injective open homomorphism gives a layer isomorphism
whenever the source formation is the restriction of the target formation. -/
def mapLayerEquiv (hf : IsOpenMap f) (hfi : Function.Injective f)
    (e : TopRep.res f F'.module ≅ F.module) :
    LayerEquiv F L F' (L.map f hf) where
  galEquiv := L.mapGalEquiv f hf hfi
  coeffEquiv := L.mapCoeffEquiv f hf e
  isIntertwiningMap := ⟨fun γ x ↦ by
    induction γ using QuotientGroup.induction_on with
    | H u =>
      -- `IsIntertwiningMap` hides the transported action behind `MonoidHom.comp`; expose its
      -- representative form because `rw` cannot see `mapGalEquiv_mk` through that wrapper.
      change L.mapCoeffEquiv f hf e ((L.rep F).ρ (QuotientGroup.mk u) x) =
        ((L.map f hf).rep F').ρ
          (L.mapGalEquiv f hf hfi (QuotientGroup.mk u)) (L.mapCoeffEquiv f hf e x)
      rw [mapGalEquiv_mk]
      exact L.mapCoeffEquiv_rep_mk f hf hfi e u x⟩

end NormalLayer

/-! ### Finite extensions of fields -/

variable (K : Type) [Field K] (E : Type) [Field E] [Algebra K E] [FiniteDimensional K E]
  (iota : E →ₐ[K] SeparableClosure K)

/-- A finite normal layer over `E` regarded as a finite normal layer over `K`, using the chosen
embedding `E → Kˢ`. -/
def NormalLayer.localFormationMap
    (L : NormalLayer (AbsoluteGaloisGroup E)) : NormalLayer (AbsoluteGaloisGroup K) :=
  L.map (localFormationHom K E iota) (isOpenMap_localFormationHom K E iota)

/-- **A layer over a finite extension as a layer over the base field.**  Restriction identifies
the units formation over `E` with the restriction of the units formation over `K`, and hence
identifies every finite normal layer over `E` with its image layer over `K`. -/
def localFormationLayerEquiv (L : NormalLayer (AbsoluteGaloisGroup E)) :
    LayerEquiv (unitsFormation E) L (unitsFormation K) (L.localFormationMap K E iota) :=
  L.mapLayerEquiv (localFormationHom K E iota) (isOpenMap_localFormationHom K E iota)
    (injective_localFormationHom K E iota) (localFormationRestrict K E iota)

end TauCeti.ClassFieldTheory
