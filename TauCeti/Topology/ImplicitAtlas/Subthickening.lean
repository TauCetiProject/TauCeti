/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.Basic
import TauCeti.Topology.Constructions.Basic

/-!
# Restricting an implicit atlas to closed subthickenings

Several constructions of Pardon's theory produce a new implicit atlas by keeping the same index
set, groups and obstruction spaces and cutting every thickening `X_I` down to a closed subset
`C_I ⊆ X_I`: the restriction of an atlas with boundary to its boundary (`C_I = ∂X_I`, Pardon,
Definition 3.2.3) and the restriction of a cell-like stratified atlas to a closed stratum
(`C_I = X_I^≤s`, Pardon, Definition 6.1.6). This file isolates what such a family must satisfy for
every datum and axiom of an implicit atlas other than its local product model to restrict.

A *closed subthickening* of `𝒜 : TauCeti.ImplicitAtlas.Core`
(`TauCeti.ImplicitAtlas.Core.IsClosedSubthickening`) is a family of closed `Γ_I`-invariant
subsets `C_I ⊆ X_I` compatible with the footprint maps: `ψ_IJ⁻¹(C_I) = Z_IJ ∩ C_J`. For such a
family and a subset `Y` of the base with `C_∅ = X_∅ ∩ Y` under the identification `X_∅ ≃ₜ X`, the
restrictions of the actions (`TauCeti.ImplicitAtlas.restrictAct`), of the Kuranishi maps, of the
regular loci and of the footprint maps form an `ImplicitAtlas.Core` on `Y`
(`TauCeti.ImplicitAtlas.Core.restrictThickening`). The compatibility is what keeps the footprint
maps defined on the restricted zero sets and the regular footprints covering `Y`; closedness is
what keeps the restricted footprint maps quotient maps onto their images, because a closed
embedding of a saturated subset of `Z_IJ` restricts a quotient map to a quotient map
(`Topology.IsQuotientMap.of_comp_eq_comp`). The regular footprints of the restriction are the
traces on `Y` of those of `𝒜` (`TauCeti.ImplicitAtlas.Core.footprint_restrictThickening`).

The local product model over the regular locus is the one axiom that does not restrict formally:
each application supplies its own charts of the restricted thickenings, such as the hyperplane
charts of the boundary (`TauCeti.ImplicitAtlasWithBoundary.boundaryAtlas`).

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definitions 3.2.3 and 6.1.6.
-/

public section

open Set Topology

namespace TauCeti

variable {A : Type*}

namespace ImplicitAtlas

/-- The action of `Γ_I` on an invariant subset `C_I` of the thickening `X_I`. -/
def restrictAct {Γ : A → Type*} [∀ α, Group (Γ α)] {T : Finset A → Type*}
    [∀ I, TopologicalSpace (T I)] (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (C : ∀ I : Finset A, Set (T I)) (hC : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I),
      x ∈ C I → act I g x ∈ C I) (I : Finset A) : ((α : I) → Γ α) →* (C I ≃ₜ C I) where
  toFun g := (act I g).subtype fun x ↦ ⟨hC I g x, fun h ↦ by
    simpa [map_inv] using hC I g⁻¹ _ h⟩
  map_one' := by
    ext
    simp
  map_mul' g g' := by
    ext
    simp

@[simp]
theorem coe_restrictAct_apply {Γ : A → Type*} [∀ α, Group (Γ α)] {T : Finset A → Type*}
    [∀ I, TopologicalSpace (T I)] {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
    {C : ∀ I : Finset A, Set (T I)} {hC : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I),
      x ∈ C I → act I g x ∈ C I} {I : Finset A} (g : (α : I) → Γ α) (x : C I) :
    (restrictAct act C hC I g x : T I) = act I g x :=
  (rfl)

variable [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X]

namespace Core

variable (𝒜 : ImplicitAtlas.Core Γ E ρ T act X)

/-- A **closed subthickening** of an implicit atlas: closed `Γ_I`-invariant subsets `C_I ⊆ X_I`
of the thickenings with `ψ_IJ⁻¹(C_I) = Z_IJ ∩ C_J` for all `I ⊆ J`. The atlas restricts to it
(`TauCeti.ImplicitAtlas.Core.restrictThickening`). -/
structure IsClosedSubthickening (C : ∀ I : Finset A, Set (T I)) : Prop where
  /-- Each `C_I` is closed in `X_I`. -/
  isClosed : ∀ I : Finset A, IsClosed (C I)
  /-- Each `C_I` is invariant under `Γ_I`. -/
  act_mem : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I), x ∈ C I → act I g x ∈ C I
  /-- `ψ_IJ⁻¹(C_I) = Z_IJ ∩ C_J`. -/
  footprintMap_mem_iff : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (x : kuranishiZeroSet 𝒜.kuranishi I J),
    𝒜.footprintMap h x ∈ C I ↔ x.val ∈ C J

variable {𝒜} {C : ∀ I : Finset A, Set (T I)}

/-- The Kuranishi maps restricted to the subthickenings `C_I`. -/
private def subKuranishi (𝒜 : ImplicitAtlas.Core Γ E ρ T act X) (C : ∀ I : Finset A, Set (T I))
    (I : Finset A) (α : I) (x : C I) : E α :=
  𝒜.kuranishi I α x

private theorem subKuranishi_apply (I : Finset A) (α : I) (x : C I) :
    subKuranishi 𝒜 C I α x = 𝒜.kuranishi I α x :=
  (rfl)

private theorem mem_kuranishiZeroSet_subKuranishi {I J : Finset A} {x : C J} :
    x ∈ kuranishiZeroSet (subKuranishi 𝒜 C) I J ↔ (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J := by
  simp only [mem_kuranishiZeroSet, subKuranishi_apply]

/-- The inclusion `Z_IJ ∩ C_J → Z_IJ`. -/
private def zeroSetInclusion {I J : Finset A}
    (x : kuranishiZeroSet (subKuranishi 𝒜 C) I J) : kuranishiZeroSet 𝒜.kuranishi I J :=
  ⟨x.val, mem_kuranishiZeroSet_subKuranishi.1 x.property⟩

@[simp]
private theorem coe_zeroSetInclusion {I J : Finset A}
    (x : kuranishiZeroSet (subKuranishi 𝒜 C) I J) : (zeroSetInclusion x : T J) = x.val :=
  (rfl)

/-- The lift of a point of `Z_IJ` lying in `C_J` to `Z_IJ ∩ C_J`. -/
private def zeroSetLift {I J : Finset A} (z : kuranishiZeroSet 𝒜.kuranishi I J) (hz : z.val ∈ C J) :
    kuranishiZeroSet (subKuranishi 𝒜 C) I J :=
  ⟨⟨z.val, hz⟩, mem_kuranishiZeroSet_subKuranishi.2 z.property⟩

/-- The image of the inclusion `Z_IJ ∩ C_J → Z_IJ` is the part of `Z_IJ` in `C_J`. -/
private theorem range_zeroSetInclusion {I J : Finset A} :
    range (zeroSetInclusion (𝒜 := 𝒜) (C := C) (I := I) (J := J)) = Subtype.val ⁻¹' C J :=
  Subset.antisymm (range_subset_iff.2 fun x ↦ x.val.property) fun z hz ↦ ⟨zeroSetLift z hz, rfl⟩

private theorem isClosedEmbedding_zeroSetInclusion (hC : ∀ I, IsClosed (C I)) {I J : Finset A} :
    IsClosedEmbedding (zeroSetInclusion (𝒜 := 𝒜) (C := C) (I := I) (J := J)) := by
  have hcomp : Subtype.val ∘ zeroSetInclusion (𝒜 := 𝒜) (C := C) (I := I) (J := J) =
      fun x ↦ (x.val : T J) :=
    funext coe_zeroSetInclusion
  refine ⟨⟨IsInducing.subtypeVal.of_comp_iff.1 ?_,
    Function.Injective.of_comp (f := Subtype.val) ?_⟩, ?_⟩
  · rw [hcomp]
    exact IsInducing.subtypeVal.comp IsInducing.subtypeVal
  · rw [hcomp]
    exact Subtype.val_injective.comp Subtype.val_injective
  rw [range_zeroSetInclusion]
  exact (hC J).preimage continuous_subtypeVal

variable (hC : 𝒜.IsClosedSubthickening C)
include hC

/-- A point of `Z_IJ` whose image under `ψ_IJ` lies in `C_I` comes from `Z_IJ ∩ C_J`. -/
private theorem mem_range_zeroSetInclusion {I J : Finset A} (h : I ⊆ J)
    {z : kuranishiZeroSet 𝒜.kuranishi I J} (hz : 𝒜.footprintMap h z ∈ C I) :
    z ∈ range (zeroSetInclusion (𝒜 := 𝒜) (C := C)) := by
  rw [range_zeroSetInclusion]
  exact (hC.footprintMap_mem_iff h z).1 hz

omit hC in
/-- The footprint maps restricted to the subthickenings. -/
private def subFootprintMap (hC : 𝒜.IsClosedSubthickening C) {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet (subKuranishi 𝒜 C) I J) : C I :=
  ⟨𝒜.footprintMap h (zeroSetInclusion x), (hC.footprintMap_mem_iff h _).2 x.val.property⟩

private theorem mem_range_subFootprintMap {I J : Finset A} (h : I ⊆ J) {y : C I} :
    y ∈ range (subFootprintMap hC h) ↔ (y : T I) ∈ range (𝒜.footprintMap h) := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨zeroSetInclusion x, congrArg Subtype.val hx⟩, fun ⟨z, hz⟩ ↦ ?_⟩
  obtain ⟨x, rfl⟩ := mem_range_zeroSetInclusion hC h (hz ▸ y.property)
  exact ⟨x, Subtype.ext hz⟩

private theorem range_subFootprintMap {I J : Finset A} (h : I ⊆ J) :
    range (subFootprintMap hC h) = Subtype.val ⁻¹' range (𝒜.footprintMap h) :=
  Set.ext fun _ ↦ mem_range_subFootprintMap hC h

/-- The restricted footprint maps are quotient maps onto their images. -/
private theorem isQuotientMap_subFootprintMap {I J : Finset A} (h : I ⊆ J) :
    IsQuotientMap (rangeFactorization (subFootprintMap hC h)) := by
  have hemb := isClosedEmbedding_zeroSetInclusion (𝒜 := 𝒜) hC.isClosed (I := I) (J := J)
  refine (𝒜.isQuotientMap_footprintMap h).of_comp_eq_comp
    (j := fun y ↦ ⟨y.val.val, (mem_range_subFootprintMap hC h).1 y.property⟩)
    (((𝒜.continuous_footprintMap h).comp hemb.continuous).subtype_mk _).rangeFactorization
    rangeFactorization_surjective hemb.isClosedMap
    ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _)
    (fun y y' hyy' ↦ Subtype.ext (Subtype.ext
      (congrArg (fun z : range (𝒜.footprintMap h) ↦ (z : T I)) hyy')))
    (funext fun _ ↦ rfl) ?_
  rintro z ⟨y, hy⟩
  have hz : 𝒜.footprintMap h z = y.val.val := (congrArg Subtype.val hy).symm
  exact mem_range_zeroSetInclusion hC h (hz ▸ y.val.property)

omit hC in
/-- **The restriction of an implicit atlas to a closed subthickening.** The closed invariant
subsets `C_I ⊆ X_I` with `ψ_IJ⁻¹(C_I) = Z_IJ ∩ C_J`, with the restricted actions, Kuranishi maps,
regular loci and footprint maps, carry the data and axioms of an implicit atlas other than its
local product model, on the subset `Y` of the base corresponding to `C_∅`. -/
noncomputable def restrictThickening (hC : 𝒜.IsClosedSubthickening C) (Y : Set X)
    (hY : C ∅ = 𝒜.baseHomeomorph ⁻¹' Y) :
    ImplicitAtlas.Core Γ E ρ (fun I ↦ C I) (restrictAct act C hC.act_mem) Y where
  baseHomeomorph := 𝒜.baseHomeomorph.sets hY
  kuranishi := subKuranishi 𝒜 C
  continuous_kuranishi I α := (𝒜.continuous_kuranishi I α).comp continuous_subtypeVal
  kuranishi_act I α g x := 𝒜.kuranishi_act I α g x
  regLocus I := Subtype.val ⁻¹' 𝒜.regLocus I
  isOpen_regLocus I := (𝒜.isOpen_regLocus I).preimage continuous_subtypeVal
  act_mem_regLocus I g x hx := 𝒜.act_mem_regLocus I g x hx
  footprintMap _ _ := subFootprintMap hC
  continuous_footprintMap _ _ h :=
    ((𝒜.continuous_footprintMap h).comp
      (isClosedEmbedding_zeroSetInclusion hC.isClosed).continuous).subtype_mk _
  footprintMap_act _ _ h g x hx := Subtype.ext
    (𝒜.footprintMap_act h g (zeroSetInclusion x) (mem_kuranishiZeroSet_subKuranishi.1 hx))
  footprintMap_self I x := Subtype.ext (𝒜.footprintMap_self I x)
  footprintMap_footprintMap _ _ _ hIJ hJK x hx hx' :=
    Subtype.ext (𝒜.footprintMap_footprintMap hIJ hJK (zeroSetInclusion x)
      (mem_kuranishiZeroSet_subKuranishi (𝒜 := 𝒜) (C := C).1 hx)
      (mem_kuranishiZeroSet_subKuranishi (𝒜 := 𝒜) (C := C).1 hx'))
  kuranishi_footprintMap _ _ h x α := 𝒜.kuranishi_footprintMap h (zeroSetInclusion x) α
  isOpen_range_footprintMap _ _ h := by
    rw [range_subFootprintMap hC h]
    exact (𝒜.isOpen_range_footprintMap h).preimage continuous_subtypeVal
  range_footprintMap_inter _ _ _ h₁ h₂ := by
    simp only [range_subFootprintMap hC, ← preimage_inter, 𝒜.range_footprintMap_inter]
  footprintMap_mem_range_iff _ _ _ hIJ hJK x := by
    rw [mem_range_subFootprintMap hC, mem_range_subFootprintMap hC]
    exact 𝒜.footprintMap_mem_range_iff hIJ hJK (zeroSetInclusion x)
  isQuotientMap_footprintMap _ _ := isQuotientMap_subFootprintMap hC
  footprintMap_eq_footprintMap_iff _ _ h x y := by
    rw [Subtype.ext_iff]
    refine (𝒜.footprintMap_eq_footprintMap_iff h (zeroSetInclusion x)
      (zeroSetInclusion y)).trans ?_
    simp only [Subtype.ext_iff, coe_restrictAct_apply, coe_zeroSetInclusion]
  mem_regLocus_of_footprintMap_mem _ _ h x hx :=
    𝒜.mem_regLocus_of_footprintMap_mem h (zeroSetInclusion x) hx
  eq_one_of_act_eq _ _ h x hx g hg hgx :=
    𝒜.eq_one_of_act_eq h (zeroSetInclusion x) hx g hg (congrArg Subtype.val hgx)
  exists_footprintMap_eq y := by
    obtain ⟨I, x, hreg, hx⟩ := 𝒜.exists_footprintMap_eq y.val
    have hxC : x.val ∈ C I := (hC.footprintMap_mem_iff _ x).1 <| by
      rw [hY, mem_preimage, hx]
      exact y.property
    exact ⟨I, zeroSetLift x hxC, hreg, Subtype.ext hx⟩

variable {Y : Set X} (hY : C ∅ = 𝒜.baseHomeomorph ⁻¹' Y)

/-- The base identification of the restriction is that of `𝒜`, restricted to `C_∅`. -/
@[simp]
theorem coe_baseHomeomorph_restrictThickening (x : C ∅) :
    ((𝒜.restrictThickening hC Y hY).baseHomeomorph x : X) = 𝒜.baseHomeomorph x :=
  (rfl)

/-- The Kuranishi maps of the restriction are the restrictions of those of `𝒜`. -/
@[simp]
theorem kuranishi_restrictThickening (I : Finset A) (α : I) (x : C I) :
    (𝒜.restrictThickening hC Y hY).kuranishi I α x = 𝒜.kuranishi I α x :=
  (rfl)

/-- The zero sets of the restriction are the zero sets of `𝒜` intersected with the
subthickenings. -/
theorem mem_kuranishiZeroSet_restrictThickening {I J : Finset A} {x : C J} :
    x ∈ kuranishiZeroSet (𝒜.restrictThickening hC Y hY).kuranishi I J ↔
      (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J :=
  mem_kuranishiZeroSet_subKuranishi

/-- The regular loci of the restriction are the regular loci of `𝒜` intersected with the
subthickenings. -/
@[simp]
theorem regLocus_restrictThickening (I : Finset A) :
    (𝒜.restrictThickening hC Y hY).regLocus I = Subtype.val ⁻¹' 𝒜.regLocus I :=
  (rfl)

/-- The footprint maps of the restriction are the restrictions of those of `𝒜`. -/
@[simp]
theorem coe_footprintMap_restrictThickening {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet (𝒜.restrictThickening hC Y hY).kuranishi I J) :
    ((𝒜.restrictThickening hC Y hY).footprintMap h x : T I) =
      𝒜.footprintMap h ⟨x.val, (mem_kuranishiZeroSet_restrictThickening hC hY).1 x.property⟩ :=
  (rfl)

/-- The regular footprints of the restriction are the traces on `Y` of the regular footprints of
`𝒜`. -/
@[simp]
theorem footprint_restrictThickening (I : Finset A) :
    (𝒜.restrictThickening hC Y hY).footprint I = Subtype.val ⁻¹' 𝒜.footprint I := by
  ext y
  simp only [mem_footprint, mem_preimage]
  refine ⟨fun ⟨x, hx, hxy⟩ ↦ ⟨zeroSetInclusion x, hx, congrArg Subtype.val hxy⟩,
    fun ⟨x, hx, hxy⟩ ↦ ?_⟩
  have hxC : x.val ∈ C I := (hC.footprintMap_mem_iff _ x).1 <| by
    rw [hY, mem_preimage, hxy]
    exact y.property
  exact ⟨zeroSetLift x hxC, hx, Subtype.ext hxy⟩

end Core

end ImplicitAtlas

end TauCeti
