/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Topology.ImplicitAtlas.Basic
import TauCeti.Geometry.Manifold.Boundary.HalfSpaceChart
import TauCeti.Topology.Constructions.Basic

/-!
# Implicit atlases with boundary

An *implicit atlas with boundary* of virtual dimension `d` on a space `X` with a specified closed
boundary `∂X ⊆ X` (`TauCeti.ImplicitAtlasWithBoundary`, Pardon, Definition 3.2.1) carries the same
data as an implicit atlas (`TauCeti.ImplicitAtlas`) together with closed `Γ_I`-invariant subsets
`∂X_I ⊆ X_I` of the thickenings, with `∂X_∅ = ∂X` and `ψ_IJ⁻¹(∂X_I) = Z_IJ ∩ ∂X_J`. Its axioms
are those of an implicit atlas, except that the local product model over the regular locus may
have a half-space as its first factor: near each point of `ψ_IJ⁻¹(X_I^reg)` the Kuranishi map
`s_(J \ I)` is the projection either of `ℝ^n × E_(J \ I)` away from `∂X_J`, or of
`H^n × E_(J \ I)` for the Euclidean half-space `H^n = {x ∈ ℝ^n | 0 ≤ x₀}`, in which `∂X_J` is the
hyperplane `x₀ = 0`. Here `(n : ℤ) = d + m_I`, with `m_I = ∑_(α ∈ I) dim E_α`. Both kinds of
atlas extend `TauCeti.ImplicitAtlas.Core`, which collects everything except the product model, so
its consequences, such as the openness and covering of the regular footprints, apply to both.

These atlases describe compactified moduli spaces whose codimension-one strata form a boundary,
such as the one-dimensional moduli spaces whose boundaries give the chain-level identities of
Floer theory. The specified boundary is data: `[0, 1]` with `∂X = ∅` does not satisfy the axioms
near `0`, although its topological frontier in itself is empty.

* **Restriction to the boundary** (`TauCeti.ImplicitAtlasWithBoundary.boundaryAtlas`, Pardon,
  Definition 3.2.3). The boundaries `∂X_I`, with the restricted actions, Kuranishi maps, regular
  loci and footprint maps, form an implicit atlas of virtual dimension `d - 1` on `∂X`, with the
  same groups and obstruction spaces. The half-space charts restrict to charts of the hyperplane
  `x₀ = 0` (`OpenPartialHomeomorph.hyperplaneChart`), and the footprint maps of the boundary
  remain quotient maps because `∂X_J` is closed (`Topology.IsQuotientMap.of_comp_eq_comp`).
* **Boundary points have positive expected dimension**
  (`TauCeti.ImplicitAtlasWithBoundary.one_le_of_mem_boundary`): a regular chart of dimension `0`
  has empty boundary. Consequently an atlas all of whose expected dimensions `d + m_I` are at most
  `0` has empty boundary (`TauCeti.ImplicitAtlasWithBoundary.eq_empty_of_forall_nonpos`).
* **Atlases without boundary** (`TauCeti.ImplicitAtlas.toImplicitAtlasWithBoundary`). An implicit
  atlas is an implicit atlas with boundary `∂X = ∅` and `∂X_I = ∅`.

Products with corner faces are not atlases with boundary in this sense; they are cell-like
stratified atlases.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definitions 3.2.1 (implicit atlases
  with boundary) and 3.2.3 (restriction to the boundary).
-/

public section

open Set Topology

namespace TauCeti

variable {A : Type*}

/-- An **implicit atlas with boundary** of virtual dimension `d` on `X` with boundary `bd ⊆ X`
(Pardon, Definition 3.2.1). It extends `TauCeti.ImplicitAtlas.Core`, the data and axioms of an
implicit atlas other than its local product model, with closed invariant boundaries
`∂X_I ⊆ X_I` (`ImplicitAtlasWithBoundary.boundary`) compatible with the base identification and
the footprint maps. In its local product model over the regular locus the first factor is either
`ℝ^n`, away from the boundary, or the Euclidean half-space `EuclideanHalfSpace (n + 1)`, whose
hyperplane `x₀ = 0` is the boundary. -/
structure ImplicitAtlasWithBoundary [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
    [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
    [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
    (ρ : ∀ α, Representation ℝ (Γ α) (E α))
    (T : Finset A → Type*) [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (X : Type*) [TopologicalSpace X] (bd : Set X) (d : ℤ)
    extends ImplicitAtlas.Core Γ E ρ T act X where
  /-- The boundary `∂X_I ⊆ X_I` of the thickening. -/
  boundary : ∀ I : Finset A, Set (T I)
  isClosed_boundary : ∀ I : Finset A, IsClosed (boundary I)
  act_mem_boundary : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I),
    x ∈ boundary I → act I g x ∈ boundary I
  /-- The base identification `X_∅ ≃ₜ X` identifies `∂X_∅` with `∂X`. -/
  boundary_empty : boundary ∅ = baseHomeomorph ⁻¹' bd
  /-- `ψ_IJ⁻¹(∂X_I) = Z_IJ ∩ ∂X_J`. -/
  footprintMap_mem_boundary_iff : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J), footprintMap h x ∈ boundary I ↔ x.val ∈ boundary J
  /-- Over `ψ_IJ⁻¹(X_I^reg)`, the map `s_(J \ I) : X_J → E_(J \ I)` is locally a product
  projection, either `ℝ^n × E_(J \ I) → E_(J \ I)` on a chart missing `∂X_J`, or
  `H^n × E_(J \ I) → E_(J \ I)` for the half-space `H^n`, on a chart in which `∂X_J` is the
  hyperplane `x₀ = 0`. In both cases `(n : ℤ) = d + m_I`. -/
  exists_openPartialHomeomorph : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J), footprintMap h x ∈ regLocus I →
      (∃ n : ℕ, (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
        ∃ e : OpenPartialHomeomorph (T J) (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → E α)),
          x.val ∈ e.source ∧ Disjoint e.source (boundary J) ∧ ∀ y ∈ e.source,
            (e y).2 = fun α : ↥(J \ I) ↦ kuranishi J ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩ y) ∨
      (∃ n : ℕ, (n + 1 : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
        ∃ e : OpenPartialHomeomorph (T J) (EuclideanHalfSpace (n + 1) × ((α : ↥(J \ I)) → E α)),
          x.val ∈ e.source ∧ (∀ y ∈ e.source, y ∈ boundary J ↔ (e y).1.val 0 = 0) ∧ ∀ y ∈ e.source,
            (e y).2 = fun α : ↥(J \ I) ↦ kuranishi J ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩ y)

variable [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ}

/-- **An implicit atlas is an implicit atlas with empty boundary.** Its boundaries `∂X_I` are
empty and its product charts are the charts of the boundaryless model. -/
def ImplicitAtlas.toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d) :
    ImplicitAtlasWithBoundary Γ E ρ T act X ∅ d where
  toCore := 𝒜.toCore
  boundary _ := ∅
  isClosed_boundary _ := isClosed_empty
  act_mem_boundary _ _ _ h := h
  boundary_empty := (preimage_empty).symm
  footprintMap_mem_boundary_iff _ _ _ _ := Iff.rfl
  exists_openPartialHomeomorph _ _ h x hx := by
    obtain ⟨n, hn, e, hxe, he⟩ := 𝒜.exists_openPartialHomeomorph h x hx
    exact Or.inl ⟨n, hn, e, hxe, disjoint_empty _, he⟩

/-- The boundaries of an implicit atlas, viewed as an atlas with boundary, are empty. -/
@[simp]
theorem ImplicitAtlas.boundary_toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d)
    (I : Finset A) : 𝒜.toImplicitAtlasWithBoundary.boundary I = ∅ :=
  (rfl)

/-- An implicit atlas, viewed as an atlas with boundary, has the same Kuranishi maps, regular loci
and footprint maps. -/
@[simp]
theorem ImplicitAtlas.toCore_toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d) :
    𝒜.toImplicitAtlasWithBoundary.toCore = 𝒜.toCore :=
  (rfl)

namespace ImplicitAtlasWithBoundary

variable {bd : Set X} (𝒜 : ImplicitAtlasWithBoundary Γ E ρ T act X bd d)

/-! ### Boundary points have positive expected dimension -/

/-- A regular point of a thickening lying on its boundary has positive expected dimension: a
regular chart of dimension `0` has empty boundary. -/
theorem one_le_of_mem_boundary {I J : Finset A} (h : I ⊆ J) (x : kuranishiZeroSet 𝒜.kuranishi I J)
    (hx : 𝒜.footprintMap h x ∈ 𝒜.regLocus I) (hxb : x.val ∈ 𝒜.boundary J) :
    1 ≤ d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) := by
  rcases 𝒜.exists_openPartialHomeomorph h x hx with ⟨_, _, _, hxe, hdisj, _⟩ | ⟨n, hn, -⟩
  · exact (disjoint_left.1 hdisj hxe hxb).elim
  · omega

/-- A point of `Z_∅I` whose footprint lies on the boundary `∂X` lies on the boundary `∂X_I`. -/
theorem mem_boundary_of_baseHomeomorph_footprintMap_mem {I : Finset A}
    (x : kuranishiZeroSet 𝒜.kuranishi ∅ I)
    (hx : 𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset I) x) ∈ bd) :
    x.val ∈ 𝒜.boundary I :=
  (𝒜.footprintMap_mem_boundary_iff _ x).1 (by rw [𝒜.boundary_empty]; exact hx)

include 𝒜 in
/-- An atlas with boundary all of whose expected dimensions `d + m_I` are at most `0` has empty
boundary. -/
theorem eq_empty_of_forall_nonpos
    (hd : ∀ I : Finset A, d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ≤ 0) : bd = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
  obtain ⟨I, x, hreg, rfl⟩ := 𝒜.exists_footprintMap_eq y
  have := 𝒜.one_le_of_mem_boundary (subset_refl I) ⟨x.val, mem_kuranishiZeroSet_self _ x.val⟩
    (by rwa [𝒜.footprintMap_self]) (𝒜.mem_boundary_of_baseHomeomorph_footprintMap_mem x hy)
  linarith [hd I]

/-! ### Restriction to the boundary -/

/-- The action of `Γ_I` on the boundary `∂X_I` of the thickening. -/
def boundaryAct (I : Finset A) : ((α : I) → Γ α) →* (𝒜.boundary I ≃ₜ 𝒜.boundary I) where
  toFun g := (act I g).subtype fun x ↦ ⟨𝒜.act_mem_boundary I g x, fun h ↦ by
    simpa [map_inv] using 𝒜.act_mem_boundary I g⁻¹ _ h⟩
  map_one' := by
    ext
    simp
  map_mul' g g' := by
    ext
    simp

@[simp]
theorem coe_boundaryAct_apply {I : Finset A} (g : (α : I) → Γ α) (x : 𝒜.boundary I) :
    (𝒜.boundaryAct I g x : T I) = act I g x :=
  (rfl)

/-- The Kuranishi maps of the boundary thickenings. -/
private def boundaryKuranishi (I : Finset A) (α : I) (x : 𝒜.boundary I) : E α :=
  𝒜.kuranishi I α x

private theorem boundaryKuranishi_apply (I : Finset A) (α : I) (x : 𝒜.boundary I) :
    𝒜.boundaryKuranishi I α x = 𝒜.kuranishi I α x :=
  (rfl)

private theorem mem_kuranishiZeroSet_boundaryKuranishi {I J : Finset A} {x : 𝒜.boundary J} :
    x ∈ kuranishiZeroSet 𝒜.boundaryKuranishi I J ↔
      (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J := by
  simp only [mem_kuranishiZeroSet, boundaryKuranishi_apply]

/-- The inclusion `Z_IJ ∩ ∂X_J → Z_IJ`. -/
private def zeroSetInclusion {I J : Finset A} (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    kuranishiZeroSet 𝒜.kuranishi I J :=
  ⟨x.val, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 x.property⟩

private theorem coe_zeroSetInclusion {I J : Finset A}
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    (𝒜.zeroSetInclusion x : T J) = x.val :=
  (rfl)

/-- The lift of a point of `Z_IJ` lying on `∂X_J` to `Z_IJ ∩ ∂X_J`. -/
private def zeroSetLift {I J : Finset A} (z : kuranishiZeroSet 𝒜.kuranishi I J)
    (hz : z.val ∈ 𝒜.boundary J) : kuranishiZeroSet 𝒜.boundaryKuranishi I J :=
  ⟨⟨z.val, hz⟩, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.2 z.property⟩

private theorem zeroSetInclusion_zeroSetLift {I J : Finset A}
    (z : kuranishiZeroSet 𝒜.kuranishi I J) (hz : z.val ∈ 𝒜.boundary J) :
    𝒜.zeroSetInclusion (𝒜.zeroSetLift z hz) = z :=
  (rfl)

/-- The image of the inclusion `Z_IJ ∩ ∂X_J → Z_IJ` is the part of `Z_IJ` on `∂X_J`. -/
private theorem range_zeroSetInclusion {I J : Finset A} :
    range (𝒜.zeroSetInclusion (I := I) (J := J)) = Subtype.val ⁻¹' 𝒜.boundary J :=
  Subset.antisymm (range_subset_iff.2 fun x ↦ x.val.property)
    fun z hz ↦ ⟨𝒜.zeroSetLift z hz, 𝒜.zeroSetInclusion_zeroSetLift z hz⟩

/-- A point of `Z_IJ` whose image under `ψ_IJ` lies on `∂X_I` comes from `Z_IJ ∩ ∂X_J`. -/
private theorem mem_range_zeroSetInclusion {I J : Finset A} (h : I ⊆ J)
    {z : kuranishiZeroSet 𝒜.kuranishi I J} (hz : 𝒜.footprintMap h z ∈ 𝒜.boundary I) :
    z ∈ range 𝒜.zeroSetInclusion :=
  𝒜.range_zeroSetInclusion ▸ (𝒜.footprintMap_mem_boundary_iff h z).1 hz

private theorem isClosedEmbedding_zeroSetInclusion {I J : Finset A} :
    IsClosedEmbedding (𝒜.zeroSetInclusion (I := I) (J := J)) := by
  have hcomp : Subtype.val ∘ 𝒜.zeroSetInclusion (I := I) (J := J) = fun x ↦ (x.val : T J) :=
    funext 𝒜.coe_zeroSetInclusion
  refine ⟨⟨IsInducing.subtypeVal.of_comp_iff.1 ?_,
    Function.Injective.of_comp (f := Subtype.val) ?_⟩, ?_⟩
  · rw [hcomp]
    exact IsInducing.subtypeVal.comp IsInducing.subtypeVal
  · rw [hcomp]
    exact Subtype.val_injective.comp Subtype.val_injective
  rw [range_zeroSetInclusion]
  exact (𝒜.isClosed_boundary J).preimage continuous_subtypeVal

/-- The footprint maps of the boundary thickenings. -/
private def boundaryFootprintMap {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) : 𝒜.boundary I :=
  ⟨𝒜.footprintMap h (𝒜.zeroSetInclusion x),
    (𝒜.footprintMap_mem_boundary_iff h _).2 x.val.property⟩

private theorem mem_range_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J)
    {y : 𝒜.boundary I} :
    y ∈ range (𝒜.boundaryFootprintMap h) ↔ (y : T I) ∈ range (𝒜.footprintMap h) := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨𝒜.zeroSetInclusion x, congrArg Subtype.val hx⟩, fun ⟨z, hz⟩ ↦ ?_⟩
  obtain ⟨x, rfl⟩ := 𝒜.mem_range_zeroSetInclusion h (hz ▸ y.property)
  exact ⟨x, Subtype.ext hz⟩

private theorem range_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J) :
    range (𝒜.boundaryFootprintMap h) = Subtype.val ⁻¹' range (𝒜.footprintMap h) :=
  Set.ext fun _ ↦ 𝒜.mem_range_boundaryFootprintMap h

/-- The footprint maps of the boundary are quotient maps onto their images. -/
private theorem isQuotientMap_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J) :
    IsQuotientMap (rangeFactorization (𝒜.boundaryFootprintMap h)) := by
  refine (𝒜.isQuotientMap_footprintMap h).of_comp_eq_comp
    (j := fun y ↦ ⟨y.val.val, (𝒜.mem_range_boundaryFootprintMap h).1 y.property⟩)
    ((((𝒜.continuous_footprintMap h).comp
      𝒜.isClosedEmbedding_zeroSetInclusion.continuous).subtype_mk _).rangeFactorization)
    rangeFactorization_surjective 𝒜.isClosedEmbedding_zeroSetInclusion.isClosedMap
    ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _)
    (fun y y' hyy' ↦ Subtype.ext (Subtype.ext
      (congrArg (fun z : range (𝒜.footprintMap h) ↦ (z : T I)) hyy')))
    (funext fun _ ↦ rfl) ?_
  rintro z ⟨y, hy⟩
  have hz : 𝒜.footprintMap h z = y.val.val := (congrArg Subtype.val hy).symm
  exact 𝒜.mem_range_zeroSetInclusion h (hz ▸ y.val.property)

/-- **The restriction of an implicit atlas with boundary to its boundary** (Pardon,
Definition 3.2.3). The boundaries `∂X_I` of the thickenings, with the restricted actions, Kuranishi
maps, regular loci and footprint maps, form an implicit atlas of virtual dimension `d - 1` on the
boundary `∂X`, with the same isotropy groups and obstruction spaces. Its product charts are the
restrictions of the half-space charts to the hyperplane `x₀ = 0`. -/
noncomputable def boundaryAtlas :
    ImplicitAtlas Γ E ρ (fun I ↦ 𝒜.boundary I) 𝒜.boundaryAct bd (d - 1) where
  baseHomeomorph := 𝒜.baseHomeomorph.sets 𝒜.boundary_empty
  kuranishi := 𝒜.boundaryKuranishi
  continuous_kuranishi I α := (𝒜.continuous_kuranishi I α).comp continuous_subtypeVal
  kuranishi_act I α g x := 𝒜.kuranishi_act I α g x
  regLocus I := Subtype.val ⁻¹' 𝒜.regLocus I
  isOpen_regLocus I := (𝒜.isOpen_regLocus I).preimage continuous_subtypeVal
  act_mem_regLocus I g x hx := 𝒜.act_mem_regLocus I g x hx
  footprintMap _ _ := 𝒜.boundaryFootprintMap
  continuous_footprintMap _ _ h :=
    ((𝒜.continuous_footprintMap h).comp
      𝒜.isClosedEmbedding_zeroSetInclusion.continuous).subtype_mk _
  footprintMap_act _ _ h g x hx := Subtype.ext
    (𝒜.footprintMap_act h g (𝒜.zeroSetInclusion x) (𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 hx))
  footprintMap_self I x := Subtype.ext (𝒜.footprintMap_self I x)
  footprintMap_footprintMap _ _ _ hIJ hJK x hx hx' :=
    Subtype.ext (𝒜.footprintMap_footprintMap hIJ hJK (𝒜.zeroSetInclusion x)
      (𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 hx)
      (𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 hx'))
  kuranishi_footprintMap _ _ h x α := 𝒜.kuranishi_footprintMap h (𝒜.zeroSetInclusion x) α
  isOpen_range_footprintMap _ _ h := by
    rw [𝒜.range_boundaryFootprintMap h]
    exact (𝒜.isOpen_range_footprintMap h).preimage continuous_subtypeVal
  range_footprintMap_inter _ _ _ h₁ h₂ := by
    simp only [range_boundaryFootprintMap, ← preimage_inter, 𝒜.range_footprintMap_inter]
  footprintMap_mem_range_iff _ _ _ hIJ hJK x := by
    rw [𝒜.mem_range_boundaryFootprintMap, 𝒜.mem_range_boundaryFootprintMap]
    exact 𝒜.footprintMap_mem_range_iff hIJ hJK (𝒜.zeroSetInclusion x)
  isQuotientMap_footprintMap _ _ := 𝒜.isQuotientMap_boundaryFootprintMap
  footprintMap_eq_footprintMap_iff _ _ h x y := by
    rw [Subtype.ext_iff]
    refine (𝒜.footprintMap_eq_footprintMap_iff h (𝒜.zeroSetInclusion x)
      (𝒜.zeroSetInclusion y)).trans ?_
    simp only [Subtype.ext_iff, coe_boundaryAct_apply, coe_zeroSetInclusion]
  mem_regLocus_of_footprintMap_mem _ _ h x hx :=
    𝒜.mem_regLocus_of_footprintMap_mem h (𝒜.zeroSetInclusion x) hx
  eq_one_of_act_eq _ _ h x hx g hg hgx :=
    𝒜.eq_one_of_act_eq h (𝒜.zeroSetInclusion x) hx g hg (congrArg Subtype.val hgx)
  exists_openPartialHomeomorph I J h x hx := by
    rcases 𝒜.exists_openPartialHomeomorph h (𝒜.zeroSetInclusion x) hx with
      ⟨_, _, _, hxe, hdisj, _⟩ | ⟨n, hn, e, hxe, hbd, he⟩
    · exact (disjoint_left.1 hdisj hxe x.val.property).elim
    refine ⟨n, by omega, e.hyperplaneChart hbd x.val, ?_, fun y hy ↦ ?_⟩
    · rw [OpenPartialHomeomorph.hyperplaneChart_source]
      exact hxe
    · rw [OpenPartialHomeomorph.hyperplaneChart_source] at hy
      rw [OpenPartialHomeomorph.hyperplaneChart_apply, Prod.map_snd, id_eq]
      exact he y.val hy
  exists_footprintMap_eq y := by
    obtain ⟨I, x, hreg, hx⟩ := 𝒜.exists_footprintMap_eq y.val
    exact ⟨I,
      𝒜.zeroSetLift x (𝒜.mem_boundary_of_baseHomeomorph_footprintMap_mem x (hx ▸ y.property)),
      hreg, Subtype.ext hx⟩

/-- The base identification of the boundary atlas is that of `𝒜`, restricted to the boundary. -/
@[simp]
theorem coe_baseHomeomorph_boundaryAtlas (x : 𝒜.boundary ∅) :
    (𝒜.boundaryAtlas.baseHomeomorph x : X) = 𝒜.baseHomeomorph x :=
  (rfl)

/-- The Kuranishi maps of the boundary atlas are the restrictions of those of `𝒜`. -/
@[simp]
theorem kuranishi_boundaryAtlas (I : Finset A) (α : I) (x : 𝒜.boundary I) :
    𝒜.boundaryAtlas.kuranishi I α x = 𝒜.kuranishi I α x :=
  (rfl)

/-- The zero sets of the boundary atlas are the zero sets of `𝒜` intersected with the boundary. -/
theorem mem_kuranishiZeroSet_boundaryAtlas {I J : Finset A} {x : 𝒜.boundary J} :
    x ∈ kuranishiZeroSet 𝒜.boundaryAtlas.kuranishi I J ↔
      (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J :=
  𝒜.mem_kuranishiZeroSet_boundaryKuranishi

/-- The regular loci of the boundary atlas are the regular loci of `𝒜` intersected with the
boundary. -/
@[simp]
theorem regLocus_boundaryAtlas (I : Finset A) :
    𝒜.boundaryAtlas.regLocus I = Subtype.val ⁻¹' 𝒜.regLocus I :=
  (rfl)

/-- The footprint maps of the boundary atlas are the restrictions of those of `𝒜`. -/
@[simp]
theorem coe_footprintMap_boundaryAtlas {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryAtlas.kuranishi I J) :
    (𝒜.boundaryAtlas.footprintMap h x : T I) =
      𝒜.footprintMap h ⟨x.val, 𝒜.mem_kuranishiZeroSet_boundaryAtlas.1 x.property⟩ :=
  (rfl)

end ImplicitAtlasWithBoundary

end TauCeti
