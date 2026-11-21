/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Topology.Constructions.Basic

/-!
# Implicit atlases with boundary

An *implicit atlas with boundary* of virtual dimension `d` on a pair `(X, Y)`, with `Y ⊆ X`
closed, is the version of `TauCeti.ImplicitAtlas` in which the regular parts of the thickenings
are topological manifolds with boundary (Pardon, Definition 3.2.1). It is the structure carried by
the one-dimensional moduli spaces whose boundaries give the relations between virtual counts,
and by the cobordisms between atlases. Its data are those of an implicit atlas together with
closed invariant subsets `∂X_I ⊆ X_I` (`TauCeti.ImplicitAtlasWithBoundary.boundary`) such that

* `∂X_∅` is identified with `Y` (`TauCeti.ImplicitAtlasWithBoundary.baseHomeomorph_mem_iff`);
* `ψ_IJ⁻¹(∂X_I) = Z_IJ ∩ ∂X_J` for the footprint maps
  (`TauCeti.ImplicitAtlasWithBoundary.footprintMap_mem_boundary_iff`);

and in the local product axiom the factor `ℝ^(d + m_I)` may be replaced by a half-space
`ℝ^(d + m_I - 1) × ℝ≥0`, with `∂X_J` the points of last coordinate `0`. The axiom is stated as a
disjunction (`TauCeti.ImplicitAtlasWithBoundary.exists_openPartialHomeomorph`): near each point of
`ψ_IJ⁻¹(X_I^reg)` there is either a chart `ℝ^(d + m_I) × E_(J \ I)` missing `∂X_J`, or a
half-space chart `(ℝ^(d + m_I - 1) × ℝ≥0) × E_(J \ I)` cutting out `∂X_J`, and in both the
second component is the Kuranishi map `s_(J \ I)`. Away from dimension `0` a chart of the first
kind can be turned into one of the second, so this is Pardon's condition; in dimension `0` only
the first kind exists, so regular charts of dimension `0` have empty boundary.

The two results of this file are the following.

* **Boundaryless atlases.** An implicit atlas is an implicit atlas with empty boundary
  (`TauCeti.ImplicitAtlas.toImplicitAtlasWithBoundary`).
* **The boundary restriction** (Pardon, Definition 3.2.3). The boundaries `∂X_I`, with the
  restricted actions, Kuranishi maps, regular loci and footprint maps, form an implicit atlas of
  virtual dimension `d - 1` on `Y` with the same groups and obstruction spaces
  (`TauCeti.ImplicitAtlasWithBoundary.boundaryAtlas`). Its product charts are the half-space
  charts restricted to their boundary slices (`OpenPartialHomeomorph.subtypeCoord`), and its
  quotient axiom is the stability of quotient maps under pullback along closed maps
  (`Topology.IsQuotientMap.of_isClosedMap_of_isEmbedding`). Consequently the regular locus meets the
  boundary only where `d + m_I > 0`
  (`TauCeti.ImplicitAtlasWithBoundary.regLocus_inter_boundary_eq_empty`), and `Y` is empty if
  `d + m_I ≤ 0` for every `I` (`TauCeti.ImplicitAtlasWithBoundary.eq_empty_of_forall_nonpos`).

The example of the interval `[0, 1]`, with boundary `{0, 1}`, is in
`TauCeti.Topology.ImplicitAtlas.Examples`.

## Implementation notes

* The data and the axioms other than the boundaries and the product axiom are those of
  `TauCeti.ImplicitAtlas`: both structures extend `TauCeti.PreImplicitAtlas`, so the regular
  footprints (`TauCeti.PreImplicitAtlas.footprint`) and their basic properties apply to both.
* The boundary `Y` of the base is a parameter, a subset of `X`; the boundary restriction is an
  implicit atlas on the subtype `Y`, with thickenings the subtypes `∂X_I`.
* The half-space is modelled as `ℝⁿ × ℝ≥0` rather than as Mathlib's `EuclideanHalfSpace (n + 1)`,
  so that its boundary slice `ℝⁿ × {0}` is parametrized by `ℝⁿ` directly.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definitions 3.2.1 (implicit
  atlases with boundary) and 3.2.3 (restriction to the boundary).
-/

public section

open Set Topology

namespace TauCeti

variable {A : Type*}

/-- An **implicit atlas with boundary** of virtual dimension `d` on a pair `(X, Y)` (Pardon,
Definition 3.2.1): a pre-implicit atlas (`TauCeti.PreImplicitAtlas`) with closed invariant
boundaries `∂X_I ⊆ X_I`, identified with `Y` at `I = ∅` and compatible with the footprint maps,
satisfying the local product axiom `exists_openPartialHomeomorph`, which allows half-space charts.
See the module docstring. -/
structure ImplicitAtlasWithBoundary [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
    [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
    [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
    (ρ : ∀ α, Representation ℝ (Γ α) (E α)) (T : Finset A → Type*)
    [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (X : Type*) [TopologicalSpace X] (Y : Set X) (d : ℤ)
    extends PreImplicitAtlas Γ E ρ T act X where
  /-- The boundary `∂X_I ⊆ X_I`. -/
  boundary : ∀ I : Finset A, Set (T I)
  /-- The boundary `∂X_I` is closed in `X_I`. -/
  isClosed_boundary : ∀ I : Finset A, IsClosed (boundary I)
  /-- The boundary `∂X_I` is invariant under the action of `Γ_I`. -/
  act_mem_boundary : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I),
    x ∈ boundary I → act I g x ∈ boundary I
  /-- The boundary `∂X_∅` is identified with `Y` by `X_∅ ≃ₜ X`. -/
  baseHomeomorph_mem_iff : ∀ x : T ∅, baseHomeomorph x ∈ Y ↔ x ∈ boundary ∅
  /-- `ψ_IJ⁻¹(∂X_I) = Z_IJ ∩ ∂X_J`. -/
  footprintMap_mem_boundary_iff : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J), footprintMap h x ∈ boundary I ↔ x.val ∈ boundary J
  /-- Over `ψ_IJ⁻¹(X_I^reg)`, the map `s_(J \ I) : X_J → E_(J \ I)` is locally a product
  projection, either `ℝ^(d + m_I) × E_(J \ I) → E_(J \ I)` away from `∂X_J`, or
  `(ℝ^(d + m_I - 1) × ℝ≥0) × E_(J \ I) → E_(J \ I)` with `∂X_J` the points of last coordinate
  `0`. -/
  exists_openPartialHomeomorph : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J), footprintMap h x ∈ regLocus I →
      (∃ n : ℕ, (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
        ∃ e : OpenPartialHomeomorph (T J) (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → E α)),
          x.val ∈ e.source ∧ ∀ y ∈ e.source, y ∉ boundary J ∧
            (e y).2 = fun α : ↥(J \ I) ↦ kuranishi J ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩ y) ∨
      (∃ n : ℕ, (n : ℤ) + 1 = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
        ∃ e : OpenPartialHomeomorph (T J)
          ((EuclideanSpace ℝ (Fin n) × NNReal) × ((α : ↥(J \ I)) → E α)),
          x.val ∈ e.source ∧ ∀ y ∈ e.source, (y ∈ boundary J ↔ (e y).1.2 = 0) ∧
            (e y).2 = fun α : ↥(J \ I) ↦ kuranishi J ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩ y)

variable [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ}

/-! ### Boundaryless atlases -/

/-- An implicit atlas is an implicit atlas with empty boundary: its product charts miss the
empty boundary. -/
def ImplicitAtlas.toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d) :
    ImplicitAtlasWithBoundary Γ E ρ T act X ∅ d where
  toPreImplicitAtlas := 𝒜.toPreImplicitAtlas
  boundary _ := ∅
  isClosed_boundary _ := isClosed_empty
  act_mem_boundary _ _ _ h := h
  baseHomeomorph_mem_iff _ := Iff.rfl
  footprintMap_mem_boundary_iff _ _ _ _ := Iff.rfl
  exists_openPartialHomeomorph _ _ h x hx :=
    let ⟨n, hn, e, hxe, he⟩ := 𝒜.exists_openPartialHomeomorph h x hx
    Or.inl ⟨n, hn, e, hxe, fun y hy ↦ ⟨notMem_empty y, he y hy⟩⟩

@[simp]
theorem ImplicitAtlas.toPreImplicitAtlas_toImplicitAtlasWithBoundary
    (𝒜 : ImplicitAtlas Γ E ρ T act X d) :
    𝒜.toImplicitAtlasWithBoundary.toPreImplicitAtlas = 𝒜.toPreImplicitAtlas :=
  (rfl)

@[simp]
theorem ImplicitAtlas.boundary_toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d)
    (I : Finset A) : 𝒜.toImplicitAtlasWithBoundary.boundary I = ∅ :=
  (rfl)

@[simp]
theorem ImplicitAtlas.footprintMap_toImplicitAtlasWithBoundary
    (𝒜 : ImplicitAtlas Γ E ρ T act X d) {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.toImplicitAtlasWithBoundary.kuranishi I J) :
    𝒜.toImplicitAtlasWithBoundary.footprintMap h x =
      𝒜.footprintMap h ⟨x.val, by simpa using x.property⟩ :=
  (rfl)

namespace ImplicitAtlasWithBoundary

variable {Y : Set X} (𝒜 : ImplicitAtlasWithBoundary Γ E ρ T act X Y d)

/-! ### Basic properties of the boundary -/

/-- The boundaries `∂X_I` are invariant under `Γ_I`. -/
@[simp]
theorem act_mem_boundary_iff {I : Finset A} (g : (α : I) → Γ α) {x : T I} :
    act I g x ∈ 𝒜.boundary I ↔ x ∈ 𝒜.boundary I := by
  refine ⟨fun h ↦ ?_, 𝒜.act_mem_boundary I g x⟩
  simpa [← Homeomorph.mul_apply, ← map_mul] using 𝒜.act_mem_boundary I g⁻¹ _ h

/-- The boundary `∂X_∅` is mapped onto `Y` by the identification `X_∅ ≃ₜ X`. -/
theorem image_baseHomeomorph_boundary : 𝒜.baseHomeomorph '' 𝒜.boundary ∅ = Y := by
  ext y
  refine ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ (𝒜.baseHomeomorph_mem_iff x).2 hx, fun hy ↦ ?_⟩
  refine ⟨𝒜.baseHomeomorph.symm y, (𝒜.baseHomeomorph_mem_iff _).1 ?_, by simp⟩
  simpa using hy

include 𝒜 in
/-- The boundary `Y` of the base is closed. -/
theorem isClosed_baseBoundary : IsClosed Y :=
  𝒜.image_baseHomeomorph_boundary ▸ 𝒜.baseHomeomorph.isClosedMap _ (𝒜.isClosed_boundary ∅)

/-! ### The boundary restriction -/

/-- The action of `Γ_I` on the boundary `∂X_I`. -/
def boundaryAct (I : Finset A) : ((α : I) → Γ α) →* (𝒜.boundary I ≃ₜ 𝒜.boundary I) where
  toFun g := (act I g).subtype fun _ ↦ (𝒜.act_mem_boundary_iff g).symm
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
theorem coe_boundaryAct_apply {I : Finset A} (g : (α : I) → Γ α) (x : 𝒜.boundary I) :
    (𝒜.boundaryAct I g x : T I) = act I g x :=
  (rfl)

/-- The Kuranishi maps of the boundary restriction are the restrictions of the Kuranishi maps. -/
def boundaryKuranishi (I : Finset A) (α : I) (x : 𝒜.boundary I) : E α :=
  𝒜.kuranishi I α x

@[simp]
theorem boundaryKuranishi_apply (I : Finset A) (α : I) (x : 𝒜.boundary I) :
    𝒜.boundaryKuranishi I α x = 𝒜.kuranishi I α x :=
  (rfl)

theorem mem_kuranishiZeroSet_boundaryKuranishi {I J : Finset A} {x : 𝒜.boundary J} :
    x ∈ kuranishiZeroSet 𝒜.boundaryKuranishi I J ↔
      (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J := by
  simp [mem_kuranishiZeroSet]

/-- The point of `Z_IJ` underlying a point of the zero set of the boundary restriction. -/
def toKuranishiZeroSet {I J : Finset A} (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    kuranishiZeroSet 𝒜.kuranishi I J :=
  ⟨x.val.val, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 x.property⟩

@[simp]
theorem coe_toKuranishiZeroSet {I J : Finset A}
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    (𝒜.toKuranishiZeroSet x : T J) = x.val.val :=
  (rfl)

theorem continuous_toKuranishiZeroSet {I J : Finset A} :
    Continuous (𝒜.toKuranishiZeroSet (I := I) (J := J)) :=
  (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _

/-- The point of the zero set of the boundary restriction underlying a point of `Z_IJ` in the
boundary `∂X_J`, inverse to `toKuranishiZeroSet`. -/
def ofKuranishiZeroSet {I J : Finset A} (z : kuranishiZeroSet 𝒜.kuranishi I J)
    (hz : (z : T J) ∈ 𝒜.boundary J) : kuranishiZeroSet 𝒜.boundaryKuranishi I J :=
  ⟨⟨z.val, hz⟩, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.2 z.property⟩

@[simp]
theorem toKuranishiZeroSet_ofKuranishiZeroSet {I J : Finset A}
    (z : kuranishiZeroSet 𝒜.kuranishi I J) (hz : (z : T J) ∈ 𝒜.boundary J) :
    𝒜.toKuranishiZeroSet (𝒜.ofKuranishiZeroSet z hz) = z :=
  (rfl)

@[simp]
theorem coe_ofKuranishiZeroSet {I J : Finset A} (z : kuranishiZeroSet 𝒜.kuranishi I J)
    (hz : (z : T J) ∈ 𝒜.boundary J) : ((𝒜.ofKuranishiZeroSet z hz).val : T J) = z :=
  (rfl)

@[simp]
theorem ofKuranishiZeroSet_toKuranishiZeroSet {I J : Finset A}
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    𝒜.ofKuranishiZeroSet (𝒜.toKuranishiZeroSet x) (by simp) = x :=
  (rfl)

/-- The inclusion of the zero set of the boundary restriction into `Z_IJ` is injective. -/
theorem toKuranishiZeroSet_injective {I J : Finset A} :
    Function.Injective (𝒜.toKuranishiZeroSet (I := I) (J := J)) :=
  fun _ _ hxy ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))

/-- The footprint maps of the boundary restriction are the restrictions of the footprint maps,
which preserve the boundaries. -/
def boundaryFootprintMap {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) : 𝒜.boundary I :=
  ⟨𝒜.footprintMap h (𝒜.toKuranishiZeroSet x),
    (𝒜.footprintMap_mem_boundary_iff h _).2 x.val.property⟩

@[simp]
theorem coe_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    (𝒜.boundaryFootprintMap h x : T I) = 𝒜.footprintMap h (𝒜.toKuranishiZeroSet x) :=
  (rfl)

/-- The image of a footprint map of the boundary restriction is the part of the image of the
footprint map lying in the boundary. -/
theorem range_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J) :
    range (𝒜.boundaryFootprintMap h) = Subtype.val ⁻¹' range (𝒜.footprintMap h) := by
  ext y
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨_, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  have hxb : x.val ∈ 𝒜.boundary J := (𝒜.footprintMap_mem_boundary_iff h x).1 (hx ▸ y.property)
  exact ⟨𝒜.ofKuranishiZeroSet x hxb, Subtype.ext hx⟩

/-- The inclusion of the zero set of the boundary restriction into `Z_IJ` is a closed embedding,
with image the points of `Z_IJ` in the boundary `∂X_J`. -/
theorem isClosedEmbedding_toKuranishiZeroSet {I J : Finset A} :
    IsClosedEmbedding (𝒜.toKuranishiZeroSet (I := I) (J := J)) := by
  -- `toKuranishiZeroSet` is the corestriction of the composite of the two subtype inclusions.
  refine ⟨(IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _
    fun x ↦ (𝒜.toKuranishiZeroSet x).property, ?_⟩
  convert (𝒜.isClosed_boundary J).preimage continuous_subtypeVal using 1
  ext z
  exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ x.val.property, fun hz ↦ ⟨𝒜.ofKuranishiZeroSet z hz, rfl⟩⟩

/-- The footprint maps of the boundary restriction are quotient maps onto their images: they are
the pullbacks of the footprint maps along the closed embeddings of the boundaries. -/
theorem isQuotientMap_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J) :
    IsQuotientMap (rangeFactorization (𝒜.boundaryFootprintMap h)) := by
  -- The inclusion of the image of the restricted footprint map into the image of `ψ_IJ`.
  have hmem (y : range (𝒜.boundaryFootprintMap h)) : y.val.val ∈ range (𝒜.footprintMap h) := by
    obtain ⟨x, hx⟩ := y.property
    exact ⟨_, congrArg Subtype.val hx⟩
  let j : range (𝒜.boundaryFootprintMap h) → range (𝒜.footprintMap h) := fun y ↦ ⟨y.val.val, hmem y⟩
  -- `j` is the corestriction of the composite of the two subtype inclusions.
  have hj : IsEmbedding j :=
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _ hmem
  have hi := 𝒜.isClosedEmbedding_toKuranishiZeroSet (I := I) (J := J)
  refine (𝒜.isQuotientMap_footprintMap h).of_isClosedMap_of_isEmbedding hi.isClosedMap
    hi.continuous hj (funext fun _ ↦ rfl) ?_
  rintro z ⟨y, hy⟩
  have hz : z.val ∈ 𝒜.boundary J := by
    refine (𝒜.footprintMap_mem_boundary_iff h z).1 ?_
    have : (j y).val = 𝒜.footprintMap h z := congrArg Subtype.val hy
    exact this ▸ y.val.property
  exact ⟨𝒜.ofKuranishiZeroSet z hz, rfl⟩

/-- Over `ψ_IJ⁻¹(X_I^reg)`, the boundary `∂X_J` carries the product charts of an implicit atlas of
virtual dimension `d - 1`: the half-space charts of `X_J` restricted to their boundary slices. -/
theorem exists_openPartialHomeomorph_boundary {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J)
    (hx : 𝒜.footprintMap h (𝒜.toKuranishiZeroSet x) ∈ 𝒜.regLocus I) :
    ∃ n : ℕ, (n : ℤ) = d - 1 + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
      ∃ e : OpenPartialHomeomorph (𝒜.boundary J)
        (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → E α)),
        x.val ∈ e.source ∧ ∀ y ∈ e.source,
          (e y).2 = fun α : ↥(J \ I) ↦
            𝒜.boundaryKuranishi J ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩ y := by
  rcases 𝒜.exists_openPartialHomeomorph h (𝒜.toKuranishiZeroSet x) hx with
    ⟨n, -, e, hxe, he⟩ | ⟨n, hn, e, hxe, he⟩
  · exact ((he _ hxe).1 x.val.property).elim
  -- The boundary slice `ℝⁿ × {0}` of the half-space and its coordinate retraction.
  let ι : EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → E α) →
      (EuclideanSpace ℝ (Fin n) × NNReal) × ((α : ↥(J \ I)) → E α) := fun p ↦ ((p.1, 0), p.2)
  let π : (EuclideanSpace ℝ (Fin n) × NNReal) × ((α : ↥(J \ I)) → E α) →
      EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → E α) := fun q ↦ (q.1.1, q.2)
  have hι {z} (hz : ι z ∈ e.target) : e.symm (ι z) ∈ 𝒜.boundary J :=
    ((he _ (e.map_target hz)).1).2 (by rw [e.right_inv hz])
  have hslice {y} (hy : y ∈ e.source) (hyb : y ∈ 𝒜.boundary J) : ι (π (e y)) = e y :=
    Prod.ext (Prod.ext rfl ((he y hy).1.1 hyb).symm) rfl
  have hπι : LeftInvOn π ι (ι ⁻¹' e.target) := by
    intro z _
    rfl
  refine ⟨n, by omega, e.subtypeCoord (𝒜.boundary J) ⟨x.val⟩ ι π hι hslice hπι
    (by fun_prop) (by fun_prop), by simpa using hxe, fun y hy ↦ ?_⟩
  rw [OpenPartialHomeomorph.subtypeCoord_apply]
  exact (he y.val (by simpa using hy)).2

/-- **The boundary restriction** of an implicit atlas with boundary (Pardon, Definition 3.2.3):
the implicit atlas of virtual dimension `d - 1` on `Y` whose thickenings are the boundaries
`∂X_I`, with the restricted actions, Kuranishi maps, regular loci and footprint maps. -/
def boundaryAtlas :
    ImplicitAtlas Γ E ρ (fun I ↦ 𝒜.boundary I) 𝒜.boundaryAct Y (d - 1) where
  baseHomeomorph := 𝒜.baseHomeomorph.subtype fun x ↦ (𝒜.baseHomeomorph_mem_iff x).symm
  kuranishi := 𝒜.boundaryKuranishi
  continuous_kuranishi I α := (𝒜.continuous_kuranishi I α).comp continuous_subtypeVal
  kuranishi_act I α g x := 𝒜.kuranishi_act I α g x
  regLocus I := Subtype.val ⁻¹' 𝒜.regLocus I
  isOpen_regLocus I := (𝒜.isOpen_regLocus I).preimage continuous_subtypeVal
  act_mem_regLocus I g x hx := 𝒜.act_mem_regLocus I g x hx
  footprintMap _ _ := 𝒜.boundaryFootprintMap
  continuous_footprintMap _ _ h :=
    ((𝒜.continuous_footprintMap h).comp 𝒜.continuous_toKuranishiZeroSet).subtype_mk _
  footprintMap_act _ _ h g x hx :=
    Subtype.ext (𝒜.footprintMap_act h g (𝒜.toKuranishiZeroSet x)
      (𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 hx))
  footprintMap_self I x := Subtype.ext (𝒜.footprintMap_self I x)
  footprintMap_footprintMap _ _ _ hIJ hJK x hx hx' :=
    Subtype.ext (𝒜.footprintMap_footprintMap hIJ hJK (𝒜.toKuranishiZeroSet x)
      (𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 hx)
      (𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 hx'))
  kuranishi_footprintMap _ _ h x α := 𝒜.kuranishi_footprintMap h (𝒜.toKuranishiZeroSet x) α
  isOpen_range_footprintMap _ _ h := by
    rw [range_boundaryFootprintMap]
    exact (𝒜.isOpen_range_footprintMap h).preimage continuous_subtypeVal
  range_footprintMap_inter _ _ _ h₁ h₂ := by
    simp only [range_boundaryFootprintMap, ← preimage_inter, 𝒜.range_footprintMap_inter]
  footprintMap_mem_range_iff _ _ _ hIJ hJK x := by
    simpa [range_boundaryFootprintMap] using
      𝒜.footprintMap_mem_range_iff hIJ hJK (𝒜.toKuranishiZeroSet x)
  isQuotientMap_footprintMap _ _ h := 𝒜.isQuotientMap_boundaryFootprintMap h
  footprintMap_eq_footprintMap_iff _ _ h x y := by
    simpa [Subtype.ext_iff] using
      𝒜.footprintMap_eq_footprintMap_iff h (𝒜.toKuranishiZeroSet x) (𝒜.toKuranishiZeroSet y)
  mem_regLocus_of_footprintMap_mem _ _ h x hx :=
    𝒜.mem_regLocus_of_footprintMap_mem h (𝒜.toKuranishiZeroSet x) hx
  eq_one_of_act_eq _ _ h x hx g hg hgx :=
    𝒜.eq_one_of_act_eq h (𝒜.toKuranishiZeroSet x) hx g hg (congrArg Subtype.val hgx)
  exists_openPartialHomeomorph _ _ h x hx := 𝒜.exists_openPartialHomeomorph_boundary h x hx
  exists_footprintMap_eq y := by
    obtain ⟨I, x, hx, hxy⟩ := 𝒜.exists_footprintMap_eq y
    have hxb : x.val ∈ 𝒜.boundary I := (𝒜.footprintMap_mem_boundary_iff _ x).1 <|
      (𝒜.baseHomeomorph_mem_iff _).1 (hxy ▸ y.property)
    exact ⟨I, 𝒜.ofKuranishiZeroSet x hxb, hx, Subtype.ext hxy⟩

@[simp]
theorem coe_baseHomeomorph_boundaryAtlas (x : 𝒜.boundary ∅) :
    (𝒜.boundaryAtlas.baseHomeomorph x : X) = 𝒜.baseHomeomorph x :=
  (rfl)

@[simp]
theorem kuranishi_boundaryAtlas : 𝒜.boundaryAtlas.kuranishi = 𝒜.boundaryKuranishi :=
  (rfl)

@[simp]
theorem regLocus_boundaryAtlas (I : Finset A) :
    𝒜.boundaryAtlas.regLocus I = Subtype.val ⁻¹' 𝒜.regLocus I :=
  (rfl)

@[simp]
theorem coe_footprintMap_boundaryAtlas {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryAtlas.kuranishi I J) :
    (𝒜.boundaryAtlas.footprintMap h x : T I) =
      𝒜.footprintMap h ⟨x.val.val, by simpa using x.property⟩ :=
  (rfl)

/-- The regular footprints of the boundary restriction are the traces on `Y` of the regular
footprints: `V_I ∩ Y`, viewed in the subtype `Y`. -/
@[simp]
theorem footprint_boundaryAtlas (I : Finset A) :
    𝒜.boundaryAtlas.footprint I = Subtype.val ⁻¹' 𝒜.footprint I := by
  ext y
  simp only [PreImplicitAtlas.mem_footprint, mem_preimage]
  refine ⟨fun ⟨x, hx, hxy⟩ ↦ ⟨𝒜.toKuranishiZeroSet x, hx, congrArg Subtype.val hxy⟩,
    fun ⟨x, hx, hxy⟩ ↦ ?_⟩
  have hxb : x.val ∈ 𝒜.boundary I := (𝒜.footprintMap_mem_boundary_iff _ x).1 <|
    (𝒜.baseHomeomorph_mem_iff _).1 (hxy ▸ y.property)
  exact ⟨𝒜.ofKuranishiZeroSet x hxb, hx, Subtype.ext hxy⟩

/-- **Regular charts of dimension `0` have empty boundary.** Where the expected dimension
`d + m_I` is at most `0`, the regular locus `X_I^reg` misses the boundary `∂X_I`: there the
boundary restriction has negative expected dimension. -/
theorem regLocus_inter_boundary_eq_empty {I : Finset A}
    (hI : d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ≤ 0) :
    𝒜.regLocus I ∩ 𝒜.boundary I = ∅ := by
  refine eq_empty_of_forall_notMem fun x ⟨hx, hxb⟩ ↦ ?_
  have h := 𝒜.boundaryAtlas.regLocus_eq_empty_of_neg (I := I) (by omega)
  rw [regLocus_boundaryAtlas, eq_empty_iff_forall_notMem] at h
  exact h ⟨x, hxb⟩ hx

include 𝒜 in
/-- If the expected dimensions `d + m_I` are all at most `0`, for instance for an atlas of virtual
dimension `0` with zero obstruction spaces, the boundary `Y` is empty. -/
theorem eq_empty_of_forall_nonpos
    (hd : ∀ I : Finset A, d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ≤ 0) : Y = ∅ :=
  isEmpty_coe_sort.1 (𝒜.boundaryAtlas.isEmpty_of_forall_neg fun I ↦ by linarith [hd I])

end ImplicitAtlasWithBoundary

end TauCeti
