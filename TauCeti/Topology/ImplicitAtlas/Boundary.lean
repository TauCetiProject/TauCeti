/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Topology.ImplicitAtlas.Subthickening
import TauCeti.Geometry.Manifold.Boundary.HalfSpaceChart

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
  Definition 3.2.3). The boundaries `∂X_I` are a closed subthickening
  (`TauCeti.ImplicitAtlasWithBoundary.isClosedSubthickening_boundary`), and with the restricted
  actions, Kuranishi maps, regular loci and footprint maps
  (`TauCeti.ImplicitAtlas.Core.restrictThickening`) they form an implicit atlas of virtual
  dimension `d - 1` on `∂X`, with the same groups and obstruction spaces. The half-space charts
  restrict to charts of the hyperplane `x₀ = 0` (`OpenPartialHomeomorph.hyperplaneChart`).
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
            (e y).2 = kuranishiSdiff kuranishi I J y) ∨
      (∃ n : ℕ, (n + 1 : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
        ∃ e : OpenPartialHomeomorph (T J) (EuclideanHalfSpace (n + 1) × ((α : ↥(J \ I)) → E α)),
          x.val ∈ e.source ∧ (∀ y ∈ e.source, y ∈ boundary J ↔ (e y).1.val 0 = 0) ∧ ∀ y ∈ e.source,
            (e y).2 = kuranishiSdiff kuranishi I J y)

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

/-! ### Basic properties of the boundary -/

/-- The boundaries `∂X_I` are invariant under `Γ_I`. -/
@[simp]
theorem act_mem_boundary_iff {I : Finset A} (g : (α : I) → Γ α) {x : T I} :
    act I g x ∈ 𝒜.boundary I ↔ x ∈ 𝒜.boundary I := by
  refine ⟨fun h ↦ ?_, 𝒜.act_mem_boundary I g x⟩
  simpa [← Homeomorph.mul_apply, ← map_mul] using 𝒜.act_mem_boundary I g⁻¹ _ h

/-- The boundary `∂X_∅` is mapped onto `∂X` by the identification `X_∅ ≃ₜ X`. -/
theorem image_baseHomeomorph_boundary : 𝒜.baseHomeomorph '' 𝒜.boundary ∅ = bd := by
  rw [𝒜.boundary_empty, Homeomorph.image_preimage]

include 𝒜 in
/-- The boundary `∂X` of the base is closed. -/
theorem isClosed_baseBoundary : IsClosed bd :=
  𝒜.image_baseHomeomorph_boundary ▸ 𝒜.baseHomeomorph.isClosedMap _ (𝒜.isClosed_boundary ∅)

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

/-- **Regular charts of dimension `0` have empty boundary.** Where the expected dimension
`d + m_I` is at most `0`, the regular locus `X_I^reg` misses the boundary `∂X_I`. -/
theorem regLocus_inter_boundary_eq_empty {I : Finset A}
    (hI : d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ≤ 0) :
    𝒜.regLocus I ∩ 𝒜.boundary I = ∅ := by
  refine eq_empty_of_forall_notMem fun x ⟨hx, hxb⟩ ↦ ?_
  have := 𝒜.one_le_of_mem_boundary (subset_refl I) ⟨x, mem_kuranishiZeroSet_self _ x⟩
    (by rwa [𝒜.footprintMap_self]) hxb
  omega

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

/-- The boundaries `∂X_I` form a closed subthickening of `𝒜`: they are closed, invariant and
compatible with the footprint maps. -/
theorem isClosedSubthickening_boundary : 𝒜.toCore.IsClosedSubthickening 𝒜.boundary :=
  ⟨𝒜.isClosed_boundary, 𝒜.act_mem_boundary, 𝒜.footprintMap_mem_boundary_iff⟩

/-- **The restriction of an implicit atlas with boundary to its boundary** (Pardon,
Definition 3.2.3). The boundaries `∂X_I` of the thickenings, with the restricted actions, Kuranishi
maps, regular loci and footprint maps (`TauCeti.ImplicitAtlas.Core.restrictThickening`), form an
implicit atlas of virtual dimension `d - 1` on the boundary `∂X`, with the same isotropy groups and
obstruction spaces. Its product charts are the restrictions of the half-space charts to the
hyperplane `x₀ = 0`. -/
noncomputable def boundaryAtlas :
    ImplicitAtlas Γ E ρ (fun I ↦ 𝒜.boundary I)
      (ImplicitAtlas.restrictAct act 𝒜.boundary 𝒜.act_mem_boundary) bd (d - 1) where
  toCore := 𝒜.toCore.restrictThickening 𝒜.isClosedSubthickening_boundary bd 𝒜.boundary_empty
  exists_openPartialHomeomorph I J h x hx := by
    simp only [ImplicitAtlas.Core.regLocus_restrictThickening, mem_preimage,
      ImplicitAtlas.Core.coe_footprintMap_restrictThickening] at hx
    rcases 𝒜.exists_openPartialHomeomorph h _ hx with
      ⟨_, _, _, hxe, hdisj, _⟩ | ⟨n, hn, e, hxe, hbd, he⟩
    · exact (disjoint_left.1 hdisj hxe x.val.property).elim
    refine ⟨n, by omega, e.hyperplaneChart hbd x.val, ?_, fun y hy ↦ ?_⟩
    · rw [OpenPartialHomeomorph.hyperplaneChart_source]
      exact hxe
    · rw [OpenPartialHomeomorph.hyperplaneChart_source] at hy
      rw [OpenPartialHomeomorph.hyperplaneChart_apply, Prod.map_snd, id_eq, he y.val hy]
      ext α
      simp

/-- The base identification of the boundary atlas is that of `𝒜`, restricted to the boundary. -/
@[simp]
theorem coe_baseHomeomorph_boundaryAtlas (x : 𝒜.boundary ∅) :
    (𝒜.boundaryAtlas.baseHomeomorph x : X) = 𝒜.baseHomeomorph x :=
  ImplicitAtlas.Core.coe_baseHomeomorph_restrictThickening _ _ x

/-- The Kuranishi maps of the boundary atlas are the restrictions of those of `𝒜`. -/
@[simp]
theorem kuranishi_boundaryAtlas (I : Finset A) (α : I) (x : 𝒜.boundary I) :
    𝒜.boundaryAtlas.kuranishi I α x = 𝒜.kuranishi I α x :=
  ImplicitAtlas.Core.kuranishi_restrictThickening _ _ I α x

/-- The zero sets of the boundary atlas are the zero sets of `𝒜` intersected with the boundary. -/
theorem mem_kuranishiZeroSet_boundaryAtlas {I J : Finset A} {x : 𝒜.boundary J} :
    x ∈ kuranishiZeroSet 𝒜.boundaryAtlas.kuranishi I J ↔
      (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J :=
  ImplicitAtlas.Core.mem_kuranishiZeroSet_restrictThickening _ _

/-- The regular loci of the boundary atlas are the regular loci of `𝒜` intersected with the
boundary. -/
@[simp]
theorem regLocus_boundaryAtlas (I : Finset A) :
    𝒜.boundaryAtlas.regLocus I = Subtype.val ⁻¹' 𝒜.regLocus I :=
  ImplicitAtlas.Core.regLocus_restrictThickening _ _ I

/-- The footprint maps of the boundary atlas are the restrictions of those of `𝒜`. -/
@[simp]
theorem coe_footprintMap_boundaryAtlas {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryAtlas.kuranishi I J) :
    (𝒜.boundaryAtlas.footprintMap h x : T I) =
      𝒜.footprintMap h ⟨x.val, 𝒜.mem_kuranishiZeroSet_boundaryAtlas.1 x.property⟩ :=
  ImplicitAtlas.Core.coe_footprintMap_restrictThickening _ _ h x

/-- The regular footprints of the boundary atlas are the traces on `∂X` of the regular footprints
of `𝒜`: `V_I ∩ ∂X`, viewed in the subtype `∂X`. -/
@[simp]
theorem footprint_boundaryAtlas (I : Finset A) :
    𝒜.boundaryAtlas.footprint I = Subtype.val ⁻¹' 𝒜.footprint I :=
  ImplicitAtlas.Core.footprint_restrictThickening _ _ I

end ImplicitAtlasWithBoundary

end TauCeti
