/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Topology.ImplicitAtlas.Basic
import TauCeti.Geometry.Manifold.Boundary.Model
import TauCeti.Topology.Constructions.Basic
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

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
hyperplane `x₀ = 0`. Here `(n : ℤ) = d + m_I`, with `m_I = ∑_(α ∈ I) dim E_α`.

These atlases describe compactified moduli spaces whose codimension-one strata form a boundary,
such as the one-dimensional moduli spaces whose boundaries give the chain-level identities of
Floer theory. The specified boundary is data: `[0, 1]` with `∂X = ∅` does not satisfy the axioms
near `0`, although its topological frontier in itself is empty.

* **Restriction to the boundary** (`TauCeti.ImplicitAtlasWithBoundary.boundaryAtlas`, Pardon,
  Definition 3.2.3). The boundaries `∂X_I`, with the restricted actions, Kuranishi maps, regular
  loci and footprint maps, form an implicit atlas of virtual dimension `d - 1` on `∂X`, with the
  same groups and obstruction spaces. The half-space charts restrict to charts of the hyperplane
  `x₀ = 0` through `OpenPartialHomeomorph.subtypeCoord`, and the footprint maps of the boundary
  remain quotient maps because `∂X_J` is closed (`Topology.IsQuotientMap.of_comp_eq_comp`).
* **Boundary points have positive expected dimension**
  (`TauCeti.ImplicitAtlasWithBoundary.one_le_of_mem_boundary`): a regular chart of dimension `0`
  has empty boundary. Consequently an atlas all of whose expected dimensions `d + m_I` are at most
  `0` has empty boundary (`TauCeti.ImplicitAtlasWithBoundary.eq_empty_of_forall_le_zero`).
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
(Pardon, Definition 3.2.1). Its data and axioms are those of `TauCeti.ImplicitAtlas`, together with
closed invariant boundaries `∂X_I ⊆ X_I` (`ImplicitAtlasWithBoundary.boundary`) compatible with the
base identification and the footprint maps. In the local product model over the regular locus the
first factor is either `ℝ^n`, away from the boundary, or the Euclidean half-space
`EuclideanHalfSpace (n + 1)`, whose hyperplane `x₀ = 0` is the boundary. -/
structure ImplicitAtlasWithBoundary [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
    [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
    [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
    (ρ : ∀ α, Representation ℝ (Γ α) (E α))
    (T : Finset A → Type*) [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I))
    (X : Type*) [TopologicalSpace X] (bd : Set X) (d : ℤ) where
  /-- The identification `X_∅ ≃ₜ X` of the thickening at the empty index set. -/
  baseHomeomorph : T ∅ ≃ₜ X
  /-- The Kuranishi map `s_α : X_I → E_α`, for `α ∈ I`. -/
  kuranishi : ∀ (I : Finset A) (α : I), T I → E α
  continuous_kuranishi : ∀ (I : Finset A) (α : I), Continuous (kuranishi I α)
  /-- The Kuranishi map `s_α` is `Γ_α`-equivariant, and the other factors of `Γ_I` act trivially
  on `E_α`. -/
  kuranishi_act : ∀ (I : Finset A) (α : I) (g : (β : I) → Γ β) (x : T I),
    kuranishi I α (act I g x) = ρ α (g α) (kuranishi I α x)
  /-- The regular locus `X_I^reg ⊆ X_I`. -/
  regLocus : ∀ I : Finset A, Set (T I)
  isOpen_regLocus : ∀ I : Finset A, IsOpen (regLocus I)
  act_mem_regLocus : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I),
    x ∈ regLocus I → act I g x ∈ regLocus I
  /-- The boundary `∂X_I ⊆ X_I` of the thickening. -/
  boundary : ∀ I : Finset A, Set (T I)
  isClosed_boundary : ∀ I : Finset A, IsClosed (boundary I)
  act_mem_boundary : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I),
    x ∈ boundary I → act I g x ∈ boundary I
  /-- The base identification `X_∅ ≃ₜ X` identifies `∂X_∅` with `∂X`. -/
  boundary_empty : boundary ∅ = baseHomeomorph ⁻¹' bd
  /-- The footprint map `ψ_IJ : Z_IJ → X_I`, for `I ⊆ J`. -/
  footprintMap : ∀ ⦃I J : Finset A⦄, I ⊆ J → kuranishiZeroSet kuranishi I J → T I
  continuous_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J), Continuous (footprintMap h)
  /-- The footprint map `ψ_IJ` is equivariant, with `Γ_J` acting on `X_I` through the
  restriction `Γ_J → Γ_I`. -/
  footprintMap_act : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (g : (α : J) → Γ α)
    (x : kuranishiZeroSet kuranishi I J)
    (hx : act J g x ∈ kuranishiZeroSet kuranishi I J),
    footprintMap h ⟨act J g x, hx⟩ = act I (Finset.restrict₂ (π := Γ) h g) (footprintMap h x)
  footprintMap_self : ∀ (I : Finset A) (x : T I),
    footprintMap (subset_refl I) ⟨x, mem_kuranishiZeroSet_self kuranishi x⟩ = x
  /-- The cocycle condition `ψ_IJ ∘ ψ_JK = ψ_IK` on the common domain. -/
  footprintMap_footprintMap : ∀ ⦃I J K : Finset A⦄ (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : kuranishiZeroSet kuranishi J K)
    (hx : footprintMap hJK x ∈ kuranishiZeroSet kuranishi I J)
    (hx' : x.1 ∈ kuranishiZeroSet kuranishi I K),
    footprintMap hIJ ⟨footprintMap hJK x, hx⟩ = footprintMap (hIJ.trans hJK) ⟨x, hx'⟩
  /-- The Kuranishi maps are compatible with the footprint maps: `s_I ∘ ψ_IJ = s_I`. -/
  kuranishi_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (x : kuranishiZeroSet kuranishi I J)
    (α : I),
    kuranishi I α (footprintMap h x) = kuranishi J ⟨α, h α.2⟩ x
  /-- `ψ_IJ⁻¹(∂X_I) = Z_IJ ∩ ∂X_J`. -/
  footprintMap_mem_boundary_iff : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J), footprintMap h x ∈ boundary I ↔ x.1 ∈ boundary J
  isOpen_range_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J), IsOpen (range (footprintMap h))
  /-- `U_IJ₁ ∩ U_IJ₂ = U_I(J₁ ∪ J₂)`. -/
  range_footprintMap_inter : ∀ ⦃I J₁ J₂ : Finset A⦄ (h₁ : I ⊆ J₁) (h₂ : I ⊆ J₂),
    range (footprintMap h₁) ∩ range (footprintMap h₂) =
      range (footprintMap (h₁.trans (Finset.subset_union_left (s₂ := J₂))))
  /-- `ψ_IJ⁻¹(U_IK) = U_JK ∩ Z_IJ`. -/
  footprintMap_mem_range_iff : ∀ ⦃I J K : Finset A⦄ (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : kuranishiZeroSet kuranishi I J),
    footprintMap hIJ x ∈ range (footprintMap (hIJ.trans hJK)) ↔ x.1 ∈ range (footprintMap hJK)
  /-- The footprint map is a quotient map onto its image `U_IJ`. -/
  isQuotientMap_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J),
    IsQuotientMap (rangeFactorization (footprintMap h))
  /-- The fibres of the footprint map `ψ_IJ` are the orbits of `Γ_(J \ I)`. -/
  footprintMap_eq_footprintMap_iff : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x y : kuranishiZeroSet kuranishi I J),
    footprintMap h x = footprintMap h y ↔
      ∃ g : (α : J) → Γ α, Finset.restrict₂ (π := Γ) h g = 1 ∧ act J g x = y
  /-- `ψ_IJ⁻¹(X_I^reg) ⊆ X_J^reg`. -/
  mem_regLocus_of_footprintMap_mem : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J),
    footprintMap h x ∈ regLocus I → x.1 ∈ regLocus J
  /-- `Γ_(J \ I)` acts freely on `ψ_IJ⁻¹(X_I^reg)`. -/
  eq_one_of_act_eq : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (x : kuranishiZeroSet kuranishi I J),
    footprintMap h x ∈ regLocus I → ∀ g : (α : J) → Γ α,
      Finset.restrict₂ (π := Γ) h g = 1 → act J g x = x → g = 1
  /-- Over `ψ_IJ⁻¹(X_I^reg)`, the map `s_(J \ I) : X_J → E_(J \ I)` is locally a product
  projection, either `ℝ^n × E_(J \ I) → E_(J \ I)` on a chart missing `∂X_J`, or
  `H^n × E_(J \ I) → E_(J \ I)` for the half-space `H^n`, on a chart in which `∂X_J` is the
  hyperplane `x₀ = 0`. In both cases `(n : ℤ) = d + m_I`. -/
  exists_openPartialHomeomorph : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet kuranishi I J), footprintMap h x ∈ regLocus I →
      (∃ n : ℕ, (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
        ∃ e : OpenPartialHomeomorph (T J) (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ I)) → E α)),
          x.1 ∈ e.source ∧ Disjoint e.source (boundary J) ∧ ∀ y ∈ e.source,
            (e y).2 = fun α : ↥(J \ I) ↦ kuranishi J ⟨α.1, (Finset.mem_sdiff.1 α.2).1⟩ y) ∨
      (∃ n : ℕ, (n + 1 : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
        ∃ e : OpenPartialHomeomorph (T J) (EuclideanHalfSpace (n + 1) × ((α : ↥(J \ I)) → E α)),
          x.1 ∈ e.source ∧ (∀ y ∈ e.source, y ∈ boundary J ↔ (e y).1.1 0 = 0) ∧ ∀ y ∈ e.source,
            (e y).2 = fun α : ↥(J \ I) ↦ kuranishi J ⟨α.1, (Finset.mem_sdiff.1 α.2).1⟩ y)
  /-- The regular footprints `V_I = ψ_∅I(X_I^reg ∩ Z_∅I)` cover `X`. -/
  exists_footprintMap_eq : ∀ y : X, ∃ (I : Finset A) (x : kuranishiZeroSet kuranishi ∅ I),
    x.1 ∈ regLocus I ∧ baseHomeomorph (footprintMap (Finset.empty_subset I) x) = y

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
  baseHomeomorph := 𝒜.baseHomeomorph
  kuranishi := 𝒜.kuranishi
  continuous_kuranishi := 𝒜.continuous_kuranishi
  kuranishi_act := 𝒜.kuranishi_act
  regLocus := 𝒜.regLocus
  isOpen_regLocus := 𝒜.isOpen_regLocus
  act_mem_regLocus := 𝒜.act_mem_regLocus
  boundary _ := ∅
  isClosed_boundary _ := isClosed_empty
  act_mem_boundary _ _ _ h := h
  boundary_empty := (preimage_empty).symm
  footprintMap := 𝒜.footprintMap
  continuous_footprintMap := 𝒜.continuous_footprintMap
  footprintMap_act := 𝒜.footprintMap_act
  footprintMap_self := 𝒜.footprintMap_self
  footprintMap_footprintMap := 𝒜.footprintMap_footprintMap
  kuranishi_footprintMap := 𝒜.kuranishi_footprintMap
  footprintMap_mem_boundary_iff _ _ _ _ := Iff.rfl
  isOpen_range_footprintMap := 𝒜.isOpen_range_footprintMap
  range_footprintMap_inter := 𝒜.range_footprintMap_inter
  footprintMap_mem_range_iff := 𝒜.footprintMap_mem_range_iff
  isQuotientMap_footprintMap := 𝒜.isQuotientMap_footprintMap
  footprintMap_eq_footprintMap_iff := 𝒜.footprintMap_eq_footprintMap_iff
  mem_regLocus_of_footprintMap_mem := 𝒜.mem_regLocus_of_footprintMap_mem
  eq_one_of_act_eq := 𝒜.eq_one_of_act_eq
  exists_openPartialHomeomorph _ _ h x hx := by
    obtain ⟨n, hn, e, hxe, he⟩ := 𝒜.exists_openPartialHomeomorph h x hx
    exact Or.inl ⟨n, hn, e, hxe, disjoint_empty _, he⟩
  exists_footprintMap_eq := 𝒜.exists_footprintMap_eq

/-- The boundaries of an implicit atlas, viewed as an atlas with boundary, are empty. -/
@[simp]
theorem ImplicitAtlas.boundary_toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d)
    (I : Finset A) : 𝒜.toImplicitAtlasWithBoundary.boundary I = ∅ :=
  (rfl)

/-- An implicit atlas, viewed as an atlas with boundary, has the same Kuranishi maps. -/
@[simp]
theorem ImplicitAtlas.kuranishi_toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d) :
    𝒜.toImplicitAtlasWithBoundary.kuranishi = 𝒜.kuranishi :=
  (rfl)

/-- An implicit atlas, viewed as an atlas with boundary, has the same regular loci. -/
@[simp]
theorem ImplicitAtlas.regLocus_toImplicitAtlasWithBoundary (𝒜 : ImplicitAtlas Γ E ρ T act X d) :
    𝒜.toImplicitAtlasWithBoundary.regLocus = 𝒜.regLocus :=
  (rfl)

/-- An implicit atlas, viewed as an atlas with boundary, has the same footprint maps. -/
@[simp]
theorem ImplicitAtlas.footprintMap_toImplicitAtlasWithBoundary
    (𝒜 : ImplicitAtlas Γ E ρ T act X d) {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.toImplicitAtlasWithBoundary.kuranishi I J) :
    𝒜.toImplicitAtlasWithBoundary.footprintMap h x = 𝒜.footprintMap h ⟨x.1, by simpa using x.2⟩ :=
  (rfl)

namespace ImplicitAtlasWithBoundary

variable {bd : Set X} (𝒜 : ImplicitAtlasWithBoundary Γ E ρ T act X bd d)

/-! ### Boundary points have positive expected dimension -/

/-- A regular point of a thickening lying on its boundary has positive expected dimension: a
regular chart of dimension `0` has empty boundary. -/
theorem one_le_of_mem_boundary {I J : Finset A} (h : I ⊆ J) (x : kuranishiZeroSet 𝒜.kuranishi I J)
    (hx : 𝒜.footprintMap h x ∈ 𝒜.regLocus I) (hxb : x.1 ∈ 𝒜.boundary J) :
    1 ≤ d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) := by
  rcases 𝒜.exists_openPartialHomeomorph h x hx with ⟨_, _, _, hxe, hdisj, _⟩ | ⟨n, hn, -⟩
  · exact (disjoint_left.1 hdisj hxe hxb).elim
  · omega

include 𝒜 in
/-- An atlas with boundary all of whose expected dimensions `d + m_I` are at most `0` has empty
boundary. -/
theorem eq_empty_of_forall_le_zero
    (hd : ∀ I : Finset A, d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ≤ 0) : bd = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
  obtain ⟨I, x, hreg, hx⟩ := 𝒜.exists_footprintMap_eq y
  have hb : 𝒜.footprintMap (Finset.empty_subset I) x ∈ 𝒜.boundary ∅ := by
    rw [𝒜.boundary_empty, mem_preimage, hx]
    exact hy
  have := 𝒜.one_le_of_mem_boundary (subset_refl I) ⟨x.1, mem_kuranishiZeroSet_self _ x.1⟩
    (by rwa [𝒜.footprintMap_self]) ((𝒜.footprintMap_mem_boundary_iff _ x).1 hb)
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

private theorem mem_kuranishiZeroSet_boundaryKuranishi {I J : Finset A} {x : 𝒜.boundary J} :
    x ∈ kuranishiZeroSet 𝒜.boundaryKuranishi I J ↔
      (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J := by
  simp only [mem_kuranishiZeroSet]
  rfl

/-- The inclusion `Z_IJ ∩ ∂X_J → Z_IJ`. -/
private def zeroSetInclusion {I J : Finset A} (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    kuranishiZeroSet 𝒜.kuranishi I J :=
  ⟨x.1, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.1 x.2⟩

private theorem coe_zeroSetInclusion {I J : Finset A}
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) :
    (𝒜.zeroSetInclusion x : T J) = x.1 :=
  (rfl)

private theorem isClosedEmbedding_zeroSetInclusion {I J : Finset A} :
    IsClosedEmbedding (𝒜.zeroSetInclusion (I := I) (J := J)) := by
  have hval : IsInducing (fun x : kuranishiZeroSet 𝒜.kuranishi I J ↦ (x : T J)) :=
    IsInducing.subtypeVal
  have hcomp : IsInducing ((fun x : kuranishiZeroSet 𝒜.kuranishi I J ↦ (x : T J)) ∘
      𝒜.zeroSetInclusion) := by
    have : ((fun x : kuranishiZeroSet 𝒜.kuranishi I J ↦ (x : T J)) ∘ 𝒜.zeroSetInclusion) =
        fun x ↦ (x.1 : T J) := rfl
    rw [this]
    exact IsInducing.subtypeVal.comp IsInducing.subtypeVal
  refine ⟨⟨hval.of_comp_iff.1 hcomp, fun x y hxy ↦ Subtype.ext (Subtype.ext
    (congrArg (fun z : kuranishiZeroSet 𝒜.kuranishi I J ↦ (z : T J)) hxy))⟩, ?_⟩
  have hrange : range 𝒜.zeroSetInclusion =
      (Subtype.val : kuranishiZeroSet 𝒜.kuranishi I J → T J) ⁻¹' 𝒜.boundary J := by
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.1.2,
      fun hx ↦ ⟨⟨⟨x.1, hx⟩, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.2 x.2⟩, rfl⟩⟩
  rw [hrange]
  exact (𝒜.isClosed_boundary J).preimage continuous_subtype_val

/-- The footprint maps of the boundary thickenings. -/
private def boundaryFootprintMap {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryKuranishi I J) : 𝒜.boundary I :=
  ⟨𝒜.footprintMap h (𝒜.zeroSetInclusion x),
    (𝒜.footprintMap_mem_boundary_iff h _).2 x.1.2⟩

private theorem mem_range_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J)
    {y : 𝒜.boundary I} :
    y ∈ range (𝒜.boundaryFootprintMap h) ↔ (y : T I) ∈ range (𝒜.footprintMap h) := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨𝒜.zeroSetInclusion x, congrArg Subtype.val hx⟩, fun ⟨z, hz⟩ ↦ ?_⟩
  have hzb : z.1 ∈ 𝒜.boundary J := (𝒜.footprintMap_mem_boundary_iff h z).1 (hz ▸ y.2)
  exact ⟨⟨⟨z.1, hzb⟩, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.2 z.2⟩, Subtype.ext hz⟩

private theorem range_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J) :
    range (𝒜.boundaryFootprintMap h) = Subtype.val ⁻¹' range (𝒜.footprintMap h) :=
  Set.ext fun _ ↦ 𝒜.mem_range_boundaryFootprintMap h

/-- The footprint maps of the boundary are quotient maps onto their images. -/
private theorem isQuotientMap_boundaryFootprintMap {I J : Finset A} (h : I ⊆ J) :
    IsQuotientMap (rangeFactorization (𝒜.boundaryFootprintMap h)) := by
  refine (𝒜.isQuotientMap_footprintMap h).of_comp_eq_comp
    (j := fun y ↦ ⟨y.1.1, (𝒜.mem_range_boundaryFootprintMap h).1 y.2⟩)
    ((((𝒜.continuous_footprintMap h).comp
      𝒜.isClosedEmbedding_zeroSetInclusion.continuous).subtype_mk _).rangeFactorization)
    rangeFactorization_surjective 𝒜.isClosedEmbedding_zeroSetInclusion.isClosedMap
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun y y' hyy' ↦ Subtype.ext (Subtype.ext
      (congrArg (fun z : range (𝒜.footprintMap h) ↦ (z : T I)) hyy')))
    (funext fun _ ↦ rfl) ?_
  rintro z ⟨y, hy⟩
  have hz : 𝒜.footprintMap h z = y.1.1 := (congrArg Subtype.val hy).symm
  have hzb : z.1 ∈ 𝒜.boundary J := (𝒜.footprintMap_mem_boundary_iff h z).1 (by rw [hz]; exact y.1.2)
  exact ⟨⟨⟨z.1, hzb⟩, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.2 z.2⟩, rfl⟩

section BoundaryChart

variable {J : Finset A} {n : ℕ} {F : Type*} [TopologicalSpace F]
  {e : OpenPartialHomeomorph (T J) (EuclideanHalfSpace (n + 1) × F)}

private theorem symm_boundaryParam_mem_boundary
    (he : ∀ y ∈ e.source, y ∈ 𝒜.boundary J ↔ (e y).1.1 0 = 0)
    {z : EuclideanSpace ℝ (Fin n) × F}
    (hz : Prod.map (EuclideanHalfSpace.boundaryParam n) id z ∈ e.target) :
    e.symm (Prod.map (EuclideanHalfSpace.boundaryParam n) id z) ∈ 𝒜.boundary J :=
  (he _ (e.map_target hz)).2 (by simp [e.right_inv hz])

private theorem boundaryParam_boundaryProj_apply
    (he : ∀ y ∈ e.source, y ∈ 𝒜.boundary J ↔ (e y).1.1 0 = 0) {y : T J} (hy : y ∈ e.source)
    (hyb : y ∈ 𝒜.boundary J) :
    Prod.map (EuclideanHalfSpace.boundaryParam n) id
      (Prod.map (EuclideanHalfSpace.boundaryProj n) id (e y)) = e y := by
  refine Prod.ext ?_ rfl
  rw [Prod.map_fst, Prod.map_fst, EuclideanHalfSpace.boundaryProj_coe]
  exact EuclideanHalfSpace.boundaryParam_boundaryProj ((he _ hy).1 hyb)

variable (e)

/-- The restriction of a half-space chart of `X_J` to the boundary hyperplane `x₀ = 0`, as a chart
of `∂X_J` on `ℝ^n × F`. -/
private noncomputable def boundaryChart (x : 𝒜.boundary J)
    (he : ∀ y ∈ e.source, y ∈ 𝒜.boundary J ↔ (e y).1.1 0 = 0) :
    OpenPartialHomeomorph (𝒜.boundary J) (EuclideanSpace ℝ (Fin n) × F) :=
  e.subtypeCoord (𝒜.boundary J) ⟨x⟩ (Prod.map (EuclideanHalfSpace.boundaryParam n) id)
    (Prod.map (EuclideanHalfSpace.boundaryProj n) id)
    (𝒜.symm_boundaryParam_mem_boundary he) (𝒜.boundaryParam_boundaryProj_apply he)
    ((Function.LeftInverse.prodMap EuclideanHalfSpace.boundaryProj_boundaryParam
      fun _ ↦ rfl).leftInvOn _)
    (EuclideanHalfSpace.continuous_boundaryParam.prodMap continuous_id)
    (EuclideanHalfSpace.continuous_boundaryProj.prodMap continuous_id).continuousOn

private theorem boundaryChart_source (x : 𝒜.boundary J)
    (he : ∀ y ∈ e.source, y ∈ 𝒜.boundary J ↔ (e y).1.1 0 = 0) :
    (𝒜.boundaryChart e x he).source = Subtype.val ⁻¹' e.source := by
  unfold boundaryChart
  rw [OpenPartialHomeomorph.subtypeCoord_source]

private theorem boundaryChart_apply (x : 𝒜.boundary J)
    (he : ∀ y ∈ e.source, y ∈ 𝒜.boundary J ↔ (e y).1.1 0 = 0) (y : 𝒜.boundary J) :
    𝒜.boundaryChart e x he y = Prod.map (EuclideanHalfSpace.boundaryProj n) id (e y) := by
  unfold boundaryChart
  rw [OpenPartialHomeomorph.subtypeCoord_apply]

end BoundaryChart

/-- **The restriction of an implicit atlas with boundary to its boundary** (Pardon,
Definition 3.2.3). The boundaries `∂X_I` of the thickenings, with the restricted actions, Kuranishi
maps, regular loci and footprint maps, form an implicit atlas of virtual dimension `d - 1` on the
boundary `∂X`, with the same isotropy groups and obstruction spaces. Its product charts are the
restrictions of the half-space charts to the hyperplane `x₀ = 0`. -/
noncomputable def boundaryAtlas :
    ImplicitAtlas Γ E ρ (fun I ↦ 𝒜.boundary I) 𝒜.boundaryAct bd (d - 1) where
  baseHomeomorph := 𝒜.baseHomeomorph.sets 𝒜.boundary_empty
  kuranishi := 𝒜.boundaryKuranishi
  continuous_kuranishi I α := (𝒜.continuous_kuranishi I α).comp continuous_subtype_val
  kuranishi_act I α g x := 𝒜.kuranishi_act I α g x
  regLocus I := Subtype.val ⁻¹' 𝒜.regLocus I
  isOpen_regLocus I := (𝒜.isOpen_regLocus I).preimage continuous_subtype_val
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
    exact (𝒜.isOpen_range_footprintMap h).preimage continuous_subtype_val
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
    · exact (disjoint_left.1 hdisj hxe x.1.2).elim
    refine ⟨n, by omega, 𝒜.boundaryChart e x.1 hbd, ?_, fun y hy ↦ ?_⟩
    · rw [boundaryChart_source]
      exact hxe
    · rw [boundaryChart_source] at hy
      rw [boundaryChart_apply, Prod.map_snd, id_eq]
      exact he y.1 hy
  exists_footprintMap_eq y := by
    obtain ⟨I, x, hreg, hx⟩ := 𝒜.exists_footprintMap_eq y.1
    have hb : x.1 ∈ 𝒜.boundary I := by
      refine (𝒜.footprintMap_mem_boundary_iff (Finset.empty_subset I) x).1 ?_
      rw [𝒜.boundary_empty, mem_preimage, hx]
      exact y.2
    exact ⟨I, ⟨⟨x.1, hb⟩, 𝒜.mem_kuranishiZeroSet_boundaryKuranishi.2 x.2⟩, hreg, Subtype.ext hx⟩

/-- The base identification of the boundary atlas is that of `𝒜`, restricted to the boundary. -/
@[simp]
theorem coe_boundaryAtlas_baseHomeomorph (x : 𝒜.boundary ∅) :
    (𝒜.boundaryAtlas.baseHomeomorph x : X) = 𝒜.baseHomeomorph x :=
  (rfl)

/-- The Kuranishi maps of the boundary atlas are the restrictions of those of `𝒜`. -/
@[simp]
theorem boundaryAtlas_kuranishi (I : Finset A) (α : I) (x : 𝒜.boundary I) :
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
theorem boundaryAtlas_regLocus (I : Finset A) :
    𝒜.boundaryAtlas.regLocus I = Subtype.val ⁻¹' 𝒜.regLocus I :=
  (rfl)

/-- The footprint maps of the boundary atlas are the restrictions of those of `𝒜`. -/
@[simp]
theorem coe_boundaryAtlas_footprintMap {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.boundaryAtlas.kuranishi I J) :
    (𝒜.boundaryAtlas.footprintMap h x : T I) =
      𝒜.footprintMap h ⟨x.1, 𝒜.mem_kuranishiZeroSet_boundaryAtlas.1 x.2⟩ :=
  (rfl)

end ImplicitAtlasWithBoundary

end TauCeti
