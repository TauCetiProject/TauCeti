/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Data.Set.Restrict
import TauCeti.Geometry.Manifold.Boundary.Charts
import TauCeti.Geometry.Manifold.Instances.Icc.Boundary
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Cell-like stratifications

A *stratification* of a topological space `X` by a poset `S` (Pardon, Definition 6.1.1) is a map
`σ : X → S` for which every closed stratum `X^≤s = σ⁻¹(Iic s)` is closed
(`TauCeti.IsStratification`). For a finite poset the open-boundary strata `X^<s = σ⁻¹(Iio s)`,
and more generally the preimages of all lower sets, are closed as well
(`TauCeti.IsStratification.isClosed_preimage`), so a stratification by a finite poset is a
continuous map to `S` with the upper set topology (`TauCeti.isStratification_iff_continuous`).
Stratifications pull back along continuous maps (`TauCeti.IsStratification.comp`).

A stratification with a dimension function `dim : S → ℤ` is *cell-like* (Pardon, Definition 6.1.2)
when every pair `(X^≤s, X^<s)` is a topological manifold with boundary of dimension `dim s`: every
closed stratum is a manifold whose boundary is exactly the union of the strata below it. The notion
of such a pair is `TauCeti.IsManifoldBoundaryPair Y B n`: every point of `Y` has a chart of `Y`,
either onto an open subset of `ℝⁿ` missing `B`, or into the half-space `{x ∈ ℝⁿ | 0 ≤ x₀}`
reading `B` as the hyperplane `x₀ = 0`. Its dimension is an integer, and a negative dimension
forces `Y` to be empty (`TauCeti.IsManifoldBoundaryPair.eq_empty_of_neg`); points of `B` force
dimension at least one (`TauCeti.IsManifoldBoundaryPair.one_le_of_mem`). The condition on a part `U`
of `X`, such as the regular locus of a thickening of an implicit atlas, is
`TauCeti.IsCellLikeOn σ U dim`, and `TauCeti.IsCellLike σ dim` is the cell-like stratification of
the whole space.

Cell-like stratifications describe compact spaces with corners, such as the compactified moduli
spaces of the comparison families in Floer theory, whose boundaries are unions of products of
smaller moduli spaces. A consequence of cell-likeness is that a point lying strictly below a
stratum `t` is a boundary point of `X^≤t`, so `dim t ≥ 1`
(`TauCeti.IsCellLikeOn.one_le_of_lt`).

A manifold with boundary contained in a subspace is one in the subspace
(`TauCeti.IsManifoldBoundaryPair.preimage_subtypeVal`). Stratifications and cell-like
stratifications restrict to the preimage `σ⁻¹(L)` of a lower set `L`, stratified by `L`
(`TauCeti.IsStratification.restrictPreimage`, `TauCeti.IsCellLike.restrictPreimage`), since the
closed strata of the elements of `L` lie in `σ⁻¹(L)`. A chart with values in a product `F × G`
that reads a subset `P` as `Y × G`, for a manifold with boundary `(Y, B)` in `F`, gives charts of
`P` as a manifold with boundary times `G`
(`TauCeti.IsManifoldBoundaryPair.exists_openPartialHomeomorph_prod`); this is how the local product
models of a cell-like stratified implicit atlas restrict to its closed strata.

The interval `[0, 1]` stratified by its two endpoints and its interior, with dimensions `0`, `0`
and `1`, is cell-like (`TauCeti.isCellLike_unitIntervalStratum`). The strata are indexed by the
subsets of `Bool`, the endpoint `0` by `{false}`, the endpoint `1` by `{true}` and the interior by
`{false, true}`, with dimension one less than the cardinality.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definitions 6.1.1 and 6.1.2.
-/

public section

open Set Topology

open scoped Manifold

namespace TauCeti

variable {X S : Type*} [TopologicalSpace X]

/-! ### Stratifications by a poset -/

section Stratification

variable [Preorder S]

/-- A **stratification** of `X` by a poset `S` (Pardon, Definition 6.1.1): a map `σ : X → S` all
of whose closed strata `X^≤s = σ⁻¹(Iic s)` are closed. -/
def IsStratification (σ : X → S) : Prop :=
  ∀ s, IsClosed (σ ⁻¹' Iic s)

theorem isStratification_iff {σ : X → S} : IsStratification σ ↔ ∀ s, IsClosed (σ ⁻¹' Iic s) :=
  Iff.rfl

/-- A stratification pulls back along a continuous map. -/
theorem IsStratification.comp {Y : Type*} [TopologicalSpace Y] {σ : X → S}
    (hσ : IsStratification σ) {f : Y → X} (hf : Continuous f) : IsStratification (σ ∘ f) :=
  fun s ↦ (hσ s).preimage hf

/-- A constant map is a stratification. -/
theorem isStratification_const (s₀ : S) : IsStratification fun _ : X ↦ s₀ :=
  fun _ ↦ isClosed_const

/-- For a stratification by a finite poset, the preimage of every lower set is closed: it is the
finite union of the closed strata `X^≤s` of its elements. -/
theorem IsStratification.isClosed_preimage [Finite S] {σ : X → S} (hσ : IsStratification σ)
    {L : Set S} (hL : IsLowerSet L) : IsClosed (σ ⁻¹' L) := by
  rw [← hL.lowerClosure, coe_lowerClosure, preimage_iUnion₂]
  exact (toFinite L).isClosed_biUnion fun s _ ↦ hσ s

/-- For a stratification by a finite poset, the open-boundary strata `X^<s = σ⁻¹(Iio s)` are
closed. -/
theorem IsStratification.isClosed_preimage_Iio [Finite S] {σ : X → S} (hσ : IsStratification σ)
    (s : S) : IsClosed (σ ⁻¹' Iio s) :=
  hσ.isClosed_preimage (IsLowerSet.Iio s)

/-- For a finite poset, a stratification is exactly a continuous map to `S` with the upper set
topology (`Topology.WithUpperSet`), whose closed sets are the lower sets. -/
theorem isStratification_iff_continuous [Finite S] {σ : X → S} :
    IsStratification σ ↔ Continuous (WithUpperSet.toUpperSet ∘ σ) := by
  refine ⟨fun hσ ↦ continuous_iff_isClosed.2 fun L hL ↦ ?_, fun h s ↦ ?_⟩
  · exact hσ.isClosed_preimage
      ((Topology.IsUpperSet.isClosed_iff_isLower (α := WithUpperSet S)).1 hL)
  · exact ((Topology.IsUpperSet.isClosed_iff_isLower (α := WithUpperSet S)).2
      (IsLowerSet.Iic (WithUpperSet.toUpperSet s))).preimage h

end Stratification

/-! ### Topological manifolds with boundary inside a space -/

section ManifoldBoundaryPair

/-- The pair `(Y, B)` of subsets of `X` is a **topological manifold with boundary** of dimension
`n`, with boundary `B`: `B ⊆ Y`, and every point of `Y` has a chart of the subspace `Y` that is
either a chart onto an open subset of `ℝⁿ` missing `B`, or a chart into the half-space
`EuclideanHalfSpace n` in which `B` is the hyperplane `x₀ = 0`. A negative `n` admits no chart, so
it forces `Y` to be empty. -/
def IsManifoldBoundaryPair (Y B : Set X) (n : ℤ) : Prop :=
  B ⊆ Y ∧ ∀ y (hy : y ∈ Y),
    (∃ m : ℕ, (m : ℤ) = n ∧ ∃ e : OpenPartialHomeomorph Y (EuclideanSpace ℝ (Fin m)),
      ⟨y, hy⟩ ∈ e.source ∧ ∀ z ∈ e.source, (z : X) ∉ B) ∨
    (∃ m : ℕ, (m + 1 : ℤ) = n ∧ ∃ e : OpenPartialHomeomorph Y (EuclideanHalfSpace (m + 1)),
      ⟨y, hy⟩ ∈ e.source ∧ ∀ z ∈ e.source, (z : X) ∈ B ↔ (e z).val 0 = 0)

theorem isManifoldBoundaryPair_iff {Y B : Set X} {n : ℤ} :
    IsManifoldBoundaryPair Y B n ↔ B ⊆ Y ∧ ∀ y (hy : y ∈ Y),
      (∃ m : ℕ, (m : ℤ) = n ∧ ∃ e : OpenPartialHomeomorph Y (EuclideanSpace ℝ (Fin m)),
        ⟨y, hy⟩ ∈ e.source ∧ ∀ z ∈ e.source, (z : X) ∉ B) ∨
      (∃ m : ℕ, (m + 1 : ℤ) = n ∧ ∃ e : OpenPartialHomeomorph Y (EuclideanHalfSpace (m + 1)),
        ⟨y, hy⟩ ∈ e.source ∧ ∀ z ∈ e.source, (z : X) ∈ B ↔ (e z).val 0 = 0) :=
  Iff.rfl

namespace IsManifoldBoundaryPair

variable {Y B : Set X} {n : ℤ}

theorem subset (h : IsManifoldBoundaryPair Y B n) : B ⊆ Y :=
  h.1

/-- A manifold with boundary has nonnegative dimension at each of its points. -/
theorem nonneg (h : IsManifoldBoundaryPair Y B n) {y : X} (hy : y ∈ Y) : 0 ≤ n := by
  rcases h.2 y hy with ⟨m, hm, -⟩ | ⟨m, hm, -⟩ <;> omega

/-- A manifold with boundary of negative dimension is empty. -/
theorem eq_empty_of_neg (h : IsManifoldBoundaryPair Y B n) (hn : n < 0) : Y = ∅ :=
  eq_empty_of_forall_notMem fun _ hy ↦ (h.nonneg hy).not_gt hn

/-- A boundary point of a manifold with boundary forces dimension at least one: a chart of
dimension `0` is a chart onto `ℝ⁰`, missing the boundary. -/
theorem one_le_of_mem (h : IsManifoldBoundaryPair Y B n) {y : X} (hyB : y ∈ B) : 1 ≤ n := by
  rcases h.2 y (h.1 hyB) with ⟨m, -, e, hye, hB⟩ | ⟨m, hm, -⟩
  · exact (hB _ hye hyB).elim
  · omega

/-- A manifold with boundary of dimension at most `0` has empty boundary. -/
theorem boundary_eq_empty_of_nonpos (h : IsManifoldBoundaryPair Y B n) (hn : n ≤ 0) : B = ∅ :=
  eq_empty_of_forall_notMem fun _ hyB ↦ by
    have := h.one_le_of_mem hyB
    omega

end IsManifoldBoundaryPair

/-- A manifold with boundary `(Y, B)` contained in a subset `Z` of `X` is a manifold with boundary
of the same dimension in the subspace `Z`. -/
theorem IsManifoldBoundaryPair.preimage_subtypeVal {Y B Z : Set X} {n : ℤ}
    (h : IsManifoldBoundaryPair Y B n) (hYZ : Y ⊆ Z) :
    IsManifoldBoundaryPair (Subtype.val ⁻¹' Y : Set Z) (Subtype.val ⁻¹' B) n := by
  -- Read the charts of the subspace `Y` of `X` on the subspace `Y` of `Z`.
  let φ := Homeomorph.Set.preimageVal hYZ
  refine ⟨fun y hy ↦ h.1 hy, fun y hy ↦ ?_⟩
  rcases h.2 y.val hy with ⟨m, hm, c, hyc, hcB⟩ | ⟨m, hm, c, hyc, hcB⟩ <;> [left; right] <;>
    exact ⟨m, hm, φ.toOpenPartialHomeomorph.trans c, by simpa [φ] using hyc,
      fun z hz ↦ by simpa [φ] using hcB (φ z) (by simpa using hz)⟩

/-- The empty set is a manifold with empty boundary in every dimension. -/
theorem isManifoldBoundaryPair_empty (n : ℤ) : IsManifoldBoundaryPair (∅ : Set X) ∅ n :=
  ⟨empty_subset _, fun _ hy ↦ (notMem_empty _ hy).elim⟩

/-- A point is a manifold of dimension `0` with empty boundary. -/
theorem isManifoldBoundaryPair_singleton (x : X) : IsManifoldBoundaryPair {x} ∅ 0 :=
  ⟨empty_subset _, fun _ _ ↦ Or.inl ⟨0, rfl,
    (Homeomorph.homeomorphOfUnique ({x} : Set X)
      (EuclideanSpace ℝ (Fin 0))).toOpenPartialHomeomorph, by simp, fun _ _ h ↦ h⟩⟩

/-- A charted space on the half-space `EuclideanHalfSpace (n + 1)` is a manifold with boundary of
dimension `n + 1`, whose boundary is its manifold boundary. -/
theorem isManifoldBoundaryPair_univ_boundary (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] :
    IsManifoldBoundaryPair (univ : Set M) ((𝓡∂ (n + 1)).boundary M) (n + 1) := by
  refine ⟨subset_univ _, fun y _ ↦ Or.inr ⟨n, rfl,
    (Homeomorph.Set.univ M).toOpenPartialHomeomorph.trans (chartAt _ y), ?_, fun z hz ↦ ?_⟩⟩
  · simp
  · have hz' : (z : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source := by simpa using hz
    simpa using ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hz'

/-- **Product charts read a manifold with boundary in their first factor.** Let `e` be a chart of
`M` with values in `F × G`, and let `(Y, B)` be a manifold with boundary of dimension `n` in `F`.
Let `P` and `Q` be the subsets of `M` that `e` reads in `Y × G` and in `B × G`. Then every point of
`P` in the source of `e` has a chart of the subspace `P` inside the source of `e`, with values
either in `ℝⁿ × G` and missing `Q`, or in `EuclideanHalfSpace n × G` and reading `Q` as the
hyperplane `x₀ = 0`, whose second coordinate is that of `e`. -/
theorem IsManifoldBoundaryPair.exists_openPartialHomeomorph_prod {M F G : Type*}
    [TopologicalSpace M] [TopologicalSpace F] [TopologicalSpace G] {Y B : Set F} {n : ℤ}
    (hYB : IsManifoldBoundaryPair Y B n) (e : OpenPartialHomeomorph M (F × G)) {P Q : Set M}
    (hP : ∀ y ∈ e.source, y ∈ P ↔ (e y).1 ∈ Y) (hQ : ∀ y ∈ e.source, y ∈ Q ↔ (e y).1 ∈ B)
    {x : M} (hxe : x ∈ e.source) (hxP : x ∈ P) :
    (∃ m : ℕ, (m : ℤ) = n ∧ ∃ c : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin m) × G),
      ⟨x, hxP⟩ ∈ c.source ∧ c.source ⊆ Subtype.val ⁻¹' e.source ∧
        Disjoint c.source (Subtype.val ⁻¹' Q) ∧ ∀ y ∈ c.source, (c y).2 = (e y).2) ∨
    (∃ m : ℕ, (m + 1 : ℤ) = n ∧ ∃ c : OpenPartialHomeomorph P (EuclideanHalfSpace (m + 1) × G),
      ⟨x, hxP⟩ ∈ c.source ∧ c.source ⊆ Subtype.val ⁻¹' e.source ∧
        (∀ y ∈ c.source, (y : M) ∈ Q ↔ (c y).1.val 0 = 0) ∧ ∀ y ∈ c.source, (c y).2 = (e y).2) := by
  -- Restrict `e` to a chart of `P` with values in `Y × G`, then compose with a chart `c` of
  -- `(Y, B)` in the first factor.
  have hY : (e x).1 ∈ Y := (hP x hxe).1 hxP
  have : Nonempty P := ⟨⟨x, hxP⟩⟩
  have : Nonempty Y := ⟨⟨_, hY⟩⟩
  rcases hYB.2 _ hY with ⟨m, hm, c, hcx, hcB⟩ | ⟨m, hm, c, hcx, hcB⟩
  · have hsrc (y : P) := e.mem_subtypeFst_trans_prod_refl_source hP c (y := y)
    have happ (y : P) := e.subtypeFst_trans_prod_refl_apply hP c (y := y)
    refine Or.inl ⟨m, hm, _, (hsrc _).2 ⟨hxe, hcx⟩, fun y hy ↦ ((hsrc y).1 hy).1,
      disjoint_left.2 fun y hy hyQ ↦ ?_, fun y hy ↦ ?_⟩
    · obtain ⟨hy', hcy⟩ := (hsrc y).1 hy
      exact hcB _ hcy ((hQ _ hy').1 hyQ)
    · rw [happ y ((hsrc y).1 hy).1]
  · have hsrc (y : P) := e.mem_subtypeFst_trans_prod_refl_source hP c (y := y)
    have happ (y : P) := e.subtypeFst_trans_prod_refl_apply hP c (y := y)
    refine Or.inr ⟨m, hm, _, (hsrc _).2 ⟨hxe, hcx⟩, fun y hy ↦ ((hsrc y).1 hy).1, fun y hy ↦ ?_,
      fun y hy ↦ ?_⟩
    · obtain ⟨hy', hcy⟩ := (hsrc y).1 hy
      rw [happ y hy', hQ _ hy']
      exact hcB _ hcy
    · rw [happ y ((hsrc y).1 hy).1]

end ManifoldBoundaryPair

/-! ### Cell-like stratifications -/

section CellLike

variable [Preorder S]

/-- The stratification `σ` is **cell-like on** a part `U` of `X`, with dimension function `dim`:
for every `s`, the pair `(U ∩ X^≤s, U ∩ X^<s)` is a topological manifold with boundary of dimension
`dim s`. -/
def IsCellLikeOn (σ : X → S) (U : Set X) (dim : S → ℤ) : Prop :=
  ∀ s, IsManifoldBoundaryPair (U ∩ σ ⁻¹' Iic s) (U ∩ σ ⁻¹' Iio s) (dim s)

/-- A **cell-like stratification** of `X` by a poset `S` with dimension function `dim` (Pardon,
Definition 6.1.2): a stratification `σ` whose closed strata `X^≤s` are topological manifolds with
boundary `X^<s` of dimension `dim s`. -/
def IsCellLike (σ : X → S) (dim : S → ℤ) : Prop :=
  IsStratification σ ∧ IsCellLikeOn σ univ dim

theorem isCellLikeOn_iff {σ : X → S} {U : Set X} {dim : S → ℤ} :
    IsCellLikeOn σ U dim ↔
      ∀ s, IsManifoldBoundaryPair (U ∩ σ ⁻¹' Iic s) (U ∩ σ ⁻¹' Iio s) (dim s) :=
  Iff.rfl

theorem isCellLike_iff {σ : X → S} {dim : S → ℤ} :
    IsCellLike σ dim ↔ IsStratification σ ∧ IsCellLikeOn σ univ dim :=
  Iff.rfl

namespace IsCellLikeOn

variable {σ : X → S} {U : Set X} {dim : S → ℤ}

/-- A cell-like stratification has nonnegative dimension at the stratum of each point. -/
theorem nonneg (h : IsCellLikeOn σ U dim) {x : X} (hx : x ∈ U) : 0 ≤ dim (σ x) :=
  (h (σ x)).nonneg ⟨hx, mem_Iic.2 le_rfl⟩

/-- In a cell-like stratification, a stratum of negative dimension has empty closure in `U`. -/
theorem inter_preimage_Iic_eq_empty (h : IsCellLikeOn σ U dim) {s : S} (hs : dim s < 0) :
    U ∩ σ ⁻¹' Iic s = ∅ :=
  (h s).eq_empty_of_neg hs

/-- In a cell-like stratification, a point lying strictly below the stratum `t` is a boundary
point of the closed stratum `X^≤t`, so `t` has dimension at least one. -/
theorem one_le_of_lt (h : IsCellLikeOn σ U dim) {x : X} (hx : x ∈ U) {t : S} (ht : σ x < t) :
    1 ≤ dim t :=
  (h t).one_le_of_mem ⟨hx, ht⟩

end IsCellLikeOn

namespace IsCellLike

variable {σ : X → S} {dim : S → ℤ}

theorem isStratification (h : IsCellLike σ dim) : IsStratification σ :=
  h.1

theorem isCellLikeOn_univ (h : IsCellLike σ dim) : IsCellLikeOn σ univ dim :=
  h.2

/-- In a cell-like stratification, the closed stratum `X^≤s` is a topological manifold with
boundary `X^<s` of dimension `dim s`. -/
theorem isManifoldBoundaryPair (h : IsCellLike σ dim) (s : S) :
    IsManifoldBoundaryPair (σ ⁻¹' Iic s) (σ ⁻¹' Iio s) (dim s) := by
  simpa using h.2 s

end IsCellLike

/-! ### Restriction to the preimage of a lower set -/

section RestrictPreimage

variable {σ : X → S} {L : Set S}

/-- A stratification restricts to a stratification of the preimage `σ⁻¹(L)` of a set `L` by `L`. -/
theorem IsStratification.restrictPreimage (hσ : IsStratification σ) (L : Set S) :
    IsStratification (L.restrictPreimage σ) := fun t ↦ by
  rw [preimage_restrictPreimage_Iic]
  exact (hσ t).preimage continuous_subtypeVal

/-- A stratification cell-like on `U` restricts to one cell-like on the part of `U` in the
preimage `σ⁻¹(L)` of a lower set `L`, stratified by `L`: the closed strata of the elements of `L`
lie in `σ⁻¹(L)`. -/
theorem IsCellLikeOn.restrictPreimage {U : Set X} {dim : S → ℤ} (h : IsCellLikeOn σ U dim)
    (hL : IsLowerSet L) :
    IsCellLikeOn (L.restrictPreimage σ) (Subtype.val ⁻¹' U) fun t ↦ dim t := fun t ↦ by
  rw [preimage_restrictPreimage_Iic, preimage_restrictPreimage_Iio, ← preimage_inter,
    ← preimage_inter]
  exact (h t).preimage_subtypeVal fun x hx ↦ hL hx.2 t.property

/-- A cell-like stratification restricts to a cell-like stratification of the preimage `σ⁻¹(L)` of
a lower set `L`, stratified by `L`. -/
theorem IsCellLike.restrictPreimage {dim : S → ℤ} (h : IsCellLike σ dim) (hL : IsLowerSet L) :
    IsCellLike (L.restrictPreimage σ) fun t ↦ dim t :=
  ⟨h.isStratification.restrictPreimage L, by
    simpa using h.isCellLikeOn_univ.restrictPreimage hL⟩

end RestrictPreimage

end CellLike

/-! ### The interval -/

section UnitInterval

/-- The stratification of the interval `[0, 1]` by its endpoints and its interior, indexed by the
subsets of `Bool`: a point lies in the stratum `{b | if b then 0 < x else x < 1}`, which is
`{false}` at `0`, `{true}` at `1` and `{false, true}` in the interior. -/
def unitIntervalStratum (x : unitInterval) : Set Bool :=
  {b | if b then 0 < x else x < 1}

@[simp]
theorem mem_unitIntervalStratum {x : unitInterval} {b : Bool} :
    b ∈ unitIntervalStratum x ↔ if b then 0 < x else x < 1 :=
  Iff.rfl

@[simp]
theorem unitIntervalStratum_zero : unitIntervalStratum 0 = {false} := by
  ext b
  cases b <;> simp

@[simp]
theorem unitIntervalStratum_one : unitIntervalStratum 1 = {true} := by
  ext b
  cases b <;> simp

theorem unitIntervalStratum_of_ne {x : unitInterval} (h₀ : x ≠ 0) (h₁ : x ≠ 1) :
    unitIntervalStratum x = univ := by
  ext b
  cases b <;> simp [unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one, h₀, h₁]

/-- Every point of the interval is an endpoint, or an interior point with stratum `univ`. -/
private theorem unitIntervalStratum_cases (x : unitInterval) :
    x = 0 ∨ x = 1 ∨ (x ≠ 0 ∧ x ≠ 1 ∧ unitIntervalStratum x = univ) := by
  by_cases h₀ : x = 0
  · exact Or.inl h₀
  by_cases h₁ : x = 1
  · exact Or.inr (Or.inl h₁)
  exact Or.inr (Or.inr ⟨h₀, h₁, unitIntervalStratum_of_ne h₀ h₁⟩)

/-- The closed stratum of the interior of the interval is the whole interval. -/
theorem preimage_unitIntervalStratum_Iic_univ : unitIntervalStratum ⁻¹' Iic univ = univ :=
  eq_univ_of_forall fun _ ↦ subset_univ _

/-- The open-boundary stratum of the interior of the interval is the pair of endpoints. -/
theorem preimage_unitIntervalStratum_Iio_univ : unitIntervalStratum ⁻¹' Iio univ = {0, 1} := by
  ext x
  rcases unitIntervalStratum_cases x with rfl | rfl | ⟨h₀, h₁, h⟩
  · simp [lt_iff_le_and_ne, Set.ext_iff]
  · simp [lt_iff_le_and_ne, Set.ext_iff]
  · simp [h₀, h₁, h]

/-- The closed stratum of the endpoint `0` is `{0}`. -/
theorem preimage_unitIntervalStratum_Iic_false : unitIntervalStratum ⁻¹' Iic {false} = {0} := by
  ext x
  rcases unitIntervalStratum_cases x with rfl | rfl | ⟨h₀, -, h⟩
  · simp
  · simp
  · simp [h₀, h]

/-- The closed stratum of the endpoint `1` is `{1}`. -/
theorem preimage_unitIntervalStratum_Iic_true : unitIntervalStratum ⁻¹' Iic {true} = {1} := by
  ext x
  rcases unitIntervalStratum_cases x with rfl | rfl | ⟨-, h₁, h⟩
  · simp
  · simp
  · simp [h₁, h]

/-- The open-boundary stratum of the endpoint `0` is empty. -/
theorem preimage_unitIntervalStratum_Iio_false : unitIntervalStratum ⁻¹' Iio {false} = ∅ := by
  ext x
  rcases unitIntervalStratum_cases x with rfl | rfl | ⟨-, -, h⟩
  · simp
  · simp [lt_iff_le_and_ne, Set.ext_iff]
  · simp [h, lt_iff_le_and_ne, Set.ext_iff]

/-- The open-boundary stratum of the endpoint `1` is empty. -/
theorem preimage_unitIntervalStratum_Iio_true : unitIntervalStratum ⁻¹' Iio {true} = ∅ := by
  ext x
  rcases unitIntervalStratum_cases x with rfl | rfl | ⟨-, -, h⟩
  · simp [lt_iff_le_and_ne, Set.ext_iff]
  · simp
  · simp [h, lt_iff_le_and_ne, Set.ext_iff]

/-- No point of the interval lies in the empty stratum. -/
theorem preimage_unitIntervalStratum_Iic_empty : unitIntervalStratum ⁻¹' Iic ∅ = ∅ := by
  ext x
  rcases unitIntervalStratum_cases x with rfl | rfl | ⟨-, -, h⟩
  · simp
  · simp
  · simp [h]

/-- **The interval is cell-like.** The stratification of `[0, 1]` by `{0} < (0, 1) > {1}`,
indexed by the subsets of `Bool` with dimension one less than their cardinality, is cell-like: the
endpoints are manifolds of dimension `0`, and `[0, 1]` is a manifold of dimension `1` with
boundary `{0, 1}`. -/
theorem isCellLike_unitIntervalStratum :
    IsCellLike unitIntervalStratum fun P : Set Bool ↦ (P.ncard : ℤ) - 1 := by
  -- A subset of `Bool` is `∅`, `{false}`, `{true}` or `{false, true} = univ`.
  have hP (P : Set Bool) := subset_pair_iff_eq.mp (Bool.univ_eq ▸ subset_univ P)
  refine ⟨fun P ↦ ?_, fun P ↦ ?_⟩
  · rcases hP P with rfl | rfl | rfl | rfl
    · rw [preimage_unitIntervalStratum_Iic_empty]
      exact isClosed_empty
    · rw [preimage_unitIntervalStratum_Iic_false]
      exact isClosed_singleton
    · rw [preimage_unitIntervalStratum_Iic_true]
      exact isClosed_singleton
    · rw [← Bool.univ_eq, preimage_unitIntervalStratum_Iic_univ]
      exact isClosed_univ
  · rw [univ_inter, univ_inter]
    rcases hP P with rfl | rfl | rfl | rfl
    -- `∅` is the bottom element of `Set Bool`, so nothing lies strictly below it.
    · rw [preimage_unitIntervalStratum_Iic_empty, show Iio (∅ : Set Bool) = ∅ from Iio_bot,
        preimage_empty]
      exact isManifoldBoundaryPair_empty _
    · rw [preimage_unitIntervalStratum_Iic_false, preimage_unitIntervalStratum_Iio_false]
      simpa using isManifoldBoundaryPair_singleton (0 : unitInterval)
    · rw [preimage_unitIntervalStratum_Iic_true, preimage_unitIntervalStratum_Iio_true]
      simpa using isManifoldBoundaryPair_singleton (1 : unitInterval)
    · rw [← Bool.univ_eq, preimage_unitIntervalStratum_Iic_univ,
        preimage_unitIntervalStratum_Iio_univ]
      convert isManifoldBoundaryPair_univ_boundary 0 unitInterval using 1
      · exact boundary_unitInterval.symm
      · simp

end UnitInterval

end TauCeti
