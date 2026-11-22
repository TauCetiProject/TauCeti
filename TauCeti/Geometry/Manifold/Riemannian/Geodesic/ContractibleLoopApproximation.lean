/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoopApproximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.VertexSlide
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Topology.Homotopy.Homotopic.PathComponent

/-!
# Approximating compact families of contractible loops by broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r > 0` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. Abouzaid's
finite-dimensional approximation of the free loop space `𝓛M` uses the distance cuts
`𝓛ⁿM = {q ∈ Mⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δᵢ}` for cut-offs `δᵢ < r`, the maps `geoⁿ : 𝓛ⁿM → 𝓛M` to the
closed broken geodesics through their vertices, and the sampling maps `evₙ₊₁` of free loops at
`n + 1` equally spaced times. This file restricts the approximation to the component `𝓛₀M` of
contractible free loops (`TauCeti.MooreFreeLoopSpace.contractibleLoops`), the loop space on which
the constant loops `M → 𝓛₀M` and the based path fibration over the constant loop live.

The **contractible distance cut** `𝓛ⁿ₀M` is the set of tuples of `𝓛ⁿM` whose closed broken
geodesic is contractible (`TauCeti.Manifold.contractibleCyclicDistanceCut`). It contains the
constant tuples, and it is closed in `Mⁿ⁺¹`
(`TauCeti.Manifold.isClosed_contractibleCyclicDistanceCut`), hence compact when `M` is: two tuples
of `𝓛ⁿM` that are close are joined by a path of tuples with consecutive distances less than `r`,
along which the broken geodesics form a path of free loops, so the tuples of `𝓛ⁿM` with a
noncontractible broken geodesic form a relatively open subset of the closed set `𝓛ⁿM`. Repeating
the first vertex does not change the broken geodesic
(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate`), so it
maps one contractible distance cut to another.

The two halves of the comparison between the approximations and the free loop space restrict to
the contractible loops, because every homotopy involved moves loops inside their path components:

* on a compact family `K ⊆ 𝓛₀M`, every sufficiently fine sampling maps `K` into a contractible
  distance cut, and `geoⁿ ∘ evₙ₊₁ : K → 𝓛₀M` is homotopic to the inclusion through contractible
  loops (`TauCeti.Manifold.exists_contractibleCyclicDistanceCutBrokenGeodesic_comp_homotopic`);
* repeating the first vertex `k` more times and sampling the broken geodesics at `n + k + 1`
  equally spaced times are homotopic maps between contractible distance cuts
  (`homotopic_contractibleCyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`).

Together with the maps `ιⁿ` between the contractible distance cuts, these are the inputs that
`TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` needs to compute the homology of `𝓛₀M`
as the colimit of the homology of the cuts.

## Main definitions

* `TauCeti.Manifold.contractibleCyclicDistanceCut`: the contractible distance cut `𝓛ⁿ₀M`.
* `TauCeti.Manifold.contractibleCyclicDistanceCutBrokenGeodesic`: the map `geoⁿ : 𝓛ⁿ₀M → 𝓛₀M`.
* `TauCeti.Manifold.contractibleCyclicDistanceCutRepeatFirstIterate`: the map
  `𝓛ⁿ₀M → 𝓛ⁿ⁺ᵏ₀M` repeating the first vertex `k` more times.
* `TauCeti.Manifold.contractibleCyclicDistanceCutSampleBrokenGeodesic`: the map
  `evₙ₊ₖ₊₁ ∘ geoⁿ : 𝓛ⁿ₀M → 𝓛ⁿ⁺ᵏ₀M`.
* `TauCeti.Manifold.contractibleCyclicDistanceCutSampleBrokenGeodesicHomotopy`: the homotopy
  between the last two, sliding the sampled vertices along the broken geodesics.

## Main results

* `TauCeti.Manifold.isClosed_contractibleCyclicDistanceCut`: the contractible distance cut is
  closed.
* `TauCeti.Manifold.exists_contractibleCyclicDistanceCutBrokenGeodesic_comp_homotopic`: on a
  compact family of contractible free loops, every sufficiently fine `geoⁿ ∘ evₙ₊₁` is homotopic
  to the inclusion in `𝓛₀M`.
* `TauCeti.Manifold.homotopic_contractibleCyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`:
  `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ` as maps `𝓛ⁿ₀M → 𝓛ⁿ⁺ᵏ₀M`.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public section

open Bundle Manifold Metric Set
open TauCeti.MooreFreeLoopSpace (contractibleLoops mem_contractibleLoops_of_joined)
open scoped ContDiff Manifold NNReal Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ} (hr : ∀ q : M, IsNormalDomain I M q (ball 0 r))

/-! ### The contractible distance cut -/

section Cut

variable {n : ℕ} {δ : Fin (n + 1) → ℝ}

/-- **The contractible distance cut** `𝓛ⁿ₀M`: for cut-offs `δ i < r`, the tuples `q` of the distance
cut `𝓛ⁿM = {q | dist (q i) (q (i - 1)) ≤ δ i}` whose closed broken geodesic `geoⁿ q`
(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`) is a contractible free loop. -/
def contractibleCyclicDistanceCut (hδ : ∀ i, δ i < r) : Set (Fin (n + 1) → M) :=
  {q | ∃ hq : q ∈ cyclicDistanceCut δ,
    cyclicDistanceCutBrokenGeodesic hr hδ ⟨q, hq⟩ ∈ contractibleLoops M}

theorem mem_contractibleCyclicDistanceCut {hδ : ∀ i, δ i < r} {q : Fin (n + 1) → M} :
    q ∈ contractibleCyclicDistanceCut hr hδ ↔
      ∃ hq : q ∈ cyclicDistanceCut δ,
        cyclicDistanceCutBrokenGeodesic hr hδ ⟨q, hq⟩ ∈ contractibleLoops M :=
  Iff.rfl

theorem contractibleCyclicDistanceCut_subset (hδ : ∀ i, δ i < r) :
    contractibleCyclicDistanceCut hr hδ ⊆ cyclicDistanceCut δ :=
  fun _ hq ↦ (mem_contractibleCyclicDistanceCut hr).1 hq |>.1

/-- The broken geodesic through a tuple of the contractible distance cut is contractible. -/
theorem cyclicDistanceCutBrokenGeodesic_mem_contractibleLoops {hδ : ∀ i, δ i < r}
    {q : Fin (n + 1) → M} (hq : q ∈ contractibleCyclicDistanceCut hr hδ) :
    cyclicDistanceCutBrokenGeodesic hr hδ ⟨q, contractibleCyclicDistanceCut_subset hr hδ hq⟩ ∈
      contractibleLoops M :=
  (mem_contractibleCyclicDistanceCut hr).1 hq |>.2

/-- The constant tuples lie in the contractible distance cut for nonnegative cut-offs: their broken
geodesics are constant loops. -/
theorem const_mem_contractibleCyclicDistanceCut (hδ : ∀ i, δ i < r) (hδ₀ : 0 ≤ δ) (x : M) :
    (fun _ ↦ x) ∈ contractibleCyclicDistanceCut hr hδ := by
  refine (mem_contractibleCyclicDistanceCut hr).2 ⟨const_mem_cyclicDistanceCut hδ₀ x, ?_⟩
  rw [cyclicDistanceCutBrokenGeodesic_apply, brokenGeodesicLoop_const]
  exact MooreFreeLoopSpace.const_mem_contractibleLoops x

/-- A tuple of a distance cut whose broken geodesic is joined to the broken geodesic of a tuple of
a contractible distance cut lies in the contractible distance cut. -/
private theorem mem_contractibleCyclicDistanceCut_of_joined {m : ℕ} {δ' : Fin (m + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (hδ' : ∀ i, δ' i < r) {q : Fin (n + 1) → M}
    (hq : q ∈ contractibleCyclicDistanceCut hr hδ) {p : cyclicDistanceCut (X := M) δ'}
    (h : Joined (cyclicDistanceCutBrokenGeodesic hr hδ
        ⟨q, contractibleCyclicDistanceCut_subset hr hδ hq⟩)
      (cyclicDistanceCutBrokenGeodesic hr hδ' p)) :
    (p : Fin (m + 1) → M) ∈ contractibleCyclicDistanceCut hr hδ' :=
  (mem_contractibleCyclicDistanceCut hr).2 ⟨p.property,
    mem_contractibleLoops_of_joined (cyclicDistanceCutBrokenGeodesic_mem_contractibleLoops hr hq) h⟩

/-- **The contractible distance cut is closed** in the space of tuples. -/
theorem isClosed_contractibleCyclicDistanceCut (hδ : ∀ i, δ i < r) :
    IsClosed (contractibleCyclicDistanceCut hr hδ) := by
  have : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  -- The open set of tuples with consecutive distances less than `r`, on which `geoⁿ` is defined.
  let U : Set (Fin (n + 1) → M) := {p | ∀ i, dist (p i) (p (i - 1)) < r}
  have hU : IsOpen U := by
    simp only [U, ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const
  -- Tuples of the cut joined within `U` have joined broken geodesics.
  have hjoined {p q : Fin (n + 1) → M} (hp : p ∈ cyclicDistanceCut δ)
      (hq : q ∈ cyclicDistanceCut δ) (h : JoinedIn U q p) :
      Joined (cyclicDistanceCutBrokenGeodesic hr hδ ⟨q, hq⟩)
        (cyclicDistanceCutBrokenGeodesic hr hδ ⟨p, hp⟩) := by
    rw [cyclicDistanceCutBrokenGeodesic_apply, cyclicDistanceCutBrokenGeodesic_apply]
    exact h.joined_subtype.map (continuous_brokenGeodesicLoop hr n)
  -- The other tuples of the cut are covered by their open path components in `U`, which miss the
  -- contractible distance cut.
  let V := ⋃ q ∈ cyclicDistanceCut δ \ contractibleCyclicDistanceCut hr hδ, pathComponentIn U q
  have hV : IsOpen V := isOpen_biUnion fun q _ ↦ hU.pathComponentIn q
  convert (isClosed_cyclicDistanceCut δ).sdiff hV using 1
  ext p
  refine ⟨fun hp ↦ ⟨contractibleCyclicDistanceCut_subset hr hδ hp, fun hpV ↦ ?_⟩,
    fun ⟨hp, hpV⟩ ↦ ?_⟩
  · obtain ⟨q, ⟨hq, hqc⟩, hqp⟩ := mem_iUnion₂.1 hpV
    exact hqc ((mem_contractibleCyclicDistanceCut hr).2 ⟨hq, mem_contractibleLoops_of_joined
      (cyclicDistanceCutBrokenGeodesic_mem_contractibleLoops hr hp)
      (hjoined (contractibleCyclicDistanceCut_subset hr hδ hp) hq hqp).symm⟩)
  · by_contra hpc
    exact hpV (mem_iUnion₂.2 ⟨p, ⟨hp, hpc⟩, mem_pathComponentIn_self fun i ↦
      (mem_cyclicDistanceCut.1 hp i).trans_lt (hδ i)⟩)

/-- In a compact manifold the contractible distance cut is compact. -/
theorem isCompact_contractibleCyclicDistanceCut [CompactSpace M] (hδ : ∀ i, δ i < r) :
    IsCompact (contractibleCyclicDistanceCut hr hδ) :=
  (isClosed_contractibleCyclicDistanceCut hr hδ).isCompact

/-- **The broken geodesics through the tuples of a contractible distance cut**,
`geoⁿ : 𝓛ⁿ₀M → 𝓛₀M`: the restriction of `TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic` to the
contractible distance cut, with values in the contractible free loops. -/
def contractibleCyclicDistanceCutBrokenGeodesic (hδ : ∀ i, δ i < r) :
    C(contractibleCyclicDistanceCut hr hδ, contractibleLoops M) where
  toFun q := ⟨cyclicDistanceCutBrokenGeodesic hr hδ
      ⟨q, contractibleCyclicDistanceCut_subset hr hδ q.property⟩,
    cyclicDistanceCutBrokenGeodesic_mem_contractibleLoops hr q.property⟩
  continuous_toFun := ((map_continuous _).comp (continuous_subtypeVal.subtype_mk
    fun q ↦ contractibleCyclicDistanceCut_subset hr hδ q.property)).subtype_mk _

@[simp]
theorem coe_contractibleCyclicDistanceCutBrokenGeodesic_apply (hδ : ∀ i, δ i < r)
    (q : contractibleCyclicDistanceCut hr hδ) :
    (contractibleCyclicDistanceCutBrokenGeodesic hr hδ q : MooreFreeLoopSpace M) =
      cyclicDistanceCutBrokenGeodesic hr hδ
        ⟨q, contractibleCyclicDistanceCut_subset hr hδ q.property⟩ :=
  (rfl)

end Cut

/-! ### Compact families of contractible loops -/

section Compact

include hr

/-- **The compact-family approximation of the contractible loops by broken geodesics.** For a
compact family `K` of contractible free Moore loops and `ε > 0` there is `N` such that for every
`n ≥ N` and all cut-offs `ε ≤ δ i < r`, the sampling `evₙ₊₁` at `n + 1` times maps `K` into the
contractible distance cut `𝓛ⁿ₀M`, and `geoⁿ ∘ evₙ₊₁ : K → 𝓛₀M` is homotopic to the inclusion of `K`
through contractible loops. -/
theorem exists_contractibleCyclicDistanceCutBrokenGeodesic_comp_homotopic
    {K : Set (contractibleLoops M)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ δ : Fin (n + 1) → ℝ, (∀ i, ε ≤ δ i) → ∀ hδ : ∀ i, δ i < r,
      ∃ e : C(K, contractibleCyclicDistanceCut hr hδ),
        (∀ γ, (e γ : Fin (n + 1) → M) =
          ((γ : contractibleLoops M) : MooreFreeLoopSpace M).toMoorePath.sample (n + 1)) ∧
        ((contractibleCyclicDistanceCutBrokenGeodesic hr hδ).comp e).Homotopic
          (ContinuousMap.subtypeVal K) := by
  obtain ⟨N, hN⟩ :=
    exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic hr (hK.image continuous_subtypeVal) hε
  refine ⟨N, fun n hn δ hεδ hδ ↦ ?_⟩
  obtain ⟨e, he, ⟨F⟩⟩ := hN n hn δ hεδ hδ
  -- Read `K` as a family of free loops.
  let φ : C(K, Subtype.val '' K) :=
    ⟨fun γ ↦ ⟨γ.val, γ.val, γ.property, rfl⟩,
      (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _⟩
  -- The homotopy joins `geoⁿ (evₙ₊₁ γ)` to the contractible loop `γ`.
  have hmem (γ : K) : (e (φ γ) : Fin (n + 1) → M) ∈ contractibleCyclicDistanceCut hr hδ :=
    (mem_contractibleCyclicDistanceCut hr).2 ⟨(e (φ γ)).property,
      mem_contractibleLoops_of_joined γ.val.property ⟨(F.evalAt (φ γ)).symm⟩⟩
  let e₀ : C(K, contractibleCyclicDistanceCut hr hδ) :=
    ⟨fun γ ↦ ⟨e (φ γ), hmem γ⟩, (continuous_subtypeVal.comp (e.comp φ).continuous).subtype_mk _⟩
  refine ⟨e₀, fun γ ↦ he (φ γ), ?_⟩
  -- The free homotopy starts at contractible loops, so it runs through contractible loops.
  exact ContinuousMap.Homotopic.codRestrict
    (fun _ hγ _ h ↦ mem_contractibleLoops_of_joined hγ h)
    ⟨(F.compContinuousMap φ).cast (ContinuousMap.ext fun _ ↦ rfl) (ContinuousMap.ext fun _ ↦ rfl)⟩

end Compact

/-! ### Repeating the first vertex and sliding the samples -/

section Slide

variable {n : ℕ} {δ : Fin (n + 1) → ℝ}

/-- Repeating the first vertex `k` more times maps a contractible distance cut to another one,
since it does not change the broken geodesic. -/
theorem cyclicDistanceCutRepeatFirstIterate_mem_contractibleCyclicDistanceCut {k : ℕ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j) {q : Fin (n + 1) → M}
    (hq : q ∈ contractibleCyclicDistanceCut hr hδ) :
    (cyclicDistanceCutRepeatFirstIterate k h ⟨q, contractibleCyclicDistanceCut_subset hr hδ hq⟩ :
      Fin (n + k + 1) → M) ∈ contractibleCyclicDistanceCut hr hδ' :=
  (mem_contractibleCyclicDistanceCut hr).2 ⟨Subtype.property _, by
    rw [cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate hr hδ hδ' h]
    exact cyclicDistanceCutBrokenGeodesic_mem_contractibleLoops hr hq⟩

/-- **`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ : 𝓛ⁿ₀M → 𝓛ⁿ⁺ᵏ₀M`**, repeating the first vertex `k` more times
(`TauCeti.cyclicDistanceCutRepeatFirstIterate`) between contractible distance cuts, for cut-offs
`δ i < r` and `δ' j < r` with `δ (j - k) ≤ δ' j` for every `j`. -/
def contractibleCyclicDistanceCutRepeatFirstIterate (k : ℕ) {δ' : Fin (n + k + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j) :
    C(contractibleCyclicDistanceCut hr hδ, contractibleCyclicDistanceCut hr hδ') where
  toFun q := ⟨cyclicDistanceCutRepeatFirstIterate k h
      ⟨q, contractibleCyclicDistanceCut_subset hr hδ q.property⟩,
    cyclicDistanceCutRepeatFirstIterate_mem_contractibleCyclicDistanceCut hr hδ hδ' h q.property⟩
  continuous_toFun := (continuous_subtypeVal.comp
    ((map_continuous (cyclicDistanceCutRepeatFirstIterate k h)).comp
      (continuous_subtypeVal.subtype_mk _))).subtype_mk _

@[simp]
theorem coe_contractibleCyclicDistanceCutRepeatFirstIterate_apply (k : ℕ)
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (q : contractibleCyclicDistanceCut hr hδ) :
    (contractibleCyclicDistanceCutRepeatFirstIterate hr k hδ hδ' h q : Fin (n + k + 1) → M) =
      cyclicDistanceCutRepeatFirstIterate k h
        ⟨q, contractibleCyclicDistanceCut_subset hr hδ q.property⟩ :=
  (rfl)

/-- `geoⁿ⁺ᵏ ∘ ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ = geoⁿ` on contractible distance cuts. -/
@[simp]
theorem contractibleCyclicDistanceCutBrokenGeodesic_contractibleCyclicDistanceCutRepeatFirstIterate
    (k : ℕ) {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (q : contractibleCyclicDistanceCut hr hδ) :
    contractibleCyclicDistanceCutBrokenGeodesic hr hδ'
        (contractibleCyclicDistanceCutRepeatFirstIterate hr k hδ hδ' h q) =
      contractibleCyclicDistanceCutBrokenGeodesic hr hδ q :=
  Subtype.ext (cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate hr hδ hδ' h _)

/-- The points of the homotopy sliding the sampled vertices of the broken geodesic through a tuple
of a contractible distance cut lie in a contractible distance cut: the slide starts at the tuple
repeating the first vertex, with the same broken geodesic, and the broken geodesics along the slide
form a path of free loops. -/
private theorem cyclicDistanceCutSampleBrokenGeodesicHomotopy_mem {k : ℕ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) (t : unitInterval)
    {q : Fin (n + 1) → M} (hq : q ∈ contractibleCyclicDistanceCut hr hδ) :
    (cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm
        (t, ⟨q, contractibleCyclicDistanceCut_subset hr hδ hq⟩) : Fin (n + k + 1) → M) ∈
      contractibleCyclicDistanceCut hr hδ' := by
  refine mem_contractibleCyclicDistanceCut_of_joined hr hδ hδ' hq ?_
  rw [← cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate hr hδ hδ' hδδ']
  exact (((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm).evalAt _).map
    (map_continuous (cyclicDistanceCutBrokenGeodesic hr hδ'))).mem_pathComponent t

/-- Sampling the broken geodesic through a tuple of a contractible distance cut at `n + k + 1`
equally spaced times gives a tuple of a contractible distance cut, for cut-offs `δ i < r` and
`δ' j < r` with `δ (j - k) ≤ δ' j` and `∑ i, δ i ≤ (n + k + 1) * δ' j` for every `j`. -/
theorem cyclicDistanceCutSampleBrokenGeodesic_mem_contractibleCyclicDistanceCut {k : ℕ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) {q : Fin (n + 1) → M}
    (hq : q ∈ contractibleCyclicDistanceCut hr hδ) :
    (cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm
        ⟨q, contractibleCyclicDistanceCut_subset hr hδ hq⟩ : Fin (n + k + 1) → M) ∈
      contractibleCyclicDistanceCut hr hδ' := by
  have h := cyclicDistanceCutSampleBrokenGeodesicHomotopy_mem hr hδ hδ' hδδ' hm 1 hq
  rwa [ContinuousMap.Homotopy.apply_one] at h

/-- **Sampling broken geodesics, `evₙ₊ₖ₊₁ ∘ geoⁿ : 𝓛ⁿ₀M → 𝓛ⁿ⁺ᵏ₀M`,** between contractible distance
cuts: the restriction of `TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesic`, for cut-offs
`δ i < r` and `δ' j < r` with `δ (j - k) ≤ δ' j` and `∑ i, δ i ≤ (n + k + 1) * δ' j` for every
`j`. -/
def contractibleCyclicDistanceCutSampleBrokenGeodesic {k : ℕ} {δ' : Fin (n + k + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    C(contractibleCyclicDistanceCut hr hδ, contractibleCyclicDistanceCut hr hδ') where
  toFun q := ⟨cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm
      ⟨q, contractibleCyclicDistanceCut_subset hr hδ q.property⟩,
    cyclicDistanceCutSampleBrokenGeodesic_mem_contractibleCyclicDistanceCut hr hδ hδ' hδδ' hm
      q.property⟩
  continuous_toFun := (continuous_subtypeVal.comp
    ((map_continuous (cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm)).comp
      (continuous_subtypeVal.subtype_mk _))).subtype_mk _

@[simp]
theorem coe_contractibleCyclicDistanceCutSampleBrokenGeodesic_apply {k : ℕ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) (q : contractibleCyclicDistanceCut hr hδ) :
    (contractibleCyclicDistanceCutSampleBrokenGeodesic hr hδ hδ' hδδ' hm q : Fin (n + k + 1) → M) =
      cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm
        ⟨q, contractibleCyclicDistanceCut_subset hr hδ q.property⟩ :=
  (rfl)

/-- **Sliding the sampled vertices along the broken geodesics, inside the contractible distance
cuts.** The homotopy `TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesicHomotopy` from the
iterate repeating the first vertex `k` more times to `evₙ₊ₖ₊₁ ∘ geoⁿ`, restricted to maps between
the contractible distance cuts. -/
def contractibleCyclicDistanceCutSampleBrokenGeodesicHomotopy {k : ℕ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    (contractibleCyclicDistanceCutRepeatFirstIterate hr k hδ hδ' hδδ').Homotopy
      (contractibleCyclicDistanceCutSampleBrokenGeodesic hr hδ hδ' hδδ' hm) where
  toFun x := ⟨cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm
      (x.1, ⟨x.2, contractibleCyclicDistanceCut_subset hr hδ x.2.property⟩),
    cyclicDistanceCutSampleBrokenGeodesicHomotopy_mem hr hδ hδ' hδδ' hm x.1 x.2.property⟩
  continuous_toFun := (continuous_subtypeVal.comp
    ((map_continuous (cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm)).comp
      (continuous_fst.prodMk
        ((continuous_subtypeVal.comp continuous_snd).subtype_mk _)))).subtype_mk _
  map_zero_left q := Subtype.ext <| by
    rw [coe_contractibleCyclicDistanceCutRepeatFirstIterate_apply]
    exact congrArg Subtype.val
      ((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm).apply_zero _)
  map_one_left q := Subtype.ext <| by
    rw [coe_contractibleCyclicDistanceCutSampleBrokenGeodesic_apply]
    exact congrArg Subtype.val
      ((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm).apply_one _)

/-- **`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ` on contractible distance cuts.** For cut-offs `δ i < r` and
`δ' j < r` with `δ (j - k) ≤ δ' j` and `∑ i, δ i ≤ (n + k + 1) * δ' j` for every `j`, repeating the
first vertex `k` more times and sampling the broken geodesics at `n + k + 1` equally spaced times
are homotopic maps from the contractible distance cut with cut-offs `δ` to the one with cut-offs
`δ'`. -/
theorem homotopic_contractibleCyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic {k : ℕ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    (contractibleCyclicDistanceCutRepeatFirstIterate hr k hδ hδ' hδδ').Homotopic
      (contractibleCyclicDistanceCutSampleBrokenGeodesic hr hδ hδ' hδδ' hm) :=
  ⟨contractibleCyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδ' hδδ' hm⟩

end Slide

end TauCeti.Manifold
