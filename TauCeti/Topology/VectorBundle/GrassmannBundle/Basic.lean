/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Topology.Grassmannian.StarProjection
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Hom
import TauCeti.Topology.FiberBundle.Proper

/-!
# The Grassmann bundle of a Riemannian vector bundle in projection form

Let `E → B` be a real vector bundle with model fibre `F` whose fibres are real inner product
spaces. The **Grassmann bundle** `G_k(E)` (`TauCeti.grassmannBundle F E k`) is the set of points
`(b, P)` of the total space of the endomorphism bundle `Hom(E, E)` such that `P` is a self-adjoint
idempotent of `E_b` with range of rank `k`, that is, a point of the Grassmannian
`Euclidean.grassmannian ℝ (E b) k` of `k`-planes of `E_b` in projection form. It carries the
subspace topology of the total space of `Hom(E, E)`. For the tangent bundle of a Riemannian
manifold `(M, g)` this is the bundle `G_k(M)` of tangent `k`-planes, each recorded by its
`g`-orthogonal projection, on which varifolds are measures (L. Simon, *Lectures on Geometric
Measure Theory*, §38, for Euclidean space; W. K. Allard, *On the first variation of a varifold*,
Section 3).

The fibre of `G_k(E)` over `b` is the Grassmannian of `E_b`, embedded by
`TauCeti.grassmannBundle.fiberIncl` (`TauCeti.grassmannBundle.isEmbedding_fiberIncl`,
`TauCeti.grassmannBundle.range_fiberIncl`). When the fibre norm is continuous on the total space
(`TauCeti.ContinuousFiberNorm F E`, which holds for continuous Riemannian bundles), a linear chart
`e` of `E`, a basis `c` of `F` and an orthonormal basis `b` of a model inner product space `V`
trivialize `G_k(E) → B` over `e.baseSet` with fibre the Grassmannian `G(V, k)`
(`Bundle.Trivialization.grassmannBundle`): a projection `P` of `E_y` is read as `σ_y⁻¹ P σ_y`,
where `σ_y : V ≃ₗᵢ[ℝ] E y` is the local Gram–Schmidt orthonormal frame `e.orthonormalFrameAt c b`.
With `V = ℝᴺ`, `N` the rank of `E`, this is, over `U = e.baseSet`, a homeomorphism
`G_k(U) ≅ U × G(ℝᴺ, k)` commuting with the projections, given by the Gram–Schmidt frame of `e`.
The chart and local triviality follow the Stiefel bundle chart
`Bundle.Trivialization.stiefelBundle` and `TauCeti.StiefelBundle.exists_trivialization` in
`TauCeti.Topology.VectorBundle.StiefelBundle`, which use the same Gram–Schmidt frame built from
`e`, `c` and `b`. Consequently, for finite rank, the projection
`G_k(E) → B` is continuous, open and proper (`TauCeti.grassmannBundle.isOpenMap_proj`,
`TauCeti.grassmannBundle.isProperMap_proj`). So the part of `G_k(E)` over a compact set of the
base is compact, `G_k(E)` is weakly locally compact over a weakly locally compact base, and
`G_k(E)` is a closed subset of the total space of `Hom(E, E)` (`TauCeti.isClosed_grassmannBundle`).

`G_k(E)` carries its Borel σ-algebra, on which varifolds are measures.

## Main declarations

* `TauCeti.grassmannBundle F E k`: the orthogonal projections of rank `k` in the fibres of `E`.
* `TauCeti.grassmannBundle.proj`: the projection `G_k(E) → B`.
* `TauCeti.grassmannBundle.fiberIncl`: the inclusion of the Grassmannian of one fibre, an embedding
  onto the fibre of the projection.
* `Bundle.Trivialization.grassmannBundle`: the chart of `G_k(E) → B` with fibre `G(V, k)` induced
  by a linear chart of `E`.

## Main results

* `TauCeti.grassmannBundle.exists_trivialization`: `G_k(E) → B` is locally trivial with fibre
  `G(V, k)` for every model `V` of the rank of `E`.
* `TauCeti.grassmannBundle.isProperMap_proj`: the projection `G_k(E) → B` is proper.
* `TauCeti.grassmannBundle.isOpenMap_proj`: the projection `G_k(E) → B` is open.
* `TauCeti.isClosed_grassmannBundle`: `G_k(E)` is closed in the total space of `Hom(E, E)`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Proceedings of the Centre for Mathematical
  Analysis, Australian National University 3, 1983, §38.
* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. (2) 95 (1972), 417–491,
  Section 3.
* M. Agnoletto, J. C. Correa Hoyos, M. F. da Silva, S. Nardulli, *Allard's interior ε-regularity
  theorem in Alexandrov spaces*, arXiv:2504.10758, Section 2 (varifolds on Riemannian manifolds).
-/

public section

noncomputable section

open Bundle Filter Set Topology

namespace TauCeti

section Definition

variable {B : Type*} (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (E : B → Type*)
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]

/-- The **Grassmann bundle** `G_k(E)` of a vector bundle `E` with model fibre `F` whose fibres are
real inner product spaces: the points `(b, P)` of the total space of the endomorphism bundle of `E`
such that `P` is the orthogonal projection of `E_b` onto a `k`-dimensional subspace, a point of the
Grassmannian `Euclidean.grassmannian ℝ (E b) k`. For the tangent bundle of a Riemannian manifold
this is the bundle of tangent `k`-planes that carries varifolds (L. Simon, *Lectures on Geometric
Measure Theory*, §38). Completeness of the fibres is needed for the adjoint on `E b →L[ℝ] E b`; it
holds for every bundle of finite rank. -/
def grassmannBundle (k : ℕ) : Set (TotalSpace (F →L[ℝ] F) fun b ↦ E b →L[ℝ] E b) :=
  {p | p.snd ∈ Euclidean.grassmannian ℝ (E p.proj) k}

variable {F E} {k : ℕ}

/-- Membership in the Grassmann bundle unfolds to membership of the fibre component in the
Grassmannian of its fibre. -/
@[simp]
theorem mem_grassmannBundle {p : TotalSpace (F →L[ℝ] F) fun b ↦ E b →L[ℝ] E b} :
    p ∈ grassmannBundle F E k ↔ p.snd ∈ Euclidean.grassmannian ℝ (E p.proj) k :=
  Iff.rfl

namespace grassmannBundle

/-- The projection `G_k(E) → B` of the Grassmann bundle to the base. -/
def proj (p : grassmannBundle F E k) : B :=
  p.val.proj

/-- The projection of a point of the Grassmann bundle is its base point. -/
theorem proj_apply (p : grassmannBundle F E k) : proj p = p.val.proj :=
  (rfl)

end grassmannBundle

end Definition

namespace grassmannBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {k : ℕ}

/-- The Borel σ-algebra of the Grassmann bundle, on which varifolds are measures. -/
instance instMeasurableSpace : MeasurableSpace (grassmannBundle F E k) :=
  borel _

instance : BorelSpace (grassmannBundle F E k) :=
  ⟨rfl⟩

/-- The projection of the Grassmann bundle to the base is continuous. -/
@[fun_prop]
theorem continuous_proj : Continuous (proj : grassmannBundle F E k → B) :=
  (FiberBundle.continuous_proj (F →L[ℝ] F) fun b ↦ E b →L[ℝ] E b).comp continuous_subtypeVal

section Fiber

variable (F E k)

/-- The inclusion `G(E_b, k) → G_k(E)` of the Grassmannian of the fibre over `b`. -/
def fiberIncl (b : B) : C(Euclidean.grassmannian ℝ (E b) k, grassmannBundle F E k) where
  toFun P := ⟨⟨b, P⟩, P.property⟩
  continuous_toFun :=
    ((FiberBundle.continuous_totalSpaceMk (F →L[ℝ] F) (fun b ↦ E b →L[ℝ] E b) b).comp
      continuous_subtypeVal).subtype_mk _

variable {F E k}

@[simp]
theorem coe_fiberIncl_apply (b : B) (P : Euclidean.grassmannian ℝ (E b) k) :
    (fiberIncl F E k b P : TotalSpace (F →L[ℝ] F) fun b ↦ E b →L[ℝ] E b) = ⟨b, P⟩ :=
  (rfl)

@[simp]
theorem proj_fiberIncl (b : B) (P : Euclidean.grassmannian ℝ (E b) k) :
    proj (fiberIncl F E k b P) = b :=
  (rfl)

variable (F E k)

/-- The projections of the fibre over `b` are exactly the fibre over `b` of the projection to the
base. -/
theorem range_fiberIncl (b : B) :
    range (fiberIncl F E k b) = (proj : grassmannBundle F E k → B) ⁻¹' {b} := by
  refine Subset.antisymm (range_subset_iff.2 fun P ↦ rfl) fun p hp ↦ ?_
  obtain ⟨⟨b', P⟩, hP⟩ := p
  obtain rfl : b' = b := hp
  exact ⟨⟨P, hP⟩, rfl⟩

/-- **The fibre of the Grassmann bundle over `b` is the Grassmannian of `E_b`**: the inclusion of
the projections of the fibre is an embedding. -/
theorem isEmbedding_fiberIncl (b : B) : IsEmbedding (fiberIncl F E k b) :=
  ⟨IsInducing.of_comp (fiberIncl F E k b).continuous continuous_subtypeVal
    ((FiberBundle.totalSpaceMk_isInducing (F →L[ℝ] F) (fun b ↦ E b →L[ℝ] E b) b).comp
      IsInducing.subtypeVal),
    fun _ _ h ↦ Subtype.ext ((FiberBundle.totalSpaceMk_isEmbedding (F →L[ℝ] F)
      (fun b ↦ E b →L[ℝ] E b) b).injective (congrArg Subtype.val h))⟩

/-- When the base is `T₁`, the fibre inclusion `G(E_b, k) → G_k(E)` is a closed embedding. -/
theorem isClosedEmbedding_fiberIncl [T1Space B] (b : B) :
    IsClosedEmbedding (fiberIncl F E k b) where
  toIsEmbedding := isEmbedding_fiberIncl F E k b
  isClosed_range := by
    rw [range_fiberIncl]
    exact isClosed_singleton.preimage continuous_proj

end Fiber

end grassmannBundle

end TauCeti

/-! ### Local triviality over the base -/

namespace Bundle.Trivialization

open TauCeti

variable {B F V : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [FiberBundle F E] [VectorBundle ℝ F E] [ContinuousFiberNorm F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  (c : Module.Basis ι ℝ F) (b : OrthonormalBasis ι ℝ V)

variable (k : ℕ)

/-- **Chart of the Grassmann bundle induced by a linear chart of `E`.** Over `e.baseSet`, an
orthogonal projection `P` of the fibre over `y` is read as `σ_y⁻¹ P σ_y` in the local Gram–Schmidt
orthonormal frame `σ_y = e.orthonormalFrameAt c b y : V ≃ₗᵢ[ℝ] E y`, giving coordinates in the
Grassmannian `G(V, k)`. -/
def grassmannBundle [FiniteDimensional ℝ F] :
    Trivialization (Euclidean.grassmannian ℝ V k)
      (grassmannBundle.proj : TauCeti.grassmannBundle F E k → B) where
  toFun p := (p.val.proj, ⟨(e.orthonormalFrameAt c b p.val.proj).symm.conjStarAlgEquiv p.val.snd,
    LinearIsometryEquiv.conjStarAlgEquiv_mem_grassmannian _ p.property⟩)
  invFun q := ⟨⟨q.1, (e.orthonormalFrameAt c b q.1).conjStarAlgEquiv q.2⟩,
    LinearIsometryEquiv.conjStarAlgEquiv_mem_grassmannian _ q.2.property⟩
  source := grassmannBundle.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p _ := by
    refine Subtype.ext (TotalSpace.ext rfl (heq_of_eq ?_))
    ext v
    simp
  right_inv' q _ := by
    refine Prod.ext rfl (Subtype.ext ?_)
    ext v
    simp
  open_source := e.open_baseSet.preimage grassmannBundle.continuous_proj
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine grassmannBundle.continuous_proj.continuousOn.prodMk ?_
    rw [IsInducing.subtypeVal.continuousOn_iff]
    exact (e.continuousOn_conjStarAlgEquiv_orthonormalFrameAt_symm c b).comp
      continuous_subtypeVal.continuousOn fun _ hp ↦ hp
  continuousOn_invFun := by
    rw [IsInducing.subtypeVal.continuousOn_iff]
    exact (e.continuousOn_totalSpaceMk_conjStarAlgEquiv_orthonormalFrameAt c b).comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)).continuousOn
      fun q hq ↦ ⟨hq.1, mem_univ _⟩
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable [FiniteDimensional ℝ F]

@[simp]
theorem grassmannBundle_baseSet : (e.grassmannBundle c b k).baseSet = e.baseSet :=
  (rfl)

/-- The Grassmann bundle chart reads a projection in the inverse of the frame
`e.orthonormalFrameAt c b`. -/
@[simp]
theorem coe_grassmannBundle_apply_snd (p : TauCeti.grassmannBundle F E k) :
    ((e.grassmannBundle c b k p).2 : V →L[ℝ] V) =
      (e.orthonormalFrameAt c b p.val.proj).symm.conjStarAlgEquiv p.val.snd :=
  (rfl)

/-- The inverse Grassmann bundle chart conjugates a model projection by the frame
`e.orthonormalFrameAt c b`. -/
@[simp]
theorem coe_grassmannBundle_symm_apply (q : B × Euclidean.grassmannian ℝ V k) :
    ((e.grassmannBundle c b k).toOpenPartialHomeomorph.symm q :
        TotalSpace (F →L[ℝ] F) fun y ↦ E y →L[ℝ] E y) =
      ⟨q.1, (e.orthonormalFrameAt c b q.1).conjStarAlgEquiv q.2⟩ :=
  (rfl)

end Bundle.Trivialization

namespace TauCeti

open Module

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [ContinuousFiberNorm F E]

namespace grassmannBundle

/-- **The Grassmann bundle is locally trivial over `B`.** When the inner product space `V` has the
dimension of `F`, every point of `B` lies in the base set of a chart of `G_k(E) → B` with fibre the
Grassmannian `G(V, k)`. -/
theorem exists_trivialization {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (h : finrank ℝ V = finrank ℝ F) (k : ℕ) (x : B) :
    ∃ t : Trivialization (Euclidean.grassmannian ℝ V k)
      (proj : grassmannBundle F E k → B), x ∈ t.baseSet :=
  ⟨(trivializationAt F E x).grassmannBundle (Module.finBasisOfFinrankEq ℝ F h.symm)
    (stdOrthonormalBasis ℝ V) k, mem_baseSet_trivializationAt F E x⟩

variable (F E)

/-- **The projection `G_k(E) → B` is proper** for a finite-rank real vector bundle with continuous
fibre norm: it is locally trivial with compact fibre `G(ℝᴺ, k)`. -/
theorem isProperMap_proj (k : ℕ) : IsProperMap (proj : grassmannBundle F E k → B) :=
  isProperMap_of_forall_exists_trivialization
    (exists_trivialization (V := EuclideanSpace ℝ (Fin (finrank ℝ F)))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ F)) k)

/-- **The projection `G_k(E) → B` is open.** -/
theorem isOpenMap_proj (k : ℕ) : IsOpenMap (proj : grassmannBundle F E k → B) := by
  refine IsOpenMap.of_nhds_le fun p ↦ ?_
  obtain ⟨t, ht⟩ := exists_trivialization (E := E) (V := EuclideanSpace ℝ (Fin (finrank ℝ F)))
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ F)) k (proj p)
  exact (t.map_proj_nhds (t.mem_source.2 ht)).ge

/-- Over a compact base, the Grassmann bundle of a finite-rank real vector bundle with continuous
fibre norm is compact. -/
instance compactSpace [CompactSpace B] (k : ℕ) : CompactSpace (grassmannBundle F E k) :=
  ⟨by simpa using (isProperMap_proj F E k).isCompact_preimage isCompact_univ⟩

/-- Over a weakly locally compact base, the Grassmann bundle of a finite-rank real vector bundle
with continuous fibre norm is weakly locally compact: the preimage of a compact neighbourhood of
the base point is a compact neighbourhood. -/
instance weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace B] (k : ℕ) :
    WeaklyLocallyCompactSpace (grassmannBundle F E k) where
  exists_compact_mem_nhds p := by
    obtain ⟨K, hK, hKp⟩ := exists_compact_mem_nhds (proj p)
    exact ⟨proj ⁻¹' K, (isProperMap_proj F E k).isCompact_preimage hK,
      continuous_proj.continuousAt.preimage_mem_nhds hKp⟩

end grassmannBundle

variable (F E) in
/-- **The Grassmann bundle is closed** in the total space of the endomorphism bundle, for a
finite-rank real vector bundle with continuous fibre norm. -/
theorem isClosed_grassmannBundle (k : ℕ) : IsClosed (grassmannBundle F E k) := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun q hq ↦ ?_)
  let V := EuclideanSpace ℝ (Fin (finrank ℝ F))
  let e := trivializationAt F E q.proj
  let c := Module.finBasisOfFinrankEq ℝ F (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  let b := stdOrthonormalBasis ℝ V
  -- Read in the local orthonormal frame, a point of the Grassmann bundle is a point of `G(V, k)`.
  have hiff : ∀ q' : TotalSpace (F →L[ℝ] F) (fun y ↦ E y →L[ℝ] E y),
      (e.orthonormalFrameAt c b q'.proj).symm.conjStarAlgEquiv q'.snd ∈
        Euclidean.grassmannian ℝ V k ↔ q' ∈ grassmannBundle F E k :=
    fun q' ↦ LinearIsometryEquiv.conjStarAlgEquiv_mem_grassmannian_iff _
  refine ⟨TotalSpace.proj ⁻¹' e.baseSet ∩ (fun q' : TotalSpace (F →L[ℝ] F)
      (fun y ↦ E y →L[ℝ] E y) ↦ (e.orthonormalFrameAt c b q'.proj).symm.conjStarAlgEquiv
        q'.snd) ⁻¹' (Euclidean.grassmannian ℝ V k)ᶜ, fun q' hq' ↦ (hiff q').not.1 hq'.2,
    (e.continuousOn_conjStarAlgEquiv_orthonormalFrameAt_symm c b).isOpen_inter_preimage
      (e.open_baseSet.preimage (FiberBundle.continuous_proj _ _))
      Euclidean.isClosed_grassmannian.isOpen_compl,
    mem_baseSet_trivializationAt F E q.proj, (hiff q).not.2 hq⟩

end TauCeti
