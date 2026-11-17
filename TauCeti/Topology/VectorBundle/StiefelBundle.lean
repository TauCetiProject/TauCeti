/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.Projection
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import TauCeti.Topology.VectorBundle.SphereBundle.Fiber
import TauCeti.Topology.FiberBundle.FiberMap
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# The Stiefel bundle of orthonormal `k`-frames of a Riemannian vector bundle

Let `E → B` be a real vector bundle with model fibre `F` whose fibres carry inner products. Its
Stiefel bundle of `k`-frames `V_k(E)` (`TauCeti.StiefelBundle F E k`) is the space of pairs of a
base point `b : B` and an orthonormal `k`-frame of the fibre `E b` (`TauCeti.stiefel (E b) k`). It
carries the coarsest topology making the base projection and each vector of the frame, read in the
total space `TotalSpace F E`, continuous (`TauCeti.StiefelBundle.continuous_iff`); including the
base projection in the induced topology ensures that `V_0(E)` is homeomorphic to `B` rather than
indiscrete. Over each point `b : B`, the fibre is `V_k(E_b)` (`TauCeti.StiefelBundle.fiberIncl`,
`TauCeti.StiefelBundle.fiberHomeomorph`).

When the fibre norm is continuous on the total space (`TauCeti.ContinuousFiberNorm F E`), a linear
chart `e` of `E`, a basis `c` of `F` and an orthonormal basis `b` of a model inner product space
`V` trivialize `V_k(E) → B` over `e.baseSet` with fibre `V_k(V)`
(`Bundle.Trivialization.stiefelBundle`), by reading frames in the Gram–Schmidt local orthonormal
frame `e.orthonormalFrame c b`. Thus in finite rank `V_k(E) → B` is locally trivial
(`TauCeti.StiefelBundle.exists_trivialization`), proper
(`TauCeti.StiefelBundle.isProperMap_proj`), and a Serre (or Hurewicz) fibration.

Each index `i : Fin k` projects `V_k(E)` to the unit sphere bundle `S(E)`
(`TauCeti.StiefelBundle.vecProj`). For `k + 1` vectors, the fibre of the first-vector projection
`vecProj 0 : V_{k+1}(E) → S(E)` over a unit vector `q ∈ S(E)` is the Stiefel manifold `V_k(q^⊥)` of
vertical orthonormal `k`-frames tangent to the sphere fibre at `q`
(`TauCeti.StiefelBundle.sphereFiberIncl`, `TauCeti.StiefelBundle.sphereFiberHomeomorph`). In local
orthonormal frames over `B`, `vecProj 0` reads as the model Stiefel projection `V_{k+1}(V) → S(V)`,
so `Bundle.Trivialization.ofFiberMap` and `TauCeti.exists_trivialization_stiefelProj_zero` make
`vecProj 0 : V_{k+1}(E) → S(E)` locally trivial with fibre `V_k(ℝⁿ)` when `finrank ℝ F = n + 1`
(`TauCeti.StiefelBundle.exists_trivialization_vecProj_zero`), hence a Serre fibration and
`(n - k)`-connected for `k ≤ n` (`TauCeti.StiefelBundle.isNConnected_vecProj_zero`). For `k = 2`,
`V₃(E) → S(E)` is the carrier of the fibered family of two-spheres of a sphere bundle in
Barraud–Damian–Humilière–Oancea, Proposition 6.23.

## Main declarations

* `TauCeti.StiefelBundle`: the bundle `V_k(E)` of orthonormal `k`-frames of the fibres of `E`.
* `TauCeti.StiefelBundle.fiberIncl`, `TauCeti.StiefelBundle.fiberHomeomorph`: the fibre `V_k(E_b)`
  over `b : B`.
* `Bundle.Trivialization.stiefelBundle`, `TauCeti.StiefelBundle.exists_trivialization`: local
  triviality of `V_k(E) → B` with fibre `V_k(V)`.
* `TauCeti.StiefelBundle.vecProj`: the vector projections `V_k(E) → S(E)`, with
  `TauCeti.StiefelBundle.oneHomeomorphSphereBundle : V₁(E) ≃ₜ S(E)`.
* `TauCeti.StiefelBundle.sphereFiberIncl`, `TauCeti.StiefelBundle.sphereFiberHomeomorph`: the
  vertical `k`-frame fibre `V_k(q^⊥)` over `q : S(E)`.
* `TauCeti.StiefelBundle.exists_trivialization_vecProj_zero`,
  `TauCeti.StiefelBundle.mem_serreFibrations_vecProj_zero`,
  `TauCeti.StiefelBundle.isNConnected_vecProj_zero`: local triviality, Serre fibration property,
  and connectivity of `V_{k+1}(E) → S(E)`.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§7.7 and 9.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §5.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric Module Set Topology
open scoped RealInnerProductSpace Topology.Homotopy

namespace TauCeti

/-- The Stiefel bundle `V_k(E)` of a vector bundle `E → B` with model fibre `F` and fibrewise real
inner products: the pairs of a base point `b : B` and an orthonormal `k`-frame of `E b`. The model
fibre `F` enters through the topology of `TotalSpace F E`. -/
structure StiefelBundle {B : Type*} (F : Type*) (E : B → Type*) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, InnerProductSpace ℝ (E b)] (k : ℕ) where
  /-- The base point. -/
  proj : B
  /-- The orthonormal `k`-frame of the fibre over `proj`. -/
  frame : stiefel (E proj) k

namespace StiefelBundle

section Basic

variable {B F : Type*} {E : B → Type*} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {k : ℕ}

/-- Two points of `StiefelBundle` over the same base point are equal exactly when their frames are
equal. -/
theorem mk_eq_mk_iff {b : B} {v w : stiefel (E b) k} :
    (⟨b, v⟩ : StiefelBundle F E k) = ⟨b, w⟩ ↔ v = w := by
  constructor
  · exact fun h ↦ eq_of_heq (StiefelBundle.mk.inj h).2
  · rintro rfl
    rfl

/-- A point of `StiefelBundle` equals the transported frame over any base point equal to its
projection. -/
theorem eq_mk_of_proj_eq {b : B} (p : StiefelBundle F E k) (h : p.proj = b) :
    p = ⟨b, h ▸ p.frame⟩ := by
  cases p
  cases h
  rfl

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]

/-- The topology of pointwise convergence of frames in `TotalSpace F E`, together with continuity
of the base projection (which is automatic for `k ≥ 1`, and makes `V_0(E)` homeomorphic to `B` via
`TauCeti.StiefelBundle.zeroHomeomorph`). -/
instance : TopologicalSpace (StiefelBundle F E k) :=
  .induced
    (fun p ↦ (p.proj, fun i : Fin k ↦ (⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ : TotalSpace F E)))
    instTopologicalSpaceProd

/-- A map into `StiefelBundle F E k` is continuous exactly when its base projection and each of its
frame vectors in `TotalSpace F E` are continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → StiefelBundle F E k} :
    Continuous f ↔
      Continuous (fun x ↦ (f x).proj) ∧
        ∀ i : Fin k,
          Continuous fun x ↦ (⟨(f x).proj, ((f x).frame : Fin k → E (f x).proj) i⟩ :
            TotalSpace F E) := by
  rw [continuous_induced_rng, continuous_prodMk, continuous_pi_iff]
  rfl

/-- The projection `V_k(E) → B` is continuous. -/
@[fun_prop]
theorem continuous_proj : Continuous (proj : StiefelBundle F E k → B) :=
  (continuous_iff.1 continuous_id).1

/-- Evaluating the `i`-th vector of the frame in `TotalSpace F E` is continuous. -/
@[fun_prop]
theorem continuous_totalSpaceMk_frame (i : Fin k) :
    Continuous fun p : StiefelBundle F E k ↦
      (⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ : TotalSpace F E) :=
  (continuous_iff.1 continuous_id).2 i

variable (F E) in
/-- **Orthonormal `0`-frames are base points**: `V₀(E) ≃ₜ B`. -/
def zeroHomeomorph : StiefelBundle F E 0 ≃ₜ B where
  toFun := proj
  invFun b := ⟨b, ⟨Fin.elim0, mem_stiefel_iff.2 (orthonormal_iff_ite.2 fun i ↦ i.elim0)⟩⟩
  left_inv p := by
    obtain ⟨b, v⟩ := p
    exact mk_eq_mk_iff.2 (Subtype.ext (funext fun i ↦ i.elim0))
  right_inv _ := rfl
  continuous_toFun := continuous_proj
  continuous_invFun := continuous_iff.2 ⟨continuous_id, fun i ↦ i.elim0⟩

@[simp]
theorem zeroHomeomorph_apply (p : StiefelBundle F E 0) :
    zeroHomeomorph F E p = p.proj := by
  rw [zeroHomeomorph]
  rfl

@[simp]
theorem proj_zeroHomeomorph_symm (b : B) :
    ((zeroHomeomorph F E).symm b).proj = b := by
  rw [zeroHomeomorph]
  rfl

private theorem isEmbedding_toProd :
    IsEmbedding fun p : StiefelBundle F E k ↦
      (p.proj, fun i : Fin k ↦ (⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ : TotalSpace F E)) where
  toIsInducing := ⟨rfl⟩
  injective := by
    rintro ⟨b, v⟩ ⟨b', w⟩ h
    obtain ⟨hb, hv⟩ := Prod.mk.inj h
    dsimp only at hb
    subst hb
    exact mk_eq_mk_iff.2 <| Subtype.ext <| funext fun i ↦ TotalSpace.mk_inj.1 (congr_fun hv i)

variable [TopologicalSpace F] [FiberBundle F E]

/-- For `k ≥ 1`, continuity of the base projection follows from continuity of the first vector in
`TotalSpace F E`. -/
theorem continuous_iff_of_neZero [NeZero k] {X : Type*} [TopologicalSpace X]
    {f : X → StiefelBundle F E k} :
    Continuous f ↔
      ∀ i : Fin k,
        Continuous fun x ↦ (⟨(f x).proj, ((f x).frame : Fin k → E (f x).proj) i⟩ :
          TotalSpace F E) :=
  continuous_iff.trans <| and_iff_right_of_imp fun h ↦
    (FiberBundle.continuous_proj F E).comp (h 0)

variable (F E k)

/-- The inclusion `V_k(E_b) → V_k(E)` of the Stiefel manifold of the fibre over `b : B`. -/
def fiberIncl (b : B) : C(stiefel (E b) k, StiefelBundle F E k) where
  toFun v := ⟨b, v⟩
  continuous_toFun := continuous_iff.2 ⟨continuous_const, fun i ↦
    (FiberBundle.continuous_totalSpaceMk F E b).comp
      ((continuous_apply i).comp continuous_subtype_val)⟩

variable {F E k}

@[simp]
theorem fiberIncl_apply (b : B) (v : stiefel (E b) k) :
    fiberIncl F E k b v = ⟨b, v⟩ := by
  rw [fiberIncl]
  -- After unfolding `fiberIncl`, evaluation is `{ proj := b, frame := v }`.
  rfl

variable (F E k)

/-- The fibre inclusion `V_k(E_b) → V_k(E)` is a topological embedding. -/
theorem isEmbedding_fiberIncl (b : B) : IsEmbedding (fiberIncl F E k b) := by
  refine isEmbedding_toProd.of_comp_iff.1 ?_
  exact (isEmbedding_prodMkRight b).comp
    ((IsEmbedding.piMap fun _ ↦ FiberBundle.totalSpaceMk_isEmbedding F E b).comp
      IsEmbedding.subtypeVal)

/-- The fibre inclusion `V_k(E_b) → V_k(E)` is injective. -/
theorem fiberIncl_injective (b : B) : Function.Injective (fiberIncl F E k b) :=
  (isEmbedding_fiberIncl F E k b).injective

/-- The range of `V_k(E_b) → V_k(E)` is the fibre of `proj : V_k(E) → B` over `b`. -/
theorem range_fiberIncl (b : B) :
    range (fiberIncl F E k b) = (proj : StiefelBundle F E k → B) ⁻¹' {b} := by
  refine Subset.antisymm (range_subset_iff.2 fun _ ↦ rfl) fun p hp ↦ ?_
  obtain ⟨b', v⟩ := p
  obtain rfl : b' = b := hp
  exact ⟨v, rfl⟩

/-- When the base is `T₁`, the fibre inclusion `V_k(E_b) → V_k(E)` is a closed embedding. -/
theorem isClosedEmbedding_fiberIncl [T1Space B] (b : B) :
    IsClosedEmbedding (fiberIncl F E k b) where
  toIsEmbedding := isEmbedding_fiberIncl F E k b
  isClosed_range := by
    rw [range_fiberIncl]
    exact isClosed_singleton.preimage continuous_proj

/-- **Homeomorphism onto a fibre of the Stiefel bundle over `B`.** -/
def fiberHomeomorph (b : B) :
    stiefel (E b) k ≃ₜ (proj : StiefelBundle F E k → B) ⁻¹' {b} :=
  (isEmbedding_fiberIncl F E k b).toHomeomorph.trans
    (Homeomorph.setCongr (range_fiberIncl F E k b))

variable {F E k}

@[simp]
theorem coe_fiberHomeomorph_apply (b : B) (v : stiefel (E b) k) :
    (fiberHomeomorph F E k b v : StiefelBundle F E k) = fiberIncl F E k b v :=
  (rfl)

theorem fiberIncl_fiberHomeomorph_symm (b : B)
    (p : (proj : StiefelBundle F E k → B) ⁻¹' {b}) :
    fiberIncl F E k b ((fiberHomeomorph F E k b).symm p) = p :=
  congrArg Subtype.val ((fiberHomeomorph F E k b).apply_symm_apply p)

@[simp]
theorem mk_fiberHomeomorph_symm (b : B)
    (p : (proj : StiefelBundle F E k → B) ⁻¹' {b}) :
    (⟨b, (fiberHomeomorph F E k b).symm p⟩ : StiefelBundle F E k) = p := by
  rw [← fiberIncl_apply, fiberIncl_fiberHomeomorph_symm]

end Basic

end StiefelBundle

end TauCeti

/-! ### Local triviality over the base -/

namespace Bundle.Trivialization

open TauCeti

variable {B F V : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiberBundle F E] [VectorBundle ℝ F E] [ContinuousFiberNorm F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  (c : Module.Basis ι ℝ F) (b : OrthonormalBasis ι ℝ V)

/-- **Chart of the Stiefel bundle induced by a linear chart of `E`.** Over `e.baseSet`, an
orthonormal `k`-frame over `y` is read in the local Gram–Schmidt orthonormal frame
`e.orthonormalFrame c b y : V ≃ₗᵢ[ℝ] E y`, giving coordinates in `V_k(V)`. -/
def stiefelBundle (k : ℕ) :
    Trivialization (stiefel V k) (StiefelBundle.proj : StiefelBundle F E k → B) where
  toFun p := (p.proj, ((e.orthonormalFrameAt c b p.proj).stiefelHomeomorph k).symm p.frame)
  invFun q := ⟨q.1, (e.orthonormalFrameAt c b q.1).stiefelHomeomorph k q.2⟩
  source := StiefelBundle.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p _ := by
    obtain ⟨y, v⟩ := p
    exact StiefelBundle.mk_eq_mk_iff.2
      (((e.orthonormalFrameAt c b y).stiefelHomeomorph k).apply_symm_apply v)
  right_inv' q _ :=
    Prod.ext rfl (((e.orthonormalFrameAt c b q.1).stiefelHomeomorph k).symm_apply_apply q.2)
  open_source := e.open_baseSet.preimage StiefelBundle.continuous_proj
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine StiefelBundle.continuous_proj.continuousOn.prodMk ?_
    rw [IsInducing.subtypeVal.continuousOn_iff, continuousOn_pi]
    intro i
    exact ((e.continuousOn_orthonormalFrameAt_symm c b).comp
      (StiefelBundle.continuous_totalSpaceMk_frame i).continuousOn fun _ hp ↦ hp).congr
      fun _ _ ↦ by simp
  continuousOn_invFun := by
    have : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
    rw [continuousOn_iff_continuous_domRestrict]
    refine StiefelBundle.continuous_iff.2 ⟨continuous_fst.comp continuous_subtype_val, fun i ↦ ?_⟩
    have hσ : Continuous fun q : (e.baseSet ×ˢ univ : Set (B × stiefel V k)) ↦
        (⟨q.1.1, e.orthonormalFrameAt c b q.1.1⟩ : OrthonormalFrameBundle ℝ F E V) :=
      ((e.continuous_orthonormalFrame c b).comp
        ((continuous_fst.comp continuous_subtype_val).subtype_mk fun q ↦ q.2.1)).congr fun q ↦
          OrthonormalFrameBundle.mk_eq_mk_iff.2 (e.orthonormalFrameAt_of_mem c b q.2.1).symm
    have hw : Continuous fun q : (e.baseSet ×ˢ univ : Set (B × stiefel V k)) ↦
        (q.1.2 : Fin k → V) i :=
      (continuous_apply i).comp (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val))
    exact (OrthonormalFrameBundle.continuous_totalSpaceMk_frame_apply.comp (hσ.prodMk hw)).congr
      fun _ ↦ TotalSpace.ext rfl (heq_of_eq (by simp))
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem stiefelBundle_baseSet (k : ℕ) : (e.stiefelBundle c b k).baseSet = e.baseSet :=
  (rfl)

/-- Over `e.baseSet`, the Stiefel bundle chart reads the `i`-th vector of a frame in the inverse of
`e.orthonormalFrame c b`. -/
@[simp]
theorem coe_stiefelBundle_apply_snd {k : ℕ} {p : StiefelBundle F E k} (hp : p.proj ∈ e.baseSet)
    (i : Fin k) :
    (((e.stiefelBundle c b k p).2 : stiefel V k) : Fin k → V) i =
      (e.orthonormalFrame c b ⟨p.proj, hp⟩).symm ((p.frame : Fin k → E p.proj) i) := by
  simp [stiefelBundle, e.orthonormalFrameAt_of_mem c b hp]

/-- At any point, the Stiefel bundle chart reads the `i`-th vector of a frame in the inverse of
`e.orthonormalFrameAt c b`. -/
theorem coe_stiefelBundle_apply_snd_eq_orthonormalFrameAt {k : ℕ} (p : StiefelBundle F E k)
    (i : Fin k) :
    (((e.stiefelBundle c b k p).2 : stiefel V k) : Fin k → V) i =
      (e.orthonormalFrameAt c b p.proj).symm ((p.frame : Fin k → E p.proj) i) := by
  simp [stiefelBundle]

/-- Over `e.baseSet`, the inverse Stiefel bundle chart applies `e.orthonormalFrame c b` to each
vector of the model frame. -/
theorem stiefelBundle_symm_apply {k : ℕ} (y : e.baseSet) (w : stiefel V k) :
    (e.stiefelBundle c b k).toOpenPartialHomeomorph.symm ((y : B), w) =
      ⟨y, (e.orthonormalFrame c b y).stiefelHomeomorph k w⟩ := by
  have hy : (y : B) ∈ e.baseSet := y.2
  -- Unfold `stiefelBundle`'s `invFun`, then rewrite `orthonormalFrameAt` on `e.baseSet`.
  change (⟨(y : B), (e.orthonormalFrameAt c b y).stiefelHomeomorph k w⟩ : StiefelBundle F E k) = _
  rw [e.orthonormalFrameAt_of_mem c b hy]

end Bundle.Trivialization

namespace TauCeti.StiefelBundle

open TauCeti

section BaseLocallyTrivial

variable {B F V : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiberBundle F E] [VectorBundle ℝ F E] [ContinuousFiberNorm F E]

/-- **The Stiefel bundle is locally trivial over `B`.** When `V` has the dimension of `F`, every
point of `B` lies in the base set of a chart of `V_k(E) → B` with fibre `V_k(V)`. -/
theorem exists_trivialization [FiniteDimensional ℝ F] [FiniteDimensional ℝ V]
    (h : finrank ℝ V = finrank ℝ F) (k : ℕ) (x : B) :
    ∃ t : Trivialization (stiefel V k) (proj : StiefelBundle F E k → B), x ∈ t.baseSet :=
  ⟨(trivializationAt F E x).stiefelBundle (Module.finBasisOfFinrankEq ℝ F h.symm)
    (stdOrthonormalBasis ℝ V) k, mem_baseSet_trivializationAt F E x⟩

variable (F E)

/-- **The projection `V_k(E) → B` is proper** for a finite-rank real vector bundle with continuous
fibre norm: it is locally trivial with compact fibre `V_k(ℝᵈ)`. -/
theorem isProperMap_proj [FiniteDimensional ℝ F] (k : ℕ) :
    IsProperMap (proj : StiefelBundle F E k → B) :=
  isProperMap_of_forall_exists_trivialization
    (exists_trivialization (V := EuclideanSpace ℝ (Fin (finrank ℝ F)))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ F)) k)

/-- Over a compact base, the Stiefel bundle of a finite-rank real vector bundle with continuous
fibre norm is compact. -/
instance compactSpace [CompactSpace B] [FiniteDimensional ℝ F] (k : ℕ) :
    CompactSpace (StiefelBundle F E k) :=
  ⟨by simpa using (isProperMap_proj F E k).isCompact_preimage isCompact_univ⟩

/-- **The projection `V_k(E) → B` is a Hurewicz fibration** over a normal paracompact base. -/
theorem isHurewiczFibration_proj.{u} [NormalSpace B] [ParacompactSpace B] [FiniteDimensional ℝ F]
    (k : ℕ) : IsHurewiczFibration.{u} (proj : StiefelBundle F E k → B) :=
  isHurewiczFibration_of_exists_trivialization
    (exists_trivialization (V := EuclideanSpace ℝ (Fin (finrank ℝ F)))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ F)) k)

end BaseLocallyTrivial

/-- **The projection `V_k(E) → B` is a Serre fibration.** -/
theorem mem_serreFibrations_proj.{w} {B : Type w} (F : Type*) (E : B → Type w)
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
    [∀ b, InnerProductSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
    [ContinuousFiberNorm F E] [FiniteDimensional ℝ F] (k : ℕ) :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨proj, continuous_proj⟩ :
        _root_.TopCat.of (StiefelBundle F E k) ⟶ _root_.TopCat.of B) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (exists_trivialization (V := EuclideanSpace ℝ (Fin (finrank ℝ F)))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ F)) k)

/-! ### Projections to the unit sphere bundle and vertical frame fibres -/

section SphereBundle

universe w

variable {B : Type w} [TopologicalSpace B] {F : Type*}
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-- Evaluating the `i`-th vector of an orthonormal `k`-frame gives a continuous map
`V_k(E) → S(E)` to the unit sphere bundle. -/
def vecProj {k : ℕ} (i : Fin k) : C(StiefelBundle F E k, sphereBundle F E) where
  toFun p := ⟨⟨p.proj, (p.frame : Fin k → E p.proj) i⟩,
    mem_sphereBundle.2 (norm_eq_one_of_mem_stiefel p.frame.2 i)⟩
  continuous_toFun := (continuous_totalSpaceMk_frame i).subtype_mk _

@[simp]
theorem coe_vecProj_apply {k : ℕ} (i : Fin k) (p : StiefelBundle F E k) :
    (vecProj i p : TotalSpace F E) = ⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ :=
  (rfl)

section TopologicalFiber

variable [TopologicalSpace F] [FiberBundle F E]

variable (F E) in
/-- **Orthonormal `1`-frames are unit vectors**: `V₁(E) ≃ₜ S(E)`. -/
def oneHomeomorphSphereBundle : StiefelBundle F E 1 ≃ₜ sphereBundle F E where
  toFun := vecProj 0
  invFun q := ⟨q.1.proj,
    (stiefelOneHomeomorphSphere (E q.1.proj)).symm (unitSphereOfSphereBundle q)⟩
  left_inv p := by
    obtain ⟨b, v⟩ := p
    exact mk_eq_mk_iff.2 <| Subtype.ext <| funext fun i ↦ by
      rw [Subsingleton.elim i 0, coe_stiefelOneHomeomorphSphere_symm_apply]
      rfl
  right_inv q := Subtype.ext <| TotalSpace.ext rfl
    (heq_of_eq (coe_stiefelOneHomeomorphSphere_symm_apply (unitSphereOfSphereBundle q) 0))
  continuous_toFun := (vecProj 0).continuous
  continuous_invFun := continuous_iff_of_neZero.2 fun i ↦ by
    rw [Subsingleton.elim i 0]
    exact continuous_subtype_val.congr fun q ↦ TotalSpace.ext rfl
      (heq_of_eq (coe_stiefelOneHomeomorphSphere_symm_apply (unitSphereOfSphereBundle q) 0).symm)

@[simp]
theorem oneHomeomorphSphereBundle_apply (p : StiefelBundle F E 1) :
    oneHomeomorphSphereBundle F E p = vecProj 0 p := by
  rw [oneHomeomorphSphereBundle]
  -- After unfolding `oneHomeomorphSphereBundle`, `toFun` is `vecProj 0`.
  rfl

theorem totalSpaceMk_oneHomeomorphSphereBundle_symm (q : sphereBundle F E) (i : Fin 1) :
    (⟨((oneHomeomorphSphereBundle F E).symm q).proj,
        (((oneHomeomorphSphereBundle F E).symm q).frame :
          Fin 1 → E ((oneHomeomorphSphereBundle F E).symm q).proj) i⟩ : TotalSpace F E) =
      q.1 := by
  rw [Subsingleton.elim i 0, oneHomeomorphSphereBundle]
  exact TotalSpace.ext rfl
    (heq_of_eq (coe_stiefelOneHomeomorphSphere_symm_apply (unitSphereOfSphereBundle q) 0))

end TopologicalFiber

section FiberBundle

variable [NormedAddCommGroup F] [FiberBundle F E]

theorem sphereBundleProj_vecProj {k : ℕ} (i : Fin k) (p : StiefelBundle F E k) :
    sphereBundleProj F E (vecProj i p) = p.proj :=
  sphereBundleProj_apply F E _

@[simp]
theorem proj_oneHomeomorphSphereBundle_symm (q : sphereBundle F E) :
    ((oneHomeomorphSphereBundle F E).symm q).proj = sphereBundleProj F E q := by
  rw [oneHomeomorphSphereBundle, sphereBundleProj_apply]
  -- After unfolding both sides, `proj` of `invFun q` is `q.1.proj`.
  rfl

theorem vecProj_fiberIncl {k : ℕ} (i : Fin k) (b : B) (v : stiefel (E b) k) :
    vecProj i (fiberIncl F E k b v) = sphereBundleFiberIncl F E b (stiefelProj (E b) k i v) :=
  Subtype.ext (by simp)

/-- **Inclusion of the vertical `k`-frame fibre `V_k(q^⊥) → V_{k+1}(E)` over `q : S(E)`.** It
prepends `q` as the first vector of an orthonormal `(k + 1)`-frame of `E q.1.proj`. -/
def sphereFiberIncl (q : sphereBundle F E) (k : ℕ) :
    C(stiefel (ℝ ∙ q.1.2)ᗮ k, StiefelBundle F E (k + 1)) :=
  (fiberIncl F E (k + 1) q.1.proj).comp (stiefelFrameIncl (unitSphereOfSphereBundle q) k)

theorem sphereFiberIncl_apply (q : sphereBundle F E) (k : ℕ) (x : stiefel (ℝ ∙ q.1.2)ᗮ k) :
    sphereFiberIncl q k x =
      fiberIncl F E (k + 1) q.1.proj (stiefelFrameIncl (unitSphereOfSphereBundle q) k x) :=
  (rfl)

@[simp]
theorem vecProj_zero_sphereFiberIncl (q : sphereBundle F E) (k : ℕ) (x : stiefel (ℝ ∙ q.1.2)ᗮ k) :
    vecProj 0 (sphereFiberIncl q k x) = q := by
  rw [sphereFiberIncl_apply, vecProj_fiberIncl, stiefelProj_zero_stiefelFrameIncl,
    sphereBundleFiberIncl_unitSphereOfSphereBundle]

/-- The vertical frame inclusion `V_k(q^⊥) → V_{k+1}(E)` is a topological embedding. -/
theorem isEmbedding_sphereFiberIncl (q : sphereBundle F E) (k : ℕ) :
    IsEmbedding (sphereFiberIncl q k) :=
  (isEmbedding_fiberIncl F E (k + 1) q.1.proj).comp
    (isClosedEmbedding_stiefelFrameIncl (unitSphereOfSphereBundle q) k).isEmbedding

/-- The range of `V_k(q^⊥) → V_{k+1}(E)` is the fibre of `vecProj 0 : V_{k+1}(E) → S(E)` over
`q`. -/
theorem range_sphereFiberIncl (q : sphereBundle F E) (k : ℕ) :
    range (sphereFiberIncl q k) = (vecProj (F := F) (E := E) (0 : Fin (k + 1))) ⁻¹' {q} := by
  refine Subset.antisymm (range_subset_iff.2 fun x ↦ by simp) fun p hp ↦ ?_
  have hproj : p.proj = q.1.proj := by
    have := congrArg (sphereBundleProj F E) (mem_singleton_iff.1 hp)
    rwa [sphereBundleProj_vecProj, sphereBundleProj_apply] at this
  obtain ⟨b, v⟩ := p
  dsimp only at hproj
  subst hproj
  have hv : v ∈ range (stiefelFrameIncl (unitSphereOfSphereBundle q) k) := by
    rw [range_stiefelFrameIncl, mem_preimage, mem_singleton_iff]
    refine Subtype.ext ?_
    have h0 := congrArg (fun r : sphereBundle F E ↦ r.1) (mem_singleton_iff.1 hp)
    simpa using TotalSpace.mk_inj.1 h0
  obtain ⟨x, rfl⟩ := hv
  exact ⟨x, rfl⟩

/-- When the base is `T₁`, the vertical frame inclusion `V_k(q^⊥) → V_{k+1}(E)` is a closed
embedding. -/
theorem isClosedEmbedding_sphereFiberIncl [T1Space B] (q : sphereBundle F E) (k : ℕ) :
    IsClosedEmbedding (sphereFiberIncl q k) :=
  (isClosedEmbedding_fiberIncl F E (k + 1) q.1.proj).comp
    (isClosedEmbedding_stiefelFrameIncl (unitSphereOfSphereBundle q) k)

/-- **Homeomorphism onto the fibre of `vecProj 0 : V_{k+1}(E) → S(E)` over `q : S(E)`.** -/
def sphereFiberHomeomorph (q : sphereBundle F E) (k : ℕ) :
    stiefel (ℝ ∙ q.1.2)ᗮ k ≃ₜ (vecProj (F := F) (E := E) (0 : Fin (k + 1))) ⁻¹' {q} :=
  (isEmbedding_sphereFiberIncl q k).toHomeomorph.trans
    (Homeomorph.setCongr (range_sphereFiberIncl q k))

@[simp]
theorem coe_sphereFiberHomeomorph_apply (q : sphereBundle F E) (k : ℕ)
    (x : stiefel (ℝ ∙ q.1.2)ᗮ k) :
    (sphereFiberHomeomorph q k x : StiefelBundle F E (k + 1)) = sphereFiberIncl q k x :=
  (rfl)

@[simp]
theorem sphereFiberIncl_sphereFiberHomeomorph_symm (q : sphereBundle F E) (k : ℕ)
    (p : (vecProj (F := F) (E := E) (0 : Fin (k + 1))) ⁻¹' {q}) :
    sphereFiberIncl q k ((sphereFiberHomeomorph q k).symm p) = p :=
  congrArg Subtype.val ((sphereFiberHomeomorph q k).apply_symm_apply p)

end FiberBundle

/-! ### Local triviality and connectivity over the sphere bundle -/

section LocallyTrivialOverSphereBundle

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]

/-- **The projection `vecProj 0 : V_{k+1}(E) → S(E)` is locally trivial over `S(E)`.** If the model
fibre `F` has dimension `n + 1`, every point of `S(E)` lies in the base set of a chart of
`vecProj 0` with fibre `V_k(ℝⁿ)`. -/
theorem exists_trivialization_vecProj_zero {n : ℕ} (hF : finrank ℝ F = n + 1) (k : ℕ)
    (q : sphereBundle F E) :
    ∃ e : Trivialization (stiefel (EuclideanSpace ℝ (Fin n)) k)
      (vecProj (F := F) (E := E) (0 : Fin (k + 1))), q ∈ e.baseSet := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let c := Module.finBasisOfFinrankEq ℝ F hF
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  refine exists_trivialization_of_fiberMap (p₁ := (proj : StiefelBundle F E (k + 1) → B))
    (p₂ := (proj : StiefelBundle F E 1 → B) ∘ (oneHomeomorphSphereBundle F E).symm)
    (vecProj 0).continuous
    (fun p ↦ (proj_oneHomeomorphSphereBundle_symm _).trans (sphereBundleProj_vecProj 0 p))
    (g := stiefelProj V (k + 1) 0) (fun x ↦ ?_)
    (exists_trivialization_stiefelProj_zero (by simp [V]) k) q
  let e₀ := trivializationAt F E x
  let e₁ := e₀.stiefelBundle c b (k + 1)
  let e₂ := ((e₀.stiefelBundle c b 1).compHomeomorph
    (oneHomeomorphSphereBundle F E).symm).transFiberHomeomorph (stiefelOneHomeomorphSphere V)
  refine ⟨e₁, e₂, mem_baseSet_trivializationAt F E x,
    mem_baseSet_trivializationAt F E x, fun p _ _ ↦ Subtype.ext ?_⟩
  let Φ : TotalSpace F E → V := fun r ↦ (e₀.orthonormalFrameAt c b r.proj).symm r.2
  have hlhs : (((e₂ (vecProj 0 p)).2 : sphere (0 : V) 1) : V) =
      Φ (vecProj 0 p : TotalSpace F E) := by
    -- Unfold `e₂` as `stiefelOneHomeomorphSphere V` applied to `e₀.stiefelBundle c b 1`.
    change (stiefelOneHomeomorphSphere V
        ((e₀.stiefelBundle c b 1 ((oneHomeomorphSphereBundle F E).symm (vecProj 0 p))).2) : V) = _
    rw [stiefelOneHomeomorphSphere_apply, coe_stiefelProj,
      e₀.coe_stiefelBundle_apply_snd_eq_orthonormalFrameAt]
    exact congrArg Φ (totalSpaceMk_oneHomeomorphSphereBundle_symm (vecProj 0 p) 0)
  have hrhs : (stiefelProj V (k + 1) 0 (e₁ p).2 : V) = Φ (vecProj 0 p : TotalSpace F E) := by
    rw [coe_stiefelProj, e₀.coe_stiefelBundle_apply_snd_eq_orthonormalFrameAt]
    rfl
  exact hlhs.trans hrhs.symm

variable (F E) in
/-- **The projection `vecProj 0 : V_{k+1}(E) → S(E)` is a Serre fibration** in finite rank. -/
theorem mem_serreFibrations_vecProj_zero [FiniteDimensional ℝ F] (k : ℕ) :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom (vecProj (F := F) (E := E) (0 : Fin (k + 1))) :
        _root_.TopCat.of (StiefelBundle F E (k + 1)) ⟶ _root_.TopCat.of (sphereBundle F E)) := by
  rcases eq_zero_or_pos (finrank ℝ F) with h0 | hpos
  · have : Subsingleton F := Module.finrank_zero_iff.1 h0
    exact TopCat.mem_serreFibrations_of_exists_trivialization (F := Empty) fun q ↦ isEmptyElim q
  · exact TopCat.mem_serreFibrations_of_exists_trivialization
      (exists_trivialization_vecProj_zero (Nat.sub_add_cancel hpos).symm k)

variable (F E) in
/-- **The projection `vecProj 0 : V_{k+1}(E) → S(E)` is a Hurewicz fibration** when `S(E)` is normal
and paracompact. -/
theorem isHurewiczFibration_vecProj_zero.{u} [NormalSpace (sphereBundle F E)]
    [ParacompactSpace (sphereBundle F E)] [FiniteDimensional ℝ F] (k : ℕ) :
    IsHurewiczFibration.{u} (vecProj (F := F) (E := E) (0 : Fin (k + 1))) := by
  rcases eq_zero_or_pos (finrank ℝ F) with h0 | hpos
  · have : Subsingleton F := Module.finrank_zero_iff.1 h0
    exact isHurewiczFibration_of_exists_trivialization (F := Empty) fun q ↦ isEmptyElim q
  · exact isHurewiczFibration_of_exists_trivialization
      (exists_trivialization_vecProj_zero (Nat.sub_add_cancel hpos).symm k)

/-- **Connectivity of `vecProj 0 : V_{k+1}(E) → S(E)`.** When the model fibre `F` has dimension
`n + 1` and `k ≤ n`, `vecProj 0` is `(n - k)`-connected: its fibres `V_k(q^⊥)` are nonempty and
`(n - k - 1)`-connected. -/
theorem isNConnected_vecProj_zero {n k : ℕ} (hF : finrank ℝ F = n + 1) (hk : k ≤ n) :
    (vecProj (F := F) (E := E) (0 : Fin (k + 1))).IsNConnected (n - k) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations
    (mem_serreFibrations_vecProj_zero F E k) (n - k)).2 fun q ↦ ?_
  let L := (trivializationAt F E q.1.proj).continuousLinearEquivAt ℝ q.1.proj
    (mem_baseSet_trivializationAt F E q.1.proj)
  have : Fact (finrank ℝ (E q.1.proj) = n + 1) := ⟨L.toLinearEquiv.finrank_eq.trans hF⟩
  have : FiniteDimensional ℝ (E q.1.proj) := .of_fact_finrank_eq_succ n
  have hperp : finrank ℝ (ℝ ∙ q.1.2)ᗮ = n :=
    Submodule.finrank_orthogonal_span_singleton
      (ne_zero_of_mem_unit_sphere (unitSphereOfSphereBundle q))
  refine ⟨?_, fun e m hm ↦ ?_⟩
  · obtain ⟨x, hx⟩ := (nonempty_stiefel (E := (ℝ ∙ q.1.2)ᗮ) (k := k)).2 (by omega)
    exact ⟨sphereFiberHomeomorph q k ⟨x, hx⟩⟩
  · let φ : (_root_.TopCat.ofHom (vecProj (F := F) (E := E) (0 : Fin (k + 1))) :
        _root_.TopCat.of (StiefelBundle F E (k + 1)) ⟶ _root_.TopCat.of (sphereBundle F E)).fiber q
        ≃ₜ stiefel (ℝ ∙ q.1.2)ᗮ k :=
      ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (sphereFiberHomeomorph q k).symm
    have := subsingleton_homotopyGroup_stiefel (M := Fin m) (by simp [hperp]; omega) (φ e)
    exact (HomotopyGroup.homeomorphEquiv φ e).subsingleton

end LocallyTrivialOverSphereBundle

end SphereBundle

end TauCeti.StiefelBundle
