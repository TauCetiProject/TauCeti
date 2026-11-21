/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.Projection
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import TauCeti.Topology.VectorBundle.SphereBundle.Fiber
public import TauCeti.Topology.VectorBundle.SphereBundle.Stiefel
import TauCeti.Topology.FiberBundle.FiberMap
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# Local triviality of the Stiefel bundle of a Riemannian vector bundle

Let `E → B` be a real vector bundle with model fibre `F` whose fibres carry inner products, and let
`V_k(E)` (`TauCeti.StiefelBundle F E k`, defined in
`TauCeti.Topology.VectorBundle.SphereBundle.Stiefel`) be its Stiefel bundle of orthonormal
`k`-frames. This file adds the identification `V_0(E) ≃ₜ B`
(`TauCeti.StiefelBundle.zeroHomeomorph`) and the homeomorphism of `V_k(E_b)` onto the fibre over
`b : B` (`TauCeti.StiefelBundle.fiberHomeomorph`), and proves local triviality over `B` and over
the unit sphere bundle.

When the fibre norm is continuous on the total space (`TauCeti.ContinuousFiberNorm F E`), a linear
chart `e` of `E`, a basis `c` of `F` and an orthonormal basis `b` of a model inner product space
`V` trivialize `V_k(E) → B` over `e.baseSet` with fibre `V_k(V)`
(`Bundle.Trivialization.stiefelBundle`), by reading frames in the Gram–Schmidt local orthonormal
frame `e.orthonormalFrame c b`. Thus in finite rank `V_k(E) → B` is locally trivial
(`TauCeti.StiefelBundle.exists_trivialization`), proper
(`TauCeti.StiefelBundle.isProperMap_proj`), and a Serre (or Hurewicz) fibration.

Each index `i : Fin k` projects `V_k(E)` to the unit sphere bundle `S(E)`
(`TauCeti.StiefelBundle.sphereProj`). For `k + 1` vectors, the fibre of the first-vector
projection `sphereProj 0 : V_{k+1}(E) → S(E)` over a unit vector `q ∈ S(E)` is the Stiefel manifold
`V_k(q^⊥)` of vertical orthonormal `k`-frames tangent to the sphere fibre at `q`
(`TauCeti.StiefelBundle.sphereFiberIncl`, `TauCeti.StiefelBundle.sphereFiberHomeomorph`). In local
orthonormal frames over `B`, `sphereProj 0` reads as the model Stiefel projection
`V_{k+1}(V) → S(V)`, so `Bundle.Trivialization.ofFiberMap` and
`TauCeti.exists_trivialization_stiefelProj_zero` make `sphereProj 0 : V_{k+1}(E) → S(E)` locally
trivial with fibre `V_k(ℝⁿ)` when `finrank ℝ F = n + 1`
(`TauCeti.StiefelBundle.exists_trivialization_sphereProj_zero`), hence a Serre fibration and
`(n - k)`-connected for `k ≤ n` (`TauCeti.StiefelBundle.isNConnected_sphereProj_zero`). For `k = 2`,
`V₃(E) → S(E)` is the carrier of the fibered family of two-spheres of a sphere bundle in
Barraud–Damian–Humilière–Oancea, Proposition 6.23.

## Main declarations

* `TauCeti.StiefelBundle.zeroHomeomorph`: `V_0(E) ≃ₜ B`.
* `TauCeti.StiefelBundle.fiberHomeomorph`: the fibre `V_k(E_b)` over `b : B`.
* `Bundle.Trivialization.stiefelBundle`, `TauCeti.StiefelBundle.exists_trivialization`: local
  triviality of `V_k(E) → B` with fibre `V_k(V)`.
* `TauCeti.StiefelBundle.oneHomeomorphSphereBundle : V₁(E) ≃ₜ S(E)`.
* `TauCeti.StiefelBundle.sphereFiberIncl`, `TauCeti.StiefelBundle.sphereFiberHomeomorph`: the
  vertical `k`-frame fibre `V_k(q^⊥)` over `q : S(E)`.
* `TauCeti.StiefelBundle.exists_trivialization_sphereProj_zero`,
  `TauCeti.StiefelBundle.mem_serreFibrations_sphereProj_zero`,
  `TauCeti.StiefelBundle.isNConnected_sphereProj_zero`: local triviality, Serre fibration property,
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

namespace StiefelBundle

section Basic

variable {B F : Type*} {E : B → Type*} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {k : ℕ}

/-- A point of `StiefelBundle` equals the transported frame over any base point equal to its
projection. -/
theorem eq_mk_of_proj_eq {b : B} (p : StiefelBundle F E k) (h : p.proj = b) :
    p = ⟨b, h ▸ p.frame⟩ := by
  cases p
  cases h
  rfl

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]

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

/-- The fibre inclusion `V_k(E_b) → V_k(E)` is injective. -/
theorem fiberIncl_injective (b : B) : Function.Injective (fiberIncl F E k b) :=
  (isEmbedding_fiberIncl F E k b).injective

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
    refine StiefelBundle.continuous_iff.2 ⟨continuous_fst.comp continuous_subtypeVal, fun i ↦ ?_⟩
    have hσ : Continuous fun q : (e.baseSet ×ˢ univ : Set (B × stiefel V k)) ↦
        (⟨q.val.1, e.orthonormalFrameAt c b q.val.1⟩ : OrthonormalFrameBundle ℝ F E V) :=
      ((e.continuous_orthonormalFrame c b).comp
        ((continuous_fst.comp continuous_subtypeVal).subtype_mk fun q ↦ q.property.1)).congr fun q ↦
          OrthonormalFrameBundle.mk_eq_mk_iff.2 (e.orthonormalFrameAt_of_mem c b q.property.1).symm
    have hw : Continuous fun q : (e.baseSet ×ˢ univ : Set (B × stiefel V k)) ↦
        (q.val.2 : Fin k → V) i :=
      (continuous_apply i).comp (continuous_subtypeVal.comp
        (continuous_snd.comp continuous_subtypeVal))
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
  have hy : (y : B) ∈ e.baseSet := y.property
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

section TopologicalFiber

variable [TopologicalSpace F] [FiberBundle F E]

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [TopologicalSpace F]
  [FiberBundle F E] in
/-- The unit vector `q` of `S(E)`, read as an orthonormal `1`-frame of its fibre, has `q` as its
vector. -/
private theorem totalSpaceMk_stiefelOneHomeomorphSphere_symm (q : sphereBundle F E) (i : Fin 1) :
    (⟨q.val.proj, ((stiefelOneHomeomorphSphere (E q.val.proj)).symm (unitSphereOfSphereBundle q) :
      Fin 1 → E q.val.proj) i⟩ : TotalSpace F E) = q.val :=
  TotalSpace.ext rfl
    (heq_of_eq (coe_stiefelOneHomeomorphSphere_symm_apply (unitSphereOfSphereBundle q) i))

variable (F E) in
/-- **Orthonormal `1`-frames are unit vectors**: `V₁(E) ≃ₜ S(E)`. -/
def oneHomeomorphSphereBundle : StiefelBundle F E 1 ≃ₜ sphereBundle F E where
  toFun := sphereProj F 1 0
  invFun q := ⟨q.val.proj,
    (stiefelOneHomeomorphSphere (E q.val.proj)).symm (unitSphereOfSphereBundle q)⟩
  left_inv p := ext (congrArg TotalSpace.proj (coe_sphereProj_apply 0 p)) fun i ↦
    (totalSpaceMk_stiefelOneHomeomorphSphere_symm _ i).trans
      ((coe_sphereProj_apply 0 p).trans (by rw [Subsingleton.elim i 0]))
  right_inv q := Subtype.ext <|
    (coe_sphereProj_apply 0 _).trans (totalSpaceMk_stiefelOneHomeomorphSphere_symm q 0)
  continuous_toFun := (sphereProj F 1 0).continuous
  continuous_invFun := continuous_iff_of_neZero.2 fun i ↦ by
    rw [Subsingleton.elim i 0]
    exact continuous_subtypeVal.congr fun q ↦ TotalSpace.ext rfl
      (heq_of_eq (coe_stiefelOneHomeomorphSphere_symm_apply (unitSphereOfSphereBundle q) 0).symm)

@[simp]
theorem oneHomeomorphSphereBundle_apply (p : StiefelBundle F E 1) :
    oneHomeomorphSphereBundle F E p = sphereProj F 1 0 p := by
  rw [oneHomeomorphSphereBundle]
  -- After unfolding `oneHomeomorphSphereBundle`, `toFun` is `sphereProj F 1 0`.
  rfl

theorem totalSpaceMk_oneHomeomorphSphereBundle_symm (q : sphereBundle F E) (i : Fin 1) :
    (⟨((oneHomeomorphSphereBundle F E).symm q).proj,
        (((oneHomeomorphSphereBundle F E).symm q).frame :
          Fin 1 → E ((oneHomeomorphSphereBundle F E).symm q).proj) i⟩ : TotalSpace F E) =
      q.val := by
  rw [Subsingleton.elim i 0, oneHomeomorphSphereBundle]
  exact TotalSpace.ext rfl
    (heq_of_eq (coe_stiefelOneHomeomorphSphere_symm_apply (unitSphereOfSphereBundle q) 0))

end TopologicalFiber

section FiberBundle

variable [NormedAddCommGroup F] [FiberBundle F E]

theorem sphereBundleProj_sphereProj {k : ℕ} (i : Fin k) (p : StiefelBundle F E k) :
    sphereBundleProj F E (sphereProj F k i p) = p.proj :=
  (sphereBundleProj_apply F E _).trans (congrArg TotalSpace.proj (coe_sphereProj_apply i p))

@[simp]
theorem proj_oneHomeomorphSphereBundle_symm (q : sphereBundle F E) :
    ((oneHomeomorphSphereBundle F E).symm q).proj = sphereBundleProj F E q := by
  rw [oneHomeomorphSphereBundle, sphereBundleProj_apply]
  -- After unfolding both sides, `proj` of `invFun q` is `q.1.proj`.
  rfl

/-- **Inclusion of the vertical `k`-frame fibre `V_k(q^⊥) → V_{k+1}(E)` over `q : S(E)`.** It
prepends `q` as the first vector of an orthonormal `(k + 1)`-frame of `E q.1.proj`. -/
def sphereFiberIncl (q : sphereBundle F E) (k : ℕ) :
    C(stiefel (ℝ ∙ q.val.snd)ᗮ k, StiefelBundle F E (k + 1)) :=
  (fiberIncl F E (k + 1) q.val.proj).comp (stiefelFrameIncl (unitSphereOfSphereBundle q) k)

theorem sphereFiberIncl_apply (q : sphereBundle F E) (k : ℕ) (x : stiefel (ℝ ∙ q.val.snd)ᗮ k) :
    sphereFiberIncl q k x =
      fiberIncl F E (k + 1) q.val.proj (stiefelFrameIncl (unitSphereOfSphereBundle q) k x) :=
  (rfl)

@[simp]
theorem sphereProj_zero_sphereFiberIncl (q : sphereBundle F E) (k : ℕ)
    (x : stiefel (ℝ ∙ q.val.snd)ᗮ k) : sphereProj F (k + 1) 0 (sphereFiberIncl q k x) = q := by
  rw [sphereFiberIncl_apply, sphereProj_fiberIncl, stiefelProj_zero_stiefelFrameIncl,
    sphereBundleFiberIncl_unitSphereOfSphereBundle]

/-- The vertical frame inclusion `V_k(q^⊥) → V_{k+1}(E)` is a topological embedding. -/
theorem isEmbedding_sphereFiberIncl (q : sphereBundle F E) (k : ℕ) :
    IsEmbedding (sphereFiberIncl q k) :=
  (isEmbedding_fiberIncl F E (k + 1) q.val.proj).comp
    (isClosedEmbedding_stiefelFrameIncl (unitSphereOfSphereBundle q) k).isEmbedding

/-- The range of `V_k(q^⊥) → V_{k+1}(E)` is the fibre of `sphereProj 0 : V_{k+1}(E) → S(E)` over
`q`. -/
theorem range_sphereFiberIncl (q : sphereBundle F E) (k : ℕ) :
    range (sphereFiberIncl q k) = (sphereProj (E := E) F (k + 1) 0) ⁻¹' {q} := by
  rw [sphereFiberIncl, ContinuousMap.coe_comp, range_fiberIncl_comp_stiefelFrameIncl,
    sphereBundleFiberIncl_unitSphereOfSphereBundle]

/-- When the base is `T₁`, the vertical frame inclusion `V_k(q^⊥) → V_{k+1}(E)` is a closed
embedding. -/
theorem isClosedEmbedding_sphereFiberIncl [T1Space B] (q : sphereBundle F E) (k : ℕ) :
    IsClosedEmbedding (sphereFiberIncl q k) :=
  (isClosedEmbedding_fiberIncl F E (k + 1) q.val.proj).comp
    (isClosedEmbedding_stiefelFrameIncl (unitSphereOfSphereBundle q) k)

/-- **Homeomorphism onto the fibre of `sphereProj 0 : V_{k+1}(E) → S(E)` over `q : S(E)`.** -/
def sphereFiberHomeomorph (q : sphereBundle F E) (k : ℕ) :
    stiefel (ℝ ∙ q.val.snd)ᗮ k ≃ₜ (sphereProj (E := E) F (k + 1) 0) ⁻¹' {q} :=
  (isEmbedding_sphereFiberIncl q k).toHomeomorph.trans
    (Homeomorph.setCongr (range_sphereFiberIncl q k))

@[simp]
theorem coe_sphereFiberHomeomorph_apply (q : sphereBundle F E) (k : ℕ)
    (x : stiefel (ℝ ∙ q.val.snd)ᗮ k) :
    (sphereFiberHomeomorph q k x : StiefelBundle F E (k + 1)) = sphereFiberIncl q k x :=
  (rfl)

@[simp]
theorem sphereFiberIncl_sphereFiberHomeomorph_symm (q : sphereBundle F E) (k : ℕ)
    (p : (sphereProj (E := E) F (k + 1) 0) ⁻¹' {q}) :
    sphereFiberIncl q k ((sphereFiberHomeomorph q k).symm p) = p :=
  congrArg Subtype.val ((sphereFiberHomeomorph q k).apply_symm_apply p)

end FiberBundle

/-! ### Local triviality and connectivity over the sphere bundle -/

section LocallyTrivialOverSphereBundle

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]

/-- **The projection `sphereProj 0 : V_{k+1}(E) → S(E)` is locally trivial over `S(E)`.** If the
model fibre `F` has dimension `n + 1`, every point of `S(E)` lies in the base set of a chart of
`sphereProj 0` with fibre `V_k(ℝⁿ)`. -/
theorem exists_trivialization_sphereProj_zero {n : ℕ} (hF : finrank ℝ F = n + 1) (k : ℕ)
    (q : sphereBundle F E) :
    ∃ e : Trivialization (stiefel (EuclideanSpace ℝ (Fin n)) k)
      (sphereProj (E := E) F (k + 1) 0), q ∈ e.baseSet := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let c := Module.finBasisOfFinrankEq ℝ F hF
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  refine exists_trivialization_of_fiberMap (p₁ := (proj : StiefelBundle F E (k + 1) → B))
    (p₂ := (proj : StiefelBundle F E 1 → B) ∘ (oneHomeomorphSphereBundle F E).symm)
    (sphereProj F (k + 1) 0).continuous
    (fun p ↦ (proj_oneHomeomorphSphereBundle_symm _).trans (sphereBundleProj_sphereProj 0 p))
    (g := stiefelProj V (k + 1) 0) (fun x ↦ ?_)
    (exists_trivialization_stiefelProj_zero (by simp [V]) k) q
  let e₀ := trivializationAt F E x
  let e₁ := e₀.stiefelBundle c b (k + 1)
  let e₂ := ((e₀.stiefelBundle c b 1).compHomeomorph
    (oneHomeomorphSphereBundle F E).symm).transFiberHomeomorph (stiefelOneHomeomorphSphere V)
  refine ⟨e₁, e₂, mem_baseSet_trivializationAt F E x,
    mem_baseSet_trivializationAt F E x, fun p _ _ ↦ Subtype.ext ?_⟩
  let Φ : TotalSpace F E → V := fun r ↦ (e₀.orthonormalFrameAt c b r.proj).symm r.snd
  have hlhs : (((e₂ (sphereProj F (k + 1) 0 p)).2 : sphere (0 : V) 1) : V) =
      Φ (sphereProj F (k + 1) 0 p : TotalSpace F E) := by
    -- Unfold `e₂` as `stiefelOneHomeomorphSphere V` applied to `e₀.stiefelBundle c b 1`.
    change (stiefelOneHomeomorphSphere V
        ((e₀.stiefelBundle c b 1
          ((oneHomeomorphSphereBundle F E).symm (sphereProj F (k + 1) 0 p))).2) : V) = _
    rw [stiefelOneHomeomorphSphere_apply, coe_stiefelProj,
      e₀.coe_stiefelBundle_apply_snd_eq_orthonormalFrameAt]
    exact congrArg Φ (totalSpaceMk_oneHomeomorphSphereBundle_symm (sphereProj F (k + 1) 0 p) 0)
  have hrhs : (stiefelProj V (k + 1) 0 (e₁ p).2 : V) =
      Φ (sphereProj F (k + 1) 0 p : TotalSpace F E) := by
    rw [coe_stiefelProj, e₀.coe_stiefelBundle_apply_snd_eq_orthonormalFrameAt,
      coe_sphereProj_apply]
  exact hlhs.trans hrhs.symm

variable (F E) in
/-- **The projection `sphereProj 0 : V_{k+1}(E) → S(E)` is a Serre fibration** in finite rank. -/
theorem mem_serreFibrations_sphereProj_zero [FiniteDimensional ℝ F] (k : ℕ) :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom (sphereProj (E := E) F (k + 1) 0) :
        _root_.TopCat.of (StiefelBundle F E (k + 1)) ⟶ _root_.TopCat.of (sphereBundle F E)) := by
  rcases eq_zero_or_pos (finrank ℝ F) with h0 | hpos
  · have : Subsingleton F := Module.finrank_zero_iff.1 h0
    exact TopCat.mem_serreFibrations_of_exists_trivialization (F := Empty) fun q ↦ isEmptyElim q
  · exact TopCat.mem_serreFibrations_of_exists_trivialization
      (exists_trivialization_sphereProj_zero (Nat.sub_add_cancel hpos).symm k)

variable (F E) in
/-- **The projection `sphereProj 0 : V_{k+1}(E) → S(E)` is a Hurewicz fibration** when `S(E)` is
normal and paracompact. -/
theorem isHurewiczFibration_sphereProj_zero.{u} [NormalSpace (sphereBundle F E)]
    [ParacompactSpace (sphereBundle F E)] [FiniteDimensional ℝ F] (k : ℕ) :
    IsHurewiczFibration.{u} (sphereProj (E := E) F (k + 1) 0) := by
  rcases eq_zero_or_pos (finrank ℝ F) with h0 | hpos
  · have : Subsingleton F := Module.finrank_zero_iff.1 h0
    exact isHurewiczFibration_of_exists_trivialization (F := Empty) fun q ↦ isEmptyElim q
  · exact isHurewiczFibration_of_exists_trivialization
      (exists_trivialization_sphereProj_zero (Nat.sub_add_cancel hpos).symm k)

/-- **Connectivity of `sphereProj 0 : V_{k+1}(E) → S(E)`.** When the model fibre `F` has dimension
`n + 1` and `k ≤ n`, `sphereProj 0` is `(n - k)`-connected: its fibres `V_k(q^⊥)` are nonempty and
`(n - k - 1)`-connected. -/
theorem isNConnected_sphereProj_zero {n k : ℕ} (hF : finrank ℝ F = n + 1) (hk : k ≤ n) :
    (sphereProj (E := E) F (k + 1) 0).IsNConnected (n - k) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations
    (mem_serreFibrations_sphereProj_zero F E k) (n - k)).2 fun q ↦ ?_
  let L := (trivializationAt F E q.val.proj).continuousLinearEquivAt ℝ q.val.proj
    (mem_baseSet_trivializationAt F E q.val.proj)
  have : Fact (finrank ℝ (E q.val.proj) = n + 1) := ⟨L.toLinearEquiv.finrank_eq.trans hF⟩
  have : FiniteDimensional ℝ (E q.val.proj) := .of_fact_finrank_eq_succ n
  have hperp : finrank ℝ (ℝ ∙ q.val.snd)ᗮ = n :=
    Submodule.finrank_orthogonal_span_singleton
      (ne_zero_of_mem_unit_sphere (unitSphereOfSphereBundle q))
  refine ⟨?_, fun e m hm ↦ ?_⟩
  · obtain ⟨x, hx⟩ := (nonempty_stiefel (E := (ℝ ∙ q.val.snd)ᗮ) (k := k)).2 (by omega)
    exact ⟨sphereFiberHomeomorph q k ⟨x, hx⟩⟩
  · let φ : (_root_.TopCat.ofHom (sphereProj (E := E) F (k + 1) 0) :
        _root_.TopCat.of (StiefelBundle F E (k + 1)) ⟶ _root_.TopCat.of (sphereBundle F E)).fiber q
        ≃ₜ stiefel (ℝ ∙ q.val.snd)ᗮ k :=
      ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (sphereFiberHomeomorph q k).symm
    have := subsingleton_homotopyGroup_stiefel (M := Fin m) (by simp [hperp]; omega) (φ e)
    exact (HomotopyGroup.homeomorphEquiv φ e).subsingleton

end LocallyTrivialOverSphereBundle

end SphereBundle

end TauCeti.StiefelBundle
