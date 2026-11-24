/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless

/-!
# Globally defined differentiable local parametrizations

Every point of a finite-dimensional boundaryless real `C^n` manifold lies in the image of a
`C^n` parametrization defined on an entire Cartesian space, with `C^n` inverse on its image,
for every finite order or smoothness order `n ≤ ∞`.
These parametrizations allow continuity and smoothness to be tested on globally defined plots,
without requiring a chart inverse to extend beyond its domain.
In particular, every point of a finite-dimensional boundaryless real manifold, on any boundaryless
model, has an open neighbourhood homeomorphic to `ℝᵐ`
(`TauCeti.exists_isOpen_mem_nonempty_homeomorph_euclideanSpace`).

The construction uses Mathlib's `OpenPartialHomeomorph.univBall` and `toEuclidean` to shrink
an ordinary manifold chart.

When the model space `F` is itself a real inner product space, no change of coordinates is needed:
every point of a boundaryless `C^n` manifold modelled on `F` is the centre of a coordinate ball, an
open embedding `F → N` which is a `C^n` local diffeomorphism
(`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`).

For an arbitrary model with corners, every interior point of a finite-dimensional real `C^n`
manifold has an open neighbourhood `C^n`-diffeomorphic to the Euclidean space of the same
dimension (`TauCeti.exists_opens_diffeomorph_euclideanSpace`). Such Euclidean neighbourhoods let
invariants computed on `ℝⁿ` be transported to small open subsets of a manifold.

Open coordinate boxes `TauCeti.openBox` in `EuclideanSpace ℝ ι` form a basis of open subsets closed
under finite intersections (`TauCeti.isBasis_openBoxes`, `TauCeti.openBox_inf_openBox`), and every
nonempty box is `C^n`-diffeomorphic to `EuclideanSpace ℝ ι` (`TauCeti.diffeomorphOpenBox`).
-/

public noncomputable section

open Set Function Metric
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : ℕ∞} [IsManifold 𝓘(ℝ, E) n M]

/-- A point of a finite-dimensional boundaryless real `C^n` manifold, for `n ≤ ∞`, has `C^n`
local coordinates parametrized by an entire Cartesian space, with a `C^n` inverse on their
open image. -/
theorem exists_contMDiff_parametrization (x : M) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M,
      e.source = univ ∧ x ∈ e.target ∧
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ, E) n e ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        n e.symm e.target := by
  let L := toEuclidean (E := E)
  let c := (chartAt E x).trans L.toHomeomorph.toOpenPartialHomeomorph
  have hc : c x ∈ c.target := c.map_source (by simp [c, mem_chart_source])
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) hc
  let b := OpenPartialHomeomorph.univBall (c x) r
  have hb : b.target ⊆ c.target := by
    simpa [b, OpenPartialHomeomorph.univBall_target _ hr] using hball
  have hbc : ∀ z, b z ∈ c.target := fun z => hb (b.map_source (by simp [b]))
  let e := b.trans c.symm
  have hs : e.source = univ := by
    apply eq_univ_of_forall
    intro z
    simp [e, hbc, b]
  have ht : x ∈ e.target := by
    simp [e, c, b, mem_chart_source,
      OpenPartialHomeomorph.univBall_target _ hr, hr]
  have hcs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      𝓘(ℝ, E) n c.symm c.target := by
    rw [OpenPartialHomeomorph.coe_trans_symm]
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).comp
      (L.symm.contDiff.contMDiff.contMDiffOn (s := c.target)) (fun z hz => hz.2)
  have hcf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      n c c.source := by
    exact L.contDiff.contMDiff.comp_contMDiffOn
      ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := x)).mono inter_subset_left)
  refine ⟨e, hs, ht, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.coe_trans]
    exact hcs.comp_contMDiff OpenPartialHomeomorph.contDiff_univBall.contMDiff
      hbc
  · rw [OpenPartialHomeomorph.coe_trans_symm]
    exact OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn.comp
      (hcf.mono inter_subset_left) (fun z hz => by
        simpa only [b, OpenPartialHomeomorph.univBall_target _ hr] using hz.2)

/-- Every point of a finite-dimensional boundaryless real manifold has an open neighbourhood
homeomorphic to `ℝᵐ`, where `m` is the dimension of the model vector space. The neighbourhood is
the image of a global parametrization of the copy of the manifold modelled on `E`. -/
theorem exists_isOpen_mem_nonempty_homeomorph_euclideanSpace {H N : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    (x : N) : ∃ U : Set N, IsOpen U ∧ x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  set e := BoundarylessModel.homeomorph I N
  -- Every charted space is a `C⁰` manifold; state it at the order used by the parametrization.
  have : IsManifold 𝓘(ℝ, E) ((0 : ℕ∞) : ℕ∞ω) (BoundarylessModel I N) :=
    inferInstanceAs (IsManifold 𝓘(ℝ, E) 0 _)
  obtain ⟨φ, hφ, hx, -⟩ :=
    exists_contMDiff_parametrization (E := E) (M := BoundarylessModel I N) (n := 0) (e x)
  exact ⟨e ⁻¹' φ.target, φ.open_target.preimage e.continuous, hx,
    ⟨(e.sets rfl).trans <| φ.toHomeomorphSourceTarget.symm.trans <|
      (Homeomorph.setCongr hφ).trans (Homeomorph.Set.univ _)⟩⟩

section CoordinateBall

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) n N]

/-- **Coordinate balls exist.** Every point `x` of a `C^n` manifold without boundary modelled on a
real inner product space `F` is the centre `e 0` of an open embedding `e : F → N` which is a `C^n`
local diffeomorphism: a chart inverse precomposed with a diffeomorphism of `F` onto a small
ball. -/
theorem exists_isOpenEmbedding_isLocalDiffeomorph (x : N) :
    ∃ e : F → N, e 0 = x ∧ Topology.IsOpenEmbedding e ∧
      IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) n e := by
  set c := chartAt F x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x)
    (c.map_source (mem_chart_source F x))
  -- A diffeomorphism of `F` onto a ball about `c x` inside the chart target.
  let b := OpenPartialHomeomorph.univBall (c x) r
  have hb (v : F) : b v ∈ c.target := hball <| by
    rw [← OpenPartialHomeomorph.univBall_target (c x) hr]
    exact b.map_source (by simp [b])
  let φ := b.trans c.symm
  have hφ : φ.source = univ := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.univBall_source,
      OpenPartialHomeomorph.symm_source, univ_inter]
    exact eq_univ_of_forall hb
  refine ⟨φ, ?_, φ.isOpenEmbedding hφ, fun v ↦ ?_⟩
  · simp [φ, b, c]
  · let Φ := PartialDiffeomorph.ofOpenPartialHomeomorph (n := n) b
      OpenPartialHomeomorph.contDiff_univBall.contDiffOn
      (by rw [OpenPartialHomeomorph.univBall_target _ hr]
          exact OpenPartialHomeomorph.contDiffOn_univBall_symm)
    have hbv : IsLocalDiffeomorphAt 𝓘(ℝ, F) 𝓘(ℝ, F) n b v :=
      isLocalDiffeomorphAt_of_eqOn (Φ := Φ) (by simp [Φ, b]) fun y _ ↦ by simp [Φ]
    exact hbv.comp (hg := c.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas x) (hb v))

end CoordinateBall

section EuclideanNeighbourhood

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I n N]

/-- **Euclidean neighbourhoods.** An interior point `x` of a finite-dimensional real `C^n` manifold
with corners, for `n ≤ ∞`, has an open neighbourhood which is `C^n`-diffeomorphic to the Euclidean
space of the same dimension. -/
theorem exists_opens_diffeomorph_euclideanSpace {x : N} (hx : I.IsInteriorPoint x) :
    ∃ U : TopologicalSpace.Opens N, x ∈ U ∧
      Nonempty (U ≃ₘ^n⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  -- The extended chart at `x`, followed by a linear equivalence with Euclidean space, maps a
  -- neighbourhood of `x` onto a ball, which `univBall` identifies with the whole space.
  let L := toEuclidean (E := E)
  set c := extChartAt I x
  -- A ball about `L (c x)` whose preimage under `L` lies in the target of the chart.
  have hT : L.symm ⁻¹' c.target ∈ 𝓝 (L (c x)) := by
    refine L.symm.continuous.continuousAt.preimage_mem_nhds ?_
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp hx)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hT
  let b := OpenPartialHomeomorph.univBall (L (c x)) r
  have hb (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : b v ∈ ball (L (c x)) r := by
    rw [← OpenPartialHomeomorph.univBall_target _ hr]
    exact b.map_source (by simp [b])
  have hbT (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : L.symm (b v) ∈ c.target :=
    hball (hb v)
  let U : TopologicalSpace.Opens N :=
    ⟨c.source ∩ c ⁻¹' (L ⁻¹' ball (L (c x)) r),
      (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x)
        (isOpen_ball.preimage L.continuous)⟩
  have hU (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : c.symm (L.symm (b v)) ∈ U := by
    refine ⟨c.map_target (hbT v), ?_⟩
    simp only [mem_preimage, c.right_inv (hbT v), ContinuousLinearEquiv.apply_symm_apply]
    exact hb v
  refine ⟨U, ⟨mem_extChartAt_source x, mem_ball_self hr⟩, ⟨
    { toFun := fun u ↦ b.symm (L (c u))
      invFun := fun v ↦ ⟨c.symm (L.symm (b v)), hU v⟩
      left_inv := fun u ↦ Subtype.ext ?_
      right_inv := fun v ↦ ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }⟩⟩
  · have hu : L (c u) ∈ b.target := by
      rw [OpenPartialHomeomorph.univBall_target _ hr]
      exact u.property.2
    simp only [b.right_inv hu, ContinuousLinearEquiv.symm_apply_apply]
    exact c.left_inv u.property.1
  · simp only [c.right_inv (hbT v), ContinuousLinearEquiv.apply_symm_apply]
    exact b.left_inv (by simp [b])
  · have hf : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) n
        (fun y ↦ b.symm (L (c y))) U :=
      OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn.comp
        (L.contDiff.contMDiff.comp_contMDiffOn
          ((contMDiffOn_extChartAt (x := x)).mono fun y hy ↦ by
            rw [← extChartAt_source I]
            exact hy.1))
        fun y hy ↦ hy.2
    exact hf.comp_contMDiff contMDiff_subtypeVal fun u ↦ u.property
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiffOn_extChartAt_symm x).comp_contMDiff
      (L.symm.contDiff.comp OpenPartialHomeomorph.contDiff_univBall).contMDiff hbT

end EuclideanNeighbourhood

section OpenBox

/-- The open coordinate box `∏ i, (a i, b i)` in `EuclideanSpace ℝ ι`. -/
def openBox {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    TopologicalSpace.Opens (EuclideanSpace ℝ ι) :=
  ⟨{x | ∀ i, x i ∈ Ioo (a i) (b i)}, by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous⟩

/-- A point lies in `openBox a b` if and only if each coordinate lies in `(a i, b i)`. -/
@[simp]
theorem mem_openBox {ι : Type*} [Fintype ι] {a b : ι → ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ openBox a b ↔ ∀ i, x i ∈ Ioo (a i) (b i) := by
  rfl

/-- The intersection of two open coordinate boxes is the box given by componentwise `max` and
`min`. -/
@[simp]
theorem openBox_inf_openBox {ι : Type*} [Fintype ι] (a₁ b₁ a₂ b₂ : ι → ℝ) :
    openBox a₁ b₁ ⊓ openBox a₂ b₂ =
      openBox (fun i ↦ max (a₁ i) (a₂ i)) (fun i ↦ min (b₁ i) (b₂ i)) := by
  refine SetLike.ext fun x ↦ ?_
  simp only [TopologicalSpace.Opens.mem_inf, mem_openBox, ← forall_and]
  exact forall_congr' fun i ↦ by rw [← mem_inter_iff, Ioo_inter_Ioo]

/-- An open coordinate box `openBox a b` is nonempty if and only if `a i < b i` for every `i`. -/
theorem nonempty_openBox_iff {ι : Type*} [Fintype ι] {a b : ι → ℝ} :
    Nonempty (openBox a b) ↔ ∀ i, a i < b i := by
  constructor
  · rintro ⟨⟨x, hx⟩⟩ i
    exact (hx i).left.trans (hx i).right
  · intro hab
    refine ⟨⟨(EuclideanSpace.equiv ι ℝ).symm (fun i ↦ (a i + b i) / 2), fun i ↦ ?_⟩⟩
    have hi : ((EuclideanSpace.equiv ι ℝ).symm (fun j ↦ (a j + b j) / 2)) i = (a i + b i) / 2 :=
      rfl
    rw [hi]
    constructor <;> linarith [hab i]

/-- An open coordinate box `openBox a b` is empty if and only if `b i ≤ a i` for some `i`. -/
theorem isEmpty_openBox_iff {ι : Type*} [Fintype ι] {a b : ι → ℝ} :
    IsEmpty (openBox a b) ↔ ∃ i, b i ≤ a i := by
  rw [← not_nonempty_iff, nonempty_openBox_iff]
  simp only [not_forall, not_lt]

/-- The open coordinate boxes form a basis of open subsets of `EuclideanSpace ℝ ι`. -/
theorem isBasis_openBoxes (ι : Type*) [Fintype ι] :
    TopologicalSpace.Opens.IsBasis
      {U : TopologicalSpace.Opens (EuclideanSpace ℝ ι) | ∃ a b, U = openBox a b} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  let L := EuclideanSpace.equiv ι ℝ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (U.isOpen.preimage L.symm.continuous) (L x) hx
  refine ⟨openBox (fun i ↦ x i - r) (fun i ↦ x i + r), ⟨_, _, rfl⟩,
    fun i ↦ ⟨sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩, fun y hy ↦ ?_⟩
  have hyb : L y ∈ Metric.ball (L x) r := by
    rw [ball_pi _ hr]
    intro i _
    dsimp only
    rw [Real.ball_eq_Ioo]
    exact (mem_openBox.mp hy) i
  have hyU : L.symm (L y) ∈ (U : Set (EuclideanSpace ℝ ι)) := hball hyb
  rwa [ContinuousLinearEquiv.symm_apply_apply] at hyU

/-- A `C^n`-diffeomorphism from `EuclideanSpace ℝ ι` onto a nonempty open coordinate box
`openBox a b`, obtained by applying `OpenPartialHomeomorph.univBall` coordinatewise. -/
def diffeomorphOpenBox {n : ℕ∞} {ι : Type*} [Fintype ι] {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    EuclideanSpace ℝ ι ≃ₘ^n⟮𝓘(ℝ, EuclideanSpace ℝ ι), 𝓘(ℝ, EuclideanSpace ℝ ι)⟯ openBox a b := by
  let L := EuclideanSpace.equiv ι ℝ
  let c (i : ι) : ℝ := (a i + b i) / 2
  let r (i : ι) : ℝ := (b i - a i) / 2
  have hr (i : ι) : 0 < r i := by dsimp [r]; linarith [hab i]
  let e (i : ι) := OpenPartialHomeomorph.univBall (c i) (r i)
  have htarget (i : ι) : (e i).target = Ioo (a i) (b i) := by
    rw [OpenPartialHomeomorph.univBall_target _ (hr i), Real.ball_eq_Ioo]
    congr <;> dsimp [c, r] <;> ring
  have hmem (v : EuclideanSpace ℝ ι) : L.symm (fun i ↦ e i (v i)) ∈ openBox a b :=
    mem_openBox.mpr fun i ↦ by
      rw [← htarget i]
      exact (e i).map_source (by simp [e])
  refine
    { toEquiv :=
        { toFun := fun v ↦ ⟨L.symm (fun i ↦ e i (v i)), hmem v⟩
          invFun := fun u ↦ L.symm (fun i ↦ (e i).symm (u.val i))
          left_inv := fun v ↦ L.injective <| funext fun i ↦ by
            simp only [L.apply_symm_apply]
            exact (e i).left_inv (by simp [e])
          right_inv := fun u ↦ Subtype.ext <| L.injective <| funext fun i ↦ by
            simp only [L.apply_symm_apply]
            exact (e i).right_inv (htarget i ▸ (mem_openBox.mp u.property) i) }
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp <|
        L.symm.contDiff.contMDiff.comp <| contMDiff_pi_module_iff.mpr fun i ↦
          OpenPartialHomeomorph.contDiff_univBall.contMDiff.comp
            (EuclideanSpace.proj (𝕜 := ℝ) i).contMDiff
      contMDiff_invFun := L.symm.contDiff.contMDiff.comp <| contMDiff_pi_module_iff.mpr fun i ↦ by
        have hcd : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n (e i).symm (Ioo (a i) (b i)) := by
          rw [← htarget i, OpenPartialHomeomorph.univBall_target _ (hr i)]
          exact (OpenPartialHomeomorph.contDiffOn_univBall_symm (n := n)).contMDiffOn
        exact hcd.comp_contMDiff
          ((EuclideanSpace.proj (𝕜 := ℝ) i).contMDiff.comp contMDiff_subtypeVal)
          fun u ↦ (mem_openBox.mp u.property) i }

/-- The `i`-th coordinate of `diffeomorphOpenBox hab v` is `univBall` applied to `v i`. -/
@[simp]
theorem coe_diffeomorphOpenBox_apply {n : ℕ∞} {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (v : EuclideanSpace ℝ ι) (i : ι) :
    (diffeomorphOpenBox (n := n) hab v : EuclideanSpace ℝ ι) i =
      OpenPartialHomeomorph.univBall ((a i + b i) / 2) ((b i - a i) / 2) (v i) := by
  rw [diffeomorphOpenBox]
  rfl

/-- The `i`-th coordinate of `(diffeomorphOpenBox hab).symm u` is `univBall.symm` applied to
`u.val i`. -/
@[simp]
theorem diffeomorphOpenBox_symm_apply {n : ℕ∞} {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (u : openBox a b) (i : ι) :
    (diffeomorphOpenBox (n := n) hab).symm u i =
      (OpenPartialHomeomorph.univBall ((a i + b i) / 2) ((b i - a i) / 2)).symm (u.val i) := by
  rw [diffeomorphOpenBox]
  rfl

end OpenBox

end TauCeti
