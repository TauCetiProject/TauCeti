/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian
public import TauCeti.Topology.VectorBundle.SphereBundle
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.MetricSpace.Isometry.Basic
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.VectorBundle.Contractible

/-!
# The cells of a disc bundle over a finite CW complex

Let `E → X` be a real vector bundle of rank `r` with a continuous fibre metric, and let `C` be a
finite CW complex in `X` relative to `D`, with `X` Hausdorff. Then the unit disc bundle `D(E)`
restricted to `C` is a finite CW complex relative to the sphere bundle `S(E)` over `C` together
with the disc bundle over `D` (`TauCeti.discBundleRelCWComplex`), with one `(q + r)`-cell over each
`q`-cell of `C` (`TauCeti.discBundleCellEquiv`, `TauCeti.discBundleCellEquivOfAdd`) and no cells
of dimension less than `r` (`TauCeti.isEmpty_cell_discBundle_of_lt`). The closed cell over a cell
of `C` is the disc bundle over its closed cell, its open cell is the open disc bundle over its open
cell, and its boundary is the disc bundle over the boundary of the base cell together with the
sphere bundle over the closed base cell. With `C` the whole of `X` and `D = ∅`, this is the
structure of `D(E)` relative to `S(E)` whose quotient is the Thom space of `E` (Milnor and
Stasheff, §18); with `D` a subcomplex, it is the relative structure over the pair `(X, D)`.

The characteristic map of the cell over the `q`-cell `i` of `C`, with characteristic map `χ`, is
built as follows. Mathlib's classical CW complexes parametrise an `n`-cell by the closed unit ball
of `Fin n → ℝ` in the sup norm, and appending coordinates
(`Fin.appendIsometryOfEq : (Fin q → ℝ) × (Fin r → ℝ) ≃ᵢ (Fin (q + r) → ℝ)`) splits that cube into
the cube of the base cell, the first `q` coordinates, and the cube of the fibre, the last `r`.
Precomposed with the radial retraction onto the closed ball, `χ` is a continuous map from the
contractible space `Fin q → ℝ` to `X`, so `E` has a continuous orthonormal frame along it
(`TauCeti.exists_continuous_orthonormalBasis_of_contractibleSpace`). A point `(x, w)` goes to the
vector over `χ x` whose coordinates in this frame are the radial rescaling of `w` from the sup norm
to the Euclidean norm (`ContinuousLinearEquiv.unitBallHomeomorph`), so that the fibre cube goes
onto the unit disc of the fibre, its boundary onto the unit sphere, and the norm of the image is
the Euclidean norm of the rescaled fibre coordinates (`TauCeti.norm_map_discBundleCellEquiv_symm`).
The map is injective on the open cube, because `χ` is injective on the open ball, and the boundary
of the cube goes over the boundary of the base cell or into the sphere bundle, both disjoint from
the open cell; as the cube is compact, the inverse is continuous on the open cell
(`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`). The frame is a choice, so the
characteristic maps are not canonical, but their closed cells, open cells, boundaries, base points
and norms are.

With finitely many cells the weak topology condition is automatic
(`Topology.RelCWComplex.mkFinite`).

## Main definitions

* `TauCeti.discBundleRelCWComplex`: the finite relative CW structure on the disc bundle over `C`,
  relative to the sphere bundle over `C` and the disc bundle over `D`. It is an instance.
* `TauCeti.discBundleCellEquiv`: its `n`-cells are the `q`-cells of `C` with `q + r = n`.
* `TauCeti.discBundleCellEquivOfAdd`: its `(q + r)`-cells are the `q`-cells of `C`.

## Main results

* `TauCeti.finite_discBundleRelCWComplex`: the disc bundle over a finite CW complex is finite.
* `TauCeti.isEmpty_cell_discBundle_of_lt`: it has no cells of dimension less than `r`.
* `TauCeti.closedCell_discBundleCellEquiv_symm`, `TauCeti.openCell_discBundleCellEquiv_symm` and
  `TauCeti.cellFrontier_discBundleCellEquiv_symm`: the closed cell, open cell and boundary of the
  cell over a cell of `C`.
* `TauCeti.proj_map_discBundleCellEquiv_symm` and `TauCeti.norm_map_discBundleCellEquiv_symm`: its
  characteristic map lies over that of the base cell, with the norm of the rescaled fibre
  coordinates.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the cells of the Thom space of a vector bundle over a CW
  complex).
-/

public section

noncomputable section

open Bundle Function Metric Module Set Topology Topology.RelCWComplex

namespace TauCeti

universe u

section Cells

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (C F) in
/-- The `n`-cells of the disc bundle over `C`: the `q`-cells of `C` with `q + rank E = n`. -/
private abbrev DiscBundleCell (n : ℕ) : Type u :=
  Σ q : {q : ℕ // q + finrank ℝ F = n}, cell C q.1

/-- The splitting of the coordinates of the cube `Fin n → ℝ` of a disc-bundle cell into those of
the base cell and those of the fibre. -/
private abbrev discBundleCellIsometry {n : ℕ} (c : DiscBundleCell C F n) :
    (Fin n → ℝ) ≃ᵢ (Fin c.1.1 → ℝ) × (Fin (finrank ℝ F) → ℝ) :=
  (Fin.appendIsometryOfEq c.1.2).symm

private theorem norm_discBundleCellIsometry {n : ℕ} (c : DiscBundleCell C F n) (z : Fin n → ℝ) :
    ‖discBundleCellIsometry c z‖ = ‖z‖ := by
  rw [← dist_zero_right, ← Fin.appendIsometryOfEq_symm_zero c.1.2, IsometryEquiv.dist_eq,
    dist_zero_right]

private theorem eventually_isEmpty_discBundleCell [RelCWComplex.FiniteDimensional C] :
    ∀ᶠ n in Filter.atTop, IsEmpty (DiscBundleCell C F n) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  refine Filter.eventually_atTop.2 ⟨N + finrank ℝ F, fun n hn ↦ ⟨fun c ↦ ?_⟩⟩
  exact (hN c.1.1 (by have := c.1.2; omega)).false c.2

private theorem finite_discBundleCell [RelCWComplex.FiniteType C] (n : ℕ) :
    _root_.Finite (DiscBundleCell C F n) :=
  have (q : ℕ) : _root_.Finite (cell C q) := FiniteType.finite_cell q
  have : Subsingleton {q : ℕ // q + finrank ℝ F = n} :=
    ⟨fun a b ↦ Subtype.ext (by have := a.2; have := b.2; omega)⟩
  inferInstance

/-- Disc-bundle cells over the same cell of `C` are equal. -/
private theorem discBundleCell_eq {n n' : ℕ} {c : DiscBundleCell C F n}
    {c' : DiscBundleCell C F n'} (h : (⟨c.1.1, c.2⟩ : Σ q, cell C q) = ⟨c'.1.1, c'.2⟩) :
    (⟨n, c⟩ : Σ n, DiscBundleCell C F n) = ⟨n', c'⟩ := by
  obtain ⟨⟨q, hq⟩, i⟩ := c
  obtain ⟨⟨q', hq'⟩, i'⟩ := c'
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq hi
  subst hq hq'
  rfl

end Cells

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : X → Type u} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]

section Cell

variable {q : ℕ} (i : cell C q)

/-- The base of the disc-bundle cell over the cell `i`: its characteristic map, made continuous on
all of `Fin q → ℝ` by first retracting radially onto the closed unit ball. -/
private def cellBase : C(Fin q → ℝ, X) :=
  ⟨fun x ↦ map q i (radialRetraction 1 x),
    (continuousOn q i).comp_continuous (lipschitzWith_radialRetraction zero_le_one).continuous
      fun x ↦ radialRetraction_mem_closedBall zero_le_one x⟩

private theorem cellBase_of_mem {x : Fin q → ℝ} (hx : x ∈ closedBall 0 1) :
    cellBase i x = map q i x := by
  simp [cellBase, radialRetraction_of_norm_le (mem_closedBall_zero_iff.1 hx)]

variable (F E) in
/-- A continuous orthonormal frame of `E` along the base of the disc-bundle cell over `i`. -/
private def cellFrame : ∀ x, OrthonormalBasis (Fin (finrank ℝ F)) ℝ (E (cellBase i x)) :=
  (exists_continuous_orthonormalBasis_of_contractibleSpace ℝ F E (cellBase i)).choose

private theorem continuous_cellFrame (j : Fin (finrank ℝ F)) :
    Continuous fun x ↦ TotalSpace.mk' F (cellBase i x) (cellFrame F E i x j) :=
  (exists_continuous_orthonormalBasis_of_contractibleSpace ℝ F E (cellBase i)).choose_spec j

/-- The radial homeomorphism from the sup norm of `Fin r → ℝ` to the Euclidean norm. -/
private abbrev toEuclidean (r : ℕ) : (Fin r → ℝ) ≃ₜ EuclideanSpace ℝ (Fin r) :=
  (EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm

variable (F E) in
/-- The disc-bundle cell over `i` on the product of the cubes of the base cell and of the fibre:
`(x, w)` goes to the vector of `E` over the base point of `x` whose coordinates in the frame
`cellFrame` are the radial rescaling of `w` to the Euclidean norm. -/
private def cellProdMap (p : (Fin q → ℝ) × (Fin (finrank ℝ F) → ℝ)) : TotalSpace F E :=
  ⟨cellBase i p.1, (cellFrame F E i p.1).repr.symm (toEuclidean _ p.2)⟩

private theorem norm_cellProdMap (p : (Fin q → ℝ) × (Fin (finrank ℝ F) → ℝ)) :
    ‖(cellProdMap F E i p).2‖ = ‖toEuclidean _ p.2‖ :=
  (cellFrame F E i p.1).repr.symm.norm_map _

private theorem continuous_cellProdMap : Continuous (cellProdMap F E i) :=
  (continuous_totalSpaceMk_repr_symm (cellBase i).continuous (cellFrame F E i)
    (continuous_cellFrame i)).comp
    (continuous_fst.prodMk ((toEuclidean _).continuous.comp continuous_snd))

/-- The image under `cellProdMap` of a product `s ×ˢ t`, with `s` in the closed unit ball and `t`
cut out by a condition `P` on the Euclidean norm: the vectors whose norm satisfies `P`, over the
image of `s` under the characteristic map of `i`. -/
private theorem image_cellProdMap_prod {s : Set (Fin q → ℝ)} (hs : s ⊆ closedBall 0 1)
    {t : Set (Fin (finrank ℝ F) → ℝ)} {P : ℝ → Prop} (ht : ∀ w, w ∈ t ↔ P ‖toEuclidean _ w‖) :
    cellProdMap F E i '' (s ×ˢ t) = {v | P ‖v.2‖} ∩ TotalSpace.proj ⁻¹' (map q i '' s) := by
  ext v
  constructor
  · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
    exact ⟨by simpa only [mem_ofPred_eq, norm_cellProdMap] using (ht w).1 hw,
      x, hx, (cellBase_of_mem i (hs hx)).symm⟩
  · obtain ⟨b, y⟩ := v
    rintro ⟨hy, x, hx, hxb⟩
    obtain rfl : cellBase i x = b := (cellBase_of_mem i (hs hx)).trans hxb
    refine ⟨(x, (toEuclidean _).symm ((cellFrame F E i x).repr y)), ⟨hx, (ht _).2 ?_⟩, ?_⟩
    · simpa only [Homeomorph.apply_symm_apply, LinearIsometryEquiv.norm_map, mem_ofPred_eq] using hy
    · simp [cellProdMap]

/-- `cellProdMap` is injective over the open unit ball of the base cell. -/
private theorem injOn_cellProdMap : InjOn (cellProdMap F E i) (ball 0 1 ×ˢ univ) := by
  rintro ⟨x, w⟩ ⟨hx, -⟩ ⟨x', w'⟩ ⟨hx', -⟩ h
  have hb : map q i x = map q i x' := by
    rw [← cellBase_of_mem i (ball_subset_closedBall hx),
      ← cellBase_of_mem i (ball_subset_closedBall hx')]
    exact congrArg TotalSpace.proj h
  obtain rfl : x = x' := (map q i).injOn (by rwa [source_eq]) (by rwa [source_eq]) hb
  have hw := TotalSpace.mk_inj.1 h
  rw [(cellFrame F E i x).repr.symm.injective.eq_iff, (toEuclidean _).injective.eq_iff] at hw
  exact Prod.ext rfl hw

end Cell

section Maps

variable (F E) in
/-- The characteristic map of a disc-bundle cell, on the cube `Fin n → ℝ`. -/
private def discBundleCellMap {n : ℕ} (c : DiscBundleCell C F n) : (Fin n → ℝ) → TotalSpace F E :=
  cellProdMap F E c.2 ∘ discBundleCellIsometry c

private theorem image_discBundleCellMap {n : ℕ} (c : DiscBundleCell C F n) (s : Set (Fin n → ℝ)) :
    discBundleCellMap F E c '' s = cellProdMap F E c.2 '' (discBundleCellIsometry c '' s) :=
  image_comp _ _ _

private theorem image_discBundleCellMap_closedBall {n : ℕ} (c : DiscBundleCell C F n) :
    discBundleCellMap F E c '' closedBall 0 1 =
      discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.1 c.2 := by
  rw [image_discBundleCellMap, IsometryEquiv.image_closedBall, Fin.appendIsometryOfEq_symm_zero,
    Prod.zero_eq_mk, ← closedBall_prod_same,
    image_cellProdMap_prod c.2 subset_rfl (P := (· ≤ 1)) fun w ↦ by simp]
  ext
  simp [closedCell]

private theorem image_discBundleCellMap_ball {n : ℕ} (c : DiscBundleCell C F n) :
    discBundleCellMap F E c '' ball 0 1 =
      {v | ‖v.2‖ < 1} ∩ TotalSpace.proj ⁻¹' openCell c.1.1 c.2 := by
  rw [image_discBundleCellMap, IsometryEquiv.image_ball, Fin.appendIsometryOfEq_symm_zero,
    Prod.zero_eq_mk, ← ball_prod_same,
    image_cellProdMap_prod c.2 ball_subset_closedBall (P := (· < 1)) fun w ↦ by simp]
  ext
  simp [openCell]

private theorem image_discBundleCellMap_sphere {n : ℕ} (c : DiscBundleCell C F n) :
    discBundleCellMap F E c '' sphere 0 1 =
      discBundle F E ∩ TotalSpace.proj ⁻¹' cellFrontier c.1.1 c.2 ∪
        sphereBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.1 c.2 := by
  rw [image_discBundleCellMap, IsometryEquiv.image_sphere, Fin.appendIsometryOfEq_symm_zero,
    sphere_prod, image_union, Prod.fst_zero, Prod.snd_zero,
    image_cellProdMap_prod c.2 sphere_subset_closedBall (P := (· ≤ 1)) fun w ↦ by simp,
    image_cellProdMap_prod c.2 subset_rfl (P := (· = 1)) fun w ↦ by simp]
  ext
  simp [closedCell, cellFrontier]

private theorem injOn_discBundleCellMap {n : ℕ} (c : DiscBundleCell C F n) :
    InjOn (discBundleCellMap F E c) (ball 0 1) := by
  refine (injOn_cellProdMap c.2).comp (discBundleCellIsometry c).injective.injOn fun z hz ↦ ?_
  have : discBundleCellIsometry c z ∈ ball 0 1 := by
    rwa [mem_ball_zero_iff, norm_discBundleCellIsometry, ← mem_ball_zero_iff]
  rw [Prod.zero_eq_mk, ← ball_prod_same] at this
  exact ⟨this.1, mem_univ _⟩

private theorem continuous_discBundleCellMap {n : ℕ} (c : DiscBundleCell C F n) :
    Continuous (discBundleCellMap F E c) :=
  (continuous_cellProdMap c.2).comp (discBundleCellIsometry c).continuous

variable (F E) in
/-- The characteristic map of a disc-bundle cell, as a partial equivalence on the open cube. -/
private def discBundleCellPartialEquiv {n : ℕ} (c : DiscBundleCell C F n) :
    PartialEquiv (Fin n → ℝ) (TotalSpace F E) :=
  (injOn_discBundleCellMap c).toPartialEquiv _ _

private theorem pairwiseDisjoint_discBundleCellMap :
    (univ : Set (Σ n, DiscBundleCell C F n)).PairwiseDisjoint
      (fun c ↦ discBundleCellMap F E c.2 '' ball 0 1) := by
  rintro ⟨n, c⟩ - ⟨n', c'⟩ - hne
  simp only [Function.onFun, image_discBundleCellMap_ball]
  exact ((disjoint_openCell_of_ne fun h ↦ hne (discBundleCell_eq h)).preimage _).mono
    inter_subset_right inter_subset_right


private theorem disjoint_discBundleCellMap_base {n : ℕ} (c : DiscBundleCell C F n) :
    Disjoint (discBundleCellMap F E c '' ball 0 1)
      (sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D) := by
  rw [image_discBundleCellMap_ball]
  refine Disjoint.union_right (disjoint_left.2 fun v hv hv' ↦ ?_)
    (disjoint_left.2 fun v hv hv' ↦ ?_)
  · exact (mem_sphereBundle.1 hv'.1).not_lt hv.1
  · exact disjoint_left.1 (disjointBase c.1.1 c.2) hv.2 hv'.2

private theorem mapsTo_discBundleCellMap {n : ℕ} (c : DiscBundleCell C F n) :
    MapsTo (discBundleCellMap F E c) (sphere 0 1)
      ((sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D) ∪
        ⋃ (m < n) (c' : DiscBundleCell C F m), discBundleCellMap F E c' '' closedBall 0 1) := by
  rw [mapsTo_iff_image_subset, image_discBundleCellMap_sphere]
  refine union_subset (fun v hv ↦ ?_) fun v hv ↦
    Or.inl (Or.inl ⟨hv.1, closedCell_subset_complex (C := C) c.1.1 c.2 hv.2⟩)
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell c.1.1 c.2
  rcases hI hv.2 with hD | hcell
  · exact Or.inl (Or.inr ⟨hv.1, hD⟩)
  · obtain ⟨m, hm, j, -, hj⟩ := by simpa only [mem_iUnion, exists_prop] using hcell
    refine Or.inr (mem_iUnion₂.2 ⟨m + finrank ℝ F, by have := c.1.2; omega,
      mem_iUnion.2 ⟨⟨⟨m, rfl⟩, j⟩, ?_⟩⟩)
    rw [image_discBundleCellMap_closedBall]
    exact ⟨hv.1, hj⟩

private theorem union_discBundleCellMap :
    (sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D) ∪
      ⋃ (n : ℕ) (c : DiscBundleCell C F n), discBundleCellMap F E c '' closedBall 0 1 =
      discBundle F E ∩ TotalSpace.proj ⁻¹' C := by
  simp_rw [image_discBundleCellMap_closedBall]
  refine subset_antisymm (union_subset (union_subset
    (inter_subset_inter_left _ (sphereBundle_subset_discBundle F E))
    (inter_subset_inter_right _ (preimage_mono (base_subset_complex (C := C)))))
    (iUnion₂_subset fun _ c ↦
      inter_subset_inter_right _ (preimage_mono (closedCell_subset_complex _ _))))
    fun v hv ↦ ?_
  rw [← RelCWComplex.union (C := C)] at hv
  rcases hv.2 with hD | hcell
  · exact Or.inl (Or.inr ⟨hv.1, hD⟩)
  · obtain ⟨q, i, hi⟩ := by simpa only [mem_iUnion] using hcell
    exact Or.inr (mem_iUnion₂.2 ⟨q + finrank ℝ F, ⟨⟨q, rfl⟩, i⟩, hv.1, hi⟩)

end Maps

section RelCWComplex

variable [T2Space X]

/-- The inverse of a characteristic map of a disc-bundle cell is continuous on the open cell: the
boundary of the cube goes to the boundary sphere bundle or over the boundary of the base cell,
both disjoint from the open cell, and the cube is compact. -/
private theorem continuousOn_discBundleCellPartialEquiv_symm {n : ℕ}
    (c : DiscBundleCell C F n) :
    ContinuousOn (discBundleCellPartialEquiv F E c).symm
      (discBundleCellPartialEquiv F E c).target := by
  refine (continuous_discBundleCellMap c).continuousOn.continuousOn_invFunOn_image_of_isCompact
    (isCompact_closedBall 0 1) ball_subset_closedBall (injOn_discBundleCellMap c) ?_
  rw [closedBall_sdiff_ball, image_discBundleCellMap_sphere, image_discBundleCellMap_ball]
  refine Disjoint.union_left (disjoint_left.2 fun v hv hv' ↦ ?_) (disjoint_left.2 fun v hv hv' ↦ ?_)
  · exact disjoint_left.1 ((disjoint_skeletonLT_openCell le_rfl).mono_left
      (cellFrontier_subset_skeletonLT _ _)) hv.2 hv'.2
  · exact (mem_sphereBundle.1 hv.1).not_lt hv'.1


omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, InnerProductSpace ℝ (E x)]
  [VectorBundle ℝ F E] in
private theorem isClosed_discBundle_base :
    IsClosed (sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D) :=
  have hnorm := ContinuousFiberNorm.continuous_norm (F := F) (E := E)
  have hproj := FiberBundle.continuous_proj F E
  have hS : sphereBundle F E = {v | ‖v.2‖ = 1} := ext fun _ ↦ mem_sphereBundle
  have hD : discBundle F E = {v | ‖v.2‖ ≤ 1} := ext fun _ ↦ mem_discBundle
  hS ▸ hD ▸ ((isClosed_eq hnorm continuous_const).inter (isClosed.preimage hproj)).union
    ((isClosed_le hnorm continuous_const).inter (isClosedBase C |>.preimage hproj))

variable [RelCWComplex.Finite C]

variable (C F E) in
/-- **The cells of a disc bundle.** Let `E` be a real vector bundle of rank `r` with a continuous
fibre metric over a Hausdorff space `X`, and `C` a finite CW complex in `X` relative to `D`. Then
the unit disc bundle of `E` over `C` is a finite CW complex relative to the unit sphere bundle over
`C` together with the disc bundle over `D`, with one `(q + r)`-cell over each `q`-cell of `C`
(`TauCeti.discBundleCellEquiv`). The cell over a cell of `C` is the disc bundle over that cell
(`TauCeti.closedCell_discBundleCellEquiv_symm`). -/
@[instance_reducible]
def discBundleRelCWComplex :
    RelCWComplex (discBundle F E ∩ TotalSpace.proj ⁻¹' C)
      (sphereBundle F E ∩ TotalSpace.proj ⁻¹' C ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' D) :=
  RelCWComplex.mkFinite _ _ (DiscBundleCell C F) (fun _ c ↦ discBundleCellPartialEquiv F E c)
    eventually_isEmpty_discBundleCell finite_discBundleCell (fun _ _ ↦ rfl)
    (fun _ c ↦ (continuous_discBundleCellMap c).continuousOn)
    (fun _ c ↦ continuousOn_discBundleCellPartialEquiv_symm c)
    pairwiseDisjoint_discBundleCellMap (fun _ c ↦ disjoint_discBundleCellMap_base c)
    (fun _ c ↦ mapsTo_discBundleCellMap c) isClosed_discBundle_base union_discBundleCellMap

attribute [instance] discBundleRelCWComplex

/-- The `n`-cells of the disc bundle over `C` are the `q`-cells of `C` with `q + rank E = n`. -/
def discBundleCellEquiv (n : ℕ) :
    cell (discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ≃
      Σ q : {q : ℕ // q + finrank ℝ F = n}, cell C q.1 :=
  -- `RelCWComplex.mkFinite` takes the `n`-cells of `discBundleRelCWComplex` to be
  -- `DiscBundleCell C F n` itself.
  Equiv.refl _

/-- The characteristic map of the cell of the disc bundle read through
`TauCeti.discBundleCellEquiv` is `discBundleCellMap`, by definition: `RelCWComplex.mkFinite` uses
the given partial equivalences `discBundleCellPartialEquiv` as characteristic maps, and these are
`discBundleCellMap` restricted to the open cube. -/
private theorem map_discBundleRelCWComplex {n : ℕ} (c : DiscBundleCell C F n) :
    ⇑(map (C := discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ((discBundleCellEquiv n).symm c)) =
      discBundleCellMap F E c :=
  rfl

/-- The disc bundle has one `(q + rank E)`-cell over each `q`-cell of `C`. -/
def discBundleCellEquivOfAdd (q : ℕ) :
    cell (discBundle F E ∩ TotalSpace.proj ⁻¹' C) (q + finrank ℝ F) ≃ cell C q :=
  letI : Unique {q' : ℕ // q' + finrank ℝ F = q + finrank ℝ F} :=
    ⟨⟨⟨q, rfl⟩⟩, fun a ↦ Subtype.ext (Nat.add_right_cancel a.2)⟩
  (discBundleCellEquiv _).trans
    (Equiv.uniqueSigma fun q' : {q' : ℕ // q' + finrank ℝ F = q + finrank ℝ F} ↦ cell C q'.1)

/-- The cell of the disc bundle over the `q`-cell `i` of `C`, read through
`TauCeti.discBundleCellEquiv`. -/
@[simp]
theorem discBundleCellEquivOfAdd_symm_apply (q : ℕ) (i : cell C q) :
    (discBundleCellEquivOfAdd (F := F) (E := E) q).symm i =
      (discBundleCellEquiv _).symm ⟨⟨q, rfl⟩, i⟩ :=
  (rfl)

/-- The disc bundle has no cells of dimension less than the rank of `E`. -/
theorem isEmpty_cell_discBundle_of_lt {n : ℕ} (hn : n < finrank ℝ F) :
    IsEmpty (cell (discBundle F E ∩ TotalSpace.proj ⁻¹' C) n) :=
  ⟨fun c ↦ by have := c.1.2; omega⟩

/-- The disc bundle over a finite CW complex is a finite CW complex. -/
instance finite_discBundleRelCWComplex :
    RelCWComplex.Finite (discBundle F E ∩ TotalSpace.proj ⁻¹' C) where
  eventually_isEmpty_cell := eventually_isEmpty_discBundleCell (D := D)
  finite_cell := finite_discBundleCell (D := D)

variable {n : ℕ} (c : Σ q : {q : ℕ // q + finrank ℝ F = n}, cell C q.1)

/-- The closed cell of the disc bundle over the cell `c.2` of `C` is the disc bundle restricted to
the closed cell `c.2`. -/
@[simp]
theorem closedCell_discBundleCellEquiv_symm :
    closedCell (C := discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ((discBundleCellEquiv n).symm c) =
      discBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.1 c.2 := by
  rw [closedCell, map_discBundleRelCWComplex, image_discBundleCellMap_closedBall]

/-- The open cell of the disc bundle over the cell `c.2` of `C` consists of the vectors of norm less
than one over the open cell `c.2`. -/
@[simp]
theorem openCell_discBundleCellEquiv_symm :
    openCell (C := discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ((discBundleCellEquiv n).symm c) =
      {v | ‖v.2‖ < 1} ∩ TotalSpace.proj ⁻¹' openCell c.1.1 c.2 := by
  rw [openCell, map_discBundleRelCWComplex, image_discBundleCellMap_ball]

/-- The boundary of the cell of the disc bundle over the cell `c.2` of `C` consists of the disc
bundle over the boundary of `c.2` and of the sphere bundle over the closed cell `c.2`. -/
@[simp]
theorem cellFrontier_discBundleCellEquiv_symm :
    cellFrontier (C := discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ((discBundleCellEquiv n).symm c) =
      discBundle F E ∩ TotalSpace.proj ⁻¹' cellFrontier c.1.1 c.2 ∪
        sphereBundle F E ∩ TotalSpace.proj ⁻¹' closedCell c.1.1 c.2 := by
  rw [cellFrontier, map_discBundleRelCWComplex, image_discBundleCellMap_sphere]

/-- The characteristic map of the cell of the disc bundle over the `c.1.1`-cell `c.2` of `C` lies
over the characteristic map of `c.2`: on the closed cube it sends `z` to a vector over the image
under the characteristic map of `c.2` of the first `c.1.1` coordinates of `z`. -/
theorem proj_map_discBundleCellEquiv_symm {z : Fin n → ℝ} (hz : z ∈ closedBall 0 1) :
    (map (C := discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ((discBundleCellEquiv n).symm c) z).proj =
      map c.1.1 c.2 ((Fin.appendIsometryOfEq c.1.2).symm z).1 := by
  rw [map_discBundleRelCWComplex]
  exact cellBase_of_mem c.2 (mem_closedBall_zero_iff.2 ((norm_fst_le _).trans
    ((norm_discBundleCellIsometry c z).trans_le (mem_closedBall_zero_iff.1 hz))))

/-- The characteristic map of the cell of the disc bundle over a cell of `C` sends `z` to a vector
whose norm is the Euclidean norm of the radial rescaling of the last `rank E` coordinates of `z`. -/
theorem norm_map_discBundleCellEquiv_symm (z : Fin n → ℝ) :
    ‖(map (C := discBundle F E ∩ TotalSpace.proj ⁻¹' C) n ((discBundleCellEquiv n).symm c) z).2‖ =
      ‖(EuclideanSpace.equiv (Fin (finrank ℝ F)) ℝ).unitBallHomeomorph.symm
        ((Fin.appendIsometryOfEq c.1.2).symm z).2‖ := by
  rw [map_discBundleRelCWComplex]
  exact norm_cellProdMap c.2 _

end RelCWComplex

end TauCeti
