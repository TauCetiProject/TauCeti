/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Topology.VectorBundle.SphereBundle
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Topology.CWComplex.Classical.OpenCells
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.FiberBundle.Trivialization
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.VectorBundle.Contractible
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# The relative CW structure of a disc bundle

Let `E → B` be a real vector bundle of finite rank `r` with a continuous fibre metric over a
Hausdorff space `B`, and let `(B, A)` be a relative CW complex, in the sense of Mathlib's
`Topology.RelCWComplex (univ : Set B) A`. Then the unit disc bundle `D(E)`
(`TauCeti.discBundle`) is a CW complex relative to the union of the unit sphere bundle `S(E)`
(`TauCeti.sphereBundle`) and of the part of `D(E)` over `A`
(`TauCeti.relCWComplexDiscBundle`). It has one `(q + r)`-cell for each `q`-cell `j` of `(B, A)`
and no other cells (`TauCeti.cellDiscBundleEquiv`): its closed cell is the part of `D(E)` over the
closed cell `j`, and its open cell consists of the vectors of norm less than one over the open cell
`j` (`TauCeti.closedCell_relCWComplexDiscBundle`, `TauCeti.openCell_relCWComplexDiscBundle`). In
particular there are no cells in dimensions below the rank
(`TauCeti.isEmpty_cell_relCWComplexDiscBundle`). No orientation of `E` is used, and in rank zero
the sphere bundle is empty and the cells are those of the base.

These are the cells through which a disc bundle attached along its sphere bundle is a relative CW
complex, as when the negative disc bundles of the critical submanifolds of a Morse–Bott function
are attached to a sublevel (compare `TauCeti.isIso_singularHomologyMap_of_attach_discBundle`).

The characteristic map of the cell over `j` is built from the characteristic map `χ` of `j` on the
closed unit ball `Dᵠ` of `Fin q → ℝ`. Since `Dᵠ` is contractible, `E` has a continuous orthonormal
frame along `χ` (`TauCeti.exists_continuous_orthonormalBasis_of_contractibleSpace`). A point of the
closed unit ball of `Fin (q + r) → ℝ` splits as `(x, y)`, with `x` in `Dᵠ` and `y` in the closed
unit ball of `Fin r → ℝ` (`Fin.appendIsometryOfEq`); it is sent to the vector of the fibre over
`χ x` whose coordinates in the frame are `ρ y`, where `ρ` is the radial homeomorphism from the
sup-norm unit ball onto the Euclidean unit ball (`ContinuousLinearEquiv.unitBallHomeomorph`). In the
sup norm the unit sphere of a product is `(S × D) ∪ (D × S)`, so the boundary of the cell lies over
the boundary of `j`, hence over `A` and finitely many cells of lower dimension, or in `S(E)`. On
the open cell the characteristic map is injective, and its inverse is continuous there because the
closed cell is compact (`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`).

The only point that is not formal is the weak topology: a subset `S` of `D(E)` whose intersections
with the parts of `D(E)` over the closed cells of the base and over `A` are closed is closed. Near a
point `y ∉ S`, in a local trivialization over `U`, choose a compact ball `K` of fibre coordinates
around those of `y` missing the coordinates of the part of `S` over the base point of `y`; this part
is compact, since the closed fibre discs are. The base points of the vectors of `S` over `U` with
coordinates in `K`, together with the complement of `U`, form a set whose intersection with each
closed cell of the base, and with `A`, is closed by a tube lemma. So that set is closed by the weak
topology of the base, and its complement gives a neighbourhood of `y` missing `S`.

## Main declarations

* `TauCeti.relCWComplexDiscBundle`: the relative CW structure on the disc bundle `D(E)`, relative
  to `S(E)` together with the part of `D(E)` over `A`.
* `TauCeti.cellDiscBundleEquiv`: its `(q + r)`-cells are the `q`-cells of the base.
* `TauCeti.closedCell_relCWComplexDiscBundle`, `TauCeti.openCell_relCWComplexDiscBundle` and
  `TauCeti.proj_map_relCWComplexDiscBundle`: its closed cells, open cells and characteristic maps
  lie over those of the base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §18 (the cell structure of a Thom space over a CW complex).
-/

public section

noncomputable section

open Bundle Metric Set Topology Module

universe u

namespace TauCeti

section Cells

variable {B : Type u} [TopologicalSpace B] {A : Set B} [RelCWComplex (univ : Set B) A]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type u} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

open Topology.RelCWComplex

/-- The characteristic map of a `q`-cell of the base, restricted to the closed unit ball. -/
private def cellBaseMap {q : ℕ} (j : cell (univ : Set B) q) : C(closedBall (0 : Fin q → ℝ) 1, B) :=
  ⟨fun x ↦ map q j x, (continuousOn q j).domRestrict⟩

private instance (q : ℕ) : ContractibleSpace (closedBall (0 : Fin q → ℝ) 1) :=
  Convex.contractibleSpace (convex_closedBall (0 : Fin q → ℝ) 1) (nonempty_closedBall.2 zero_le_one)

variable (F E) in
/-- A continuous orthonormal frame of `E` along the closed `q`-cell `j` of the base. -/
private def cellFrame {q : ℕ} (j : cell (univ : Set B) q) (x : closedBall (0 : Fin q → ℝ) 1) :
    OrthonormalBasis (Fin (finrank ℝ F)) ℝ (E (map q j x)) :=
  (exists_continuous_orthonormalBasis_of_contractibleSpace F E (cellBaseMap j)).choose x

private theorem continuous_cellFrame {q : ℕ} (j : cell (univ : Set B) q)
    (i : Fin (finrank ℝ F)) :
    Continuous fun x : closedBall (0 : Fin q → ℝ) 1 ↦
      TotalSpace.mk' F (map q j (x : Fin q → ℝ)) (cellFrame F E j x i) :=
  (exists_continuous_orthonormalBasis_of_contractibleSpace F E (cellBaseMap j)).choose_spec i

/-- The vector of `E` over the point `x` of the closed `q`-cell `j` with coordinates `w` in the
frame `cellFrame`. -/
private def cellVector {q : ℕ} (j : cell (univ : Set B) q) (x : closedBall (0 : Fin q → ℝ) 1)
    (w : EuclideanSpace ℝ (Fin (finrank ℝ F))) : TotalSpace F E :=
  ⟨map q j x, (cellFrame F E j x).repr.symm w⟩

private theorem norm_cellVector {q : ℕ} (j : cell (univ : Set B) q)
    (x : closedBall (0 : Fin q → ℝ) 1) (w : EuclideanSpace ℝ (Fin (finrank ℝ F))) :
    ‖(cellVector (F := F) (E := E) j x w).2‖ = ‖w‖ :=
  (cellFrame F E j x).repr.symm.norm_map w

private theorem continuous_cellVector {q : ℕ} (j : cell (univ : Set B) q) :
    Continuous fun p : closedBall (0 : Fin q → ℝ) 1 × EuclideanSpace ℝ (Fin (finrank ℝ F)) ↦
      cellVector (F := F) (E := E) j p.1 p.2 := by
  refine (continuous_finsetSum_totalSpace ℝ Finset.univ
    ((cellBaseMap j).continuous.comp continuous_fst) fun i _ ↦
      ((EuclideanSpace.proj i).continuous.comp continuous_snd).smul_totalSpace
        ((continuous_cellFrame j i).comp continuous_fst)).congr fun p ↦ ?_
  rw [cellVector, ← OrthonormalBasis.sum_repr_symm]
  -- The two sides now differ only by unfolding `cellBaseMap j` and the coordinate projections
  -- `EuclideanSpace.proj i`.
  rfl

/-- The identification of the sup-norm unit ball of `Fin r → ℝ` with the Euclidean unit ball,
`r` the rank of `E`. -/
private abbrev fiberBallHomeomorph :
    (Fin (finrank ℝ F) → ℝ) ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
  (EuclideanSpace.equiv (Fin (finrank ℝ F)) ℝ).symm.unitBallHomeomorph

/-- The characteristic map of the disc bundle over the `q`-cell `j`, before the coordinates are
appended: `(x, y) ↦ cellVector j x (ρ y)`, retracted radially onto the closed unit balls. -/
private def discCellFun {q : ℕ} (j : cell (univ : Set B) q)
    (z : (Fin q → ℝ) × (Fin (finrank ℝ F) → ℝ)) : discBundle F E :=
  ⟨cellVector j (radialRetractionToClosedBall zero_le_one z.1)
      (radialRetractionToClosedBall zero_le_one (fiberBallHomeomorph (F := F) z.2) :
        EuclideanSpace ℝ _), by
    rw [mem_discBundle, norm_cellVector, ← mem_closedBall_zero_iff]
    exact Subtype.prop _⟩

private theorem continuous_discCellFun {q : ℕ} (j : cell (univ : Set B) q) :
    Continuous (discCellFun (F := F) (E := E) j) :=
  ((continuous_cellVector j).comp
    (((continuous_radialRetractionToClosedBall zero_le_one).comp continuous_fst).prodMk
      (continuous_subtype_val.comp ((continuous_radialRetractionToClosedBall zero_le_one).comp
        ((fiberBallHomeomorph (F := F)).continuous.comp continuous_snd))))).subtype_mk _

private theorem coe_discCellFun {q : ℕ} (j : cell (univ : Set B) q)
    {z : (Fin q → ℝ) × (Fin (finrank ℝ F) → ℝ)} (h₁ : z.1 ∈ closedBall 0 1)
    (h₂ : z.2 ∈ closedBall 0 1) :
    (discCellFun (F := F) (E := E) j z : TotalSpace F E) =
      cellVector j ⟨z.1, h₁⟩ (fiberBallHomeomorph (F := F) z.2) := by
  have h₂' : ‖fiberBallHomeomorph (F := F) z.2‖ ≤ 1 := by
    simpa [mem_closedBall_zero_iff] using h₂
  simp only [discCellFun, radialRetractionToClosedBall_of_norm_le zero_le_one
    (mem_closedBall_zero_iff.1 h₁), coe_radialRetractionToClosedBall,
    radialRetraction_of_norm_le h₂']

private theorem proj_discCellFun {q : ℕ} (j : cell (univ : Set B) q)
    {z : (Fin q → ℝ) × (Fin (finrank ℝ F) → ℝ)} (h₁ : z.1 ∈ closedBall 0 1)
    (h₂ : z.2 ∈ closedBall 0 1) :
    (discCellFun (F := F) (E := E) j z : TotalSpace F E).proj = map q j z.1 := by
  rw [coe_discCellFun j h₁ h₂]
  rfl

private theorem norm_discCellFun {q : ℕ} (j : cell (univ : Set B) q)
    {z : (Fin q → ℝ) × (Fin (finrank ℝ F) → ℝ)} (h₁ : z.1 ∈ closedBall 0 1)
    (h₂ : z.2 ∈ closedBall 0 1) :
    ‖(discCellFun (F := F) (E := E) j z : TotalSpace F E).2‖ =
      ‖fiberBallHomeomorph (F := F) z.2‖ := by
  rw [coe_discCellFun j h₁ h₂, norm_cellVector]

/-- The closed disc-bundle cell over `j` is the part of the disc bundle over the closed cell
`j`. -/
private theorem image_discCellFun_closedBall {q : ℕ} (j : cell (univ : Set B) q) :
    discCellFun (F := F) (E := E) j '' (closedBall 0 1 ×ˢ closedBall 0 1) =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈ closedCell q j} := by
  refine Set.ext fun v ↦ ⟨?_, ?_⟩
  · rintro ⟨z, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨z.1, h₁, (proj_discCellFun j h₁ h₂).symm⟩
  · obtain ⟨⟨b, w⟩, hv⟩ := v
    rintro ⟨x, hx, rfl⟩
    have hy : (fiberBallHomeomorph (F := F)).symm ((cellFrame F E j ⟨x, hx⟩).repr w) ∈
        closedBall 0 1 := by
      rw [mem_closedBall_zero_iff,
        ContinuousLinearEquiv.norm_unitBallHomeomorph_symm_le_one_iff,
        LinearIsometryEquiv.norm_map]
      exact mem_discBundle.1 hv
    refine ⟨(x, _), ⟨hx, hy⟩, Subtype.ext ?_⟩
    rw [coe_discCellFun j hx hy]
    simp [cellVector]

/-- The open disc-bundle cell over `j` is the part of the open disc bundle over the open cell
`j`. -/
private theorem image_discCellFun_ball {q : ℕ} (j : cell (univ : Set B) q) :
    discCellFun (F := F) (E := E) j '' (ball 0 1 ×ˢ ball 0 1) =
      {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell q j ∧ ‖(v : TotalSpace F E).2‖ < 1} := by
  refine Set.ext fun v ↦ ⟨?_, ?_⟩
  · rintro ⟨z, ⟨h₁, h₂⟩, rfl⟩
    refine ⟨⟨z.1, h₁, (proj_discCellFun j (ball_subset_closedBall h₁)
      (ball_subset_closedBall h₂)).symm⟩, ?_⟩
    rw [norm_discCellFun j (ball_subset_closedBall h₁) (ball_subset_closedBall h₂),
      ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff, ← mem_ball_zero_iff]
    exact h₂
  · obtain ⟨⟨b, w⟩, hv⟩ := v
    rintro ⟨⟨x, hx, rfl⟩, hw⟩
    have hy : (fiberBallHomeomorph (F := F)).symm ((cellFrame F E j
        ⟨x, ball_subset_closedBall hx⟩).repr w) ∈ ball 0 1 := by
      rw [mem_ball_zero_iff,
        ContinuousLinearEquiv.norm_unitBallHomeomorph_symm_lt_one_iff,
        LinearIsometryEquiv.norm_map]
      exact hw
    refine ⟨(x, _), ⟨hx, hy⟩, Subtype.ext ?_⟩
    rw [coe_discCellFun j (ball_subset_closedBall hx) (ball_subset_closedBall hy)]
    simp [cellVector]

/-- The disc-bundle cell over `j` is injective on the product of the open unit balls. -/
private theorem injOn_discCellFun {q : ℕ} (j : cell (univ : Set B) q) :
    InjOn (discCellFun (F := F) (E := E) j) (ball 0 1 ×ˢ ball 0 1) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨x', y'⟩ ⟨hx', hy'⟩ h
  have h := congrArg Subtype.val h
  rw [coe_discCellFun j (ball_subset_closedBall hx) (ball_subset_closedBall hy),
    coe_discCellFun j (ball_subset_closedBall hx') (ball_subset_closedBall hy')] at h
  have hxx' : x = x' := by
    have h' := congrArg TotalSpace.proj h
    refine (map q j).injOn ?_ ?_ h' <;> rw [source_eq] <;> assumption
  subst hxx'
  have h' := TotalSpace.mk_inj.1 h
  simp only [Prod.mk.injEq, true_and]
  exact (fiberBallHomeomorph (F := F)).injective ((cellFrame F E j _).repr.symm.injective h')

/-- The boundary of the disc-bundle cell over `j` lies over the boundary of `j` or in the sphere
bundle. -/
private theorem discCellFun_mem_of_mem_sphere {q : ℕ} (j : cell (univ : Set B) q)
    {z : (Fin q → ℝ) × (Fin (finrank ℝ F) → ℝ)} (hz : z ∈ sphere 0 1) :
    (discCellFun (F := F) (E := E) j z : TotalSpace F E).proj ∈ cellFrontier q j ∨
      (discCellFun (F := F) (E := E) j z : TotalSpace F E) ∈ sphereBundle F E := by
  rw [sphere_prod] at hz
  rcases hz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨z.1, h₁, (proj_discCellFun j (sphere_subset_closedBall h₁) h₂).symm⟩
  · refine Or.inr ?_
    rw [mem_sphereBundle, norm_discCellFun j h₁ (sphere_subset_closedBall h₂),
      ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff, ← mem_sphere_zero_iff_norm]
    exact h₂

omit [RelCWComplex (univ : Set B) A] [FiniteDimensional ℝ F] in
/-- The image in the total space of a closed subset of the disc bundle is closed. -/
private theorem isClosed_image_val {T : Set (discBundle F E)} (hT : IsClosed T) :
    IsClosed ((↑) '' T : Set (TotalSpace F E)) :=
  (isClosed_discBundle (continuous_norm_bundle F E)).isClosedEmbedding_subtypeVal.isClosedMap _ hT

omit [RelCWComplex (univ : Set B) A] in
/-- If the part over the base point of `y` of a set `S` of the disc bundle is closed and misses
`y`, then in the preferred trivialization at that base point the fibre coordinates of this part
stay at a positive distance from those of `y`. The part is compact, since the closed fibre discs
are. -/
private theorem exists_pos_forall_notMem_closedBall {S : Set (discBundle F E)}
    {y : discBundle F E} (hy : y ∉ S)
    (hfib : IsClosed (S ∩ {v | (v : TotalSpace F E).proj = (y : TotalSpace F E).proj})) :
    ∃ ε > 0, ∀ v ∈ S, (v : TotalSpace F E).proj = (y : TotalSpace F E).proj →
      (trivializationAt F E (y : TotalSpace F E).proj v).2 ∉
        closedBall (trivializationAt F E (y : TotalSpace F E).proj y).2 ε := by
  set b := (y : TotalSpace F E).proj
  set e := trivializationAt F E b
  have hbU : b ∈ e.baseSet := mem_baseSet_trivializationAt F E b
  have hysrc : (y : TotalSpace F E) ∈ e.source := e.mem_source.2 hbU
  set Z₀ : Set (TotalSpace F E) := (↑) '' (S ∩ {v | (v : TotalSpace F E).proj = b})
  have hZ₀ : IsCompact Z₀ := by
    refine (IsCompact.norm_le_bundle (F := F) (E := E) (isCompact_singleton (x := b)) 1)
      |>.of_isClosed_subset (isClosed_image_val hfib) ?_
    rintro _ ⟨v, ⟨-, hvb⟩, rfl⟩
    exact ⟨hvb, mem_discBundle.1 v.2⟩
  have hZ₀src : Z₀ ⊆ e.source := by
    rintro _ ⟨v, ⟨-, hvb⟩, rfl⟩
    exact e.mem_source.2 (hvb ▸ hbU)
  set g : TotalSpace F E → F := fun v ↦ (e v).2
  have hK₀ : IsCompact (g '' Z₀) :=
    hZ₀.image_of_continuousOn ((continuous_snd.comp_continuousOn e.continuousOn).mono hZ₀src)
  -- Only `y` itself has the coordinates of `y` over `b`, so they are not those of a point of `S`.
  have hgy : g y ∉ g '' Z₀ := by
    rintro ⟨_, ⟨v, ⟨hvS, hvb⟩, rfl⟩, hgv⟩
    have hvsrc : (v : TotalSpace F E) ∈ e.source := hZ₀src ⟨v, ⟨hvS, hvb⟩, rfl⟩
    have hv : (v : TotalSpace F E) = y := e.injOn hvsrc hysrc
      (Prod.ext ((e.coe_fst hvsrc).trans (hvb.trans (e.coe_fst hysrc).symm)) hgv)
    exact hy (Subtype.ext hv ▸ hvS)
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 hK₀.isClosed.isOpen_compl (g y) hgy
  refine ⟨ε / 2, half_pos hε, fun v hvS hvb hvK ↦ ?_⟩
  exact (closedBall_subset_ball (half_lt_self hε)).trans hεK hvK ⟨v, ⟨⟨v, ⟨hvS, hvb⟩, rfl⟩, rfl⟩⟩

omit [RelCWComplex (univ : Set B) A] [FiniteDimensional ℝ F] in
/-- Let `T` be a closed set of the base over which a set `S` of the disc bundle is closed. Then the
base points of the vectors of `S` over the base set of `e` with coordinates in a compact set `K`,
together with the complement of the base set, meet `T` in a closed set
(`Bundle.Trivialization.isClosed_image_union_compl_baseSet`). -/
private theorem isClosed_image_union_compl_baseSet_inter (e : Trivialization F (π F E))
    {K : Set F} (hK : IsCompact K) {S : Set (discBundle F E)} {T : Set B} (hTc : IsClosed T)
    (hT : IsClosed (S ∩ {v | (v : TotalSpace F E).proj ∈ T})) :
    IsClosed ((π F E '' ((↑) '' S ∩ e.source ∩ e ⁻¹' (univ ×ˢ K)) ∪ e.baseSetᶜ) ∩ T) := by
  have heq : (π F E '' ((↑) '' S ∩ e.source ∩ e ⁻¹' (univ ×ˢ K)) ∪ e.baseSetᶜ) ∩ T =
      (π F E '' ((↑) '' (S ∩ {v | (v : TotalSpace F E).proj ∈ T}) ∩ e.source ∩
        e ⁻¹' (univ ×ˢ K)) ∪ e.baseSetᶜ) ∩ T := by
    ext x
    constructor
    · rintro ⟨⟨_, ⟨⟨⟨v, hvS, rfl⟩, hvsrc⟩, hvK⟩, rfl⟩ | hx, hxT⟩
      · exact ⟨Or.inl ⟨v, ⟨⟨⟨v, ⟨hvS, hxT⟩, rfl⟩, hvsrc⟩, hvK⟩, rfl⟩, hxT⟩
      · exact ⟨Or.inr hx, hxT⟩
    · rintro ⟨⟨_, ⟨⟨⟨v, ⟨hvS, -⟩, rfl⟩, hvsrc⟩, hvK⟩, rfl⟩ | hx, hxT⟩
      · exact ⟨Or.inl ⟨v, ⟨⟨⟨v, hvS, rfl⟩, hvsrc⟩, hvK⟩, rfl⟩, hxT⟩
      · exact ⟨Or.inr hx, hxT⟩
  rw [heq]
  exact (e.isClosed_image_union_compl_baseSet hK (isClosed_image_val hT)).inter hTc

variable [T2Space B] in
/-- **The disc bundle has the weak topology of its parts over the closed cells.** A subset `S` of
the disc bundle is closed as soon as its intersections with the parts of the disc bundle over the
closed cells of the base and over `A` are closed. Near a point `y ∉ S`, the vectors of `S` over the
base set of the preferred trivialization at the base point `b` of `y` with coordinates near those
of `y` lie over a set which does not contain `b` and is closed by the weak topology of the base. -/
private theorem isClosed_of_isClosed_inter_proj_mem (S : Set (discBundle F E))
    (hcell : ∀ q (j : cell (univ : Set B) q),
      IsClosed (S ∩ {v | (v : TotalSpace F E).proj ∈ closedCell q j}))
    (hA : IsClosed (S ∩ {v | (v : TotalSpace F E).proj ∈ A})) : IsClosed S := by
  -- Every point of the base lies in `A` or in a closed cell, over which `S` is closed.
  have hcover (x : B) : ∃ T : Set B, x ∈ T ∧ IsClosed T ∧
      IsClosed (S ∩ {v | (v : TotalSpace F E).proj ∈ T}) := by
    have hx : x ∈ A ∪ ⋃ (n : ℕ) (j : cell (univ : Set B) n), closedCell n j := by
      rw [RelCWComplex.union]
      exact mem_univ x
    rcases hx with hxA | hx
    · exact ⟨A, hxA, isClosedBase univ, hA⟩
    · obtain ⟨n, j, hxj⟩ := by simpa only [mem_iUnion] using hx
      exact ⟨closedCell n j, hxj, isClosed_closedCell, hcell n j⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  set b := (y : TotalSpace F E).proj
  set e := trivializationAt F E b
  have hbU : b ∈ e.baseSet := mem_baseSet_trivializationAt F E b
  have hysrc : (y : TotalSpace F E) ∈ e.source := e.mem_source.2 hbU
  have hfib : IsClosed (S ∩ {v | (v : TotalSpace F E).proj = b}) := by
    obtain ⟨T, hbT, -, hT⟩ := hcover b
    have heq : S ∩ {v | (v : TotalSpace F E).proj ∈ T} ∩
        {v : discBundle F E | (v : TotalSpace F E).proj ∈ ({b} : Set B)} =
        S ∩ {v | (v : TotalSpace F E).proj = b} :=
      Set.ext fun v ↦ ⟨fun h ↦ ⟨h.1.1, mem_singleton_iff.1 h.2⟩, fun h ↦
        ⟨⟨h.1, (h.2 ▸ hbT : (v : TotalSpace F E).proj ∈ T)⟩, mem_singleton_iff.2 h.2⟩⟩
    exact heq ▸ hT.inter (isClosed_singleton.preimage
      ((FiberBundle.continuous_proj F E).comp continuous_subtype_val))
  obtain ⟨ε, hε, hεS⟩ := exists_pos_forall_notMem_closedBall hy hfib
  -- The base points of the vectors of `S` with coordinates near those of `y` form, with the
  -- complement of the base set, a closed set `W` missing `b`.
  set W := π F E '' ((↑) '' S ∩ e.source ∩ e ⁻¹' (univ ×ˢ closedBall (e y).2 ε)) ∪ e.baseSetᶜ
  have hW : IsClosed W := by
    rw [RelCWComplex.closed (univ : Set B) _ (subset_univ _)]
    exact ⟨fun n j ↦ isClosed_image_union_compl_baseSet_inter e (isCompact_closedBall _ _)
      isClosed_closedCell (hcell n j), isClosed_image_union_compl_baseSet_inter e
        (isCompact_closedBall _ _) (isClosedBase univ) hA⟩
  have hbW : b ∉ W := by
    rintro (⟨_, ⟨⟨⟨v, hvS, rfl⟩, -⟩, -, hvK⟩, hvb⟩ | hb)
    · exact hεS v hvS hvb hvK
    · exact hb hbU
  -- The vectors over the complement of `W` with coordinates near those of `y` miss `S`.
  set N : Set (discBundle F E) :=
    (↑) ⁻¹' (e.source ∩ e ⁻¹' (Wᶜ ×ˢ ball (e y).2 ε))
  have hN : IsOpen N :=
    (e.continuousOn.isOpen_inter_preimage e.open_source
      (hW.isOpen_compl.prod isOpen_ball)).preimage continuous_subtype_val
  have hyN : y ∈ N := ⟨hysrc, by rw [e.coe_fst hysrc]; exact hbW, mem_ball_self hε⟩
  filter_upwards [hN.mem_nhds hyN] with v ⟨hvsrc, hv1, hv2⟩ hvS
  exact hv1 (Or.inl ⟨v, ⟨⟨⟨v, hvS, rfl⟩, hvsrc⟩, mem_univ _, ball_subset_closedBall hv2⟩,
    (e.coe_fst hvsrc).symm⟩)

variable (F) in
/-- The cells of dimension `n` of the disc bundle: the `q`-cells of the base with `q + r = n`,
where `r` is the rank of the bundle. -/
private abbrev DiscCell (n : ℕ) : Type u :=
  Σ q : {q : ℕ // q + finrank ℝ F = n}, cell (univ : Set B) (q : ℕ)

/-- The splitting of the coordinates of a disc-bundle cell into base and fibre coordinates. -/
private abbrev discCellIsometry {n : ℕ} (c : DiscCell (B := B) F n) :
    (Fin n → ℝ) ≃ᵢ (Fin (c.1 : ℕ) → ℝ) × (Fin (finrank ℝ F) → ℝ) :=
  (Fin.appendIsometryOfEq c.1.2).symm

omit [FiniteDimensional ℝ F] in
private theorem discCellIsometry_zero {n : ℕ} (c : DiscCell (B := B) F n) :
    discCellIsometry c 0 = 0 := by
  ext <;> simp

omit [FiniteDimensional ℝ F] in
private theorem image_discCellIsometry_ball {n : ℕ} (c : DiscCell (B := B) F n) :
    discCellIsometry c '' ball 0 1 = ball 0 1 ×ˢ ball 0 1 := by
  rw [IsometryEquiv.image_ball, discCellIsometry_zero, Prod.zero_eq_mk, ball_prod_same]

omit [FiniteDimensional ℝ F] in
private theorem image_discCellIsometry_closedBall {n : ℕ} (c : DiscCell (B := B) F n) :
    discCellIsometry c '' closedBall 0 1 = closedBall 0 1 ×ˢ closedBall 0 1 := by
  rw [IsometryEquiv.image_closedBall, discCellIsometry_zero, Prod.zero_eq_mk,
    closedBall_prod_same]

omit [FiniteDimensional ℝ F] in
private theorem discCellIsometry_mem_sphere {n : ℕ} (c : DiscCell (B := B) F n)
    {z : Fin n → ℝ} (hz : z ∈ sphere 0 1) : discCellIsometry c z ∈ sphere 0 1 := by
  rwa [mem_sphere, ← discCellIsometry_zero c, IsometryEquiv.dist_eq]

/-- The characteristic map of the disc-bundle cell `c`, as a function. -/
private def discCellMapFun {n : ℕ} (c : DiscCell (B := B) F n) (z : Fin n → ℝ) :
    discBundle F E :=
  discCellFun c.2 (discCellIsometry c z)

private theorem continuous_discCellMapFun {n : ℕ} (c : DiscCell (B := B) F n) :
    Continuous (discCellMapFun (E := E) c) :=
  (continuous_discCellFun c.2).comp (discCellIsometry c).continuous

private theorem image_discCellMapFun {n : ℕ} (c : DiscCell (B := B) F n) (s : Set (Fin n → ℝ)) :
    discCellMapFun (E := E) c '' s = discCellFun c.2 '' (discCellIsometry c '' s) :=
  image_comp _ _ _

private theorem injOn_discCellMapFun {n : ℕ} (c : DiscCell (B := B) F n) :
    InjOn (discCellMapFun (E := E) c) (ball 0 1) :=
  (injOn_discCellFun c.2).comp (discCellIsometry c).injective.injOn fun _ hz ↦
    image_discCellIsometry_ball c ▸ mem_image_of_mem _ hz

/-- The characteristic map of the disc-bundle cell `c`. -/
private def discCellMap {n : ℕ} (c : DiscCell (B := B) F n) :
    PartialEquiv (Fin n → ℝ) (discBundle F E) :=
  InjOn.toPartialEquiv (discCellMapFun c) (ball 0 1) (injOn_discCellMapFun c)

private theorem coe_discCellMap {n : ℕ} (c : DiscCell (B := B) F n) :
    ⇑(discCellMap (E := E) c) = discCellMapFun c :=
  rfl

private theorem coe_discCellMap_symm {n : ℕ} (c : DiscCell (B := B) F n) :
    ⇑(discCellMap (E := E) c).symm = Function.invFunOn (discCellMapFun c) (ball 0 1) :=
  rfl

private theorem discCellMap_target {n : ℕ} (c : DiscCell (B := B) F n) :
    (discCellMap (E := E) c).target = discCellMapFun c '' ball 0 1 :=
  rfl

private theorem image_discCellMap_closedBall {n : ℕ} (c : DiscCell (B := B) F n) :
    discCellMap (E := E) c '' closedBall 0 1 =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈ closedCell (c.1 : ℕ) c.2} := by
  rw [coe_discCellMap, image_discCellMapFun, image_discCellIsometry_closedBall,
    image_discCellFun_closedBall]

private theorem image_discCellMap_ball {n : ℕ} (c : DiscCell (B := B) F n) :
    discCellMap (E := E) c '' ball 0 1 =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈ openCell (c.1 : ℕ) c.2 ∧
        ‖(v : TotalSpace F E).2‖ < 1} := by
  rw [coe_discCellMap, image_discCellMapFun, image_discCellIsometry_ball, image_discCellFun_ball]

private theorem discCellMap_mem_of_mem_sphere {n : ℕ} (c : DiscCell (B := B) F n)
    {z : Fin n → ℝ} (hz : z ∈ sphere 0 1) :
    (discCellMap (E := E) c z : TotalSpace F E).proj ∈ cellFrontier (c.1 : ℕ) c.2 ∨
      (discCellMap (E := E) c z : TotalSpace F E) ∈ sphereBundle F E :=
  discCellFun_mem_of_mem_sphere c.2 (discCellIsometry_mem_sphere c hz)

/-- The disc-bundle cell over the `q`-cell `j` of the base. -/
private abbrev discCellOf {q : ℕ} (j : cell (univ : Set B) q) :
    DiscCell (B := B) F (q + finrank ℝ F) :=
  ⟨⟨q, rfl⟩, j⟩

omit [FiniteDimensional ℝ F] in
/-- A disc-bundle cell is determined by its base cell. -/
private theorem injective_discCell_sigma (m : ℕ) :
    Function.Injective fun d : DiscCell (B := B) F m ↦
      (⟨d.1, d.2⟩ : Σ k : ℕ, cell (univ : Set B) k) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq hi
  rfl

omit [FiniteDimensional ℝ F] in
/-- The disc-bundle cells of a given dimension over a finite family of base cells of dimension
less than `q` form a finite set. -/
private theorem finite_setOf_discCell (I : Π k, Finset (cell (univ : Set B) k)) (q m : ℕ) :
    {d : DiscCell (B := B) F m | (d.1 : ℕ) < q ∧ d.2 ∈ I d.1}.Finite := by
  refine Finite.of_finite_image ?_ (injective_discCell_sigma m).injOn
  refine ((Finset.range q).sigma I).finite_toSet.subset ?_
  rintro _ ⟨d, ⟨hd, hdI⟩, rfl⟩
  exact Finset.mem_sigma.2 ⟨Finset.mem_range.2 hd, hdI⟩

/-- The boundary of a disc-bundle cell lies in the base of the relative CW structure and finitely
many disc-bundle cells of smaller dimension. -/
private theorem exists_mapsTo_discCellMap {n : ℕ} (c : DiscCell (B := B) F n) :
    ∃ I : Π m, Finset (DiscCell (B := B) F m), MapsTo (discCellMap (E := E) c) (sphere 0 1)
      ((↑) ⁻¹' (sphereBundle F E ∪ π F E ⁻¹' A) ∪
        ⋃ (m < n) (d ∈ I m), discCellMap (E := E) d '' closedBall 0 1) := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (c.1 : ℕ) c.2
  refine ⟨fun m ↦ (finite_setOf_discCell (F := F) I c.1 m).toFinset, fun z hz ↦ ?_⟩
  rcases discCellMap_mem_of_mem_sphere (E := E) c hz with h | h
  · rcases hI h with hA | h
    · exact Or.inl (Or.inr hA)
    obtain ⟨m, hm, k, hk, hvk⟩ : ∃ m < (c.1 : ℕ), ∃ k ∈ I m,
        (discCellMap (E := E) c z : TotalSpace F E).proj ∈ closedCell m k := by
      simpa only [mem_iUnion, exists_prop] using h
    refine Or.inr (mem_iUnion₂.2 ⟨m + finrank ℝ F, by have := c.1.2; omega, mem_iUnion₂.2
      ⟨discCellOf k, (finite_setOf_discCell (F := F) I _ _).mem_toFinset.2 ⟨hm, hk⟩, ?_⟩⟩)
    rw [image_discCellMap_closedBall]
    exact hvk
  · exact Or.inl (Or.inl h)

/-- The open disc-bundle cells are pairwise disjoint. -/
private theorem pairwiseDisjoint_discCellMap :
    (univ : Set (Σ n, DiscCell (B := B) F n)).PairwiseDisjoint
      (fun c ↦ discCellMap (E := E) c.2 '' ball 0 1) := by
  rintro ⟨n, ⟨q, hq⟩, j⟩ - ⟨n', ⟨q', hq'⟩, j'⟩ - hne
  simp only [Function.onFun, image_discCellMap_ball]
  refine disjoint_left.2 fun v hv hv' ↦ hne ?_
  have hjj' := not_disjoint_iff.2 ⟨_, hv.1, hv'.1⟩
  obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.1 (not_not.1 (mt disjoint_openCell_of_ne hjj'))
  obtain rfl := eq_of_heq hj
  obtain rfl : n = n' := hq.symm.trans hq'
  rfl

variable [T2Space B]

/-- The inverse of the characteristic map of a disc-bundle cell is continuous on the open cell. -/
private theorem continuousOn_discCellMap_symm {n : ℕ} (c : DiscCell (B := B) F n) :
    ContinuousOn (discCellMap (E := E) c).symm (discCellMap (E := E) c).target := by
  rw [coe_discCellMap_symm, discCellMap_target]
  refine (continuous_discCellMapFun c).continuousOn.continuousOn_invFunOn_image_of_isCompact
    (isCompact_closedBall 0 1) ball_subset_closedBall (injOn_discCellMapFun c) ?_
  rw [closedBall_sdiff_ball, disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ hball
  rw [← coe_discCellMap, image_discCellMap_ball] at hball
  rcases discCellMap_mem_of_mem_sphere (E := E) c hz with h | h
  · exact disjoint_left.1 (disjoint_openCell_cellFrontier _ c.2) hball.1 h
  · exact (mem_sphereBundle.1 h).not_lt hball.2

omit [T2Space B] in
/-- The base of the relative CW structure and the closed disc-bundle cells cover the disc
bundle. -/
private theorem union_discCellMap :
    (↑) ⁻¹' (sphereBundle F E ∪ π F E ⁻¹' A) ∪
      ⋃ (n : ℕ) (c : DiscCell (B := B) F n), discCellMap (E := E) c '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun v ↦ ?_
  have hv : (v : TotalSpace F E).proj ∈ A ∪ ⋃ (n : ℕ) (j : cell (univ : Set B) n),
      closedCell n j := by
    rw [RelCWComplex.union]
    exact mem_univ _
  rcases hv with hA | hv
  · exact Or.inl (Or.inr hA)
  · obtain ⟨q, j, hj⟩ := by simpa only [mem_iUnion] using hv
    refine Or.inr (mem_iUnion₂.2 ⟨q + finrank ℝ F, discCellOf j, ?_⟩)
    rw [image_discCellMap_closedBall]
    exact hj

/-- The disc bundle has the weak topology of its closed cells and its base. -/
private theorem isClosed_of_isClosed_inter_discCellMap (S : Set (discBundle F E))
    (h : (∀ n (c : DiscCell (B := B) F n),
        IsClosed (S ∩ discCellMap (E := E) c '' closedBall 0 1)) ∧
      IsClosed (S ∩ (↑) ⁻¹' (sphereBundle F E ∪ π F E ⁻¹' A))) : IsClosed S := by
  refine isClosed_of_isClosed_inter_proj_mem S (fun q j ↦ ?_) ?_
  · simpa only [image_discCellMap_closedBall] using h.1 _ (discCellOf j)
  · have hA : IsClosed {v : discBundle F E | (v : TotalSpace F E).proj ∈ A} :=
      (isClosedBase univ).preimage ((FiberBundle.continuous_proj F E).comp continuous_subtype_val)
    have heq : S ∩ ((↑) ⁻¹' (sphereBundle F E ∪ π F E ⁻¹' A)) ∩
        {v : discBundle F E | (v : TotalSpace F E).proj ∈ A} =
        S ∩ {v | (v : TotalSpace F E).proj ∈ A} :=
      Set.ext fun v ↦ ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, Or.inr h.2⟩, h.2⟩⟩
    exact heq ▸ h.2.inter hA

variable (A F E) in
/-- **The relative CW structure of a disc bundle.** Let `E` be a finite-rank real vector bundle
with a continuous fibre metric over a relative CW complex `(B, A)`, where `B` is Hausdorff. Its
unit disc bundle `D(E)` is a CW complex relative to the union of its unit sphere bundle `S(E)` and
of the part of `D(E)` over `A`. It has one `(q + r)`-cell for each `q`-cell of `(B, A)`, where `r`
is the rank of `E`: the part of `D(E)` over the closed cell. Its characteristic map is the product
of the characteristic map of the base cell with a continuous orthonormal frame of `E` along it,
read on the closed unit ball of the fibre coordinates. No orientation of `E` is used.

It is not an instance: the base of a relative CW complex is an `outParam`, and `univ` carries other
relative CW structures. -/
@[instance_reducible]
def relCWComplexDiscBundle :
    RelCWComplex (univ : Set (discBundle F E)) ((↑) ⁻¹' (sphereBundle F E ∪ π F E ⁻¹' A)) where
  cell := DiscCell F
  map _ c := discCellMap c
  source_eq _ _ := rfl
  continuousOn _ c := (continuous_discCellMapFun c).continuousOn
  continuousOn_symm _ c := continuousOn_discCellMap_symm c
  pairwiseDisjoint' := pairwiseDisjoint_discCellMap
  disjointBase' _ c := by
    rw [image_discCellMap_ball, disjoint_left]
    rintro v ⟨hv, hv1⟩ (hS | hA)
    · exact (mem_sphereBundle.1 hS).not_lt hv1
    · exact disjoint_left.1 (disjointBase _ c.2) hv hA
  mapsTo _ c := exists_mapsTo_discCellMap c
  closed' S _ h := isClosed_of_isClosed_inter_discCellMap S h
  isClosedBase :=
    ((isClosed_sphereBundle (continuous_norm_bundle F E)).union
      ((isClosedBase univ).preimage (FiberBundle.continuous_proj F E))).preimage
      continuous_subtype_val
  union' := union_discCellMap

variable (A F E) in
/-- The `(q + r)`-cells of the relative CW structure on the disc bundle, where `r` is the rank, are
the `q`-cells of the base. -/
def cellDiscBundleEquiv (q : ℕ) :
    @cell _ _ (univ : Set (discBundle F E)) _ (relCWComplexDiscBundle A F E)
      (q + finrank ℝ F) ≃ cell (univ : Set B) q where
  toFun c := (Nat.add_right_cancel c.1.2 : (c.1 : ℕ) = q) ▸ c.2
  invFun j := ⟨⟨q, rfl⟩, j⟩
  left_inv := by
    rintro ⟨⟨q', h⟩, j⟩
    obtain rfl : q' = q := Nat.add_right_cancel h
    rfl
  right_inv _ := rfl

/-- The relative CW structure on the disc bundle has no cells of dimension less than the rank. -/
theorem isEmpty_cell_relCWComplexDiscBundle {n : ℕ} (hn : n < finrank ℝ F) :
    IsEmpty (@cell _ _ (univ : Set (discBundle F E)) _ (relCWComplexDiscBundle A F E) n) :=
  ⟨fun c ↦ by have := c.1.2; omega⟩

/-- The closed cell of the disc bundle over the `q`-cell `j` of the base is the part of the disc
bundle over the closed cell `j`. -/
@[simp]
theorem closedCell_relCWComplexDiscBundle {q : ℕ} (j : cell (univ : Set B) q) :
    @closedCell _ _ (univ : Set (discBundle F E)) _ (relCWComplexDiscBundle A F E)
      (q + finrank ℝ F) ((cellDiscBundleEquiv A F E q).symm j) =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈ closedCell q j} :=
  image_discCellMap_closedBall (discCellOf j)

/-- The open cell of the disc bundle over the `q`-cell `j` of the base consists of the vectors of
norm less than one over the open cell `j`. -/
@[simp]
theorem openCell_relCWComplexDiscBundle {q : ℕ} (j : cell (univ : Set B) q) :
    @openCell _ _ (univ : Set (discBundle F E)) _ (relCWComplexDiscBundle A F E)
      (q + finrank ℝ F) ((cellDiscBundleEquiv A F E q).symm j) =
      {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell q j ∧ ‖(v : TotalSpace F E).2‖ < 1} :=
  image_discCellMap_ball (discCellOf j)

/-- On the closed unit ball, the characteristic map of the disc bundle over the `q`-cell `j` of the
base lies over the characteristic map of `j`, evaluated on the first `q` coordinates. -/
theorem proj_map_relCWComplexDiscBundle {q : ℕ} (j : cell (univ : Set B) q)
    {x : Fin (q + finrank ℝ F) → ℝ} (hx : x ∈ closedBall 0 1) :
    ((@map _ _ (univ : Set (discBundle F E)) _ (relCWComplexDiscBundle A F E)
      (q + finrank ℝ F) ((cellDiscBundleEquiv A F E q).symm j) x : discBundle F E) :
        TotalSpace F E).proj = map q j fun i ↦ x (Fin.castAdd _ i) := by
  have hx' := image_discCellIsometry_closedBall (discCellOf (F := F) j) ▸ mem_image_of_mem _ hx
  exact (proj_discCellFun j hx'.1 hx'.2).trans (by simp [discCellIsometry])

end Cells

end TauCeti
