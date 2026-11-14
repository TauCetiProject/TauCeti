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
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.MetricSpace.Isometry.Basic
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.VectorBundle.Contractible

/-!
# The disc bundle of a vector bundle over a CW complex

Let `E → B` be a real vector bundle of finite rank `r` whose fibre norm is continuous on the total
space, over a Hausdorff space `B` which is a finite CW complex relative to its base `A`. Then
the unit disc bundle `D(E)` (`TauCeti.discBundle`), taken as a space, is a finite CW complex
relative to `S(E) ∪ D(E)|_A`, the unit sphere bundle together with the disc bundle over `A`
(`TauCeti.discBundleRelCWComplex`). Its `m`-cells are the `n`-cells of `B` with `n + r = m`
(`TauCeti.discBundleRelCWComplexCellEquiv`), so it has no cells below dimension `r`
(`TauCeti.isEmpty_cell_discBundleRelCWComplex_of_lt`). No orientation of `E` is needed. In rank `0`
the sphere bundle is empty, `D(E)` is the total space and its cells are those of `B`.

The cell over an `n`-cell `j` of `B` with characteristic map `φ` is built in the pullback of `E`
along `φ`. The closed unit ball is contractible, so `E` has an orthonormal frame
`L y : ℝʳ ≃ₗᵢ E (φ y)` along `φ`, depending continuously on `y`
(`TauCeti.exists_continuous_linearIsometryEquiv_of_contractibleSpace`). The characteristic map
splits the coordinates of `x ∈ ℝⁿ⁺ʳ` into base coordinates `y` first and fibre coordinates `z`
last (`Fin.appendIsometryOfEq`), and sends `x` to the vector `L y (ρ z)` over `φ y`, where `ρ`
is the radial homeomorphism of the sup-norm unit ball of `ℝʳ` onto the Euclidean one
(`ContinuousLinearEquiv.unitBallHomeomorph`); this form is exported as
`TauCeti.exists_linearIsometryEquiv_map_discBundleRelCWComplex`. So the open cell over `j`
consists of the vectors of norm less than one over the open cell of `j`
(`TauCeti.openCell_discBundleRelCWComplex`), the closed cell is the disc bundle over the closed
cell of `j` (`TauCeti.closedCell_discBundleRelCWComplex`), and the frontier is the disc bundle over
the frontier of `j` together with the sphere bundle over its closed cell
(`TauCeti.cellFrontier_discBundleRelCWComplex`). The inverse of a characteristic map is continuous
on its open cell because the closed ball is compact
(`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`), and the weak topology is automatic for
finitely many cells. The characteristic maps depend on the chosen frames; the cells do not.

For an infinite complex the weak topology of `D(E)` needs a separate argument through the local
compactness of the disc fibre, and is not treated here.

## Main declarations

* `TauCeti.discBundleRelCWComplex`: the relative CW structure on `D(E)` over
  `S(E) ∪ D(E)|_A`.
* `TauCeti.discBundleRelCWComplexCellEquiv`, `TauCeti.discBundleRelCWComplexCellAddRankEquiv`:
  its `m`-cells are the `n`-cells of `B` with `n + r = m`; the cell over the `n`-cell `j` lies over
  `j` (`TauCeti.discBundleRelCWComplexCellEquiv_cellAddRankEquiv_symm`).
* `TauCeti.openCell_discBundleRelCWComplex`, `TauCeti.closedCell_discBundleRelCWComplex`,
  `TauCeti.cellFrontier_discBundleRelCWComplex`: its open cells, closed cells and cell frontiers.
* `TauCeti.proj_map_discBundleRelCWComplex`, `TauCeti.norm_map_discBundleRelCWComplex`: its
  characteristic maps cover those of `B` and read the fibre coordinates radially.
* `TauCeti.exists_linearIsometryEquiv_map_discBundleRelCWComplex`: over each base point, its
  characteristic maps are a continuous orthonormal frame applied to the radial image of the fibre
  coordinates.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §18 (the cell structure of the Thom space of a bundle over a CW complex).
-/

public section

noncomputable section

open Bundle Function Metric Module Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section CW

variable {B : Type u} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type u} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {A : Set B} [RelCWComplex (univ : Set B) A]

/-- The splitting `ℝᵐ ≃ ℝⁿ × ℝʳ` of the coordinates of a cell of `D(E)` into base coordinates
first and fibre coordinates last, in the sup norm. -/
private abbrev splitIso {n r m : ℕ} (h : n + r = m) : (Fin m → ℝ) ≃ᵢ (Fin n → ℝ) × (Fin r → ℝ) :=
  (Fin.appendIsometryOfEq h).symm

/-- The radial homeomorphism of `ℝʳ` with the sup norm onto Euclidean `ℝʳ`, carrying the closed
unit ball, the open unit ball and the unit sphere onto the corresponding Euclidean ones. -/
private abbrev ballCoord (r : ℕ) : (Fin r → ℝ) ≃ₜ EuclideanSpace ℝ (Fin r) :=
  (EuclideanSpace.equiv (Fin r) ℝ).symm.unitBallHomeomorph

/-- The characteristic map of an `n`-cell of `B`, as a continuous map on the closed unit ball. -/
private def cellBaseMap {n : ℕ} (j : cell (univ : Set B) n) : C(closedBall (0 : Fin n → ℝ) 1, B) :=
  ⟨(closedBall 0 1).domRestrict (map n j), (RelCWComplex.continuousOn n j).domRestrict⟩

private theorem exists_cellFrame {n : ℕ} (j : cell (univ : Set B) n) :
    ∃ L : ∀ y : closedBall (0 : Fin n → ℝ) 1,
        EuclideanSpace ℝ (Fin (finrank ℝ F)) ≃ₗᵢ[ℝ] E (map n j y),
      Continuous fun p : closedBall (0 : Fin n → ℝ) 1 × EuclideanSpace ℝ (Fin (finrank ℝ F)) ↦
        TotalSpace.mk' F (map n j p.1) (L p.1 p.2) := by
  let : ContractibleSpace (closedBall (0 : Fin n → ℝ) 1) :=
    (convex_closedBall 0 1).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩
  exact exists_continuous_linearIsometryEquiv_of_contractibleSpace F E (cellBaseMap j)

/-- An orthonormal frame of `E` along the characteristic map of a cell of `B`. -/
private def cellFrame {n : ℕ} (j : cell (univ : Set B) n) (y : closedBall (0 : Fin n → ℝ) 1) :
    EuclideanSpace ℝ (Fin (finrank ℝ F)) ≃ₗᵢ[ℝ] E (map n j y) :=
  (exists_cellFrame (F := F) (E := E) j).choose y

private theorem continuous_cellFrame {n : ℕ} (j : cell (univ : Set B) n) :
    Continuous fun p : closedBall (0 : Fin n → ℝ) 1 × EuclideanSpace ℝ (Fin (finrank ℝ F)) ↦
      TotalSpace.mk' F (map n j p.1) (cellFrame (F := F) (E := E) j p.1 p.2) :=
  (exists_cellFrame (F := F) (E := E) j).choose_spec

open scoped Classical in
/-- The characteristic map of the cell of `D(E)` over the `n`-cell `j` of `B`: the point with base
coordinates `y` and fibre coordinates `z` goes to the vector `L y (ρ z)` over `φ y`, where `φ` is
the characteristic map of `j`, `L` an orthonormal frame along `φ` and `ρ` the radial comparison of
the sup-norm and Euclidean balls. Outside the closed unit ball it is the zero vector over `φ 0`. -/
private def discCellFun {n m : ℕ} (j : cell (univ : Set B) n) (h : n + finrank ℝ F = m)
    (x : Fin m → ℝ) : discBundle F E :=
  if hx : x ∈ closedBall 0 1 then
    ⟨TotalSpace.mk' F (map n j (splitIso h x).1)
        (cellFrame j ⟨_, ((Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).1 hx).1⟩
          (ballCoord _ (splitIso h x).2)), by
      rw [mem_discBundle, LinearIsometryEquiv.norm_map,
        ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff]
      exact mem_closedBall_zero_iff.1 ((Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).1 hx).2⟩
  else ⟨TotalSpace.mk' F (map n j 0) 0, by simp⟩

private theorem coe_discCellFun_of_mem {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) {x : Fin m → ℝ} (hx : x ∈ closedBall 0 1)
    (hy : (splitIso h x).1 ∈ closedBall 0 1) :
    (discCellFun (E := E) j h x : TotalSpace F E) =
      TotalSpace.mk' F (map n j (splitIso h x).1)
        (cellFrame j ⟨_, hy⟩ (ballCoord _ (splitIso h x).2)) := by
  rw [discCellFun, dite_eq_left hx]

/-- The frame vectors over equal base points with equal coordinates are equal; this transports the
membership proof in the closed ball along an equation of coordinates. -/
private theorem mk_cellFrame_congr {n : ℕ} (j : cell (univ : Set B) n)
    {p q : (Fin n → ℝ) × (Fin (finrank ℝ F) → ℝ)} (hpq : p = q) (hp : p.1 ∈ closedBall 0 1)
    (hq : q.1 ∈ closedBall 0 1) :
    TotalSpace.mk' F (map n j p.1) (cellFrame (E := E) j ⟨_, hp⟩ (ballCoord _ p.2)) =
      TotalSpace.mk' F (map n j q.1) (cellFrame j ⟨_, hq⟩ (ballCoord _ q.2)) := by
  subst hpq
  rfl

private theorem coe_discCellFun_appendIsometryOfEq {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) {y : Fin n → ℝ} {z : Fin (finrank ℝ F) → ℝ}
    (hy : y ∈ closedBall 0 1) (hz : z ∈ closedBall 0 1) :
    (discCellFun (E := E) j h (Fin.appendIsometryOfEq h (y, z)) : TotalSpace F E) =
      TotalSpace.mk' F (map n j y) (cellFrame j ⟨y, hy⟩ (ballCoord _ z)) := by
  have hsplit : splitIso h (Fin.appendIsometryOfEq h (y, z)) = (y, z) :=
    IsometryEquiv.symm_apply_apply _ _
  have hy' : (splitIso h (Fin.appendIsometryOfEq h (y, z))).1 ∈ closedBall 0 1 := by
    rw [hsplit]
    exact hy
  have hx : Fin.appendIsometryOfEq h (y, z) ∈ closedBall 0 1 :=
    (Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).2 (by rw [hsplit]; exact ⟨hy, hz⟩)
  rw [coe_discCellFun_of_mem j h hx hy']
  exact mk_cellFrame_congr j hsplit hy' hy

private theorem continuousOn_discCellFun {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) : ContinuousOn (discCellFun (E := E) j h) (closedBall 0 1) := by
  rw [IsInducing.subtypeVal.continuousOn_iff, continuousOn_iff_continuous_domRestrict]
  have hfst (x : closedBall (0 : Fin m → ℝ) 1) : (splitIso h x).1 ∈ closedBall 0 1 :=
    ((Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).1 x.2).1
  refine ((continuous_cellFrame (F := F) (E := E) j).comp (Continuous.prodMk
    (((continuous_fst.comp (splitIso h).continuous).comp continuous_subtype_val).subtype_mk hfst)
    ((ballCoord _).continuous.comp
      ((continuous_snd.comp (splitIso h).continuous).comp continuous_subtype_val)))).congr
    fun x ↦ ?_
  simp only [domRestrict_apply, Function.comp_apply, discCellFun, dite_eq_left x.2]

/-- The image under `discCellFun` of the points whose base coordinates lie in `S` and whose fibre
coordinates satisfy a norm condition `P` preserved by the radial comparison. -/
private theorem image_discCellFun {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) {S : Set (Fin n → ℝ)} (hS : S ⊆ closedBall 0 1) {P : ℝ → Prop}
    (hP : ∀ t, P t → t ≤ 1) (hPρ : ∀ z, P ‖ballCoord (finrank ℝ F) z‖ ↔ P ‖z‖) :
    discCellFun (E := E) j h '' {x | (splitIso h x).1 ∈ S ∧ P ‖(splitIso h x).2‖} =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈ map n j '' S ∧
        P ‖(v : TotalSpace F E).2‖} := by
  refine Set.ext fun v ↦ ?_
  obtain ⟨⟨b, w⟩, hw⟩ := v
  constructor
  · rintro ⟨x, ⟨hxS, hxP⟩, hx⟩
    have hmem : x ∈ closedBall (0 : Fin m → ℝ) 1 :=
      (Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).2
        ⟨hS hxS, mem_closedBall_zero_iff.2 (hP _ hxP)⟩
    have hv := congrArg Subtype.val hx
    rw [coe_discCellFun_of_mem j h hmem (hS hxS)] at hv
    obtain rfl := congrArg TotalSpace.proj hv
    refine ⟨⟨_, hxS, rfl⟩, ?_⟩
    have hw' := TotalSpace.mk_inj.1 hv
    simp only [← hw', LinearIsometryEquiv.norm_map, hPρ]
    exact hxP
  · rintro ⟨⟨y, hyS, rfl⟩, hwP⟩
    let z := (ballCoord _).symm ((cellFrame (F := F) (E := E) j ⟨y, hS hyS⟩).symm w)
    have hzP : P ‖z‖ := by
      rw [← hPρ]
      simpa [z] using hwP
    refine ⟨Fin.appendIsometryOfEq h (y, z), ⟨by simpa using hyS, by simpa using hzP⟩,
      Subtype.ext ?_⟩
    rw [coe_discCellFun_appendIsometryOfEq j h (hS hyS) (mem_closedBall_zero_iff.2 (hP _ hzP))]
    simp [z]

/-- The open cell over `j`: the vectors of norm less than one over the open cell of `j`. -/
private theorem image_ball_discCellFun {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) :
    discCellFun (E := E) j h '' ball 0 1 =
      {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell n j ∧ ‖(v : TotalSpace F E).2‖ < 1} := by
  have hball : ball (0 : Fin m → ℝ) 1 =
      {x | (splitIso h x).1 ∈ ball 0 1 ∧ ‖(splitIso h x).2‖ < 1} :=
    Set.ext fun _ ↦ (Fin.mem_ball_iff_appendIsometryOfEq_symm h).trans
      (and_congr_right' mem_ball_zero_iff)
  rw [hball]
  exact image_discCellFun (E := E) j h ball_subset_closedBall (fun (_ : ℝ) (ht : _ < 1) ↦ ht.le)
    fun _ ↦ ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff _

/-- The closed cell over `j`: the whole disc bundle over the closed cell of `j`. -/
private theorem image_closedBall_discCellFun {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) :
    discCellFun (E := E) j h '' closedBall 0 1 =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈ closedCell n j} := by
  have hclosedBall : closedBall (0 : Fin m → ℝ) 1 =
      {x | (splitIso h x).1 ∈ closedBall 0 1 ∧ ‖(splitIso h x).2‖ ≤ 1} :=
    Set.ext fun _ ↦ (Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).trans
      (and_congr_right' mem_closedBall_zero_iff)
  rw [hclosedBall,
    image_discCellFun (E := E) j h subset_rfl (fun (_ : ℝ) (ht : _ ≤ 1) ↦ ht)
      fun _ ↦ ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff _]
  exact Set.ext fun v ↦ and_iff_left (mem_discBundle.1 v.2)

/-- The frontier of the cell over `j`: the disc bundle over the frontier of `j` together with the
sphere bundle over its closed cell. -/
private theorem image_sphere_discCellFun {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) :
    discCellFun (E := E) j h '' sphere 0 1 =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈ cellFrontier n j} ∪
        {v : discBundle F E |
          (v : TotalSpace F E).proj ∈ closedCell n j ∧ ‖(v : TotalSpace F E).2‖ = 1} := by
  have hsphere : sphere (0 : Fin m → ℝ) 1 =
      {x | (splitIso h x).1 ∈ sphere 0 1 ∧ ‖(splitIso h x).2‖ ≤ 1} ∪
        {x | (splitIso h x).1 ∈ closedBall 0 1 ∧ ‖(splitIso h x).2‖ = 1} :=
    Set.ext fun _ ↦ (Fin.mem_sphere_iff_appendIsometryOfEq_symm h).trans
      (or_congr (and_congr_right' mem_closedBall_zero_iff)
        (and_congr_right' mem_sphere_zero_iff_norm))
  rw [hsphere, image_union,
    image_discCellFun (E := E) j h sphere_subset_closedBall (fun (_ : ℝ) (ht : _ ≤ 1) ↦ ht)
      fun _ ↦ ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff _,
    image_discCellFun (E := E) j h subset_rfl (fun (_ : ℝ) (ht : _ = 1) ↦ ht.le)
      fun _ ↦ ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff _]
  congr 1
  exact Set.ext fun v ↦ and_iff_left (mem_discBundle.1 v.2)

/-- Two frame vectors over the same base point are equal only if their coordinates are. -/
private theorem eq_of_mk_cellFrame_eq {n : ℕ} (j : cell (univ : Set B) n)
    {y y' : closedBall (0 : Fin n → ℝ) 1} {w w' : EuclideanSpace ℝ (Fin (finrank ℝ F))}
    (hyy' : (y : Fin n → ℝ) = y')
    (H : TotalSpace.mk' F (map n j y) (cellFrame (E := E) j y w) =
      TotalSpace.mk' F (map n j y') (cellFrame j y' w')) : w = w' := by
  obtain rfl : y = y' := Subtype.ext hyy'
  exact (cellFrame j y).injective (TotalSpace.mk_inj.1 H)

private theorem injOn_discCellFun {n m : ℕ} (j : cell (univ : Set B) n)
    (h : n + finrank ℝ F = m) : InjOn (discCellFun (E := E) j h) (ball 0 1) := by
  intro x hx x' hx' hxx'
  have hx₁ := (Fin.mem_ball_iff_appendIsometryOfEq_symm h).1 hx
  have hx₁' := (Fin.mem_ball_iff_appendIsometryOfEq_symm h).1 hx'
  have hv := congrArg Subtype.val hxx'
  rw [coe_discCellFun_of_mem j h (ball_subset_closedBall hx) (ball_subset_closedBall hx₁.1),
    coe_discCellFun_of_mem j h (ball_subset_closedBall hx') (ball_subset_closedBall hx₁'.1)] at hv
  have hy : (splitIso h x).1 = (splitIso h x').1 :=
    (map n j).injOn (by rw [source_eq]; exact hx₁.1) (by rw [source_eq]; exact hx₁'.1)
      (congrArg TotalSpace.proj hv)
  exact (splitIso h).injective (Prod.ext hy ((ballCoord _).injective (eq_of_mk_cellFrame_eq j
    (y := ⟨_, ball_subset_closedBall hx₁.1⟩) (y' := ⟨_, ball_subset_closedBall hx₁'.1⟩) hy hv)))

variable (F) in
/-- The cells of `D(E)` in dimension `m`: the cells of `B` of dimension `n` with `n + r = m`, `r`
the rank of `E`. It is reducible so that the cells of `D(E)` unfold to it by instance-transparency
unification, as `rw` and `simp` need. -/
@[reducible] private def DiscBundleCell (m : ℕ) : Type u :=
  {c : Σ n, cell (univ : Set B) n // c.1 + finrank ℝ F = m}

/-- The characteristic map of a cell of `D(E)`, as a partial equivalence with source the open unit
ball. -/
private def discCellMap {m : ℕ} (c : DiscBundleCell (A := A) F m) :
    PartialEquiv (Fin m → ℝ) (discBundle F E) :=
  Set.InjOn.toPartialEquiv (discCellFun c.1.2 c.2) (ball 0 1) (injOn_discCellFun c.1.2 c.2)

private theorem coe_discCellMap {m : ℕ} (c : DiscBundleCell (A := A) F m) :
    ⇑(discCellMap (E := E) c) = discCellFun c.1.2 c.2 :=
  (rfl)

omit [FiniteDimensional ℝ F] in
private theorem eventually_isEmpty_discBundleCell [RelCWComplex.Finite (univ : Set B)] :
    ∀ᶠ m in Filter.atTop, IsEmpty (DiscBundleCell (A := A) F m) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (RelCWComplex.FiniteDimensional.eventually_isEmpty_cell (C := (univ : Set B)) (D := A))
  refine Filter.eventually_atTop.2 ⟨N + finrank ℝ F, fun m hm ↦ ⟨fun c ↦ ?_⟩⟩
  have := c.2
  exact (hN c.1.1 (by omega)).false c.1.2

omit [FiniteDimensional ℝ F] in
private theorem finite_discBundleCell [RelCWComplex.Finite (univ : Set B)] (m : ℕ) :
    _root_.Finite (DiscBundleCell (A := A) F m) :=
  have := RelCWComplex.finite_cells_of_finite (C := (univ : Set B))
  Subtype.finite

variable (F E A) in
/-- The base `S(E) ∪ D(E)|_A` of the relative CW structure on the disc bundle: the vectors of norm
one together with the vectors over `A`. -/
private abbrev discBundleBase : Set (discBundle F E) :=
  {v | (v : TotalSpace F E) ∈ sphereBundle F E ∨ (v : TotalSpace F E).proj ∈ A}

variable [T2Space B]

private theorem continuousOn_symm_discCellMap {m : ℕ} (c : DiscBundleCell (A := A) F m) :
    ContinuousOn (discCellMap (E := E) c).symm (discCellMap (E := E) c).target := by
  refine (continuousOn_discCellFun c.1.2 c.2).continuousOn_invFunOn_image_of_isCompact
    (isCompact_closedBall 0 1) ball_subset_closedBall (injOn_discCellFun c.1.2 c.2) ?_
  rw [closedBall_sdiff_ball, image_sphere_discCellFun, image_ball_discCellFun]
  refine Set.disjoint_left.2 fun v hv hv' ↦ ?_
  rcases hv with hv | ⟨-, hv⟩
  · exact ((disjoint_skeletonLT_openCell le_rfl).mono_left
      (cellFrontier_subset_skeletonLT _ _)).notMem_of_mem_left hv hv'.1
  · exact hv'.2.ne hv

omit [T2Space B] in
private theorem pairwiseDisjoint_discCellMap :
    (univ : Set (Σ m, DiscBundleCell (A := A) F m)).PairwiseDisjoint
      fun c ↦ discCellMap (E := E) c.2 '' ball 0 1 := by
  rintro ⟨m, ⟨⟨n, j⟩, h⟩⟩ - ⟨m', ⟨⟨n', j'⟩, h'⟩⟩ - hne
  simp only [Function.onFun, coe_discCellMap, image_ball_discCellFun]
  refine Set.disjoint_left.2 fun v hv hv' ↦ hne ?_
  obtain ⟨rfl, hjj'⟩ := Sigma.mk.inj_iff.1
    (eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨_, hv.1, hv'.1⟩))
  obtain rfl := eq_of_heq hjj'
  subst h h'
  rfl

omit [T2Space B] in
private theorem disjoint_discCellMap_discBundleBase {m : ℕ} (c : DiscBundleCell (A := A) F m) :
    Disjoint (discCellMap (E := E) c '' ball 0 1) (discBundleBase F E A) := by
  rw [coe_discCellMap, image_ball_discCellFun]
  refine Set.disjoint_left.2 fun v hv hv' ↦ ?_
  rcases hv' with hv' | hv'
  · exact hv.2.ne (mem_sphereBundle.1 hv')
  · exact (disjointBase _ _).notMem_of_mem_left hv.1 hv'

omit [T2Space B] in
/-- The frontier of a cell of `D(E)` lies in the base and in closed cells of lower dimension. -/
private theorem mapsTo_discCellMap {m : ℕ} (c : DiscBundleCell (A := A) F m) :
    MapsTo (discCellMap (E := E) c) (sphere 0 1) (discBundleBase F E A ∪
      ⋃ (m' < m) (c' : DiscBundleCell (A := A) F m'), discCellMap c' '' closedBall 0 1) := by
  obtain ⟨⟨n, j⟩, h⟩ := c
  intro x hx
  have hv : discCellFun (E := E) j h x ∈ discCellFun j h '' sphere 0 1 :=
    mem_image_of_mem _ hx
  rw [image_sphere_discCellFun] at hv
  rcases hv with hv | ⟨-, hv⟩
  · obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n j
    rcases hI hv with hA | hcell
    · exact Or.inl (Or.inr hA)
    obtain ⟨n', hn', j', -, hj'⟩ :
        ∃ n' < n, ∃ j' ∈ I n', (discCellFun (E := E) j h x : TotalSpace F E).proj ∈
          closedCell n' j' := by
      simpa using hcell
    refine Or.inr (mem_iUnion₂.2 ⟨n' + finrank ℝ F, h ▸ Nat.add_lt_add_right hn' _,
      mem_iUnion.2 ⟨⟨⟨n', j'⟩, rfl⟩, ?_⟩⟩)
    rw [coe_discCellMap, image_closedBall_discCellFun]
    exact hj'
  · exact Or.inl (Or.inl (mem_sphereBundle.2 hv))

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, InnerProductSpace ℝ (E b)]
  [VectorBundle ℝ F E] [T2Space B] in
private theorem isClosed_discBundleBase : IsClosed (discBundleBase F E A) :=
  ((isClosed_sphereBundle F E ContinuousFiberNorm.continuous_norm).preimage
    continuous_subtype_val).union ((isClosedBase (univ : Set B)).preimage
    ((FiberBundle.continuous_proj F E).comp continuous_subtype_val))

omit [T2Space B] in
/-- Every vector of `D(E)` lies in the base or in the closed cell over a cell of `B` containing its
base point. -/
private theorem discBundleBase_union_iUnion_image_discCellMap :
    discBundleBase F E A ∪
      ⋃ (m : ℕ) (c : DiscBundleCell (A := A) F m), discCellMap c '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun v ↦ ?_
  have hb : (v : TotalSpace F E).proj ∈ A ∪ ⋃ (n : ℕ) (j : cell (univ : Set B) n),
      closedCell n j := by
    rw [RelCWComplex.union]
    exact mem_univ _
  rcases hb with hA | hcell
  · exact Or.inl (Or.inr hA)
  obtain ⟨n, j, hj⟩ := mem_iUnion₂.1 hcell
  refine Or.inr (mem_iUnion₂.2 ⟨n + finrank ℝ F, ⟨⟨n, j⟩, rfl⟩, ?_⟩)
  rw [coe_discCellMap, image_closedBall_discCellFun]
  exact hj

variable (F E A) in
/-- **The disc bundle of a vector bundle over a finite CW complex is a relative CW complex.** Let
`E → B` be a real vector bundle of finite rank `r` with continuous fibre norm, over a Hausdorff
space `B` which is a finite CW complex relative to its base `A`. Then the unit disc bundle
`D(E)`, as a space, is a finite CW complex relative to `S(E) ∪ D(E)|_A`, the unit sphere bundle
together with the part of the disc bundle over `A`. Its `(n + r)`-cells are the `n`-cells of `B`
(`TauCeti.discBundleRelCWComplexCellAddRankEquiv`), it has no cells of dimension below `r`, and
the closed cell over a cell of `B` is the disc bundle over its closed cell
(`TauCeti.closedCell_discBundleRelCWComplex`).

The characteristic map of the cell over the `n`-cell `j` with characteristic map `φ` sends a point
with base coordinates `y` and fibre coordinates `z` to the vector `L y (ρ z)` over `φ y`, where
`L` is an orthonormal frame of `E` along `φ` and `ρ` the radial homeomorphism of the sup-norm unit
ball of `ℝʳ` onto the Euclidean one. No orientation of `E` is needed.

It is not an instance: the base of a relative CW complex is an `outParam`, and the
characteristic maps depend on a choice of frames. -/
@[instance_reducible]
def discBundleRelCWComplex [RelCWComplex.Finite (univ : Set B)] :
    RelCWComplex (univ : Set (discBundle F E))
      {v | (v : TotalSpace F E) ∈ sphereBundle F E ∨ (v : TotalSpace F E).proj ∈ A} :=
  RelCWComplex.mkFinite _ _ (DiscBundleCell (A := A) F) (fun _ c ↦ discCellMap c)
    eventually_isEmpty_discBundleCell finite_discBundleCell (fun _ _ ↦ rfl)
    (fun _ c ↦ continuousOn_discCellFun c.1.2 c.2) (fun _ ↦ continuousOn_symm_discCellMap)
    pairwiseDisjoint_discCellMap (fun _ ↦ disjoint_discCellMap_discBundleBase)
    (fun _ ↦ mapsTo_discCellMap) isClosed_discBundleBase
    discBundleBase_union_iUnion_image_discCellMap

variable [RelCWComplex.Finite (univ : Set B)]

/-- The structure `TauCeti.discBundleRelCWComplex` is a finite relative CW complex. -/
instance finite_discBundleRelCWComplex :
    @RelCWComplex.Finite (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) :=
  letI := discBundleRelCWComplex F E A
  { eventually_isEmpty_cell := eventually_isEmpty_discBundleCell (F := F)
    finite_cell := finite_discBundleCell (F := F) }

variable (F E A) in
/-- The `m`-cells of the disc bundle `D(E)` are the cells of `B` of dimension `n` with
`n + r = m`, `r` the rank of `E`. -/
def discBundleRelCWComplexCellEquiv (m : ℕ) :
    @cell (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m ≃
      {c : Σ n, cell (univ : Set B) n // c.1 + finrank ℝ F = m} :=
  Equiv.refl _

variable (F E A) in
/-- The `(n + r)`-cells of the disc bundle `D(E)` are the `n`-cells of `B`, `r` the rank of `E`. -/
def discBundleRelCWComplexCellAddRankEquiv (n : ℕ) :
    @cell (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) (n + finrank ℝ F) ≃
      cell (univ : Set B) n :=
  ((discBundleRelCWComplexCellEquiv F E A _).trans
    (Equiv.subtypeEquivRight fun _ ↦ Nat.add_right_cancel_iff)).trans (Equiv.sigmaSubtype n)

/-- The cell of the disc bundle `D(E)` over the `n`-cell `j` of `B` lies over `j`. -/
@[simp]
theorem discBundleRelCWComplexCellEquiv_cellAddRankEquiv_symm (n : ℕ)
    (j : cell (univ : Set B) n) :
    (discBundleRelCWComplexCellEquiv F E A _
      ((discBundleRelCWComplexCellAddRankEquiv F E A n).symm j)).1 = ⟨n, j⟩ :=
  (rfl)

/-- An `(n + r)`-cell of the disc bundle `D(E)` lies over the `n`-cell of `B` that it corresponds
to under `TauCeti.discBundleRelCWComplexCellAddRankEquiv`. -/
theorem discBundleRelCWComplexCellEquiv_apply_fst (n : ℕ)
    (c : @cell (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) (n + finrank ℝ F)) :
    (discBundleRelCWComplexCellEquiv F E A _ c).1 =
      ⟨n, discBundleRelCWComplexCellAddRankEquiv F E A n c⟩ := by
  rw [← discBundleRelCWComplexCellEquiv_cellAddRankEquiv_symm (F := F) (E := E) (A := A) n
    (discBundleRelCWComplexCellAddRankEquiv F E A n c), Equiv.symm_apply_apply]

/-- The disc bundle `D(E)` has no cells of dimension less than the rank of `E`. -/
theorem isEmpty_cell_discBundleRelCWComplex_of_lt {m : ℕ} (hm : m < finrank ℝ F) :
    IsEmpty (@cell (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m) :=
  ⟨fun c ↦ by
    have := (discBundleRelCWComplexCellEquiv F E A m c).2
    omega⟩

variable {m : ℕ} (c : @cell (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m)

/-- The characteristic maps of the cells of the disc bundle `D(E)` cover the characteristic maps
of the corresponding cells of `B`: on the closed unit ball, the base point of the image of a point
is the image of its first `n` coordinates. -/
theorem proj_map_discBundleRelCWComplex {x : Fin m → ℝ} (hx : x ∈ closedBall 0 1) :
    ((@map (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m c x : discBundle F E) :
        TotalSpace F E).proj =
      map _ (discBundleRelCWComplexCellEquiv F E A m c).1.2
        ((Fin.appendIsometryOfEq (discBundleRelCWComplexCellEquiv F E A m c).2).symm x).1 := by
  obtain ⟨⟨n, j⟩, h⟩ := c
  have hy := ((Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).1 hx).1
  exact congrArg TotalSpace.proj (coe_discCellFun_of_mem (E := E) j h hx hy)

/-- On the closed unit ball, the fibre vector of the image of a point under a characteristic map
of the disc bundle `D(E)` has the norm of the radial image `ρ z` of its last `r` coordinates `z`,
where `ρ` is the radial homeomorphism of the sup-norm and Euclidean unit balls of `ℝʳ`. -/
theorem norm_map_discBundleRelCWComplex {x : Fin m → ℝ} (hx : x ∈ closedBall 0 1) :
    ‖((@map (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m c x : discBundle F E) :
        TotalSpace F E).2‖ =
      ‖(EuclideanSpace.equiv (Fin (finrank ℝ F)) ℝ).symm.unitBallHomeomorph
        ((Fin.appendIsometryOfEq (discBundleRelCWComplexCellEquiv F E A m c).2).symm x).2‖ := by
  obtain ⟨⟨n, j⟩, h⟩ := c
  have hy := ((Fin.mem_closedBall_iff_appendIsometryOfEq_symm h).1 hx).1
  have hv := coe_discCellFun_of_mem (E := E) j h hx hy
  rw [← LinearIsometryEquiv.norm_map (cellFrame (F := F) (E := E) j ⟨_, hy⟩)]
  exact congrArg (fun v : TotalSpace F E ↦ ‖v.2‖) hv

/-- The characteristic map of the cell of the disc bundle `D(E)` over the `n`-cell `j` of `B`, with
characteristic map `φ`, is fibrewise an orthonormal frame applied to the radial image of the fibre
coordinates: there is an orthonormal frame `L y : ℝʳ ≃ₗᵢ E (φ y)` along `φ`, depending
continuously on `y`, such that the point of the closed unit ball with base coordinates `y` and fibre
coordinates `z` goes to the vector `L y (ρ z)` over `φ y`, where `ρ` is the radial homeomorphism of
the sup-norm and Euclidean unit balls of `ℝʳ`. -/
theorem exists_linearIsometryEquiv_map_discBundleRelCWComplex {n : ℕ}
    (j : cell (univ : Set B) n) (h : n + finrank ℝ F = m) :
    ∃ L : ∀ y : closedBall (0 : Fin n → ℝ) 1,
        EuclideanSpace ℝ (Fin (finrank ℝ F)) ≃ₗᵢ[ℝ] E (map n j y),
      (Continuous fun p : closedBall (0 : Fin n → ℝ) 1 × EuclideanSpace ℝ (Fin (finrank ℝ F)) ↦
        TotalSpace.mk' F (map n j p.1) (L p.1 p.2)) ∧
      ∀ (y : Fin n → ℝ) (hy : y ∈ closedBall 0 1) (z : Fin (finrank ℝ F) → ℝ),
        z ∈ closedBall 0 1 →
          ((@map (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m
              ((discBundleRelCWComplexCellEquiv F E A m).symm ⟨⟨n, j⟩, h⟩)
              (Fin.appendIsometryOfEq h (y, z)) : discBundle F E) : TotalSpace F E) =
            TotalSpace.mk' F (map n j y) (L ⟨y, hy⟩
              ((EuclideanSpace.equiv (Fin (finrank ℝ F)) ℝ).symm.unitBallHomeomorph z)) :=
  ⟨cellFrame j, continuous_cellFrame j,
    fun _ hy _ hz ↦ coe_discCellFun_appendIsometryOfEq j h hy hz⟩

/-- The open cell of the disc bundle `D(E)` over a cell of `B` consists of the vectors of norm
less than one over its open cell. -/
@[simp]
theorem openCell_discBundleRelCWComplex :
    @openCell (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m c =
      {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell _ (discBundleRelCWComplexCellEquiv F E A m c).1.2 ∧
          ‖(v : TotalSpace F E).2‖ < 1} :=
  image_ball_discCellFun _ _

/-- The closed cell of the disc bundle `D(E)` over a cell of `B` is the disc bundle over its
closed cell. -/
@[simp]
theorem closedCell_discBundleRelCWComplex :
    @closedCell (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m c =
      {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ closedCell _ (discBundleRelCWComplexCellEquiv F E A m c).1.2} :=
  image_closedBall_discCellFun _ _

/-- The frontier of the cell of the disc bundle `D(E)` over a cell of `B` is the disc bundle over
the frontier of that cell together with the sphere bundle over its closed cell. -/
@[simp]
theorem cellFrontier_discBundleRelCWComplex :
    @cellFrontier (discBundle F E) _ univ _ (discBundleRelCWComplex F E A) m c =
      {v : discBundle F E | (v : TotalSpace F E).proj ∈
          cellFrontier _ (discBundleRelCWComplexCellEquiv F E A m c).1.2} ∪
        {v : discBundle F E | (v : TotalSpace F E).proj ∈
          closedCell _ (discBundleRelCWComplexCellEquiv F E A m c).1.2 ∧
            ‖(v : TotalSpace F E).2‖ = 1} :=
  image_sphere_discCellFun _ _

end CW

end TauCeti
