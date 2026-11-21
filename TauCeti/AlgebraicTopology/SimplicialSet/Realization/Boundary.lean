/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.CWComplex.Abstract.Basic
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.ConvexSpace.CellBall
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Geometric realization of simplex boundaries

This file identifies the geometric realization of each simplex boundary inclusion
`|∂Δ[n].ι| : |∂Δ[n]| ⟶ |Δ[n]|` with the standard sphere-to-disk inclusion
`TopCat.diskBoundaryInclusion n : ∂𝔻 n ⟶ 𝔻 n` in `Arrow TopCat`.

Because `SSet.toTop` is a left adjoint, it preserves the multicoequalizer presentation
`SSet.boundary.isColimit` of `∂Δ[n + 1]` by its codimension-one faces. From this presentation we
deduce that `|∂Δ[n]|` is compact, that `|∂Δ[n].ι|` is a closed embedding, and that under
`SimplexCategory.toTopHomeo ⦋n⦌` its image is precisely the topological boundary of the ordered
standard `n`-simplex, i.e. the points with a vanishing barycentric weight. Composing with
`TauCeti.standardCellBallToOrderedSimplex` and `TauCeti.diskHomeomorphClosedBall` identifies the
realized boundary inclusion with `TopCat.diskBoundaryInclusion n`
(`SSet.toTopBoundaryInclusionArrowIso`).

## Main definitions and results

* `SSet.toTop_map_yonedaEquiv_symm_toTopHomeo_symm`: on the realization of a standard simplex,
  realizing the classifying map `yonedaEquiv.symm σ : Δ[n] ⟶ X` sends a barycentric point `w` to
  `SSet.toTopObjMk σ w`.
* `SSet.isClosedEmbedding_toTop_map_boundary_ι`: `|∂Δ[n].ι|` is a closed embedding.
* `SSet.range_toTopHomeo_comp_toTop_map_boundary_ι`: the image of `|∂Δ[n].ι|` in
  `StdSimplex ℝ (Fin (n + 1))` consists of the points with a vanishing barycentric weight.
* `SSet.toTopStdSimplexIsoDisk`: the canonical isomorphism `|Δ[n]| ≅ 𝔻 n` in `TopCat`.
* `SSet.toTopBoundaryIsoDiskBoundary`: the canonical isomorphism `|∂Δ[n]| ≅ ∂𝔻 n` in `TopCat`.
* `SSet.toTopBoundaryInclusionArrowIso`: the arrow isomorphism
  `Arrow.mk |∂Δ[n].ι| ≅ Arrow.mk (TopCat.diskBoundaryInclusion n)`.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial Convexity Metric

universe u

namespace SSet

/-- Realizing the classifying map `yonedaEquiv.symm σ : Δ[n] ⟶ X` of an `n`-simplex `σ` sends
the point with barycentric coordinates `w` to `SSet.toTopObjMk σ w`. -/
lemma toTop_map_yonedaEquiv_symm_toTopHomeo_symm {X : SSet.{u}} {n : ℕ} (σ : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (yonedaEquiv.symm σ) (⦋n⦌.toTopHomeo.symm w) = toTopObjMk σ w := by
  rw [toTopObjMk_def]
  have hunit := sSetTopAdj_unit_app_app_down X (op ⦋n⦌) σ
  exact (ConcreteCategory.congr_hom hunit (ULift.up w)).symm

/-- The geometric realization of a standard simplex is compact. -/
instance compactSpace_toTop_stdSimplex (n : ℕ) : CompactSpace |(Δ[n] : SSet.{u})| :=
  (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm.compactSpace

/-- The geometric realization of a standard simplex is Hausdorff. -/
private instance t2Space_toTop_stdSimplex (n : ℕ) : T2Space |(Δ[n] : SSet.{u})| :=
  (SimplexCategory.toTopHomeo.{u} ⦋n⦌).isEmbedding.t2Space

/-- The geometric realization of `∂Δ[0]` is empty. -/
instance isEmpty_toTop_boundary_zero : IsEmpty |(∂Δ[0] : SSet.{u})| := by
  have hinit : IsInitial (∂Δ[0] : SSet.{u}) :=
    Subcomplex.isInitialBot.ofIso (Subcomplex.eqToIso boundary_zero).symm
  have f : |(∂Δ[0] : SSet.{u})| ⟶ TopCat.of PEmpty.{u + 1} :=
    (sSetTopAdj.homEquiv _ _).symm (hinit.to _)
  exact ⟨fun x ↦ PEmpty.elim (f x)⟩

/-- Every point of `|∂Δ[n + 1]|` lies in the image of one of the codimension-one faces
`|boundary.ι j| : |Δ[n]| ⟶ |∂Δ[n + 1]|`. -/
lemma exists_toTop_map_boundary_ι {n : ℕ} (x : |(∂Δ[n + 1] : SSet.{u})|) :
    ∃ (j : Fin (n + 2)) (z : |(Δ[n] : SSet.{u})|),
      toTop.map (boundary.ι j) z = x := by
  let c := (boundary.multicoequalizerDiagram.{u} (n + 1)).multicofork.toLinearOrder.map
    Subcomplex.toSSetFunctor
  have hc := isColimitOfPreserves (toTop ⋙ forget TopCat) (boundary.isColimit.{u} (n + 1))
  obtain ⟨s, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  have hright (j : Fin (n + 2)) (y' : |(stdSimplex.face.{u} {j}ᶜ : SSet.{u})|)
      (hy' : toTop.map (boundary.faceι j) y' = x) :
      ∃ (j : Fin (n + 2)) (z : |(Δ[n] : SSet.{u})|), toTop.map (boundary.ι j) z = x := by
    refine ⟨j, toTop.map (stdSimplex.faceSingletonComplIso j).inv y', ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      boundary.faceSingletonComplIso_inv_ι]
    exact hy'
  cases s with
  | right j => exact hright j y hy
  | left a =>
    have hw := ((toTop ⋙ forget TopCat).mapCocone c).w (WalkingMultispan.Hom.fst a)
    have hval := congrArg (fun g ↦ g y) hw
    exact hright a.1.1 _ (hval.trans hy)

/-- The geometric realization of `∂Δ[n]` is compact. -/
instance compactSpace_toTop_boundary (n : ℕ) : CompactSpace |(∂Δ[n] : SSet.{u})| := by
  cases n with
  | zero => infer_instance
  | succ m =>
    let f : Fin (m + 2) × |(Δ[m] : SSet.{u})| → |(∂Δ[m + 1] : SSet.{u})| :=
      fun p ↦ toTop.map (boundary.ι p.1) p.2
    have hf_cont : Continuous f := by
      rw [continuous_iff_continuousAt]
      intro ⟨j, z⟩
      have hj : ({j} : Set (Fin (m + 2))) ×ˢ (Set.univ : Set |(Δ[m] : SSet.{u})|) ∈ nhds (j, z) :=
        IsOpen.mem_nhds ((isOpen_discrete _).prod isOpen_univ) ⟨rfl, trivial⟩
      refine ((toTop.map (boundary.ι j)).hom.continuous.comp continuous_snd).continuousAt.congr ?_
      filter_upwards [hj] with ⟨k, w⟩ ⟨hk, _⟩
      cases hk
      rfl
    have hf_surj : Function.Surjective f := fun x ↦ by
      obtain ⟨j, z, rfl⟩ := exists_toTop_map_boundary_ι x
      exact ⟨(j, z), rfl⟩
    refine ⟨?_⟩
    rw [← hf_surj.range_eq, ← Set.image_univ]
    exact isCompact_univ.image hf_cont

private lemma toTopHomeo_toTop_map_δ {m : ℕ} (j : Fin (m + 2)) (z : |(Δ[m] : SSet.{u})|) :
    ⦋m + 1⦌.toTopHomeo (toTop.map (stdSimplex.δ j) z) =
      (⦋m⦌.toTopHomeo z).map j.succAbove :=
  SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ j) z

private lemma toTop_map_boundary_ι_eq_of_lt {m : ℕ} {j k : Fin (m + 2)} (hjk : j < k)
    {z₁ z₂ : |(Δ[m] : SSet.{u})|}
    (h : (⦋m⦌.toTopHomeo z₁).map j.succAbove = (⦋m⦌.toTopHomeo z₂).map k.succAbove) :
    toTop.map (boundary.ι j) z₁ = toTop.map (boundary.ι k) z₂ := by
  cases m with
  | zero =>
    set p : StdSimplex ℝ (Fin 2) := (⦋0⦌.toTopHomeo z₁).map j.succAbove
    have hj : p.weights j = 0 := StdSimplex.weights_map_succAbove_self j _
    have hk : p.weights k = 0 := h ▸ StdSimplex.weights_map_succAbove_self k _
    have htot := StdSimplex.total_of_fintype p
    rw [Fin.sum_univ_two] at htot
    fin_cases j <;> fin_cases k
    · exact absurd hjk (lt_irrefl _)
    · dsimp at hj hk
      linarith
    · exact absurd hjk (by decide)
    · exact absurd hjk (lt_irrefl _)
  | succ r =>
    obtain ⟨w, hw₁, hw₂⟩ := StdSimplex.exists_map_succAbove_of_map_succAbove_eq hjk h
    have hz₁ : z₁ = toTop.map (stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)))
        (⦋r⦌.toTopHomeo.symm w) := by
      apply ⦋r + 1⦌.toTopHomeo.injective
      rw [hw₁, toTopHomeo_toTop_map_δ, Homeomorph.apply_symm_apply]
    have hz₂ : z₂ = toTop.map (stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)))
        (⦋r⦌.toTopHomeo.symm w) := by
      apply ⦋r + 1⦌.toTopHomeo.injective
      rw [hw₂, toTopHomeo_toTop_map_δ, Homeomorph.apply_symm_apply]
    rw [hz₁, hz₂, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    have hcompat := (boundary.IsCompatible.of_hom (𝟙 (∂Δ[r + 2] : SSet.{u}))).δ_pred_comp j k hjk
    simp only [Category.comp_id] at hcompat
    rw [hcompat]

/-- The geometric realization of the boundary inclusion `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]` is injective. -/
lemma toTop_map_boundary_ι_injective (n : ℕ) :
    Function.Injective (toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) := by
  cases n with
  | zero => exact Function.injective_of_subsingleton _
  | succ m =>
    intro x₁ x₂ hx
    obtain ⟨j, z₁, rfl⟩ := exists_toTop_map_boundary_ι x₁
    obtain ⟨k, z₂, rfl⟩ := exists_toTop_map_boundary_ι x₂
    have hmap : (⦋m⦌.toTopHomeo z₁).map j.succAbove = (⦋m⦌.toTopHomeo z₂).map k.succAbove := by
      have h1 := congrArg (⦋m + 1⦌.toTopHomeo) hx
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, boundary.ι_ι] at h1
      simpa only [toTopHomeo_toTop_map_δ] using h1
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact toTop_map_boundary_ι_eq_of_lt hjk hmap
    · have hz : z₁ = z₂ := ⦋m⦌.toTopHomeo.injective
        (StdSimplex.map_injective Fin.succAbove_right_injective hmap)
      rw [hz]
    · exact (toTop_map_boundary_ι_eq_of_lt hkj hmap.symm).symm

/-- The geometric realization of the boundary inclusion `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]` is a closed
embedding. -/
theorem isClosedEmbedding_toTop_map_boundary_ι (n : ℕ) :
    Topology.IsClosedEmbedding (toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) :=
  (toTop.map ∂Δ[n].ι).hom.continuous.isClosedEmbedding (toTop_map_boundary_ι_injective n)

/-- Under `SimplexCategory.toTopHomeo ⦋n⦌`, the image of `|∂Δ[n].ι|` consists of the points of
the ordered standard `n`-simplex with a vanishing barycentric weight. -/
lemma range_toTopHomeo_comp_toTop_map_boundary_ι (n : ℕ) :
    Set.range (⦋n⦌.toTopHomeo ∘ toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) =
      Set.ofPred fun y : StdSimplex ℝ (Fin (n + 1)) ↦ ∃ i, y.weights i = 0 := by
  cases n with
  | zero =>
    ext y
    simp only [Set.mem_range, Function.comp_apply, Set.mem_ofPred_eq,
      IsEmpty.exists_iff, false_iff, not_exists]
    intro i
    fin_cases i
    have h := StdSimplex.total_of_fintype y
    rw [Fin.sum_univ_one] at h
    dsimp
    linarith
  | succ m =>
    ext y
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨j, z, rfl⟩ := exists_toTop_map_boundary_ι x
      refine ⟨j, ?_⟩
      simp only [Function.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        boundary.ι_ι, toTopHomeo_toTop_map_δ]
      exact StdSimplex.weights_map_succAbove_self j _
    · rintro ⟨j, hj⟩
      obtain ⟨w, rfl⟩ := (StdSimplex.mem_range_map_succAbove_iff j y).2 hj
      refine ⟨toTop.map (boundary.ι j) (⦋m⦌.toTopHomeo.symm w), ?_⟩
      simp only [Function.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        boundary.ι_ι, toTopHomeo_toTop_map_δ, Homeomorph.apply_symm_apply]

/-- The canonical isomorphism `|Δ[n]| ≅ 𝔻 n` in `TopCat`, obtained by composing
`SimplexCategory.toTopHomeo ⦋n⦌` with the inverses of `TauCeti.standardCellBallToOrderedSimplex n`
and `TauCeti.diskHomeomorphClosedBall n`. -/
def toTopStdSimplexIsoDisk (n : ℕ) : |(Δ[n] : SSet.{u})| ≅ TopCat.disk.{u} n :=
  TopCat.isoOfHomeo <|
    (SimplexCategory.toTopHomeo.{u} ⦋n⦌).trans <|
      (TauCeti.standardCellBallToOrderedSimplex n).symm.trans
        (TauCeti.diskHomeomorphClosedBall.{u} n).symm

/-- Reading the inverse of `toTopStdSimplexIsoDisk n` through `TauCeti.diskHomeomorphClosedBall n`
cancels the ball-to-disk comparison and recovers `standardCellBallToOrderedSimplex n`. -/
@[simp]
lemma toTopStdSimplexIsoDisk_inv_diskHomeomorphClosedBall_symm (n : ℕ)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    (toTopStdSimplexIsoDisk.{u} n).inv ((TauCeti.diskHomeomorphClosedBall.{u} n).symm x) =
      ⦋n⦌.toTopHomeo.symm (TauCeti.standardCellBallToOrderedSimplex n x) := by
  simp [toTopStdSimplexIsoDisk]

private lemma mem_range_toTopBoundary_toDisk_iff (n : ℕ) (z : TopCat.disk.{u} n) :
    z ∈ Set.range (toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫
        (toTopStdSimplexIsoDisk.{u} n).hom) ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} n) := by
  rw [← TauCeti.norm_diskHomeomorphClosedBall_eq_one_iff,
    ← TauCeti.exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff]
  have hrange :
      TauCeti.standardCellBallToOrderedSimplex n (TauCeti.diskHomeomorphClosedBall.{u} n z) ∈
        Set.range (⦋n⦌.toTopHomeo ∘ toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) ↔
      ∃ i, (TauCeti.standardCellBallToOrderedSimplex n
        (TauCeti.diskHomeomorphClosedBall.{u} n z)).weights i = 0 := by
    rw [range_toTopHomeo_comp_toTop_map_boundary_ι]
    rfl
  rw [← hrange]
  simp only [Set.mem_range, Function.comp_apply, ConcreteCategory.comp_apply]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hx]
    simp [toTopStdSimplexIsoDisk]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply (TauCeti.diskHomeomorphClosedBall.{u} n).injective
    apply (TauCeti.standardCellBallToOrderedSimplex n).injective
    simpa [toTopStdSimplexIsoDisk] using hx

/-- The canonical isomorphism `|∂Δ[n]| ≅ ∂𝔻 n` in `TopCat` compatible with
`toTopStdSimplexIsoDisk n`. -/
def toTopBoundaryIsoDiskBoundary (n : ℕ) :
    |(∂Δ[n] : SSet.{u})| ≅ TopCat.diskBoundary.{u} n := by
  have hcl := TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion.{u} n
  have hex : ∀ x : |(∂Δ[n] : SSet.{u})|, ∃ s : TopCat.diskBoundary.{u} n,
      TopCat.diskBoundaryInclusion.{u} n s =
        (toTopStdSimplexIsoDisk.{u} n).hom (toTop.map ∂Δ[n].ι x) :=
    fun x ↦ (mem_range_toTopBoundary_toDisk_iff n _).1 ⟨x, rfl⟩
  choose f hf using hex
  have hf_cont : Continuous f := by
    rw [hcl.isInducing.continuous_iff]
    have heq : (TopCat.diskBoundaryInclusion.{u} n) ∘ f =
        (toTopStdSimplexIsoDisk.{u} n).hom ∘ toTop.map ∂Δ[n].ι := funext hf
    rw [heq]
    exact (toTopStdSimplexIsoDisk.{u} n).hom.hom.continuous.comp
      (toTop.map ∂Δ[n].ι).hom.continuous
  have hf_inj : Function.Injective f := fun x₁ x₂ h ↦ by
    have h1 : (toTopStdSimplexIsoDisk.{u} n).hom (toTop.map ∂Δ[n].ι x₁) =
        (toTopStdSimplexIsoDisk.{u} n).hom (toTop.map ∂Δ[n].ι x₂) := by
      rw [← hf x₁, ← hf x₂, h]
    exact toTop_map_boundary_ι_injective n
      ((TopCat.homeoOfIso (toTopStdSimplexIsoDisk.{u} n)).injective h1)
  have hf_surj : Function.Surjective f := fun s ↦ by
    obtain ⟨x, hx⟩ := (mem_range_toTopBoundary_toDisk_iff n
      (TopCat.diskBoundaryInclusion.{u} n s)).2 ⟨s, rfl⟩
    exact ⟨x, hcl.injective ((hf x).trans hx)⟩
  exact TopCat.isoOfHomeo
    (hf_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩))

/-- The boundary isomorphism `toTopBoundaryIsoDiskBoundary n` commutes with the boundary inclusions
into `|Δ[n]|` and `𝔻 n`. -/
@[reassoc]
lemma toTopBoundaryIsoDiskBoundary_hom_comp_diskBoundaryInclusion (n : ℕ) :
    (toTopBoundaryIsoDiskBoundary.{u} n).hom ≫ TopCat.diskBoundaryInclusion.{u} n =
      toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ (toTopStdSimplexIsoDisk.{u} n).hom := by
  ext x
  dsimp [toTopBoundaryIsoDiskBoundary]
  exact Classical.choose_spec
    ((mem_range_toTopBoundary_toDisk_iff.{u} n _).1 ⟨x, rfl⟩)

/-- The canonical isomorphism in `Arrow TopCat` identifying the realized simplex boundary inclusion
`|∂Δ[n].ι| : |∂Δ[n]| ⟶ |Δ[n]|` with the standard sphere-to-disk inclusion
`TopCat.diskBoundaryInclusion n : ∂𝔻 n ⟶ 𝔻 n`. -/
def toTopBoundaryInclusionArrowIso (n : ℕ) :
    Arrow.mk (toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) ≅
      Arrow.mk (TopCat.diskBoundaryInclusion.{u} n) :=
  Arrow.isoMk (toTopBoundaryIsoDiskBoundary.{u} n) (toTopStdSimplexIsoDisk.{u} n)
    (toTopBoundaryIsoDiskBoundary_hom_comp_diskBoundaryInclusion.{u} n)

@[simp]
lemma toTopBoundaryInclusionArrowIso_left (n : ℕ) :
    (toTopBoundaryInclusionArrowIso.{u} n).hom.left = (toTopBoundaryIsoDiskBoundary.{u} n).hom :=
  (rfl)

@[simp]
lemma toTopBoundaryInclusionArrowIso_right (n : ℕ) :
    (toTopBoundaryInclusionArrowIso.{u} n).hom.right = (toTopStdSimplexIsoDisk.{u} n).hom :=
  (rfl)

@[simp]
lemma toTopBoundaryInclusionArrowIso_inv_right (n : ℕ) :
    (toTopBoundaryInclusionArrowIso.{u} n).inv.right = (toTopStdSimplexIsoDisk.{u} n).inv :=
  (rfl)

end SSet
