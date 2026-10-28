/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CellAttachment
public import TauCeti.Topology.Category.TopCat.Pushout

/-!
# Negative disks and cell adjunctions in Morse charts

A normalized Morse chart embeds a closed disk in its negative coordinate plane. The function
has value `c - ‖u‖²` on this disk, and its intersection with the lower sublevel `f ≤ c - r²`
is precisely its boundary sphere. These are the characteristic and attaching maps for the
cell attachment across a nondegenerate critical level.

The main theorem `TauCeti.exists_sublevel_negativeDisk_attachment` identifies the topological
pushout of the attaching maps with the upper sublevel up to homotopy relative to the lower
sublevel. The comparison is induced by the actual disk maps, has a strict left inverse, and
allows simultaneous critical points of different indices, including index zero.

The construction uses `EuclideanSpace.sumComplEquivProd`, Mathlib's set-level pushout criterion
`CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'`, and the strong deformation
retraction `TauCeti.exists_sublevel_union_cells_deformation`. Closedness of the two structure
maps ensures that the set-level adjunction has the correct topology; compactness is needed for
the finite disk family, but not for the lower sublevel.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Theorem 3.2.
-/

public section

open Function Set Topology Metric
open scoped ContDiff Manifold

noncomputable section

namespace PartialDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}
  (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
    (EuclideanSpace ℝ (Fin n)) ∞) (k : ℕ) {r : ℝ}

variable (hball : closedBall 0 r ⊆ φ.target)
include hball

private theorem negativeCoord_mem_target
    (u : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r) :
    (EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).symm (u, 0) ∈ φ.target := by
  apply hball
  simpa only [mem_closedBall_zero_iff, EuclideanSpace.norm_sumComplEquivProd_symm_zero] using u.2

/-- The negative disk of a chart: insert zero in the positive coordinates and apply the inverse
chart. The radius is arbitrary provided the ambient closed ball lies in the chart target. -/
def negativeDiskMap : C(closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r, M) where
  toFun u := φ.toOpenPartialHomeomorph.symm
    ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).symm (u, 0))
  continuous_toFun := φ.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).symm.continuous.comp
      (continuous_subtype_val.prodMk continuous_const)) (negativeCoord_mem_target φ k hball)

/-- Evaluation of the negative-disk map in inverse-chart coordinates. -/
theorem negativeDiskMap_apply
    (u : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r) :
    φ.negativeDiskMap k hball u = φ.toOpenPartialHomeomorph.symm
      ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).symm (u, 0)) :=
  (rfl)

/-- The negative disk is contained in the chart source. -/
theorem negativeDiskMap_mem_source
    (u : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r) :
    φ.negativeDiskMap k hball u ∈ φ.source :=
  φ.toOpenPartialHomeomorph.map_target (negativeCoord_mem_target φ k hball u)

/-- Applying the chart recovers the inserted negative coordinates. -/
@[simp]
theorem apply_negativeDiskMap
    (u : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r) :
    φ (φ.negativeDiskMap k hball u) =
      (EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).symm (u, 0) :=
  φ.toOpenPartialHomeomorph.right_inv (negativeCoord_mem_target φ k hball u)

/-- A negative disk is parametrized injectively. -/
theorem injective_negativeDiskMap : Injective (φ.negativeDiskMap k hball) := by
  intro u v huv
  have h := congrArg φ huv
  simp only [apply_negativeDiskMap] at h
  exact Subtype.ext (congrArg Prod.fst
    ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).symm.injective h))

/-- The negative-disk parametrization is a closed embedding into a Hausdorff manifold. -/
theorem isClosedEmbedding_negativeDiskMap [T2Space M] :
    IsClosedEmbedding (φ.negativeDiskMap k hball) :=
  (φ.negativeDiskMap k hball).continuous.isClosedEmbedding (φ.injective_negativeDiskMap k hball)

/-- The image of the negative-disk map is the negative-coordinate disk in the chart source. -/
theorem range_negativeDiskMap (hr : 0 ≤ r) :
    range (φ.negativeDiskMap k hball) = φ.source ∩
      φ ⁻¹' {y | ‖y‖ ^ 2 ≤ r ^ 2 ∧ ∀ j : Fin n, k ≤ j.val → y j = 0} := by
  let e := EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨φ.negativeDiskMap_mem_source k hball u, ?_⟩
    rw [mem_preimage, mem_ofPred, apply_negativeDiskMap]
    constructor
    · rw [EuclideanSpace.norm_sumComplEquivProd_symm_zero]
      exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 u.2) 2
    · intro j hj
      simp [EuclideanSpace.sumComplEquivProd_symm_apply, not_lt.2 hj]
  · rintro ⟨hx, hxnorm, hxzero⟩
    have hz : (e (φ x)).2 = 0 := EuclideanSpace.snd_sumComplEquivProd_eq_zero_iff.2
      (fun j hj ↦ hxzero j (not_lt.1 hj))
    have hnorm := EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq
      (p := fun j : Fin n ↦ j.val < k) (φ x)
    have hu : ‖(e (φ x)).1‖ ≤ r := by
      rw [hz, norm_zero] at hnorm
      nlinarith [norm_nonneg (e (φ x)).1]
    let u : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r :=
      ⟨(e (φ x)).1, mem_closedBall_zero_iff.2 hu⟩
    refine ⟨u, ?_⟩
    have he : e.symm ((u : EuclideanSpace ℝ {j : Fin n // j.val < k}), 0) = φ x := by
      apply e.injective
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      exact Prod.ext rfl hz.symm
    rw [negativeDiskMap_apply, he]
    exact φ.toOpenPartialHomeomorph.left_inv hx

variable {f : M → ℝ} {c : ℝ}
  (hf : ∀ x ∈ φ.source, f x = c + ∑ j, (if j.val < k then -1 else 1) * φ x j ^ 2)
include hf

/-- The function on the negative disk is `c - ‖u‖²`. -/
theorem comp_negativeDiskMap
    (u : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r) :
    f (φ.negativeDiskMap k hball u) =
      c - ‖(u : EuclideanSpace ℝ {j : Fin n // j.val < k})‖ ^ 2 := by
  rw [hf _ (φ.negativeDiskMap_mem_source k hball u), apply_negativeDiskMap,
    EuclideanSpace.sum_ite_neg_one_mul_sq_eq]
  simp [sub_eq_add_neg]

/-- The negative disk meets the lower sublevel exactly on its boundary. This includes index zero,
where a positive-radius sphere in the zero-dimensional negative space is empty. -/
theorem negativeDiskMap_le_iff
    (u : closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k}) r) :
    f (φ.negativeDiskMap k hball u) ≤ c - r ^ 2 ↔
      ‖(u : EuclideanSpace ℝ {j : Fin n // j.val < k})‖ = r := by
  have hu : ‖(u : EuclideanSpace ℝ {j : Fin n // j.val < k})‖ ≤ r := mem_closedBall_zero_iff.1 u.2
  have hr : 0 ≤ r := (norm_nonneg _).trans hu
  rw [φ.comp_negativeDiskMap k hball hf]
  constructor
  · intro h
    nlinarith [norm_nonneg (u : EuclideanSpace ℝ {j : Fin n // j.val < k})]
  · rintro h
    rw [h]

end PartialDiffeomorph

universe u

namespace TauCeti

open CategoryTheory Limits

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type u} {n : ℕ} {f : M → ℝ} {c r : ℝ}

/-- Disjoint negative disks attached to a closed lower sublevel form a topological pushout along
exactly their boundary spheres. The disks can have different dimensions, including zero, and
the lower sublevel need not be compact. The characteristic maps are the inverse-chart maps.
-/
theorem exists_isPushout_negativeDisks [Finite ι] [T2Space M]
    {ε : ℝ} (hε : 0 ≤ ε) (hfs : Continuous f)
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ)
    (hball : ∀ i, closedBall 0 √ε ⊆ (ψ i).target)
    (hf : ∀ i, ∀ x ∈ (ψ i).source,
      f x = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i x j ^ 2) :
    let D := fun i ↦ closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k i}) √ε
    let S := fun i ↦ sphere (0 : EuclideanSpace ℝ {j : Fin n // j.val < k i}) √ε
    let m : TopCat.of (Σ i, S i) ⟶ TopCat.of (Σ i, D i) := TopCat.ofHom
      (ContinuousMap.sigma fun i ↦ (ContinuousMap.sigmaMk i).comp
        (ContinuousMap.inclusion sphere_subset_closedBall))
    let A := {x | f x ≤ c - ε}
    let Y := A ∪ ⋃ i, range ((ψ i).negativeDiskMap (k i) (hball i))
    ∃ (α : TopCat.of (Σ i, S i) ⟶ TopCat.of A)
      (χ : TopCat.of (Σ i, D i) ⟶ TopCat.of Y),
      IsPushout α m (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)) χ ∧
        (∀ i u, (χ ⟨i, u⟩ : M) = (ψ i).negativeDiskMap (k i) (hball i) u) ∧
        ∀ i u, (α ⟨i, u⟩ : M) = (ψ i).negativeDiskMap (k i) (hball i)
          (Set.inclusion sphere_subset_closedBall u) := by
  classical
  intro D S m A Y
  -- The finite disk union is compact and embeds in the ambient manifold.
  let q : C((Σ i, D i), M) := ContinuousMap.sigma fun i ↦
    (ψ i).negativeDiskMap (k i) (hball i)
  have hqinj : Injective q := by
    rintro ⟨i, u⟩ ⟨j, v⟩ h
    by_cases hij : i = j
    · subst hij
      congr 1
      exact (ψ i).injective_negativeDiskMap (k i) (hball i) h
    · exact False.elim ((hψ hij).ne_of_mem
        ((ψ i).negativeDiskMap_mem_source (k i) (hball i) u)
        ((ψ j).negativeDiskMap_mem_source (k j) (hball j) v) h)
  have hqclosed : IsClosedMap q := q.continuous.isClosedEmbedding hqinj |>.isClosedMap
  let χ : TopCat.of (Σ i, D i) ⟶ TopCat.of Y := TopCat.ofHom
    ⟨fun z ↦ ⟨q z, Or.inr (mem_iUnion.2 ⟨z.1, z.2, rfl⟩)⟩,
      q.continuous.subtype_mk _⟩
  have hbound (z : Σ i, S i) : q (m z) ∈ A := by
    have h := (ψ z.1).negativeDiskMap_le_iff (k z.1) (hball z.1) (hf z.1)
      (Set.inclusion sphere_subset_closedBall z.2)
    rw [Real.sq_sqrt hε] at h
    exact h.2 (mem_sphere_zero_iff_norm.1 z.2.2)
  let α : TopCat.of (Σ i, S i) ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun z ↦ ⟨q (m z), hbound z⟩,
      (q.continuous.comp m.hom.continuous).subtype_mk _⟩
  let inc : TopCat.of A ⟶ TopCat.of Y :=
    TopCat.ofHom (ContinuousMap.inclusion subset_union_left)
  have hw : α ≫ inc = m ≫ χ := by ext z; rfl
  have hinc : Injective inc := by
    intro a b h
    exact Subtype.ext (congrArg (fun y : Y ↦ (y : M)) h)
  have hχ : Injective χ := fun _ _ h ↦ hqinj (congrArg Subtype.val h)
  -- Identify the intersection with the lower sublevel before checking the final topology.
  have hpull : IsPullback ((forget TopCat).map α) ((forget TopCat).map m)
      ((forget TopCat).map inc) ((forget TopCat).map χ) := by
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨(forget TopCat).congr_map hw, ?_, ?_⟩
    · intro z w h
      -- The boundary inclusion is the componentwise subtype inclusion.
      rcases z with ⟨i, u⟩
      rcases w with ⟨j, v⟩
      have hij : i = j := congrArg Sigma.fst h.2
      subst hij
      congr 1
      have he : (⟨i, Set.inclusion sphere_subset_closedBall u⟩ : Σ j, D j) =
          ⟨i, Set.inclusion sphere_subset_closedBall v⟩ := h.2
      have huv : Set.inclusion (sphere_subset_closedBall : S i ⊆ D i) u =
          Set.inclusion sphere_subset_closedBall v :=
        @sigma_mk_injective ι (fun j ↦ ↥(D j)) i _ _ he
      exact Set.inclusion_injective sphere_subset_closedBall huv
    · rintro a ⟨i, u⟩ ha
      have hu : f ((ψ i).negativeDiskMap (k i) (hball i) u) ≤ c - ε := by
        have heq : (a : M) = (ψ i).negativeDiskMap (k i) (hball i) u :=
          congrArg (fun y : Y ↦ (y : M)) ha
        rw [← heq]
        exact a.2
      have hus : (u : EuclideanSpace ℝ {j : Fin n // j.val < k i}) ∈ sphere 0 √ε :=
        mem_sphere_zero_iff_norm.2
          (((ψ i).negativeDiskMap_le_iff (k i) (hball i) (hf i) u).1
            (by simpa only [Real.sq_sqrt hε] using hu))
      refine ⟨⟨i, ⟨u, hus⟩⟩, ?_, rfl⟩
      apply hinc
      exact ha.symm
  have : Mono ((forget TopCat).map inc) := (CategoryTheory.mono_iff_injective _).2 hinc
  have hcover : range inc ∪ range χ = univ := by
    apply eq_univ_of_forall
    rintro ⟨x, hx | hx⟩
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · obtain ⟨i, u, rfl⟩ := mem_iUnion.1 hx
      exact Or.inr ⟨⟨i, u⟩, rfl⟩
  have hsets := Types.isPushout_of_isPullback_of_mono' hpull hcover
    (fun _ _ _ _ h ↦ hχ h)
  refine ⟨α, χ, hsets.of_map_forget_of_isClosedMap ?_ ?_,
    fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  · exact (isClosed_le hfs continuous_const).isClosedMap_inclusion subset_union_left
  · exact hqclosed.codRestrict _

/-- **Cell attachment as a relative homotopy equivalence.** Across a compact critical band
covered by disjoint normalized Morse charts, the upper sublevel is homotopy equivalent to the
pushout attaching the negative disks along their boundary spheres. The comparison is induced by
the lower-sublevel inclusion and the inverse-chart characteristic maps. Its inverse is a strict
left inverse, and the other inverse homotopy fixes the entire lower sublevel.

The negative coordinate space at a chart with `k ≤ n` has dimension `k`; no common index is
required, and index-zero disks and empty families are included. -/
theorem exists_sublevel_negativeDisk_attachment [Finite ι] [T2Space M]
    [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ)
    {ε : ℝ} (hε : 0 < ε) (hball : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ i).target)
    (hf : ∀ i, ∀ x ∈ (ψ i).source,
      f x = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i x j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ i).source) :
    let hb : ∀ i, closedBall 0 √ε ⊆ (ψ i).target := fun i ↦
      (closedBall_subset_closedBall (Real.sqrt_le_sqrt (by linarith))).trans (hball i)
    let D := fun i ↦ closedBall (0 : EuclideanSpace ℝ {j : Fin n // j.val < k i}) √ε
    let S := fun i ↦ sphere (0 : EuclideanSpace ℝ {j : Fin n // j.val < k i}) √ε
    let m : TopCat.of (Σ i, S i) ⟶ TopCat.of (Σ i, D i) := TopCat.ofHom
      (ContinuousMap.sigma fun i ↦ (ContinuousMap.sigmaMk i).comp
        (ContinuousMap.inclusion sphere_subset_closedBall))
    ∃ (α : TopCat.of (Σ i, S i) ⟶ TopCat.of {x | f x ≤ c - ε})
      (e : ContinuousMap.HomotopyEquiv (pushout α m : TopCat) {x | f x ≤ c + ε}),
      (∀ z, e.symm (e z) = z) ∧
      Nonempty ((e.toFun.comp e.invFun).HomotopyRel (ContinuousMap.id _)
        {x | f (x : M) ≤ c - ε}) ∧
      (∀ x, (e (pushout.inl α m x) : M) = x) ∧
      (∀ i u, (e (pushout.inr α m ⟨i, u⟩) : M) = (ψ i).negativeDiskMap (k i) (hb i) u) ∧
      ∀ i u, (α ⟨i, u⟩ : M) = (ψ i).negativeDiskMap (k i) (hb i)
        (Set.inclusion sphere_subset_closedBall u) := by
  classical
  intro hb D S m
  let A := {x | f x ≤ c - ε}
  let B := {x | f x ≤ c + ε}
  let Y := A ∪ ⋃ i, range ((ψ i).negativeDiskMap (k i) (hb i))
  have hsquare : (√ε) ^ 2 = ε := Real.sq_sqrt hε.le
  obtain ⟨α, χ, hsq, hχ, hα⟩ :=
    exists_isPushout_negativeDisks hε.le hfs.continuous ψ hψ k hb hf
  have hYB : Y ⊆ B := by
    rintro x (hx | hx)
    · simp only [A, B, mem_ofPred_eq] at hx ⊢
      exact le_trans hx (by linarith)
    · obtain ⟨i, u, rfl⟩ := mem_iUnion.1 hx
      simp only [B, mem_ofPred_eq]
      rw [(ψ i).comp_negativeDiskMap (k i) (hb i) (hf i)]
      linarith [sq_nonneg ‖(u : EuclideanSpace ℝ {j : Fin n // j.val < k i})‖]
  have hcell : {x | f x ≤ c - ε} ∪ ⋃ i, (ψ i).source ∩
      ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0} = Y := by
    simp only [Y, A, PartialDiffeomorph.range_negativeDiskMap _ _ _ (Real.sqrt_nonneg ε), hsquare]
  have hdeform := exists_sublevel_union_cells_deformation hfs ψ hψ k hε hball hf
    hcompact hcrit
  rw [hcell] at hdeform
  obtain ⟨R, hR, ⟨H⟩⟩ := hdeform
  let Z := B ∩ Y
  let inc : C(Z, B) := ContinuousMap.inclusion inter_subset_left
  have hRinc (y : Z) : R (inc y) = y := hR y
  -- The set-theoretic disk union is the actual topological adjunction, with its prescribed maps.
  let h₀ : (pushout α m : TopCat) ≃ₜ Y := TopCat.homeoOfIso hsq.isoPushout.symm
  let h : (pushout α m : TopCat) ≃ₜ Z := h₀.trans
    (Homeomorph.setCongr (inter_eq_right.2 hYB)).symm
  let q : C((pushout α m : TopCat), B) := inc.comp (ContinuousMap.ofClass h)
  -- Changing the subtype from `Y` to `B ∩ Y` preserves its ambient point.
  have hval (z : (pushout α m : TopCat)) : (q z : M) = (h₀ z : M) := (rfl)
  let p : C(B, (pushout α m : TopCat)) := (ContinuousMap.ofClass h.symm).comp R
  have hpq (z : (pushout α m : TopCat)) : p (q z) = z := by
    simp only [p, q, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, hRinc,
      Homeomorph.symm_apply_apply]
  have hqp : q.comp p = inc.comp R := by
    ext x
    simp only [p, q, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
      Homeomorph.apply_symm_apply]
  have H' : (q.comp p).HomotopyRel (ContinuousMap.id B)
      {x | f (x : M) ≤ c - ε} := by
    rw [hqp]
    -- Both inclusion maps are subtype inclusions; the native homotopy fixes all of `Y`.
    exact { H with prop' := fun t x hx ↦ H.eq_fst t (Or.inl hx) }
  let e : ContinuousMap.HomotopyEquiv (pushout α m : TopCat) B :=
    { toFun := q
      invFun := p
      left_inv := by
        have heq : p.comp q = ContinuousMap.id _ := ContinuousMap.ext hpq
        rw [heq]
      right_inv := ⟨H'.toHomotopy⟩ }
  refine ⟨α, e, hpq, ⟨H'⟩, ?_, ?_, hα⟩
  · intro x
    have hx : h₀ (pushout.inl α m x) =
        (TopCat.ofHom (ContinuousMap.inclusion subset_union_left) : TopCat.of A ⟶ TopCat.of Y) x :=
      ConcreteCategory.congr_hom hsq.inl_isoPushout_inv x
    exact (hval _).trans (congrArg (fun y : Y ↦ (y : M)) hx)
  · intro i u
    have hu : h₀ (pushout.inr α m ⟨i, u⟩) = χ ⟨i, u⟩ :=
      ConcreteCategory.congr_hom hsq.inr_isoPushout_inv ⟨i, u⟩
    exact (hval _).trans ((congrArg (fun y : Y ↦ (y : M)) hu).trans (hχ i u))

end TauCeti
