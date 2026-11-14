/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Selection
public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
public import TauCeti.Topology.Algebra.Polynomial.Root.Extension
import TauCeti.Analysis.Analytic.Submanifold.Dimension

/-!
# Frontier compatibility and approach regions of stacks

Let `C` and `B` be subsets of `ℝⁿ` with `B ⊆ closure C`, carrying strictly ordered stacks
`θ : Fin k → C → ℝ` and `η : Fin m → B → ℝ`. Suppose each section `θ i` converges along `C` at
every point of `B` to a section `η (σ i)` of the boundary stack. Then:

* `σ : Fin k → Fin m` is unique (over a nonempty `B`) and monotone;
* the closure of the `i`-th ambient section over `C`, intersected with the cylinder over `B`, is
  exact: it equals the `(σ i)`-th ambient section over `B`;
* the closure of the `j`-th ambient sector over `C`, intersected with the cylinder over `B`, is
  cut out by the weak inequalities `η (σ i) x ≤ t` for `i < j` and `t ≤ η (σ i) x` for `j ≤ i`,
  and decomposes into an explicit union of sections and sectors of `stackCells B η`. Both root
  coalescence (`σ i = σ (i + 1)`, collapsing a bounded sector to a single boundary section) and
  additional boundary roots (`σ` non-surjective, splitting a sector closure across several
  boundary cells) are handled uniformly;
* every cell `E' ∈ stackCells B η` meeting `closure E` for `E ∈ stackCells C θ` is contained in
  `closure E`, and when `B` and `C` are analytic submanifolds with `dim B < dim C` and analytic
  sections (or `B = C` with `E' ≠ E`), `dim E' < dim E`;
* preconnected approach regions (`TauCeti.IsPreconnectedApproachAt`) lift from `C` to every cell
  of `stackCells C θ` at any point whose base projection has finite section limits along `C`.

Combining `TauCeti.continuousOn_extendFrom_of_isRoot_of_subset_closure` with
`TauCeti.Delineation.exists_eq_root_of_continuous` discharges the root-matching hypothesis `σ`
for polynomial delineations over connected boundary strata `B ⊆ closure C` whenever `C` has
preconnected approach regions along `B` and each root section of `C` is witnessed by a family
member that remains nonzero and of non-increasing degree at `B`. Together with approach-region
lifting, this propagates both parts of the frontier condition and the frontier local-connectedness
invariant across inductive coordinate liftings on cylinders and bounded open boxes.

## Main declarations

* `TauCeti.eq_of_tendsto_section`, `TauCeti.monotone_of_tendsto_section`,
  `TauCeti.tail_mem_closure_of_mem_closure_stackCells`: uniqueness and monotonicity of the
  boundary section-matching map `σ`, and base-closure projection of stack cells.
* `TauCeti.closure_image_cylinder_sectionSet_inter_eq`,
  `TauCeti.closure_image_cylinder_sectorSet_inter_eq`,
  `TauCeti.closure_image_cylinder_sectorSet_inter_eq_union`: exact trace of section and sector
  closures over `B ⊆ closure C`.
* `TauCeti.subset_closure_of_mem_stackCells_of_nonempty_inter`,
  `TauCeti.subset_closure_of_mem_stackCells_self_of_nonempty_inter`: first part of the frontier
  condition (`E' ∩ closure E ≠ ∅ → E' ⊆ closure E`).
* `TauCeti.dim_lt_of_mem_stackCells_of_subset_closure`,
  `TauCeti.dim_lt_of_mem_stackCells_self_of_subset_closure`: second part of the frontier
  condition (`E' ⊆ closure E, E' ≠ E → dim E' < dim E`) for analytic submanifold cells.
* `TauCeti.isPreconnectedApproachAt_image_cylinder_sectionSet`,
  `TauCeti.isPreconnectedApproachAt_image_cylinder_sectorSet`,
  `TauCeti.isPreconnectedApproachAt_of_mem_stackCells`: lifting of preconnected approach regions
  from the base to stack cells.
* `TauCeti.Delineation.exists_root_tendsto_of_subset_closure`: existence of the monotone root
  matching `σ : Fin D_C.count → Fin D_B.count` between delineations on `C` and `B ⊆ closure C`.
* `TauCeti.subset_closure_of_mem_biUnion_stackCells`,
  `TauCeti.inter_closure_eq_biUnion_of_mem_biUnion_stackCells`,
  `TauCeti.dim_lt_of_mem_biUnion_stackCells`,
  `TauCeti.isPreconnectedApproachAt_of_mem_biUnion_stackCells`,
  `TauCeti.isConnected_inter_Ioo_of_mem_stackCells`: lifting of frontier-compatible partitions
  and approach-region invariants to cylinders and bounded open boxes.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.3
  and 9.1–9.2.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
  di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-! ### Boundary closures of sections and sectors -/

section BoundaryClosure

variable {n k m : ℕ}

section Topological

variable {α : Type*} [TopologicalSpace α] {C B : Set (Fin n → α)}
  {θ : Fin k → C → α} {η : Fin m → B → α} {σ σ' : Fin k → Fin m}

/-- Over a nonempty boundary set `B ⊆ closure C` on which the sections `η` are pointwise
distinct, at most one index map `σ` can match the limits of `θ` along `C` to `η`. -/
theorem eq_of_tendsto_section [T2Space α] (hBC : B ⊆ closure C) (hB : B.Nonempty)
    (hη : ∀ x : B, Injective fun l ↦ η l x)
    (hσ : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    (hσ' : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ' i) x))) :
    σ = σ' := by
  obtain ⟨x₀, hx₀⟩ := hB
  have hne : (comap (Subtype.val : C → Fin n → α) (𝓝 x₀)).NeBot :=
    mem_closure_iff_comap_neBot.mp (hBC hx₀)
  funext i
  exact hη ⟨x₀, hx₀⟩ (tendsto_nhds_unique (hσ i ⟨x₀, hx₀⟩) (hσ' i ⟨x₀, hx₀⟩))

/-- If pointwise monotone sections `θ` on `C` converge along `C` at a nonempty `B ⊆ closure C`
to pointwise strictly monotone sections `η` on `B`, the matching index map `σ` is monotone. -/
theorem monotone_of_tendsto_section [LinearOrder α] [OrderClosedTopology α]
    (hBC : B ⊆ closure C) (hB : B.Nonempty)
    (hθ : ∀ y : C, Monotone fun i ↦ θ i y) (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x))) :
    Monotone σ := by
  obtain ⟨x₀, hx₀⟩ := hB
  have hne : (comap (Subtype.val : C → Fin n → α) (𝓝 x₀)).NeBot :=
    mem_closure_iff_comap_neBot.mp (hBC hx₀)
  intro i j hij
  exact (hη ⟨x₀, hx₀⟩).le_iff_le.mp <|
    le_of_tendsto_of_tendsto (hlim i ⟨x₀, hx₀⟩) (hlim j ⟨x₀, hx₀⟩)
      (Eventually.of_forall fun y ↦ hθ y hij)

/-- If a point `v` lies in the closure of a cell of a strictly ordered stack over `C`, its base
projection `Fin.tail v` lies in `closure C`. -/
theorem tail_mem_closure_of_mem_closure_stackCells [LinearOrder α] [Nonempty α]
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) {E : Set (Fin (n + 1) → α)}
    (hE : E ∈ stackCells C θ) {v : Fin (n + 1) → α} (hv : v ∈ closure E) :
    Fin.tail v ∈ closure C := by
  have htail : Continuous (Fin.tail : (Fin (n + 1) → α) → Fin n → α) := by fun_prop
  have hmem := image_closure_subset_closure_image htail (mem_image_of_mem Fin.tail hv)
  rwa [image_tail_of_mem_stackCells hθ hE] at hmem

/-- The closure of the `i`-th ambient section over `C`, intersected with the cylinder over
`B ⊆ closure C`, is exactly the `(σ i)`-th ambient section over `B`. -/
theorem closure_image_cylinder_sectionSet_inter_eq [T2Space α] (hBC : B ⊆ closure C)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    (i : Fin k) :
    closure (cylinder C '' sectionSet θ i) ∩ {v | Fin.tail v ∈ B} =
      cylinder B '' sectionSet η (σ i) := by
  let q : C → Fin (n + 1) → α := fun y ↦ Fin.cons (θ i y) y.1
  have hrange : range q = cylinder C '' sectionSet θ i := by
    ext v
    simp only [mem_range, mem_image_cylinder, mem_sectionSet, q]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨hy ▸ y.2, by simp [← hy]⟩,
      fun ⟨hv, hθv⟩ ↦ ⟨⟨Fin.tail v, hv⟩, by rw [hθv, Fin.cons_self_tail]⟩⟩
  ext v
  simp only [mem_inter_iff, mem_ofPred_eq, mem_image_cylinder, mem_sectionSet]
  constructor
  · rintro ⟨hv_cl, hxB⟩
    have : (comap q (𝓝 v)).NeBot := by
      rw [← Filter.map_neBot_iff q, Filter.map_comap, hrange]
      exact mem_closure_iff_nhdsWithin_neBot.mp hv_cl
    have htail : Tendsto (Subtype.val : C → Fin n → α) (comap q (𝓝 v)) (𝓝 (Fin.tail v)) := by
      have hc : Continuous (Fin.tail : (Fin (n + 1) → α) → Fin n → α) := by fun_prop
      exact (hc.tendsto v).comp tendsto_comap
    have hzero : Tendsto (θ i) (comap q (𝓝 v)) (𝓝 (v 0)) :=
      ((continuous_apply 0).tendsto v).comp tendsto_comap
    have hηv : Tendsto (θ i) (comap q (𝓝 v)) (𝓝 (η (σ i) ⟨Fin.tail v, hxB⟩)) :=
      (hlim i ⟨Fin.tail v, hxB⟩).mono_left (tendsto_comap_iff.mpr htail)
    exact ⟨hxB, tendsto_nhds_unique hηv hzero⟩
  · rintro ⟨hxB, hηv⟩
    have hne : (comap (Subtype.val : C → Fin n → α) (𝓝 (Fin.tail v))).NeBot :=
      mem_closure_iff_comap_neBot.mp (hBC hxB)
    have hq_lim : Tendsto q (comap Subtype.val (𝓝 (Fin.tail v))) (𝓝 v) := by
      rw [← Fin.cons_self_tail v, ← hηv]
      exact (hlim i ⟨Fin.tail v, hxB⟩).finCons tendsto_comap
    refine ⟨?_, hxB⟩
    rw [← hrange]
    exact mem_closure_of_tendsto hq_lim (Eventually.of_forall fun y ↦ mem_range_self y)

end Topological

section Real

variable {C B : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ} {η : Fin m → B → ℝ} {σ : Fin k → Fin m}

private lemma mem_closure_image_cylinder_sectorSet_of_tendsto {x : Fin n → ℝ} (hx : x ∈ closure C)
    {j : Fin (k + 1)} {h : C → ℝ} {t : ℝ} (hh : ∀ y : C, (y, h y) ∈ sectorSet θ j)
    (ht : Tendsto h (comap Subtype.val (𝓝 x)) (𝓝 t)) :
    Fin.cons t x ∈ closure (cylinder C '' sectorSet θ j) := by
  have hne : (comap (Subtype.val : C → Fin n → ℝ) (𝓝 x)).NeBot := mem_closure_iff_comap_neBot.mp hx
  have hcons : Tendsto (fun y : C ↦ (Fin.cons (h y) y.1 : Fin (n + 1) → ℝ))
      (comap Subtype.val (𝓝 x)) (𝓝 (Fin.cons t x : Fin (n + 1) → ℝ)) :=
    ht.finCons tendsto_comap
  exact mem_closure_of_tendsto hcons
    (Eventually.of_forall fun y ↦ mem_image_cylinder.mpr ⟨y.2, hh y⟩)

private lemma mem_closure_sectorSet_castSucc_succ_of_le {k : ℕ} {C : Set (Fin n → ℝ)}
    {θ : Fin (k + 1) → C → ℝ} (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {x : Fin n → ℝ} (hx : x ∈ closure C) {i₀ : Fin k} {a b t : ℝ} (ha : a ≤ t) (hb : t ≤ b)
    (hlim_a : Tendsto (θ i₀.castSucc) (comap Subtype.val (𝓝 x)) (𝓝 a))
    (hlim_b : Tendsto (θ i₀.succ) (comap Subtype.val (𝓝 x)) (𝓝 b)) :
    Fin.cons t x ∈ closure (cylinder C '' sectorSet θ i₀.castSucc.succ) := by
  have hm : ∀ y : C, Monotone fun i ↦ θ i y := fun y ↦ (hθ y).monotone
  have hline (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
      Fin.cons (AffineMap.lineMap a b c) x ∈
        closure (cylinder C '' sectorSet θ i₀.castSucc.succ) := by
    refine mem_closure_image_cylinder_sectorSet_of_tendsto hx
      (h := fun y ↦ AffineMap.lineMap (θ i₀.castSucc y) (θ i₀.succ y) c) (fun y ↦ ?_) ?_
    · rw [sectorSet_castSucc_succ hm, mem_ofPred_eq, ← mem_Ioo,
        ← openSegment_eq_Ioo (hθ y i₀.castSucc_lt_succ), openSegment_eq_image_lineMap]
      exact mem_image_of_mem _ hc
    · simp only [AffineMap.lineMap_apply_ring]
      exact (hlim_a.const_mul (1 - c)).add (hlim_b.const_mul c)
  rcases eq_or_lt_of_le (ha.trans hb) with hab | hab
  · have ht : t = a := le_antisymm (hab ▸ hb) ha
    have hmid : AffineMap.lineMap a b (1 / 2 : ℝ) = t := by simp [← hab, ht]
    simpa only [hmid] using hline (1 / 2) ⟨by norm_num, by norm_num⟩
  · have htIcc : t ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact ⟨ha, hb⟩
    have hcont_cons : Continuous (fun r : ℝ ↦ (Fin.cons r x : Fin (n + 1) → ℝ)) := by fun_prop
    have hsub : Ioo a b ⊆ {r | Fin.cons r x ∈
        closure (cylinder C '' sectorSet θ i₀.castSucc.succ)} := by
      rw [← openSegment_eq_Ioo hab, openSegment_eq_image_lineMap]
      rintro _ ⟨c, hc, rfl⟩
      exact hline c hc
    exact (isClosed_closure.preimage hcont_cons).closure_subset_iff.mpr hsub htIcc

private lemma mem_closure_image_cylinder_sectorSet_of_le (hBC : B ⊆ closure C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    {j : Fin (k + 1)} {v : Fin (n + 1) → ℝ} (hxB : Fin.tail v ∈ B)
    (hlow : ∀ i : Fin k, i.castSucc < j → η (σ i) ⟨Fin.tail v, hxB⟩ ≤ v 0)
    (hhigh : ∀ i : Fin k, j ≤ i.castSucc → v 0 ≤ η (σ i) ⟨Fin.tail v, hxB⟩) :
    v ∈ closure (cylinder C '' sectorSet θ j) := by
  let x : B := ⟨Fin.tail v, hxB⟩
  have hx_cl : Fin.tail v ∈ closure C := hBC hxB
  cases k with
  | zero =>
    simpa only [Fin.cons_self_tail] using mem_closure_image_cylinder_sectorSet_of_tendsto hx_cl
      (h := fun _ ↦ v 0) (fun _ ↦ by simp) tendsto_const_nhds
  | succ k =>
    have hm : ∀ y : C, Monotone fun i ↦ θ i y := fun y ↦ (hθ y).monotone
    cases j using Fin.cases with
    | zero =>
      have hε (ε : ℝ) (hε : 0 < ε) :
          Fin.cons (v 0 - ε) (Fin.tail v) ∈ closure (cylinder C '' sectorSet θ 0) := by
        have hmin : min (v 0 - ε) (η (σ 0) x - ε) = v 0 - ε :=
          min_eq_left (by linarith [hhigh 0 (Fin.zero_le _)])
        rw [← hmin]
        exact mem_closure_image_cylinder_sectorSet_of_tendsto hx_cl
          (h := fun y ↦ min (v 0 - ε) (θ 0 y - ε))
          (fun y ↦ by rw [sectorSet_zero hm]; exact (min_le_right _ _).trans_lt (sub_lt_self _ hε))
          (tendsto_const_nhds.min ((hlim 0 x).sub_const ε))
      have hlim_ε : Tendsto (fun ε : ℝ ↦ (Fin.cons (v 0 - ε) (Fin.tail v) : Fin (n + 1) → ℝ))
          (𝓝[>] 0) (𝓝 v) := by
        have hc : Continuous (fun ε : ℝ ↦ (Fin.cons (v 0 - ε) (Fin.tail v) : Fin (n + 1) → ℝ)) := by
          fun_prop
        simpa only [sub_zero, Fin.cons_self_tail] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact isClosed_closure.mem_of_tendsto hlim_ε
        (eventually_nhdsWithin_iff.mpr <| Eventually.of_forall hε)
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        have hε (ε : ℝ) (hε : 0 < ε) :
            Fin.cons (v 0 + ε) (Fin.tail v) ∈
              closure (cylinder C '' sectorSet θ (Fin.last (k + 1))) := by
          have hmax : max (v 0 + ε) (η (σ (Fin.last k)) x + ε) = v 0 + ε :=
            max_eq_left (by linarith [hlow (Fin.last k) (Fin.castSucc_lt_last _)])
          rw [← hmax, ← Fin.succ_last]
          exact mem_closure_image_cylinder_sectorSet_of_tendsto hx_cl
            (h := fun y ↦ max (v 0 + ε) (θ (Fin.last k) y + ε))
            (fun y ↦ by
              rw [Fin.succ_last, sectorSet_last hm]
              exact (lt_add_of_pos_right _ hε).trans_le (le_max_right _ _))
            (tendsto_const_nhds.max ((hlim (Fin.last k) x).add_const ε))
        have hlim_ε : Tendsto (fun ε : ℝ ↦ (Fin.cons (v 0 + ε) (Fin.tail v) : Fin (n + 1) → ℝ))
            (𝓝[>] 0) (𝓝 v) := by
          have hc :
              Continuous (fun ε : ℝ ↦ (Fin.cons (v 0 + ε) (Fin.tail v) : Fin (n + 1) → ℝ)) := by
            fun_prop
          simpa only [add_zero, Fin.cons_self_tail] using
            (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        exact isClosed_closure.mem_of_tendsto hlim_ε
          (eventually_nhdsWithin_iff.mpr <| Eventually.of_forall hε)
      | cast i₀ =>
        simpa only [Fin.cons_self_tail] using mem_closure_sectorSet_castSucc_succ_of_le hθ hx_cl
          (hlow i₀.castSucc Fin.castSucc_lt_succ) (hhigh i₀.succ le_rfl)
          (hlim i₀.castSucc x) (hlim i₀.succ x)

/-- The closure of the `j`-th ambient sector over `C`, intersected with the cylinder over
`B ⊆ closure C`, consists of the points over `B` lying weakly above `η (σ i)` for `i < j` and
weakly below `η (σ i)` for `j ≤ i`. -/
theorem closure_image_cylinder_sectorSet_inter_eq (hBC : B ⊆ closure C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    (j : Fin (k + 1)) :
    closure (cylinder C '' sectorSet θ j) ∩ {v | Fin.tail v ∈ B} =
      {v : Fin (n + 1) → ℝ | ∃ hx : Fin.tail v ∈ B,
        (∀ i : Fin k, i.castSucc < j → η (σ i) ⟨Fin.tail v, hx⟩ ≤ v 0) ∧
        ∀ i : Fin k, j ≤ i.castSucc → v 0 ≤ η (σ i) ⟨Fin.tail v, hx⟩} := by
  let S := sectorSet θ j
  let q : S → Fin (n + 1) → ℝ := cylinder C ∘ Subtype.val
  have hrange : range q = cylinder C '' sectorSet θ j := by
    rw [range_comp, Subtype.range_val]
  ext v
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hv_cl, hxB⟩
    have : (comap q (𝓝 v)).NeBot := by
      rw [← Filter.map_neBot_iff q, Filter.map_comap, hrange]
      exact mem_closure_iff_nhdsWithin_neBot.mp hv_cl
    have htail : Tendsto (fun w : S ↦ w.1.1.1) (comap q (𝓝 v)) (𝓝 (Fin.tail v)) := by
      have hc : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
      simpa only [Function.comp_def, q, tail_cylinder] using
        (hc.tendsto v).comp (tendsto_comap (f := q))
    have hbase : Tendsto (fun w : S ↦ w.1.1) (comap q (𝓝 v))
        (comap Subtype.val (𝓝 (Fin.tail v))) := tendsto_comap_iff.mpr htail
    have hzero : Tendsto (fun w : S ↦ w.1.2) (comap q (𝓝 v)) (𝓝 (v 0)) := by
      simpa only [Function.comp_def, q, cylinder_apply_zero] using
        ((continuous_apply 0).tendsto v).comp (tendsto_comap (f := q))
    refine ⟨hxB, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · exact le_of_tendsto_of_tendsto ((hlim i ⟨Fin.tail v, hxB⟩).comp hbase) hzero
        (Eventually.of_forall fun w ↦ ((mem_sectorSet.mp w.2).1 i hi).le)
    · exact le_of_tendsto_of_tendsto hzero ((hlim i ⟨Fin.tail v, hxB⟩).comp hbase)
        (Eventually.of_forall fun w ↦ ((mem_sectorSet.mp w.2).2 i hi).le)
  · rintro ⟨hxB, hlow, hhigh⟩
    exact ⟨mem_closure_image_cylinder_sectorSet_of_le hBC hθ hlim hxB hlow hhigh, hxB⟩

/-- A point on the `l`-th boundary section over `B` belongs to the closure of the `j`-th sector
over `C` if and only if the index `l` lies weakly between `σ i` for `i < j` and `σ i` for
`j ≤ i`, a condition independent of the base point in `B`. -/
theorem mem_closure_sectorSet_iff_of_mem_sectionSet (hBC : B ⊆ closure C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    {j : Fin (k + 1)} {l : Fin m} {v : Fin (n + 1) → ℝ}
    (hv : v ∈ cylinder B '' sectionSet η l) :
    v ∈ closure (cylinder C '' sectorSet θ j) ↔
      (∀ i : Fin k, i.castSucc < j → σ i ≤ l) ∧
        ∀ i : Fin k, j ≤ i.castSucc → l ≤ σ i := by
  obtain ⟨hxB, hvl⟩ := mem_image_cylinder.mp hv
  simp only [mem_sectionSet] at hvl
  have hmem : v ∈ closure (cylinder C '' sectorSet θ j) ↔
      v ∈ closure (cylinder C '' sectorSet θ j) ∩ {w | Fin.tail w ∈ B} :=
    ⟨fun h ↦ ⟨h, hxB⟩, fun h ↦ h.1⟩
  rw [hmem, closure_image_cylinder_sectorSet_inter_eq hBC hθ hlim j]
  simp only [mem_ofPred_eq, hxB, exists_true_left, ← hvl, (hη ⟨Fin.tail v, hxB⟩).le_iff_le]

/-- A point in the `r`-th boundary sector over `B` belongs to the closure of the `j`-th sector
over `C` if and only if `(σ i).castSucc < r` for `i < j` and `r ≤ (σ i).castSucc` for `j ≤ i`,
a condition independent of the point in the boundary sector. -/
theorem mem_closure_sectorSet_iff_of_mem_sectorSet (hBC : B ⊆ closure C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    {j : Fin (k + 1)} {r : Fin (m + 1)} {v : Fin (n + 1) → ℝ}
    (hv : v ∈ cylinder B '' sectorSet η r) :
    v ∈ closure (cylinder C '' sectorSet θ j) ↔
      (∀ i : Fin k, i.castSucc < j → (σ i).castSucc < r) ∧
        ∀ i : Fin k, j ≤ i.castSucc → r ≤ (σ i).castSucc := by
  obtain ⟨hxB, hvr⟩ := mem_image_cylinder.mp hv
  simp only [mem_sectorSet] at hvr
  have hmem : v ∈ closure (cylinder C '' sectorSet θ j) ↔
      v ∈ closure (cylinder C '' sectorSet θ j) ∩ {w | Fin.tail w ∈ B} :=
    ⟨fun h ↦ ⟨h, hxB⟩, fun h ↦ h.1⟩
  rw [hmem, closure_image_cylinder_sectorSet_inter_eq (η := η) (σ := σ) hBC hθ hlim j]
  simp only [mem_ofPred_eq, hxB, exists_true_left]
  refine and_congr (forall₂_congr fun i _ ↦ ?_) (forall₂_congr fun i _ ↦ ?_)
  · exact ⟨fun hle ↦ not_le.mp fun hge ↦ (hvr.2 (σ i) hge).not_ge hle,
      fun hlt ↦ (hvr.1 (σ i) hlt).le⟩
  · exact ⟨fun hle ↦ not_lt.mp fun hlt ↦ (hvr.1 (σ i) hlt).not_ge hle,
      fun hge ↦ (hvr.2 (σ i) hge).le⟩

/-- Over `B ⊆ closure C`, the closure of a sector of `stackCells C θ` is the explicit union of
those boundary sections and boundary sectors of `stackCells B η` whose indices lie between the
matched boundary indices of the lower and upper bounding sections of the sector. -/
theorem closure_image_cylinder_sectorSet_inter_eq_union (hBC : B ⊆ closure C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    (j : Fin (k + 1)) :
    closure (cylinder C '' sectorSet θ j) ∩ {v | Fin.tail v ∈ B} =
      (⋃ (l : Fin m) (_ : (∀ i : Fin k, i.castSucc < j → σ i ≤ l) ∧
          ∀ i : Fin k, j ≤ i.castSucc → l ≤ σ i), cylinder B '' sectionSet η l) ∪
        ⋃ (r : Fin (m + 1)) (_ : (∀ i : Fin k, i.castSucc < j → (σ i).castSucc < r) ∧
          ∀ i : Fin k, j ≤ i.castSucc → r ≤ (σ i).castSucc), cylinder B '' sectorSet η r := by
  ext v
  constructor
  · rintro ⟨hv_cl, hxB⟩
    have hcover : v ∈ ⋃₀ stackCells B η := by
      rw [sUnion_stackCells fun x ↦ (hη x).monotone]
      exact hxB
    obtain ⟨E', hE', hvE'⟩ := hcover
    rcases mem_stackCells.mp hE' with ⟨l, rfl⟩ | ⟨r, rfl⟩
    · exact Or.inl <| mem_iUnion₂.mpr
        ⟨l, (mem_closure_sectorSet_iff_of_mem_sectionSet hBC hθ hη hlim hvE').mp hv_cl, hvE'⟩
    · exact Or.inr <| mem_iUnion₂.mpr
        ⟨r, (mem_closure_sectorSet_iff_of_mem_sectorSet hBC hθ hlim hvE').mp hv_cl, hvE'⟩
  · rintro (hv | hv)
    · obtain ⟨l, hl, hv⟩ := mem_iUnion₂.mp hv
      exact ⟨(mem_closure_sectorSet_iff_of_mem_sectionSet hBC hθ hη hlim hv).mpr hl,
        (mem_image_cylinder.mp hv).1⟩
    · obtain ⟨r, hr, hv⟩ := mem_iUnion₂.mp hv
      exact ⟨(mem_closure_sectorSet_iff_of_mem_sectorSet hBC hθ hlim hv).mpr hr,
        (mem_image_cylinder.mp hv).1⟩

end Real

end BoundaryClosure

/-! ### Both parts of the frontier condition for stacks -/

section FrontierCondition

variable {n k m : ℕ} {C B : Set (Fin n → ℝ)}
  {θ : Fin k → C → ℝ} {η : Fin m → B → ℝ} {σ : Fin k → Fin m}

/-- **Frontier condition, part 1 (across strata).** Under section boundary matching from `C` to
`B ⊆ closure C`, any cell `E' ∈ stackCells B η` meeting `closure E` for `E ∈ stackCells C θ` is
contained in `closure E`. -/
theorem subset_closure_of_mem_stackCells_of_nonempty_inter (hBC : B ⊆ closure C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells B η)
    (hne : (E' ∩ closure E).Nonempty) : E' ⊆ closure E := by
  obtain ⟨v, hvE', hvcl⟩ := hne
  rcases mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · have hxB : Fin.tail v ∈ B := by
      rcases mem_stackCells.mp hE' with ⟨l, rfl⟩ | ⟨r, rfl⟩ <;> exact (mem_image_cylinder.mp hvE').1
    have hv_sec : v ∈ cylinder B '' sectionSet η (σ i) := by
      rw [← closure_image_cylinder_sectionSet_inter_eq hBC hlim i]
      exact ⟨hvcl, hxB⟩
    have hEq : E' = cylinder B '' sectionSet η (σ i) :=
      (pairwiseDisjoint_stackCells fun x ↦ (hη x).injective).eq hE'
        (image_cylinder_sectionSet_mem_stackCells (σ i)) (not_disjoint_iff.mpr ⟨v, hvE', hv_sec⟩)
    rw [hEq, ← closure_image_cylinder_sectionSet_inter_eq hBC hlim i]
    exact inter_subset_left
  · rcases mem_stackCells.mp hE' with ⟨l, rfl⟩ | ⟨r, rfl⟩
    · have hl := (mem_closure_sectorSet_iff_of_mem_sectionSet hBC hθ hη hlim hvE').mp hvcl
      exact fun w hw ↦ (mem_closure_sectorSet_iff_of_mem_sectionSet hBC hθ hη hlim hw).mpr hl
    · have hr := (mem_closure_sectorSet_iff_of_mem_sectorSet hBC hθ hlim hvE').mp hvcl
      exact fun w hw ↦ (mem_closure_sectorSet_iff_of_mem_sectorSet hBC hθ hlim hw).mpr hr

/-- **Frontier condition, part 1 (same base).** Over a single base `C`, any cell `E'` of a
continuous strictly ordered stack meeting `closure E` for another cell `E` of the same stack is
contained in `closure E`. -/
theorem subset_closure_of_mem_stackCells_self_of_nonempty_inter
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells C θ)
    (hne : (E' ∩ closure E).Nonempty) : E' ⊆ closure E :=
  subset_closure_of_mem_stackCells_of_nonempty_inter (σ := id) subset_closure hθ hθ
    (fun i x ↦ by rw [← nhds_subtype]; exact (hc i).tendsto x) hE hE' hne

/-- Over a nonempty base `C`, if two distinct cells `E' ≠ E` of a continuous strictly ordered
stack satisfy `E' ⊆ closure E`, then `E` is a sector and `E'` is either its lower or its upper
bounding section. -/
theorem eq_sectionSet_and_eq_sectorSet_of_subset_closure_of_ne (hC : C.Nonempty)
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells C θ)
    (hsub : E' ⊆ closure E) (hne : E' ≠ E) :
    ∃ (i : Fin k) (j : Fin (k + 1)),
      (i.succ = j ∨ i.castSucc = j) ∧
        E' = cylinder C '' sectionSet θ i ∧ E = cylinder C '' sectorSet θ j := by
  have hlim : ∀ i (x : C), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (θ (id i) x)) :=
    fun i x ↦ by rw [← nhds_subtype]; exact (hc i).tendsto x
  have : Nonempty C := hC.to_subtype
  have hE'_ne : E'.Nonempty := by
    rcases mem_stackCells.mp hE' with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (sectionSet_nonempty θ i).image _
    · exact (sectorSet_nonempty hθ j).image _
  obtain ⟨v, hvE'⟩ := hE'_ne
  have hvC : Fin.tail v ∈ C := by
    rcases mem_stackCells.mp hE' with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> exact (mem_image_cylinder.mp hvE').1
  rcases mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · have hvE : v ∈ cylinder C '' sectionSet θ i := by
      have htr := closure_image_cylinder_sectionSet_inter_eq (σ := id) subset_closure hlim i
      exact htr ▸ ⟨hsub hvE', hvC⟩
    exact absurd ((pairwiseDisjoint_stackCells fun y ↦ (hθ y).injective).eq hE'
      (image_cylinder_sectionSet_mem_stackCells i) (not_disjoint_iff.mpr ⟨v, hvE', hvE⟩)) hne
  · rcases mem_stackCells.mp hE' with ⟨i, rfl⟩ | ⟨r, rfl⟩
    · obtain ⟨hlow, hhigh⟩ :=
        (mem_closure_sectorSet_iff_of_mem_sectionSet subset_closure hθ hθ hlim hvE').mp (hsub hvE')
      refine ⟨i, j, ?_, rfl, rfl⟩
      rcases lt_trichotomy i.castSucc j with hij | hij | hij
      · have hij_val : i.val + 1 ≤ j.val := Nat.succ_le_of_lt (Fin.lt_def.mp hij)
        rcases eq_or_lt_of_le hij_val with heq | hlt
        · exact Or.inl (Fin.ext heq)
        · exfalso
          have hi'_lt : i.val + 1 < k := by omega
          let i' : Fin k := ⟨i.val + 1, hi'_lt⟩
          have hi' : i'.castSucc < j := Fin.lt_def.mpr hlt
          exact Nat.not_succ_le_self i.val (Fin.le_def.mp (hlow i' hi'))
      · exact Or.inr hij
      · exfalso
        let i' : Fin k := ⟨j.val, by omega⟩
        have hi' : j ≤ i'.castSucc := le_rfl
        exact (not_le_of_gt hij) (Fin.castSucc_le_castSucc_iff.mpr (hhigh i' hi'))
    · obtain ⟨hlow, hhigh⟩ :=
        (mem_closure_sectorSet_iff_of_mem_sectorSet subset_closure hθ hlim hvE').mp (hsub hvE')
      exfalso
      refine hne (congrArg (cylinder C '' sectorSet θ ·) (le_antisymm ?_ ?_))
      · by_contra hlt
        replace hlt := lt_of_not_ge hlt
        let i' : Fin k := ⟨j.val, by omega⟩
        exact (not_le_of_gt hlt) (hhigh i' le_rfl)
      · by_contra hlt
        replace hlt := lt_of_not_ge hlt
        let i' : Fin k := ⟨r.val, by omega⟩
        exact (lt_irrefl r) (hlow i' hlt)

/-- **Frontier condition, part 2 (across lower-dimensional strata).** Let `C` and `B` be analytic
submanifolds with `B ⊆ closure C` and `dB < dC`, carrying strictly ordered stacks whose sections
are analytic on their bases and match along `B`. If `E ∈ stackCells C θ` and
`E' ∈ stackCells B η` satisfy `E' ⊆ closure E`, then `dim E' < dim E`. -/
theorem dim_lt_of_mem_stackCells_of_subset_closure {dC dB e e' : ℕ}
    (hC : IsAnalyticSubmanifold dC C) (hB : IsAnalyticSubmanifold dB B)
    (hBC : B ⊆ closure C) (hd : dB < dC)
    (haC : ∀ i, ∃ r, (∀ y : C, r y = θ i y) ∧ AnalyticOnSubmanifold dC r C)
    (haB : ∀ l, ∃ r, (∀ x : B, r x = η l x) ∧ AnalyticOnSubmanifold dB r B)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells B η)
    (hE_sub : IsAnalyticSubmanifold e E) (hE'_sub : IsAnalyticSubmanifold e' E')
    (hsub : E' ⊆ closure E) : e' < e := by
  have hcC (i : Fin k) : Continuous (θ i) := by
    obtain ⟨r, hr, har⟩ := haC i
    exact (continuousOn_iff_continuous_domRestrict.mp har.continuousOn).congr hr
  have hcB (l : Fin m) : Continuous (η l) := by
    obtain ⟨r, hr, har⟩ := haB l
    exact (continuousOn_iff_continuous_domRestrict.mp har.continuousOn).congr hr
  have he' : e' = dB ∨ e' = dB + 1 := by
    rcases mem_stackCells.mp hE' with ⟨l, rfl⟩ | ⟨r, rfl⟩
    · obtain ⟨fn, hfn, hafn⟩ := haB l
      exact Or.inl (hE'_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectionSet hB l hfn hafn))
    · exact Or.inr (hE'_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectorSet hB hcB hη r))
  rcases mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · obtain ⟨fn, hfn, hafn⟩ := haC i
    have he : e = dC :=
      hE_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectionSet hC i hfn hafn)
    obtain ⟨v, hvE'⟩ := hE'_sub.nonempty
    have hxB : Fin.tail v ∈ B := by
      rcases mem_stackCells.mp hE' with ⟨l, rfl⟩ | ⟨r, rfl⟩ <;> exact (mem_image_cylinder.mp hvE').1
    have hv_sec : v ∈ cylinder B '' sectionSet η (σ i) := by
      rw [← closure_image_cylinder_sectionSet_inter_eq hBC hlim i]
      exact ⟨hsub hvE', hxB⟩
    have hEq : E' = cylinder B '' sectionSet η (σ i) :=
      (pairwiseDisjoint_stackCells fun x ↦ (hη x).injective).eq hE'
        (image_cylinder_sectionSet_mem_stackCells (σ i)) (not_disjoint_iff.mpr ⟨v, hvE', hv_sec⟩)
    obtain ⟨fnB, hfnB, hafnB⟩ := haB (σ i)
    have he'_eq : e' = dB := hE'_sub.dim_eq
      (hEq ▸ isAnalyticSubmanifold_image_cylinder_sectionSet hB (σ i) hfnB hafnB)
    omega
  · have he : e = dC + 1 :=
      hE_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectorSet hC hcC hθ j)
    rcases he' with rfl | rfl <;> omega

/-- **Frontier condition, part 2 (same base).** Over an analytic submanifold `C`, if two distinct
cells `E' ≠ E` of an analytic-section stack satisfy `E' ⊆ closure E`, then `dim E' < dim E`
(`dim E' = dC < dC + 1 = dim E`). -/
theorem dim_lt_of_mem_stackCells_self_of_subset_closure {dC e e' : ℕ}
    (hC : IsAnalyticSubmanifold dC C)
    (haC : ∀ i, ∃ r, (∀ y : C, r y = θ i y) ∧ AnalyticOnSubmanifold dC r C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells C θ)
    (hE_sub : IsAnalyticSubmanifold e E) (hE'_sub : IsAnalyticSubmanifold e' E')
    (hsub : E' ⊆ closure E) (hne : E' ≠ E) : e' < e := by
  have hcC (i : Fin k) : Continuous (θ i) := by
    obtain ⟨r, hr, har⟩ := haC i
    exact (continuousOn_iff_continuous_domRestrict.mp har.continuousOn).congr hr
  obtain ⟨i, j, -, rfl, rfl⟩ :=
    eq_sectionSet_and_eq_sectorSet_of_subset_closure_of_ne hC.nonempty hcC hθ hE hE' hsub hne
  obtain ⟨fn, hfn, hafn⟩ := haC i
  have he' : e' = dC :=
    hE'_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectionSet hC i hfn hafn)
  have he : e = dC + 1 :=
    hE_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectorSet hC hcC hθ j)
  omega

end FrontierCondition

/-! ### Lifting preconnected approach regions through stacks -/

section ApproachRegions

variable {n k : ℕ} {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}

private lemma image_cylinder_sectorSet_inter_eq_image_lineMap {j : Fin (k + 1)}
    {U : Set (Fin n → ℝ)} {a b : ℝ} {low high : C → ℝ}
    (hlt : ∀ y : C, y.1 ∈ U → low y < high y)
    (hIoo : ∀ (y : C) (r : ℝ),
      r ∈ Ioo (low y) (high y) ↔ (y, r) ∈ sectorSet θ j ∧ r ∈ Ioo a b) :
    (cylinder C '' sectorSet θ j) ∩ {v | Fin.tail v ∈ U ∧ v 0 ∈ Ioo a b} =
      (fun p : C × ℝ ↦ Fin.cons (AffineMap.lineMap (low p.1) (high p.1) p.2) p.1.1) ''
        (((Subtype.val : C → _) ⁻¹' U) ×ˢ Ioo (0 : ℝ) 1) := by
  ext v
  rw [mem_inter_iff, mem_image_cylinder, mem_image]
  simp only [mem_prod, mem_preimage, Prod.exists]
  constructor
  · rintro ⟨⟨hxC, hv_sec⟩, hxt, hv_Ioo⟩
    let y : C := ⟨Fin.tail v, hxC⟩
    have hr : v 0 ∈ AffineMap.lineMap (low y) (high y) '' Ioo (0 : ℝ) 1 := by
      rw [← openSegment_eq_image_lineMap, openSegment_eq_Ioo (hlt y hxt), hIoo]
      exact ⟨hv_sec, hv_Ioo⟩
    obtain ⟨c, hcIoo, hcv⟩ := hr
    exact ⟨y, c, ⟨hxt, hcIoo⟩, by simp [hcv, y, Fin.cons_self_tail]⟩
  · rintro ⟨y, c, ⟨hyt, hcIoo⟩, rfl⟩
    have hr : AffineMap.lineMap (low y) (high y) c ∈ Ioo (low y) (high y) := by
      rw [← openSegment_eq_Ioo (hlt y hyt), openSegment_eq_image_lineMap]
      exact mem_image_of_mem _ hcIoo
    obtain ⟨hsec, hv_Ioo⟩ := (hIoo y _).mp hr
    exact ⟨⟨y.2, hsec⟩, hyt, hv_Ioo⟩

/-- An ambient section of a continuous function `θ i` inherits preconnected approach regions at
`v₀` whenever the base `C` has preconnected approach regions at `Fin.tail v₀` and `θ i` has a
limit along `C` at `Fin.tail v₀`. -/
theorem isPreconnectedApproachAt_image_cylinder_sectionSet (i : Fin k) (hc : Continuous (θ i))
    {v₀ : Fin (n + 1) → ℝ} (hconn : IsPreconnectedApproachAt C (Fin.tail v₀))
    (hlim : ∃ L, Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v₀))) (𝓝 L)) :
    IsPreconnectedApproachAt (cylinder C '' sectionSet θ i) v₀ := by
  by_cases hv₀ : v₀ ∈ closure (cylinder C '' sectionSet θ i)
  · obtain ⟨L, hL⟩ := hlim
    have hx_cl : Fin.tail v₀ ∈ closure C := by
      have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
      have hmem := image_closure_subset_closure_image htail (mem_image_of_mem Fin.tail hv₀)
      refine closure_mono ?_ hmem
      rw [image_tail_image_cylinder, fst_image_sectionSet, Subtype.coe_image_univ]
    have hLv₀ : L = v₀ 0 := by
      have hsec_eq : sectionSet (fun _ : Fin 1 ↦ θ i) 0 = sectionSet θ i := by
        ext ⟨y, t⟩
        simp only [mem_sectionSet]
      have htr := closure_image_cylinder_sectionSet_inter_eq
        (B := {Fin.tail v₀}) (θ := fun _ : Fin 1 ↦ θ i) (η := fun _ : Fin 1 ↦ fun _ ↦ L)
        (σ := id) (singleton_subset_iff.mpr hx_cl)
        (fun _ x ↦ by simpa [mem_singleton_iff.mp x.2] using hL) 0
      have hv_in :
          v₀ ∈ cylinder {Fin.tail v₀} '' sectionSet (fun _ : Fin 1 ↦ fun _ ↦ L) (id 0) := by
        rw [← htr, hsec_eq]
        exact ⟨hv₀, rfl⟩
      exact mem_sectionSet.mp (mem_image_cylinder.mp hv_in).2
    subst hLv₀
    refine isPreconnectedApproachAt_def.mpr fun s hs ↦ ?_
    obtain ⟨G, hG, W, hW, hGW⟩ := mem_nhds_prod_iff.mp <|
      (by fun_prop : Continuous fun p : (Fin n → ℝ) × ℝ ↦
        (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)).continuousAt
          (x := (Fin.tail v₀, v₀ 0)) |>.preimage_mem_nhds
        (by simpa only [Fin.cons_self_tail] using hs)
    obtain ⟨G₁, hG₁, hG₁W⟩ := mem_comap.mp (hL.eventually hW)
    obtain ⟨t_base, ht_nhds, ht_sub, ht_pre⟩ :=
      isPreconnectedApproachAt_def.mp hconn (G ∩ G₁) (inter_mem hG hG₁)
    have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
    refine ⟨{v | Fin.tail v ∈ t_base ∧ v 0 ∈ W},
      inter_mem (htail.continuousAt.preimage_mem_nhds ht_nhds)
        ((continuous_apply 0).continuousAt.preimage_mem_nhds hW),
      fun v hv ↦ by
        simpa only [mem_preimage, Fin.cons_self_tail] using
          hGW (mk_mem_prod (ht_sub hv.1).1 hv.2), ?_⟩
    have hA_pre : IsPreconnected ((Subtype.val : C → _) ⁻¹' t_base) :=
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        (by rwa [Subtype.image_preimage_val])
    have heq : (cylinder C '' sectionSet θ i) ∩ {v | Fin.tail v ∈ t_base ∧ v 0 ∈ W} =
        (fun y : C ↦ (Fin.cons (θ i y) y.1 : Fin (n + 1) → ℝ)) ''
          ((Subtype.val : C → _) ⁻¹' t_base) := by
      ext v
      rw [mem_inter_iff, mem_image_cylinder, mem_image]
      simp only [mem_sectionSet, mem_preimage]
      constructor
      · rintro ⟨⟨hxC, hθv⟩, hxt, -⟩
        exact ⟨⟨Fin.tail v, hxC⟩, hxt, by rw [hθv, Fin.cons_self_tail]⟩
      · rintro ⟨y, hyt, rfl⟩
        exact ⟨⟨y.2, rfl⟩, hyt, hG₁W (ht_sub hyt).2⟩
    rw [heq]
    exact hA_pre.image _
      (by fun_prop : Continuous fun y : C ↦ (Fin.cons (θ i y) y.1 : Fin (n + 1) → ℝ)).continuousOn
  · exact isPreconnectedApproachAt_of_notMem_closure hv₀

private lemma exists_continuous_Ioo_eq_sectorSet_inter
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (j : Fin (k + 1)) {x₀ : Fin n → ℝ} {t₀ δ : ℝ} (hδ : 0 < δ) {L : Fin k → ℝ}
    (hlim : ∀ i, Tendsto (θ i) (comap Subtype.val (𝓝 x₀)) (𝓝 (L i)))
    (hlow₀ : ∀ i : Fin k, i.castSucc < j → L i ≤ t₀)
    (hhigh₀ : ∀ i : Fin k, j ≤ i.castSucc → t₀ ≤ L i) :
    ∃ (low high : C → ℝ) (G₁ : Set (Fin n → ℝ)),
      G₁ ∈ 𝓝 x₀ ∧ Continuous low ∧ Continuous high ∧
      (∀ y : C, y.1 ∈ G₁ → low y < high y) ∧
      ∀ (y : C) (r : ℝ),
        r ∈ Ioo (low y) (high y) ↔ (y, r) ∈ sectorSet θ j ∧ r ∈ Ioo (t₀ - δ) (t₀ + δ) := by
  cases k with
  | zero =>
    refine ⟨fun _ ↦ t₀ - δ, fun _ ↦ t₀ + δ, univ, univ_mem,
      continuous_const, continuous_const, fun _ _ ↦ by linarith, fun y r ↦ ?_⟩
    simp [sectorSet_fin_zero]
  | succ k =>
    have hm : ∀ y : C, Monotone fun i ↦ θ i y := fun y ↦ (hθ y).monotone
    cases j using Fin.cases with
    | zero =>
      obtain ⟨G₁, hG₁, hG₁_lt⟩ := mem_comap.mp <|
        (hlim 0).eventually (Ioi_mem_nhds (by linarith [hhigh₀ 0 (Fin.zero_le _)] : t₀ - δ < L 0))
      refine ⟨fun _ ↦ t₀ - δ, fun y ↦ min (t₀ + δ) (θ 0 y), G₁, hG₁,
        continuous_const, continuous_const.min (hc 0),
        fun y hy ↦ lt_min (by linarith) (hG₁_lt hy), fun y r ↦ ?_⟩
      simp only [mem_Ioo, lt_min_iff, sectorSet_zero hm, mem_ofPred_eq]
      tauto
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        have hltL : L (Fin.last k) < t₀ + δ :=
          by linarith [hlow₀ (Fin.last k) (Fin.castSucc_lt_last _)]
        obtain ⟨G₁, hG₁, hG₁_lt⟩ := mem_comap.mp <|
          (hlim (Fin.last k)).eventually (Iio_mem_nhds hltL)
        refine ⟨fun y ↦ max (t₀ - δ) (θ (Fin.last k) y), fun _ ↦ t₀ + δ, G₁, hG₁,
          continuous_const.max (hc (Fin.last k)), continuous_const,
          fun y hy ↦ max_lt (by linarith) (hG₁_lt hy), fun y r ↦ ?_⟩
        simp only [mem_Ioo, max_lt_iff, Fin.succ_last, sectorSet_last hm, mem_ofPred_eq]
        tauto
      | cast i₀ =>
        have hlt₁ : L i₀.castSucc < t₀ + δ :=
          by linarith [hlow₀ i₀.castSucc Fin.castSucc_lt_succ]
        have hlt₂ : t₀ - δ < L i₀.succ := by linarith [hhigh₀ i₀.succ le_rfl]
        obtain ⟨G₁, hG₁, hG₁_lt⟩ := mem_comap.mp <|
          ((hlim i₀.castSucc).eventually (Iio_mem_nhds hlt₁)).and
            ((hlim i₀.succ).eventually (Ioi_mem_nhds hlt₂))
        refine ⟨fun y ↦ max (t₀ - δ) (θ i₀.castSucc y), fun y ↦ min (t₀ + δ) (θ i₀.succ y),
          G₁, hG₁, continuous_const.max (hc i₀.castSucc), continuous_const.min (hc i₀.succ),
          fun y hy ↦ ?_, fun y r ↦ ?_⟩
        · exact max_lt (lt_min (by linarith) (hG₁_lt hy).2)
            (lt_min (hG₁_lt hy).1 (hθ y i₀.castSucc_lt_succ))
        · simp only [mem_Ioo, max_lt_iff, lt_min_iff, sectorSet_castSucc_succ hm, mem_ofPred_eq]
          tauto

/-- An ambient sector of a continuous strictly ordered stack inherits preconnected approach
regions at `v₀` whenever the base `C` has preconnected approach regions at `Fin.tail v₀` and all
sections `θ i` have finite limits along `C` at `Fin.tail v₀`. Coalescing limits at `Fin.tail v₀`
are allowed. -/
theorem isPreconnectedApproachAt_image_cylinder_sectorSet (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) (j : Fin (k + 1))
    {v₀ : Fin (n + 1) → ℝ} (hconn : IsPreconnectedApproachAt C (Fin.tail v₀))
    (hlim : ∀ i, ∃ L, Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v₀))) (𝓝 L)) :
    IsPreconnectedApproachAt (cylinder C '' sectorSet θ j) v₀ := by
  by_cases hv₀ : v₀ ∈ closure (cylinder C '' sectorSet θ j)
  · choose L hL using hlim
    have hx_cl : Fin.tail v₀ ∈ closure C :=
      tail_mem_closure_of_mem_closure_stackCells hθ (image_cylinder_sectorSet_mem_stackCells j) hv₀
    have hbounds : (∀ i : Fin k, i.castSucc < j → L i ≤ v₀ 0) ∧
        ∀ i : Fin k, j ≤ i.castSucc → v₀ 0 ≤ L i := by
      have htr := closure_image_cylinder_sectorSet_inter_eq
        (B := {Fin.tail v₀}) (θ := θ) (η := fun i _ ↦ L i) (σ := id)
        (singleton_subset_iff.mpr hx_cl) hθ
        (fun i x ↦ by simpa [mem_singleton_iff.mp x.2] using hL i) j
      have hv_in : v₀ ∈ closure (cylinder C '' sectorSet θ j) ∩
          {v | Fin.tail v ∈ ({Fin.tail v₀} : Set _)} := ⟨hv₀, rfl⟩
      rw [htr] at hv_in
      obtain ⟨_, h₁, h₂⟩ := hv_in
      exact ⟨h₁, h₂⟩
    refine isPreconnectedApproachAt_def.mpr fun s hs ↦ ?_
    obtain ⟨G, hG, W, hW, hGW⟩ := mem_nhds_prod_iff.mp <|
      (by fun_prop : Continuous fun p : (Fin n → ℝ) × ℝ ↦
        (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)).continuousAt
          (x := (Fin.tail v₀, v₀ 0)) |>.preimage_mem_nhds
        (by simpa only [Fin.cons_self_tail] using hs)
    obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
    have hIooW : Ioo (v₀ 0 - δ) (v₀ 0 + δ) ⊆ W := by simpa only [Real.ball_eq_Ioo] using hδW
    obtain ⟨low, high, G₁, hG₁, hlow_c, hhigh_c, hlt_G₁, hIoo_eq⟩ :=
      exists_continuous_Ioo_eq_sectorSet_inter hc hθ j hδ hL hbounds.1 hbounds.2
    obtain ⟨t_base, ht_nhds, ht_sub, ht_pre⟩ :=
      isPreconnectedApproachAt_def.mp hconn (G ∩ G₁) (inter_mem hG hG₁)
    have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
    refine ⟨{v | Fin.tail v ∈ t_base ∧ v 0 ∈ Ioo (v₀ 0 - δ) (v₀ 0 + δ)},
      inter_mem (htail.continuousAt.preimage_mem_nhds ht_nhds)
        ((continuous_apply 0).continuousAt.preimage_mem_nhds
          (Ioo_mem_nhds (by linarith) (by linarith))),
      fun v hv ↦ by
        simpa only [mem_preimage, Fin.cons_self_tail] using
          hGW (mk_mem_prod (ht_sub hv.1).1 (hIooW hv.2)), ?_⟩
    have hA_pre : IsPreconnected ((Subtype.val : C → _) ⁻¹' t_base) :=
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        (by rwa [Subtype.image_preimage_val])
    rw [image_cylinder_sectorSet_inter_eq_image_lineMap
      (fun y hy ↦ hlt_G₁ y (ht_sub hy).2) hIoo_eq]
    exact (hA_pre.prod isPreconnected_Ioo).image _
      (by simp only [AffineMap.lineMap_apply_ring]; fun_prop :
        Continuous fun p : C × ℝ ↦
          (Fin.cons (AffineMap.lineMap (low p.1) (high p.1) p.2) p.1.1 :
            Fin (n + 1) → ℝ)).continuousOn
  · exact isPreconnectedApproachAt_of_notMem_closure hv₀

/-- Every ambient cell of a continuous strictly ordered stack over `C` inherits preconnected
approach regions at `v₀` whenever `C` has preconnected approach regions at `Fin.tail v₀` and
every section `θ i` has a finite limit along `C` at `Fin.tail v₀`. -/
theorem isPreconnectedApproachAt_of_mem_stackCells (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) {E : Set (Fin (n + 1) → ℝ)}
    (hE : E ∈ stackCells C θ) {v₀ : Fin (n + 1) → ℝ}
    (hconn : IsPreconnectedApproachAt C (Fin.tail v₀))
    (hlim : ∀ i, ∃ L, Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v₀))) (𝓝 L)) :
    IsPreconnectedApproachAt E v₀ := by
  rcases mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact isPreconnectedApproachAt_image_cylinder_sectionSet i (hc i) hconn (hlim i)
  · exact isPreconnectedApproachAt_image_cylinder_sectorSet hc hθ j hconn hlim

/-- At any point `v₀` whose base projection already lies in `C`, continuity of the sections
supplies their limits automatically, so `IsPreconnectedApproachAt` lifts directly from `C` to
every cell of `stackCells C θ`. -/
theorem isPreconnectedApproachAt_of_mem_stackCells_of_tail_mem (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) {E : Set (Fin (n + 1) → ℝ)}
    (hE : E ∈ stackCells C θ) {v₀ : Fin (n + 1) → ℝ} (hx : Fin.tail v₀ ∈ C)
    (hconn : IsPreconnectedApproachAt C (Fin.tail v₀)) :
    IsPreconnectedApproachAt E v₀ :=
  let x : C := ⟨Fin.tail v₀, hx⟩
  isPreconnectedApproachAt_of_mem_stackCells hc hθ hE hconn fun i ↦
    ⟨θ i x, by rw [← nhds_subtype C x]; exact (hc i).tendsto x⟩

end ApproachRegions

/-! ### Frontier root matching for polynomial delineations -/

namespace Delineation

variable {n : ℕ} {ι : Type*} {C B : Set (Fin n → ℝ)} {P : ι → (Fin n → ℝ) → ℝ[X]}

/-- **Frontier root matching for delineations.** Let `D_C` and `D_B` be delineations of `P` over
`C` and over a connected boundary set `B ⊆ closure C` along which `C` has preconnected approach
regions. Suppose each root section `i` of `D_C` has positive multiplicity in some member `P k`
that does not vanish on `B` and whose coefficients up to `(P k x).natDegree` converge along
`𝓝[C] x` without degree increase. Then there exists a monotone map
`σ : Fin D_C.count → Fin D_B.count` matching the boundary limits of every root section of `D_C`
to a root section of `D_B`. -/
theorem exists_root_tendsto_of_subset_closure
    (D_C : Delineation fun k (y : C) ↦ P k y)
    (D_B : Delineation fun k (x : B) ↦ P k x)
    (hBC : B ⊆ closure C) (hB_conn : IsConnected B)
    (hconn : ∀ x ∈ B, IsPreconnectedApproachAt C x)
    (hwit : ∀ i : Fin D_C.count, ∃ k, 0 < D_C.multiplicity k i ∧ (∀ x ∈ B, P k x ≠ 0) ∧
      (∀ x ∈ B, ∀ d ≤ (P k x).natDegree,
        Tendsto (fun y ↦ (P k y).coeff d) (𝓝[C] x) (𝓝 ((P k x).coeff d))) ∧
      ∀ x ∈ B, ∀ᶠ y in 𝓝[C] x, (P k y).natDegree ≤ (P k x).natDegree) :
    ∃ σ : Fin D_C.count → Fin D_B.count, Monotone σ ∧
      ∀ i (x : B), Tendsto (D_C.root i) (comap Subtype.val (𝓝 x.1)) (𝓝 (D_B.root (σ i) x)) := by
  have : ConnectedSpace B := isConnected_iff_connectedSpace.mp hB_conn
  have hsec (i : Fin D_C.count) :
      ∃ l : Fin D_B.count, ∀ x : B,
        Tendsto (D_C.root i) (comap Subtype.val (𝓝 x.1)) (𝓝 (D_B.root l x)) := by
    obtain ⟨k, hmult, hne, hcoeff, hdeg⟩ := hwit i
    let f : (Fin n → ℝ) → ℝ := Function.extend Subtype.val (D_C.root i) 0
    have hf_apply (y : C) : f y.1 = D_C.root i y := Subtype.val_injective.extend_apply _ _ y
    have hf_cont : ContinuousOn f C :=
      continuousOn_iff_continuous_domRestrict.mpr <| (D_C.continuous_root i).congr fun y ↦
        (hf_apply y).symm
    have hf_root (y : Fin n → ℝ) (hy : y ∈ C) : (P k y).eval (f y) = 0 := by
      rw [hf_apply ⟨y, hy⟩]
      exact ((D_C.multiplicity_pos_iff ⟨y, hy⟩).mp hmult).2
    have hF_cont : ContinuousOn (extendFrom C f) B :=
      continuousOn_extendFrom_of_isRoot_of_subset_closure hBC hconn hf_cont hf_root hcoeff hdeg hne
    have hF_root (x : B) : (P k x.1).eval (extendFrom C f x.1) = 0 :=
      eval_extendFrom_eq_zero_of_isRoot (hBC x.2) (hconn x.1 x.2) hf_cont
        (eventually_nhdsWithin_of_forall hf_root) (hcoeff x.1 x.2) (hdeg x.1 x.2) (hne x.1 x.2)
    obtain ⟨l, hl⟩ := D_B.exists_eq_root_of_continuous
      (continuousOn_iff_continuous_domRestrict.mp hF_cont) (fun x ↦ hne x.1 x.2) hF_root
    refine ⟨l, fun x ↦ ?_⟩
    have hF_lim : Tendsto f (𝓝[C] x.1) (𝓝 (extendFrom C f x.1)) :=
      tendsto_extendFrom_of_isRoot (hBC x.2) (hconn x.1 x.2) hf_cont
        (eventually_nhdsWithin_of_forall hf_root) (hcoeff x.1 x.2) (hdeg x.1 x.2) (hne x.1 x.2)
    have hmap : map (Subtype.val : C → Fin n → ℝ) (comap Subtype.val (𝓝 x.1)) = 𝓝[C] x.1 := by
      rw [Filter.map_comap, Subtype.range_val]
      rfl
    have hlim_sub : Tendsto (f ∘ Subtype.val) (comap Subtype.val (𝓝 x.1))
        (𝓝 (extendFrom C f x.1)) := tendsto_map'_iff.mp (hmap.symm ▸ hF_lim)
    have hfeq : f ∘ Subtype.val = D_C.root i := funext hf_apply
    have hlext : extendFrom C f x.1 = D_B.root l x := congrFun hl x
    rwa [hfeq, hlext] at hlim_sub
  choose σ hσ using hsec
  exact ⟨σ, monotone_of_tendsto_section hBC hB_conn.nonempty
    (fun y ↦ (D_C.strictMono_root y).monotone) D_B.strictMono_root hσ, hσ⟩

/-- **Frontier containment for delineations.** Under the hypotheses of
`TauCeti.Delineation.exists_root_tendsto_of_subset_closure`, any cell `E'` of `D_B` meeting
`closure E` for a cell `E` of `D_C` is contained in `closure E`. -/
theorem subset_closure_of_mem_stackCells_of_nonempty_inter
    (D_C : Delineation fun k (y : C) ↦ P k y)
    (D_B : Delineation fun k (x : B) ↦ P k x)
    (hBC : B ⊆ closure C) (hB_conn : IsConnected B)
    (hconn : ∀ x ∈ B, IsPreconnectedApproachAt C x)
    (hwit : ∀ i : Fin D_C.count, ∃ k, 0 < D_C.multiplicity k i ∧ (∀ x ∈ B, P k x ≠ 0) ∧
      (∀ x ∈ B, ∀ d ≤ (P k x).natDegree,
        Tendsto (fun y ↦ (P k y).coeff d) (𝓝[C] x) (𝓝 ((P k x).coeff d))) ∧
      ∀ x ∈ B, ∀ᶠ y in 𝓝[C] x, (P k y).natDegree ≤ (P k x).natDegree)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C D_C.root)
    (hE' : E' ∈ stackCells B D_B.root) (hne : (E' ∩ closure E).Nonempty) :
    E' ⊆ closure E := by
  obtain ⟨σ, -, hσ⟩ := D_C.exists_root_tendsto_of_subset_closure D_B hBC hB_conn hconn hwit
  exact TauCeti.subset_closure_of_mem_stackCells_of_nonempty_inter hBC
    D_C.strictMono_root D_B.strictMono_root hσ hE hE' hne

/-- **Strict dimension drop for delineations.** Over analytic submanifolds `C` and `B` with
`B ⊆ closure C` and `dB < dC`, if `D_C` and `D_B` have intrinsically analytic coefficients and
satisfy the frontier root-matching hypotheses, then `E' ⊆ closure E` implies `dim E' < dim E`. -/
theorem dim_lt_of_mem_stackCells_of_subset_closure {dC dB e e' : ℕ}
    (D_C : Delineation fun k (y : C) ↦ P k y)
    (D_B : Delineation fun k (x : B) ↦ P k x)
    (hC : IsAnalyticSubmanifold dC C) (hB : IsAnalyticSubmanifold dB B)
    (hBC : B ⊆ closure C) (hd : dB < dC) (hB_conn : IsConnected B)
    (hconn : ∀ x ∈ B, IsPreconnectedApproachAt C x)
    (haC : ∀ k j, AnalyticOnSubmanifold dC (fun y ↦ (P k y).coeff j) C)
    (haB : ∀ k j, AnalyticOnSubmanifold dB (fun x ↦ (P k x).coeff j) B)
    (hwit : ∀ i : Fin D_C.count, ∃ k, 0 < D_C.multiplicity k i ∧ (∀ x ∈ B, P k x ≠ 0) ∧
      (∀ x ∈ B, ∀ d ≤ (P k x).natDegree,
        Tendsto (fun y ↦ (P k y).coeff d) (𝓝[C] x) (𝓝 ((P k x).coeff d))) ∧
      ∀ x ∈ B, ∀ᶠ y in 𝓝[C] x, (P k y).natDegree ≤ (P k x).natDegree)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C D_C.root)
    (hE' : E' ∈ stackCells B D_B.root)
    (hE_sub : IsAnalyticSubmanifold e E) (hE'_sub : IsAnalyticSubmanifold e' E')
    (hsub : E' ⊆ closure E) : e' < e := by
  obtain ⟨σ, -, hσ⟩ := D_C.exists_root_tendsto_of_subset_closure D_B hBC hB_conn hconn hwit
  refine TauCeti.dim_lt_of_mem_stackCells_of_subset_closure hC hB hBC hd (fun i ↦ ?_) (fun l ↦ ?_)
    D_C.strictMono_root D_B.strictMono_root hσ hE hE' hE_sub hE'_sub hsub
  · let r := Function.extend Subtype.val (D_C.root i) 0
    have hr (y : C) : r y = D_C.root i y := Subtype.val_injective.extend_apply _ _ y
    exact ⟨r, hr, D_C.analyticOnSubmanifold_root hC haC i hr⟩
  · let r := Function.extend Subtype.val (D_B.root l) 0
    have hr (x : B) : r x = D_B.root l x := Subtype.val_injective.extend_apply _ _ x
    exact ⟨r, hr, D_B.analyticOnSubmanifold_root hB haB l hr⟩

end Delineation

/-! ### Lifting frontier-compatible partitions and open-box restrictions -/

section PartitionLifting

variable {n : ℕ} {W : Set (Fin n → ℝ)} {ℬ : Set (Set (Fin n → ℝ))}
  {k : Set (Fin n → ℝ) → ℕ} {θ : ∀ C : Set (Fin n → ℝ), Fin (k C) → C → ℝ}

/-- **Lifting the first part of the frontier condition.** If `ℬ` satisfies the frontier
containment condition and boundary section matching holds whenever `B ⊆ closure C` (`B ≠ C`),
then the lifted cell family `⋃ C ∈ ℬ, stackCells C (θ C)` also satisfies
`(E' ∩ closure E).Nonempty → E' ⊆ closure E`. -/
theorem subset_closure_of_mem_biUnion_stackCells
    (hfront₁ : ∀ B ∈ ℬ, ∀ C ∈ ℬ, (B ∩ closure C).Nonempty → B ⊆ closure C)
    (hc : ∀ C ∈ ℬ, ∀ i, Continuous (θ C i))
    (hθ : ∀ C ∈ ℬ, ∀ y : C, StrictMono fun i ↦ θ C i y)
    (hmatch : ∀ B ∈ ℬ, ∀ C ∈ ℬ, B ⊆ closure C → B ≠ C →
      ∃ σ : Fin (k C) → Fin (k B),
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.1)) (𝓝 (θ B (σ i) x)))
    {E' E : Set (Fin (n + 1) → ℝ)} (hE' : E' ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    (hE : E ∈ ⋃ C ∈ ℬ, stackCells C (θ C)) (hne : (E' ∩ closure E).Nonempty) :
    E' ⊆ closure E := by
  obtain ⟨B, hB, hE'B⟩ := mem_iUnion₂.mp hE'
  obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.mp hE
  obtain ⟨v, hvE', hvcl⟩ := hne
  have hvB : Fin.tail v ∈ B := by
    rw [← image_tail_of_mem_stackCells (hθ B hB) hE'B]
    exact mem_image_of_mem Fin.tail hvE'
  have hvC_cl : Fin.tail v ∈ closure C :=
    tail_mem_closure_of_mem_closure_stackCells (hθ C hC) hEC hvcl
  have hBC : B ⊆ closure C := hfront₁ B hB C hC ⟨Fin.tail v, hvB, hvC_cl⟩
  by_cases hBC_eq : B = C
  · subst hBC_eq
    exact subset_closure_of_mem_stackCells_self_of_nonempty_inter (hc B hB) (hθ B hB) hEC hE'B
      ⟨v, hvE', hvcl⟩
  · obtain ⟨σ, hσ⟩ := hmatch B hB C hC hBC hBC_eq
    exact subset_closure_of_mem_stackCells_of_nonempty_inter hBC (hθ C hC) (hθ B hB) hσ hEC hE'B
      ⟨v, hvE', hvcl⟩

/-- Inside `{v | Fin.tail v ∈ W}`, the closure of every lifted cell is the union of the lifted
cells contained in its closure. -/
theorem inter_closure_eq_biUnion_of_mem_biUnion_stackCells (hcover : ⋃₀ ℬ = W)
    (hfront₁ : ∀ B ∈ ℬ, ∀ C ∈ ℬ, (B ∩ closure C).Nonempty → B ⊆ closure C)
    (hc : ∀ C ∈ ℬ, ∀ i, Continuous (θ C i))
    (hθ : ∀ C ∈ ℬ, ∀ y : C, StrictMono fun i ↦ θ C i y)
    (hmatch : ∀ B ∈ ℬ, ∀ C ∈ ℬ, B ⊆ closure C → B ≠ C →
      ∃ σ : Fin (k C) → Fin (k B),
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.1)) (𝓝 (θ B (σ i) x)))
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ ⋃ C ∈ ℬ, stackCells C (θ C)) :
    {v : Fin (n + 1) → ℝ | Fin.tail v ∈ W} ∩ closure E =
      ⋃ E' ∈ {E' ∈ ⋃ C ∈ ℬ, stackCells C (θ C) | E' ⊆ closure E}, E' := by
  let ℰ := ⋃ C ∈ ℬ, stackCells C (θ C)
  ext v
  rw [mem_inter_iff, mem_ofPred_eq, mem_iUnion₂]
  constructor
  · rintro ⟨hvW, hvcl⟩
    have hv_cov : v ∈ ⋃₀ ℰ := by
      rw [sUnion_biUnion_stackCells fun C hC y ↦ (hθ C hC y).monotone, hcover]
      exact hvW
    obtain ⟨E', hE', hvE'⟩ := hv_cov
    exact ⟨E', ⟨hE', subset_closure_of_mem_biUnion_stackCells hfront₁ hc hθ hmatch hE' hE
      ⟨v, hvE', hvcl⟩⟩, hvE'⟩
  · rintro ⟨E', ⟨hE', hsub⟩, hvE'⟩
    have hv_cov : v ∈ ⋃₀ ℰ := ⟨E', hE', hvE'⟩
    rw [sUnion_biUnion_stackCells fun C hC y ↦ (hθ C hC y).monotone, hcover] at hv_cov
    exact ⟨hv_cov, hsub hvE'⟩

/-- **Lifting the second part of the frontier condition.** If `ℬ` is a family of analytic
submanifolds satisfying both parts of the frontier condition, and each stack `θ C` has
intrinsically analytic sections and boundary section matching, then `E' ⊆ closure E` and `E' ≠ E`
imply `dim E' < dim E` for any lifted cells `E', E ∈ ⋃ C ∈ ℬ, stackCells C (θ C)`. -/
theorem dim_lt_of_mem_biUnion_stackCells {d : Set (Fin n → ℝ) → ℕ} {e' e : ℕ}
    (hsubm : ∀ C ∈ ℬ, IsAnalyticSubmanifold (d C) C)
    (hfront₁ : ∀ B ∈ ℬ, ∀ C ∈ ℬ, (B ∩ closure C).Nonempty → B ⊆ closure C)
    (hfront₂ : ∀ B ∈ ℬ, ∀ C ∈ ℬ, B ⊆ closure C → B ≠ C → d B < d C)
    (ha : ∀ C ∈ ℬ, ∀ i, ∃ r, (∀ y : C, r y = θ C i y) ∧ AnalyticOnSubmanifold (d C) r C)
    (hθ : ∀ C ∈ ℬ, ∀ y : C, StrictMono fun i ↦ θ C i y)
    (hmatch : ∀ B ∈ ℬ, ∀ C ∈ ℬ, B ⊆ closure C → B ≠ C →
      ∃ σ : Fin (k C) → Fin (k B),
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.1)) (𝓝 (θ B (σ i) x)))
    {E' E : Set (Fin (n + 1) → ℝ)} (hE' : E' ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    (hE : E ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    (hE'_sub : IsAnalyticSubmanifold e' E') (hE_sub : IsAnalyticSubmanifold e E)
    (hsub : E' ⊆ closure E) (hne : E' ≠ E) : e' < e := by
  obtain ⟨B, hB, hE'B⟩ := mem_iUnion₂.mp hE'
  obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.mp hE
  obtain ⟨v, hvE'⟩ := hE'_sub.nonempty
  have hvB : Fin.tail v ∈ B := by
    rw [← image_tail_of_mem_stackCells (hθ B hB) hE'B]
    exact mem_image_of_mem Fin.tail hvE'
  have hvC_cl : Fin.tail v ∈ closure C :=
    tail_mem_closure_of_mem_closure_stackCells (hθ C hC) hEC (hsub hvE')
  have hBC : B ⊆ closure C := hfront₁ B hB C hC ⟨Fin.tail v, hvB, hvC_cl⟩
  by_cases hBC_eq : B = C
  · subst hBC_eq
    exact dim_lt_of_mem_stackCells_self_of_subset_closure (hsubm B hB) (ha B hB) (hθ B hB)
      hEC hE'B hE_sub hE'_sub hsub hne
  · obtain ⟨σ, hσ⟩ := hmatch B hB C hC hBC hBC_eq
    exact dim_lt_of_mem_stackCells_of_subset_closure (hsubm C hC) (hsubm B hB) hBC
      (hfront₂ B hB C hC hBC hBC_eq) (ha C hC) (ha B hB) (hθ C hC) (hθ B hB) hσ
      hEC hE'B hE_sub hE'_sub hsub

/-- **Lifting the preconnected-approach induction invariant.** If `ℬ` covers `W`, satisfies
frontier containment, and every `C ∈ ℬ` has preconnected approach regions at all points of
`W ∩ closure C`, then under boundary section matching every lifted cell `E` has preconnected
approach regions at every point `v₀` with `Fin.tail v₀ ∈ W`. -/
theorem isPreconnectedApproachAt_of_mem_biUnion_stackCells (hcover : ⋃₀ ℬ = W)
    (hfront₁ : ∀ B ∈ ℬ, ∀ C ∈ ℬ, (B ∩ closure C).Nonempty → B ⊆ closure C)
    (hconn : ∀ C ∈ ℬ, ∀ x ∈ W ∩ closure C, IsPreconnectedApproachAt C x)
    (hc : ∀ C ∈ ℬ, ∀ i, Continuous (θ C i))
    (hθ : ∀ C ∈ ℬ, ∀ y : C, StrictMono fun i ↦ θ C i y)
    (hmatch : ∀ B ∈ ℬ, ∀ C ∈ ℬ, B ⊆ closure C → B ≠ C →
      ∃ σ : Fin (k C) → Fin (k B),
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.1)) (𝓝 (θ B (σ i) x)))
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    {v₀ : Fin (n + 1) → ℝ} (hv₀W : Fin.tail v₀ ∈ W) :
    IsPreconnectedApproachAt E v₀ := by
  by_cases hv₀_cl : v₀ ∈ closure E
  · obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.mp hE
    obtain ⟨B, hB, hvB⟩ := mem_sUnion.mp (hcover.symm ▸ hv₀W)
    have hvC_cl : Fin.tail v₀ ∈ closure C :=
      tail_mem_closure_of_mem_closure_stackCells (hθ C hC) hEC hv₀_cl
    have hBC : B ⊆ closure C := hfront₁ B hB C hC ⟨Fin.tail v₀, hvB, hvC_cl⟩
    have hconnC : IsPreconnectedApproachAt C (Fin.tail v₀) :=
      hconn C hC (Fin.tail v₀) ⟨hv₀W, hvC_cl⟩
    by_cases hBC_eq : B = C
    · subst hBC_eq
      exact isPreconnectedApproachAt_of_mem_stackCells_of_tail_mem (hc B hB) (hθ B hB) hEC hvB
        hconnC
    · obtain ⟨σ, hσ⟩ := hmatch B hB C hC hBC hBC_eq
      exact isPreconnectedApproachAt_of_mem_stackCells (hc C hC) (hθ C hC) hEC hconnC fun i ↦
        ⟨θ B (σ i) ⟨Fin.tail v₀, hvB⟩, hσ i ⟨Fin.tail v₀, hvB⟩⟩
  · exact isPreconnectedApproachAt_of_notMem_closure hv₀_cl

private lemma exists_continuous_Ioo_eq_sectorSet_inter_of_mem_Ioo {k : ℕ} {C : Set (Fin n → ℝ)}
    {θ : Fin k → C → ℝ} {a b : ℝ} (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) (hab : a < b)
    (hbnd : ∀ i (y : C), θ i y ∈ Ioo a b) (j : Fin (k + 1)) :
    ∃ low high : C → ℝ, Continuous low ∧ Continuous high ∧ (∀ y : C, low y < high y) ∧
      ∀ (y : C) (r : ℝ), r ∈ Ioo (low y) (high y) ↔ (y, r) ∈ sectorSet θ j ∧ r ∈ Ioo a b := by
  cases k with
  | zero =>
    exact ⟨fun _ ↦ a, fun _ ↦ b, continuous_const, continuous_const, fun _ ↦ hab,
      fun _ r ↦ by simp [sectorSet_fin_zero]⟩
  | succ k =>
    have hm : ∀ y : C, Monotone fun i ↦ θ i y := fun y ↦ (hθ y).monotone
    cases j using Fin.cases with
    | zero =>
      refine ⟨fun _ ↦ a, θ 0, continuous_const, hc 0, fun y ↦ (hbnd 0 y).1, fun y r ↦ ?_⟩
      simp only [mem_Ioo, sectorSet_zero hm, mem_ofPred_eq]
      exact ⟨fun h ↦ ⟨h.2, h.1, h.2.trans (hbnd 0 y).2⟩, fun h ↦ ⟨h.2.1, h.1⟩⟩
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        refine ⟨θ (Fin.last k), fun _ ↦ b, hc (Fin.last k), continuous_const,
          fun y ↦ (hbnd (Fin.last k) y).2, fun y r ↦ ?_⟩
        simp only [mem_Ioo, Fin.succ_last, sectorSet_last hm, mem_ofPred_eq]
        exact ⟨fun h ↦ ⟨h.1, (hbnd (Fin.last k) y).1.trans h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
      | cast i₀ =>
        refine ⟨θ i₀.castSucc, θ i₀.succ, hc i₀.castSucc, hc i₀.succ,
          fun y ↦ hθ y i₀.castSucc_lt_succ, fun y r ↦ ?_⟩
        simp only [mem_Ioo, sectorSet_castSucc_succ hm, mem_ofPred_eq]
        exact ⟨fun h ↦ ⟨h, (hbnd i₀.castSucc y).1.trans h.1, h.2.trans (hbnd i₀.succ y).2⟩,
          fun h ↦ h.1⟩

/-- When all section values of a continuous strictly ordered stack over a connected base `C` lie
strictly inside an open interval `Ioo a b` (`a < b`), intersecting any cell `E ∈ stackCells C θ`
with the open slab `{v | v 0 ∈ Ioo a b}` yields a connected (hence nonempty) set. -/
theorem isConnected_inter_Ioo_of_mem_stackCells {k : ℕ} {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}
    {a b : ℝ} (hC : IsConnected C) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) (hab : a < b)
    (hbnd : ∀ i (y : C), θ i y ∈ Ioo a b) {E : Set (Fin (n + 1) → ℝ)}
    (hE : E ∈ stackCells C θ) : IsConnected (E ∩ {v | v 0 ∈ Ioo a b}) := by
  rcases mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · have hsub : cylinder C '' sectionSet θ i ⊆ {v | v 0 ∈ Ioo a b} := by
      intro v hv
      obtain ⟨hxC, hv0⟩ := mem_image_cylinder.mp hv
      simp only [mem_sectionSet] at hv0
      rw [mem_ofPred_eq, ← hv0]
      exact hbnd i ⟨Fin.tail v, hxC⟩
    rw [inter_eq_left.mpr hsub]
    exact isConnected_of_mem_stackCells hC hc hθ (image_cylinder_sectionSet_mem_stackCells i)
  · have : ConnectedSpace C := isConnected_iff_connectedSpace.mp hC
    obtain ⟨low, high, hlow_c, hhigh_c, hlt, hIoo_eq⟩ :=
      exists_continuous_Ioo_eq_sectorSet_inter_of_mem_Ioo hc hθ hab hbnd j
    have huniv : {v : Fin (n + 1) → ℝ | v 0 ∈ Ioo a b} =
        {v : Fin (n + 1) → ℝ | Fin.tail v ∈ (univ : Set (Fin n → ℝ)) ∧ v 0 ∈ Ioo a b} := by simp
    rw [huniv, image_cylinder_sectorSet_inter_eq_image_lineMap (fun y _ ↦ hlt y) hIoo_eq,
      preimage_univ]
    exact (isConnected_univ.prod (isConnected_Ioo zero_lt_one)).image _
      (by simp only [AffineMap.lineMap_apply_ring]; fun_prop :
        Continuous fun p : C × ℝ ↦
          (Fin.cons (AffineMap.lineMap (low p.1) (high p.1) p.2) p.1.1 :
            Fin (n + 1) → ℝ)).continuousOn

end PartitionLifting

end TauCeti
