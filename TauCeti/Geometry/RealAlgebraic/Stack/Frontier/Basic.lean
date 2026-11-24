/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
import TauCeti.Analysis.Analytic.Submanifold.Dimension
import TauCeti.Order.Fin.Basic
import TauCeti.Topology.Constructions.Basic

/-!
# Boundary closures and frontier condition for stacks

Let `C` and `B` be subsets of `ℝⁿ` with `B ⊆ closure C`, carrying strictly ordered stacks
`θ : Fin k → C → ℝ` and `η : Fin m → B → ℝ`. Suppose each section `θ i` converges along `C` at
every point of `B` to a section `η (σ i)` of the boundary stack. Then:

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
  sections (or `B = C` with `E' ≠ E`), `dim E' < dim E`.

See `TauCeti.Geometry.RealAlgebraic.Stack.Frontier.Lifting` for the lifting of preconnected
approach regions, root matching for polynomial delineations, and inductive partition lifting.

## Main declarations

* `TauCeti.tail_mem_closure_of_mem_closure_stackCells`: base-closure projection of stack cells.
* `TauCeti.closure_image_cylinder_sectionSet_inter_eq`,
  `TauCeti.eq_image_cylinder_sectionSet_of_nonempty_inter_closure`,
  `TauCeti.mem_closure_image_cylinder_sectorSet_iff`,
  `TauCeti.closure_image_cylinder_sectorSet_inter_eq`,
  `TauCeti.mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet`,
  `TauCeti.mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectorSet`,
  `TauCeti.closure_image_cylinder_sectorSet_inter_eq_union`: exact trace of section and sector
  closures over `B ⊆ closure C`.
* `TauCeti.subset_closure_of_mem_stackCells_of_nonempty_inter`,
  `TauCeti.subset_closure_of_mem_stackCells_self_of_nonempty_inter`: first part of the frontier
  condition (`E' ∩ closure E ≠ ∅ → E' ⊆ closure E`).
* `TauCeti.image_cylinder_sectionSet_subset_closure_image_cylinder_sectorSet_iff`,
  `TauCeti.image_cylinder_sectorSet_subset_closure_image_cylinder_sectorSet_iff`,
  `exists_eq_image_cylinder_sectionSet_and_eq_image_cylinder_sectorSet_of_subset_closure_of_ne`:
  same-base closure incidence characterization between sections and sectors.
* `TauCeti.dim_lt_of_mem_stackCells_of_subset_closure`,
  `TauCeti.dim_lt_of_mem_stackCells_self_of_subset_closure`: second part of the frontier
  condition (`E' ⊆ closure E, E' ≠ E → dim E' < dim E`) for analytic submanifold cells.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.3
  and 9.1–9.2.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
  di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Function Set Topology

namespace TauCeti

/-! ### Boundary closures of sections and sectors -/

section BoundaryClosure

variable {n k m : ℕ}

section Topological

variable {α : Type*} [TopologicalSpace α] {C B : Set (Fin n → α)}
  {θ : Fin k → C → α} {η : Fin m → B → α} {σ : Fin k → Fin m}

/-- If a point `v` lies in the closure of a cell of a stack over `C`, its base projection
`Fin.tail v` lies in `closure C`. -/
theorem tail_mem_closure_of_mem_closure_stackCells [LinearOrder α]
    {E : Set (Fin (n + 1) → α)} (hE : E ∈ stackCells C θ)
    {v : Fin (n + 1) → α} (hv : v ∈ closure E) :
    Fin.tail v ∈ closure C := by
  have htail : Continuous (Fin.tail : (Fin (n + 1) → α) → Fin n → α) := by fun_prop
  have hsub : Fin.tail '' E ⊆ C := by
    rintro _ ⟨w, hw, rfl⟩
    exact tail_mem_of_mem_stackCells hE hw
  exact closure_mono hsub (image_closure_subset_closure_image htail (mem_image_of_mem Fin.tail hv))

/-- The closure of the `i`-th ambient section over `C`, intersected with the cylinder over
`B ⊆ closure C`, is exactly the `(σ i)`-th ambient section over `B`. -/
theorem closure_image_cylinder_sectionSet_inter_eq [T2Space α] (hBC : B ⊆ closure C)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    (i : Fin k) :
    closure (cylinder C '' sectionSet θ i) ∩ {v | Fin.tail v ∈ B} =
      cylinder B '' sectionSet η (σ i) := by
  let q : C → Fin (n + 1) → α := fun y ↦ Fin.cons (θ i y) y.val
  have hrange : range q = cylinder C '' sectionSet θ i := by
    ext v
    simp only [mem_range, mem_image_cylinder, mem_sectionSet, q]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨hy ▸ y.property, by simp [← hy]⟩,
      fun ⟨hv, hθv⟩ ↦ ⟨⟨Fin.tail v, hv⟩, by rw [hθv, Fin.cons_self_tail]⟩⟩
  ext v
  simp only [mem_inter_iff, mem_ofPred_eq, mem_image_cylinder, mem_sectionSet]
  constructor
  · -- Any limit point `v` over `B` has height `η (σ i) (Fin.tail v)` by Hausdorff uniqueness.
    rintro ⟨hv_cl, hxB⟩
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
  · -- Conversely, `Fin.cons (θ i y) y` converges to `v` along `C` as `y → Fin.tail v`.
    rintro ⟨hxB, hηv⟩
    have hne : (comap (Subtype.val : C → Fin n → α) (𝓝 (Fin.tail v))).NeBot :=
      mem_closure_iff_comap_neBot.mp (hBC hxB)
    have hq_lim : Tendsto q (comap Subtype.val (𝓝 (Fin.tail v))) (𝓝 v) := by
      rw [← Fin.cons_self_tail v, ← hηv]
      exact (hlim i ⟨Fin.tail v, hxB⟩).finCons tendsto_comap
    refine ⟨?_, hxB⟩
    rw [← hrange]
    exact mem_closure_of_tendsto hq_lim (Eventually.of_forall fun y ↦ mem_range_self y)

/-- Any boundary stack cell `E' ∈ stackCells B η` meeting the closure of the `i`-th ambient
section over `C` must equal the matched `(σ i)`-th boundary section over `B`. -/
theorem eq_image_cylinder_sectionSet_of_nonempty_inter_closure [LinearOrder α] [T2Space α]
    (hBC : B ⊆ closure C) (hη : ∀ x : B, Injective fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    {E' : Set (Fin (n + 1) → α)} (hE' : E' ∈ stackCells B η) (i : Fin k)
    (hne : (E' ∩ closure (cylinder C '' sectionSet θ i)).Nonempty) :
    E' = cylinder B '' sectionSet η (σ i) := by
  obtain ⟨v, hvE', hvcl⟩ := hne
  have hv_sec : v ∈ cylinder B '' sectionSet η (σ i) := by
    rw [← closure_image_cylinder_sectionSet_inter_eq hBC hlim i]
    exact ⟨hvcl, tail_mem_of_mem_stackCells hE' hvE'⟩
  exact (pairwiseDisjoint_stackCells hη).eq hE' (image_cylinder_sectionSet_mem_stackCells (σ i))
    (not_disjoint_iff.mpr ⟨v, hvE', hv_sec⟩)

end Topological

section Real

variable {C B : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ} {η : Fin m → B → ℝ} {σ : Fin k → Fin m}

private lemma mem_closure_image_cylinder_sectorSet_of_tendsto {x : Fin n → ℝ} (hx : x ∈ closure C)
    {j : Fin (k + 1)} {h : C → ℝ} {t : ℝ} (hh : ∀ y : C, (y, h y) ∈ sectorSet θ j)
    (ht : Tendsto h (comap Subtype.val (𝓝 x)) (𝓝 t)) :
    Fin.cons t x ∈ closure (cylinder C '' sectorSet θ j) := by
  have hne : (comap (Subtype.val : C → Fin n → ℝ) (𝓝 x)).NeBot := mem_closure_iff_comap_neBot.mp hx
  have hcons : Tendsto (fun y : C ↦ (Fin.cons (h y) y.val : Fin (n + 1) → ℝ))
      (comap Subtype.val (𝓝 x)) (𝓝 (Fin.cons t x : Fin (n + 1) → ℝ)) :=
    ht.finCons tendsto_comap
  exact mem_closure_of_tendsto hcons
    (Eventually.of_forall fun y ↦ mem_image_cylinder.mpr ⟨y.property, hh y⟩)

private lemma mem_closure_sectorSet_zero_of_le {k : ℕ} {C : Set (Fin n → ℝ)}
    {θ : Fin (k + 1) → C → ℝ} (hm : ∀ y : C, Monotone fun i ↦ θ i y)
    {x : Fin n → ℝ} (hx : x ∈ closure C) {b t : ℝ} (hb : t ≤ b)
    (hlim : Tendsto (θ 0) (comap Subtype.val (𝓝 x)) (𝓝 b)) :
    Fin.cons t x ∈ closure (cylinder C '' sectorSet θ 0) := by
  -- Approximate `t` from below by `t - ε`, realized along `C` by `min (t - ε) (θ 0 y - ε)`.
  have hε (ε : ℝ) (hε : 0 < ε) :
      Fin.cons (t - ε) x ∈ closure (cylinder C '' sectorSet θ 0) := by
    have hmin : min (t - ε) (b - ε) = t - ε := min_eq_left (sub_le_sub_right hb ε)
    rw [← hmin]
    exact mem_closure_image_cylinder_sectorSet_of_tendsto hx
      (h := fun y ↦ min (t - ε) (θ 0 y - ε))
      (fun y ↦ by rw [sectorSet_zero hm]; exact (min_le_right _ _).trans_lt (sub_lt_self _ hε))
      (tendsto_const_nhds.min (hlim.sub_const ε))
  have hlim_ε : Tendsto (fun ε : ℝ ↦ (Fin.cons (t - ε) x : Fin (n + 1) → ℝ))
      (𝓝[>] 0) (𝓝 (Fin.cons t x)) := by
    have hc : Continuous (fun ε : ℝ ↦ (Fin.cons (t - ε) x : Fin (n + 1) → ℝ)) := by fun_prop
    simpa only [sub_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact isClosed_closure.mem_of_tendsto hlim_ε
    (eventually_nhdsWithin_iff.mpr <| Eventually.of_forall hε)

private lemma mem_closure_sectorSet_last_of_le {k : ℕ} {C : Set (Fin n → ℝ)}
    {θ : Fin (k + 1) → C → ℝ} (hm : ∀ y : C, Monotone fun i ↦ θ i y)
    {x : Fin n → ℝ} (hx : x ∈ closure C) {a t : ℝ} (ha : a ≤ t)
    (hlim : Tendsto (θ (Fin.last k)) (comap Subtype.val (𝓝 x)) (𝓝 a)) :
    Fin.cons t x ∈ closure (cylinder C '' sectorSet θ (Fin.last (k + 1))) := by
  -- Approximate `t` from above by `t + ε`, realized along `C` by `max (t + ε) (θ k y + ε)`.
  have hε (ε : ℝ) (hε : 0 < ε) :
      Fin.cons (t + ε) x ∈ closure (cylinder C '' sectorSet θ (Fin.last (k + 1))) := by
    have hmax : max (t + ε) (a + ε) = t + ε := max_eq_left (add_le_add_left ha ε)
    rw [← hmax]
    exact mem_closure_image_cylinder_sectorSet_of_tendsto hx
      (h := fun y ↦ max (t + ε) (θ (Fin.last k) y + ε))
      (fun y ↦ by
        rw [sectorSet_last hm]
        exact (lt_add_of_pos_right _ hε).trans_le (le_max_right _ _))
      (tendsto_const_nhds.max (hlim.add_const ε))
  have hlim_ε : Tendsto (fun ε : ℝ ↦ (Fin.cons (t + ε) x : Fin (n + 1) → ℝ))
      (𝓝[>] 0) (𝓝 (Fin.cons t x)) := by
    have hc : Continuous (fun ε : ℝ ↦ (Fin.cons (t + ε) x : Fin (n + 1) → ℝ)) := by fun_prop
    simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact isClosed_closure.mem_of_tendsto hlim_ε
    (eventually_nhdsWithin_iff.mpr <| Eventually.of_forall hε)

private lemma mem_closure_sectorSet_castSucc_succ_of_le {k : ℕ} {C : Set (Fin n → ℝ)}
    {θ : Fin (k + 1) → C → ℝ} (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {x : Fin n → ℝ} (hx : x ∈ closure C) {i₀ : Fin k} {a b t : ℝ} (ha : a ≤ t) (hb : t ≤ b)
    (hlim_a : Tendsto (θ i₀.castSucc) (comap Subtype.val (𝓝 x)) (𝓝 a))
    (hlim_b : Tendsto (θ i₀.succ) (comap Subtype.val (𝓝 x)) (𝓝 b)) :
    Fin.cons t x ∈ closure (cylinder C '' sectorSet θ i₀.castSucc.succ) := by
  have hm : ∀ y : C, Monotone fun i ↦ θ i y := fun y ↦ (hθ y).monotone
  -- Every strict convex combination of `a` and `b` is a limit of interior sector heights along `C`.
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
  -- Either `a = b = t` (the midpoint suffices) or `a < b` and `t ∈ Icc a b = closure (Ioo a b)`.
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

private lemma mem_closure_image_cylinder_sectorSet_of_le {L : Fin k → ℝ}
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) {j : Fin (k + 1)} {v : Fin (n + 1) → ℝ}
    (hx : Fin.tail v ∈ closure C)
    (hlim : ∀ i, Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v))) (𝓝 (L i)))
    (hlow : ∀ i : Fin k, i.castSucc < j → L i ≤ v 0)
    (hhigh : ∀ i : Fin k, j ≤ i.castSucc → v 0 ≤ L i) :
    v ∈ closure (cylinder C '' sectorSet θ j) := by
  rw [← Fin.cons_self_tail v]
  cases k with
  | zero =>
    -- With no sections, the single sector is the full cylinder over `C`.
    exact mem_closure_image_cylinder_sectorSet_of_tendsto hx
      (h := fun _ ↦ v 0) (fun _ ↦ by simp) tendsto_const_nhds
  | succ k =>
    -- Dispatch to the lower unbounded, upper unbounded, or interior bounded sector lemma.
    have hm : ∀ y : C, Monotone fun i ↦ θ i y := fun y ↦ (hθ y).monotone
    cases j using Fin.cases with
    | zero =>
      exact mem_closure_sectorSet_zero_of_le hm hx (hhigh 0 (Fin.zero_le _)) (hlim 0)
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        rw [Fin.succ_last]
        exact mem_closure_sectorSet_last_of_le hm hx
          (hlow (Fin.last k) (Fin.castSucc_lt_last _)) (hlim (Fin.last k))
      | cast i₀ =>
        exact mem_closure_sectorSet_castSucc_succ_of_le hθ hx
          (hlow i₀.castSucc Fin.castSucc_lt_succ) (hhigh i₀.succ le_rfl)
          (hlim i₀.castSucc) (hlim i₀.succ)

/-- When every section `θ i` converges along `C` at `Fin.tail v` to `L i`, the point `v` belongs
to the closure of the `j`-th ambient sector over `C` if and only if `Fin.tail v ∈ closure C` and
`v 0` lies weakly above `L i` for `i < j` and weakly below `L i` for `j ≤ i`. -/
theorem mem_closure_image_cylinder_sectorSet_iff {L : Fin k → ℝ}
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y) {j : Fin (k + 1)} {v : Fin (n + 1) → ℝ}
    (hlim : ∀ i, Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v))) (𝓝 (L i))) :
    v ∈ closure (cylinder C '' sectorSet θ j) ↔
      Fin.tail v ∈ closure C ∧
        (∀ i : Fin k, i.castSucc < j → L i ≤ v 0) ∧
        ∀ i : Fin k, j ≤ i.castSucc → v 0 ≤ L i := by
  let S := sectorSet θ j
  let q : S → Fin (n + 1) → ℝ := cylinder C ∘ Subtype.val
  have hrange : range q = cylinder C '' sectorSet θ j := by
    rw [range_comp, Subtype.range_val]
  constructor
  · -- Strict sector inequalities pass to weak inequalities in the limit along `comap q (𝓝 v)`.
    intro hv_cl
    have hx_cl : Fin.tail v ∈ closure C :=
      tail_mem_closure_of_mem_closure_stackCells (image_cylinder_sectorSet_mem_stackCells j) hv_cl
    have : (comap q (𝓝 v)).NeBot := by
      rw [← Filter.map_neBot_iff q, Filter.map_comap, hrange]
      exact mem_closure_iff_nhdsWithin_neBot.mp hv_cl
    have htail : Tendsto (fun w : S ↦ w.val.1.val) (comap q (𝓝 v)) (𝓝 (Fin.tail v)) := by
      have hc : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
      simpa only [Function.comp_def, q, tail_cylinder] using
        (hc.tendsto v).comp (tendsto_comap (f := q))
    have hbase : Tendsto (fun w : S ↦ w.val.1) (comap q (𝓝 v))
        (comap Subtype.val (𝓝 (Fin.tail v))) := tendsto_comap_iff.mpr htail
    have hzero : Tendsto (fun w : S ↦ w.val.2) (comap q (𝓝 v)) (𝓝 (v 0)) := by
      simpa only [Function.comp_def, q, cylinder_apply_zero] using
        ((continuous_apply 0).tendsto v).comp (tendsto_comap (f := q))
    refine ⟨hx_cl, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · exact le_of_tendsto_of_tendsto ((hlim i).comp hbase) hzero
        (Eventually.of_forall fun w ↦ ((mem_sectorSet.mp w.property).1 i hi).le)
    · exact le_of_tendsto_of_tendsto hzero ((hlim i).comp hbase)
        (Eventually.of_forall fun w ↦ ((mem_sectorSet.mp w.property).2 i hi).le)
  · rintro ⟨hx_cl, hlow, hhigh⟩
    exact mem_closure_image_cylinder_sectorSet_of_le hθ hx_cl hlim hlow hhigh

/-- The closure of the `j`-th ambient sector over `C`, intersected with the cylinder over
`B ⊆ closure C`, consists of the points over `B` lying weakly above `η (σ i)` for `i < j` and
weakly below `η (σ i)` for `j ≤ i`. -/
theorem closure_image_cylinder_sectorSet_inter_eq (hBC : B ⊆ closure C)
    (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    (j : Fin (k + 1)) :
    closure (cylinder C '' sectorSet θ j) ∩ {v | Fin.tail v ∈ B} =
      {v : Fin (n + 1) → ℝ | ∃ hx : Fin.tail v ∈ B,
        (∀ i : Fin k, i.castSucc < j → η (σ i) ⟨Fin.tail v, hx⟩ ≤ v 0) ∧
        ∀ i : Fin k, j ≤ i.castSucc → v 0 ≤ η (σ i) ⟨Fin.tail v, hx⟩} := by
  ext v
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun ⟨hv, hx⟩ ↦ ⟨hx, ((mem_closure_image_cylinder_sectorSet_iff hθ
      fun i ↦ hlim i ⟨Fin.tail v, hx⟩).mp hv).2⟩,
    fun ⟨hx, h⟩ ↦ ⟨(mem_closure_image_cylinder_sectorSet_iff hθ
      fun i ↦ hlim i ⟨Fin.tail v, hx⟩).mpr ⟨hBC hx, h⟩, hx⟩⟩

/-- A point on the `l`-th ambient boundary section over `B` belongs to the closure of the `j`-th
ambient sector over `C` if and only if the index `l` lies weakly between `σ i` for `i < j` and
`σ i` for `j ≤ i`, a condition independent of the base point in `B`. -/
theorem mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet
    (hBC : B ⊆ closure C) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    {j : Fin (k + 1)} {l : Fin m} {v : Fin (n + 1) → ℝ}
    (hv : v ∈ cylinder B '' sectionSet η l) :
    v ∈ closure (cylinder C '' sectorSet θ j) ↔
      (∀ i : Fin k, i.castSucc < j → σ i ≤ l) ∧
        ∀ i : Fin k, j ≤ i.castSucc → l ≤ σ i := by
  obtain ⟨hxB, hvl⟩ := mem_image_cylinder.mp hv
  simp only [mem_sectionSet] at hvl
  rw [mem_closure_image_cylinder_sectorSet_iff hθ fun i ↦ hlim i ⟨Fin.tail v, hxB⟩]
  simp only [hBC hxB, true_and, ← hvl, (hη ⟨Fin.tail v, hxB⟩).le_iff_le]

/-- A point in the `r`-th ambient boundary sector over `B` belongs to the closure of the `j`-th
ambient sector over `C` if and only if `(σ i).castSucc < r` for `i < j` and `r ≤ (σ i).castSucc`
for `j ≤ i`, a condition independent of the point in the boundary sector. -/
theorem mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectorSet
    (hBC : B ⊆ closure C) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    {j : Fin (k + 1)} {r : Fin (m + 1)} {v : Fin (n + 1) → ℝ}
    (hv : v ∈ cylinder B '' sectorSet η r) :
    v ∈ closure (cylinder C '' sectorSet θ j) ↔
      (∀ i : Fin k, i.castSucc < j → (σ i).castSucc < r) ∧
        ∀ i : Fin k, j ≤ i.castSucc → r ≤ (σ i).castSucc := by
  obtain ⟨hxB, hvr⟩ := mem_image_cylinder.mp hv
  simp only [mem_sectorSet] at hvr
  rw [mem_closure_image_cylinder_sectorSet_iff hθ fun i ↦ hlim i ⟨Fin.tail v, hxB⟩]
  simp only [hBC hxB, true_and]
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
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
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
        ⟨l, (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet
          hBC hθ hη hlim hvE').mp hv_cl, hvE'⟩
    · exact Or.inr <| mem_iUnion₂.mpr
        ⟨r, (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectorSet
          hBC hθ hlim hvE').mp hv_cl, hvE'⟩
  · rintro (hv | hv)
    · obtain ⟨l, hl, hv⟩ := mem_iUnion₂.mp hv
      exact ⟨(mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet
        hBC hθ hη hlim hv).mpr hl, (mem_image_cylinder.mp hv).1⟩
    · obtain ⟨r, hr, hv⟩ := mem_iUnion₂.mp hv
      exact ⟨(mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectorSet
        hBC hθ hlim hv).mpr hr, (mem_image_cylinder.mp hv).1⟩

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
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells B η)
    (hne : (E' ∩ closure E).Nonempty) : E' ⊆ closure E := by
  rcases mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [eq_image_cylinder_sectionSet_of_nonempty_inter_closure hBC (fun x ↦ (hη x).injective)
      hlim hE' i hne, ← closure_image_cylinder_sectionSet_inter_eq hBC hlim i]
    exact inter_subset_left
  · obtain ⟨v, hvE', hvcl⟩ := hne
    rcases mem_stackCells.mp hE' with ⟨l, rfl⟩ | ⟨r, rfl⟩
    · have hl := (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet
        hBC hθ hη hlim hvE').mp hvcl
      exact fun w hw ↦ (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet
        hBC hθ hη hlim hw).mpr hl
    · have hr := (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectorSet
        hBC hθ hlim hvE').mp hvcl
      exact fun w hw ↦ (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectorSet
        hBC hθ hlim hw).mpr hr

/-- **Frontier condition, part 1 (same base).** Over a single base `C`, any cell `E'` of a
continuous strictly ordered stack meeting `closure E` for another cell `E` of the same stack is
contained in `closure E`. -/
theorem subset_closure_of_mem_stackCells_self_of_nonempty_inter
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells C θ)
    (hne : (E' ∩ closure E).Nonempty) : E' ⊆ closure E :=
  subset_closure_of_mem_stackCells_of_nonempty_inter (σ := id) subset_closure hθ hθ
    (fun i ↦ (hc i).tendsto_comap_val) hE hE' hne

/-- Over a nonempty base `C`, the `i`-th ambient section of a continuous strictly ordered stack lies
in the closure of the `j`-th ambient sector if and only if it is the lower (`i.succ = j`) or upper
(`i.castSucc = j`) bounding section of that sector. -/
theorem image_cylinder_sectionSet_subset_closure_image_cylinder_sectorSet_iff (hC : C.Nonempty)
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {i : Fin k} {j : Fin (k + 1)} :
    cylinder C '' sectionSet θ i ⊆ closure (cylinder C '' sectorSet θ j) ↔
      i.succ = j ∨ i.castSucc = j := by
  have : Nonempty C := hC.to_subtype
  obtain ⟨v, hv⟩ := (sectionSet_nonempty θ i).image (cylinder C)
  rw [Fin.succ_eq_or_castSucc_eq_iff_forall_le]
  exact ⟨fun hsub ↦
      (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet (σ := id)
        subset_closure hθ hθ (fun i' ↦ (hc i').tendsto_comap_val) hv).mp (hsub hv),
    fun h w hw ↦
      (mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectionSet (σ := id)
        subset_closure hθ hθ (fun i' ↦ (hc i').tendsto_comap_val) hw).mpr h⟩

/-- Over a nonempty base `C`, one ambient sector of a continuous strictly ordered stack lies in the
closure of another if and only if the two sectors are equal. -/
theorem image_cylinder_sectorSet_subset_closure_image_cylinder_sectorSet_iff (hC : C.Nonempty)
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {r j : Fin (k + 1)} :
    cylinder C '' sectorSet θ r ⊆ closure (cylinder C '' sectorSet θ j) ↔ r = j := by
  have : Nonempty C := hC.to_subtype
  obtain ⟨v, hv⟩ := (sectorSet_nonempty hθ r).image (cylinder C)
  refine ⟨fun hsub ↦ Fin.eq_iff_forall_castSucc_lt_and_le.mpr
      ((mem_closure_image_cylinder_sectorSet_iff_of_mem_image_cylinder_sectorSet (σ := id)
        subset_closure hθ (fun i' ↦ (hc i').tendsto_comap_val) hv).mp (hsub hv)),
    by rintro rfl; exact subset_closure⟩

/-- Over a nonempty base `C`, if two distinct cells `E' ≠ E` of a continuous strictly ordered
stack satisfy `E' ⊆ closure E`, then `E` is a sector and `E'` is either its lower or its upper
bounding section. -/
theorem exists_eq_image_cylinder_sectionSet_and_eq_image_cylinder_sectorSet_of_subset_closure_of_ne
    (hC : C.Nonempty) (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells C θ)
    (hsub : E' ⊆ closure E) (hne : E' ≠ E) :
    ∃ (i : Fin k) (j : Fin (k + 1)),
      (i.succ = j ∨ i.castSucc = j) ∧
        E' = cylinder C '' sectionSet θ i ∧ E = cylinder C '' sectorSet θ j := by
  obtain ⟨v, hvE'⟩ := image_nonempty.mp ((image_tail_of_mem_stackCells hθ hE').symm ▸ hC)
  rcases mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · -- No distinct stack cell can lie in the closure of a section.
    exact absurd (eq_image_cylinder_sectionSet_of_nonempty_inter_closure (σ := id) subset_closure
      (fun y ↦ (hθ y).injective) (fun i' ↦ (hc i').tendsto_comap_val) hE' i
      ⟨v, hvE', hsub hvE'⟩) hne
  · -- Inside a sector closure, a distinct stack cell must be an adjacent bounding section.
    rcases mem_stackCells.mp hE' with ⟨i, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨i, j,
        (image_cylinder_sectionSet_subset_closure_image_cylinder_sectorSet_iff hC hc hθ).mp hsub,
        rfl, rfl⟩
    · exact absurd (congrArg (cylinder C '' sectorSet θ ·)
        ((image_cylinder_sectorSet_subset_closure_image_cylinder_sectorSet_iff hC hc hθ).mp hsub))
        hne

private lemma continuous_of_exists_analyticOnSubmanifold {d : ℕ} {S : Set (Fin n → ℝ)} {f : S → ℝ}
    (hf : ∃ r, (∀ y : S, r y = f y) ∧ AnalyticOnSubmanifold d r S) : Continuous f := by
  obtain ⟨r, hr, har⟩ := hf
  exact (continuousOn_iff_continuous_domRestrict.mp har.continuousOn).congr hr

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
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) (hE' : E' ∈ stackCells B η)
    (hE_sub : IsAnalyticSubmanifold e E) (hE'_sub : IsAnalyticSubmanifold e' E')
    (hsub : E' ⊆ closure E) : e' < e := by
  have hcC (i : Fin k) : Continuous (θ i) := continuous_of_exists_analyticOnSubmanifold (haC i)
  have hcB (l : Fin m) : Continuous (η l) := continuous_of_exists_analyticOnSubmanifold (haB l)
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
    have hEq : E' = cylinder B '' sectionSet η (σ i) :=
      eq_image_cylinder_sectionSet_of_nonempty_inter_closure hBC (fun x ↦ (hη x).injective)
        hlim hE' i ⟨v, hvE', hsub hvE'⟩
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
  have hcC (i : Fin k) : Continuous (θ i) := continuous_of_exists_analyticOnSubmanifold (haC i)
  obtain ⟨i, j, -, rfl, rfl⟩ :=
    exists_eq_image_cylinder_sectionSet_and_eq_image_cylinder_sectorSet_of_subset_closure_of_ne
      hC.nonempty hcC hθ hE hE' hsub hne
  obtain ⟨fn, hfn, hafn⟩ := haC i
  have he' : e' = dC :=
    hE'_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectionSet hC i hfn hafn)
  have he : e = dC + 1 :=
    hE_sub.dim_eq (isAnalyticSubmanifold_image_cylinder_sectorSet hC hcC hθ j)
  omega

end FrontierCondition

end TauCeti
