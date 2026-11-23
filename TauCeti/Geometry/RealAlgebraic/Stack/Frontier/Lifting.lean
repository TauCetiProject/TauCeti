/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Frontier.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Selection
public import TauCeti.Topology.ClusterSet
import TauCeti.Topology.Algebra.Polynomial.Root.Extension
import TauCeti.Topology.Constructions.Basic
import TauCeti.Topology.ContinuousOn.Extension
import TauCeti.Topology.Order.OrderClosed

/-!
# Approach-region lifting and frontier compatibility for delineated stacks

This module builds on the boundary-closure and frontier-condition results in
`TauCeti.Geometry.RealAlgebraic.Stack.Frontier.Basic` to lift frontier compatibility and
preconnected approach regions across inductive stack constructions:

* preconnected approach regions (`TauCeti.IsPreconnectedApproachAt`) lift from a base `C` to
  every cell of `stackCells C θ` at any point whose base projection has finite section limits
  along `C`;
* combining `TauCeti.continuousOn_extendFrom_of_isRoot_of_subset_closure` with
  `TauCeti.Delineation.exists_eq_root_of_continuous` and `TauCeti.monotone_of_tendsto_section`
  discharges the monotone root-matching hypothesis `σ` for polynomial delineations over connected
  boundary strata `B ⊆ closure C` whenever `C` has preconnected approach regions along `B` and
  each root section of `C` is witnessed by a family member that remains nonzero and of
  non-increasing degree at `B`;
* together with approach-region lifting, this propagates both parts of the frontier condition and
  the frontier local-connectedness invariant across inductive coordinate liftings on cylinders;
* when all section values of a stack over a connected base lie in `Ioo a b`, intersecting any cell
  with the open slab `{v | v 0 ∈ Ioo a b}` preserves connectedness.

## Main declarations

* `TauCeti.isPreconnectedApproachAt_image_cylinder_sectionSet`,
  `TauCeti.isPreconnectedApproachAt_image_cylinder_sectorSet`,
  `TauCeti.isPreconnectedApproachAt_of_mem_stackCells`,
  `TauCeti.isPreconnectedApproachAt_of_mem_stackCells_of_tail_mem`: lifting of preconnected
  approach regions from the base to stack cells.
* `TauCeti.Delineation.exists_root_tendsto_of_subset_closure`,
  `TauCeti.Delineation.subset_closure_of_mem_stackCells_of_nonempty_inter`,
  `TauCeti.Delineation.dim_lt_of_mem_stackCells_of_subset_closure`: existence of the monotone root
  matching `σ : Fin D_C.count → Fin D_B.count` and both parts of the frontier condition between
  delineations on `C` and `B ⊆ closure C`.
* `TauCeti.subset_closure_of_mem_biUnion_stackCells`,
  `TauCeti.inter_closure_eq_biUnion_of_mem_biUnion_stackCells`,
  `TauCeti.dim_lt_of_mem_biUnion_stackCells`,
  `TauCeti.isPreconnectedApproachAt_of_mem_biUnion_stackCells`: lifting of frontier-compatible
  partitions and approach-region invariants to cylinders.
* `TauCeti.isConnected_inter_Ioo_of_mem_stackCells`: connectedness of a stack cell intersected
  with the open slab `{v | v 0 ∈ Ioo a b}` when all section values lie in `Ioo a b`.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.3
  and 9.1–9.2.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
  di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

/-! ### Lifting preconnected approach regions through stacks -/

section ApproachRegions

variable {n k : ℕ} {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}

private lemma image_cylinder_sectorSet_inter_eq_image_lineMap {j : Fin (k + 1)}
    {U : Set (Fin n → ℝ)} {a b : ℝ} {low high : C → ℝ}
    (hlt : ∀ y : C, y.val ∈ U → low y < high y)
    (hIoo : ∀ (y : C) (r : ℝ),
      r ∈ Ioo (low y) (high y) ↔ (y, r) ∈ sectorSet θ j ∧ r ∈ Ioo a b) :
    (cylinder C '' sectorSet θ j) ∩ {v | Fin.tail v ∈ U ∧ v 0 ∈ Ioo a b} =
      (fun p : C × ℝ ↦ Fin.cons (AffineMap.lineMap (low p.1) (high p.1) p.2) p.1.val) ''
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
    exact ⟨⟨y.property, hsec⟩, hyt, hv_Ioo⟩

private lemma isPreconnectedApproachAt_of_forall_pos_exists_image {β : Type*} [TopologicalSpace β]
    {E : Set (Fin (n + 1) → ℝ)} {v₀ : Fin (n + 1) → ℝ}
    (hconn : IsPreconnectedApproachAt C (Fin.tail v₀))
    (hparam : ∀ δ > 0, ∃ (G₁ : Set (Fin n → ℝ)) (F : Set β) (φ : C × β → Fin (n + 1) → ℝ),
      G₁ ∈ 𝓝 (Fin.tail v₀) ∧ IsPreconnected F ∧ Continuous φ ∧
      ∀ U ⊆ G₁, E ∩ {v | Fin.tail v ∈ U ∧ v 0 ∈ Ioo (v₀ 0 - δ) (v₀ 0 + δ)} =
        φ '' (((Subtype.val : C → _) ⁻¹' U) ×ˢ F)) :
    IsPreconnectedApproachAt E v₀ := by
  refine isPreconnectedApproachAt_def.mpr fun s hs ↦ ?_
  -- Split `s ∈ 𝓝 v₀` into a product box `G × Ioo (v₀ 0 - δ) (v₀ 0 + δ)` in `(Fin.tail v, v 0)`.
  obtain ⟨G, hG, W, hW, hGW⟩ := mem_nhds_prod_iff.mp <|
    (by fun_prop : Continuous fun p : (Fin n → ℝ) × ℝ ↦
      (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)).continuousAt
        (x := (Fin.tail v₀, v₀ 0)) |>.preimage_mem_nhds
      (by simpa only [Fin.cons_self_tail] using hs)
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
  have hIooW : Ioo (v₀ 0 - δ) (v₀ 0 + δ) ⊆ W := by simpa only [Real.ball_eq_Ioo] using hδW
  -- Intersect `G` with the parameterization's base domain `G₁` and shrink to an approach `t_base`.
  obtain ⟨G₁, F, φ, hG₁, hF_pre, hφ_cont, hφ_eq⟩ := hparam δ hδ
  obtain ⟨t_base, ht_nhds, ht_sub, ht_pre⟩ :=
    isPreconnectedApproachAt_def.mp hconn (G ∩ G₁) (inter_mem hG hG₁)
  have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
  refine ⟨{v | Fin.tail v ∈ t_base ∧ v 0 ∈ Ioo (v₀ 0 - δ) (v₀ 0 + δ)},
    inter_mem (htail.continuousAt.preimage_mem_nhds ht_nhds)
      ((continuous_apply 0).continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (sub_lt_self _ hδ) (lt_add_of_pos_right _ hδ))),
    fun v hv ↦ by
      simpa only [mem_preimage, Fin.cons_self_tail] using
        hGW (mk_mem_prod (ht_sub hv.1).1 (hIooW hv.2)), ?_⟩
  -- Pull back `C ∩ t_base` to `C`, cross with `F`, and take the continuous image under `φ`.
  have hA_pre : IsPreconnected ((Subtype.val : C → _) ⁻¹' t_base) :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp (by rwa [Subtype.image_preimage_val])
  rw [hφ_eq t_base fun x hx ↦ (ht_sub hx).2]
  exact (hA_pre.prod hF_pre).image φ hφ_cont.continuousOn

private lemma eq_apply_zero_of_mem_closure_sectionSet (i : Fin k) {v₀ : Fin (n + 1) → ℝ}
    (hv₀ : v₀ ∈ closure (cylinder C '' sectionSet θ i)) {L : ℝ}
    (hL : Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v₀))) (𝓝 L)) :
    L = v₀ 0 := by
  have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
  have hx_cl : Fin.tail v₀ ∈ closure C := by
    have hmem := image_closure_subset_closure_image htail (mem_image_of_mem Fin.tail hv₀)
    rwa [image_tail_image_cylinder, fst_image_sectionSet, Subtype.coe_image_univ] at hmem
  have hsec_eq : sectionSet (fun _ : Fin 1 ↦ θ i) 0 = sectionSet θ i := by
    ext ⟨y, t⟩
    simp only [mem_sectionSet]
  have htr := closure_image_cylinder_sectionSet_inter_eq
    (B := {Fin.tail v₀}) (θ := fun _ : Fin 1 ↦ θ i) (η := fun _ : Fin 1 ↦ fun _ ↦ L)
    (σ := id) (singleton_subset_iff.mpr hx_cl)
    (fun _ x ↦ by simpa [mem_singleton_iff.mp x.property] using hL) 0
  have hv_in :
      v₀ ∈ cylinder {Fin.tail v₀} '' sectionSet (fun _ : Fin 1 ↦ fun _ ↦ L) (id 0) := by
    rw [← htr, hsec_eq]
    exact ⟨hv₀, rfl⟩
  exact mem_sectionSet.mp (mem_image_cylinder.mp hv_in).2

/-- An ambient section of a continuous function `θ i` inherits preconnected approach regions at
`v₀` whenever the base `C` has preconnected approach regions at `Fin.tail v₀` and `θ i` has a
limit along `C` at `Fin.tail v₀`. -/
theorem isPreconnectedApproachAt_image_cylinder_sectionSet (i : Fin k) (hc : Continuous (θ i))
    {v₀ : Fin (n + 1) → ℝ} (hconn : IsPreconnectedApproachAt C (Fin.tail v₀))
    (hlim : ∃ L, Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v₀))) (𝓝 L)) :
    IsPreconnectedApproachAt (cylinder C '' sectionSet θ i) v₀ := by
  by_cases hv₀ : v₀ ∈ closure (cylinder C '' sectionSet θ i)
  · -- Match the section limit `L` with `v₀ 0`, then parameterize the local slice over `C × univ`.
    obtain ⟨L, hL⟩ := hlim
    obtain rfl := eq_apply_zero_of_mem_closure_sectionSet i hv₀ hL
    refine isPreconnectedApproachAt_of_forall_pos_exists_image (β := Unit) hconn fun δ hδ ↦ ?_
    obtain ⟨G₁, hG₁, hG₁_Ioo⟩ := mem_comap.mp <|
      hL.eventually (Ioo_mem_nhds (sub_lt_self _ hδ) (lt_add_of_pos_right _ hδ))
    refine ⟨G₁, univ, fun p ↦ Fin.cons (θ i p.1) p.1.val, hG₁, isPreconnected_univ,
      by fun_prop, fun U hUG₁ ↦ ?_⟩
    ext v
    rw [mem_inter_iff, mem_image_cylinder, mem_image]
    simp only [mem_sectionSet, mem_prod, mem_preimage, mem_univ, and_true, Prod.exists,
      Unique.exists_iff]
    exact ⟨fun ⟨⟨hxC, hθv⟩, hxt, _⟩ ↦ ⟨⟨Fin.tail v, hxC⟩, hxt, by rw [hθv, Fin.cons_self_tail]⟩,
      fun ⟨y, hyt, hv⟩ ↦ hv ▸ ⟨⟨y.property, rfl⟩, hyt, hG₁_Ioo (hUG₁ hyt)⟩⟩
  · exact isPreconnectedApproachAt_of_notMem_closure hv₀

private lemma exists_continuous_Ioo_eq_sectorSet_inter
    (hc : ∀ i, Continuous (θ i)) (hθ : ∀ y : C, StrictMono fun i ↦ θ i y)
    (j : Fin (k + 1)) {x₀ : Fin n → ℝ} {t₀ δ : ℝ} (hδ : 0 < δ) {L : Fin k → ℝ}
    (hlim : ∀ i, Tendsto (θ i) (comap Subtype.val (𝓝 x₀)) (𝓝 (L i)))
    (hlow₀ : ∀ i : Fin k, i.castSucc < j → L i ≤ t₀)
    (hhigh₀ : ∀ i : Fin k, j ≤ i.castSucc → t₀ ≤ L i) :
    ∃ (low high : C → ℝ) (G₁ : Set (Fin n → ℝ)),
      G₁ ∈ 𝓝 x₀ ∧ Continuous low ∧ Continuous high ∧
      (∀ y : C, y.val ∈ G₁ → low y < high y) ∧
      ∀ (y : C) (r : ℝ),
        r ∈ Ioo (low y) (high y) ↔ (y, r) ∈ sectorSet θ j ∧ r ∈ Ioo (t₀ - δ) (t₀ + δ) := by
  cases k with
  | zero =>
    -- With no sections, the vertical window `Ioo (t₀ - δ) (t₀ + δ)` works over all of `C`.
    refine ⟨fun _ ↦ t₀ - δ, fun _ ↦ t₀ + δ, univ, univ_mem,
      continuous_const, continuous_const, fun _ _ ↦ by linarith, fun y r ↦ ?_⟩
    simp [sectorSet_fin_zero]
  | succ k =>
    -- Clip the lower, upper, or interior sector bounds against `t₀ - δ` and `t₀ + δ` near `x₀`.
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
  · -- Bound `v₀ 0` between the section limits, then parameterize the slice over `C × Ioo 0 1`.
    choose L hL using hlim
    obtain ⟨_, hlow₀, hhigh₀⟩ := (mem_closure_image_cylinder_sectorSet_iff hθ hL).mp hv₀
    refine isPreconnectedApproachAt_of_forall_pos_exists_image (β := ℝ) hconn fun δ hδ ↦ ?_
    obtain ⟨low, high, G₁, hG₁, hlow_c, hhigh_c, hlt_G₁, hIoo_eq⟩ :=
      exists_continuous_Ioo_eq_sectorSet_inter hc hθ j hδ hL hlow₀ hhigh₀
    refine ⟨G₁, Ioo (0 : ℝ) 1,
      fun p ↦ Fin.cons (AffineMap.lineMap (low p.1) (high p.1) p.2) p.1.val,
      hG₁, isPreconnected_Ioo, by simp only [AffineMap.lineMap_apply_ring]; fun_prop,
      fun U hUG₁ ↦ image_cylinder_sectorSet_inter_eq_image_lineMap
        (fun y hy ↦ hlt_G₁ y (hUG₁ hy)) hIoo_eq⟩
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
    ⟨θ i x, (hc i).tendsto_comap_val x⟩

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
      ∀ i (x : B), Tendsto (D_C.root i) (comap Subtype.val (𝓝 x.val)) (𝓝 (D_B.root (σ i) x)) := by
  have : ConnectedSpace B := isConnected_iff_connectedSpace.mp hB_conn
  -- Extend each section `D_C.root i` continuously to `B` via `extendFrom` and match it in `D_B`.
  have hsec (i : Fin D_C.count) :
      ∃ l : Fin D_B.count, ∀ x : B,
        Tendsto (D_C.root i) (comap Subtype.val (𝓝 x.val)) (𝓝 (D_B.root l x)) := by
    obtain ⟨k, hmult, hne, hcoeff, hdeg⟩ := hwit i
    obtain ⟨f, hf_cont, hf_apply⟩ := (D_C.continuous_root i).exists_continuousOn_eq
    have hf_root (y : Fin n → ℝ) (hy : y ∈ C) : (P k y).eval (f y) = 0 := by
      rw [hf_apply ⟨y, hy⟩]
      exact ((D_C.multiplicity_pos_iff ⟨y, hy⟩).mp hmult).2
    have hF_cont : ContinuousOn (extendFrom C f) B :=
      continuousOn_extendFrom_of_isRoot_of_subset_closure hBC hconn hf_cont hf_root hcoeff hdeg hne
    have hF_root (x : B) : (P k x.val).eval (extendFrom C f x.val) = 0 :=
      eval_extendFrom_eq_zero_of_isRoot (hBC x.property) (hconn x.val x.property) hf_cont
        (eventually_nhdsWithin_of_forall hf_root) (hcoeff x.val x.property) (hdeg x.val x.property)
        (hne x.val x.property)
    -- Over connected `B`, the continuous root `extendFrom C f` matches a single `D_B.root l`.
    obtain ⟨l, hl⟩ := D_B.exists_eq_root_of_continuous
      (continuousOn_iff_continuous_domRestrict.mp hF_cont) (fun x ↦ hne x.val x.property) hF_root
    refine ⟨l, fun x ↦ ?_⟩
    have hF_lim : Tendsto f (𝓝[C] x.val) (𝓝 (extendFrom C f x.val)) :=
      tendsto_extendFrom_of_isRoot (hBC x.property) (hconn x.val x.property) hf_cont
        (eventually_nhdsWithin_of_forall hf_root) (hcoeff x.val x.property) (hdeg x.val x.property)
        (hne x.val x.property)
    have hmap : map (Subtype.val : C → Fin n → ℝ) (comap Subtype.val (𝓝 x.val)) = 𝓝[C] x.val := by
      rw [nhdsWithin, Filter.map_comap_setCoe_val]
    have hlim_sub : Tendsto (f ∘ Subtype.val) (comap Subtype.val (𝓝 x.val))
        (𝓝 (extendFrom C f x.val)) := tendsto_map'_iff.mp (hmap.symm ▸ hF_lim)
    have hfeq : f ∘ Subtype.val = D_C.root i := funext hf_apply
    have hlext : extendFrom C f x.val = D_B.root l x := congrFun hl x
    rwa [hfeq, hlext] at hlim_sub
  -- Monotonicity of `σ` follows from order-closedness along the nonempty boundary `B`.
  choose σ hσ using hsec
  exact ⟨σ, monotone_of_tendsto_section (hB_conn.nonempty.mono (subset_inter subset_rfl hBC))
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
  · obtain ⟨r, -, hr⟩ := (D_C.continuous_root i).exists_continuousOn_eq
    exact ⟨r, hr, D_C.analyticOnSubmanifold_root hC haC i hr⟩
  · obtain ⟨r, -, hr⟩ := (D_B.continuous_root l).exists_continuousOn_eq
    exact ⟨r, hr, D_B.analyticOnSubmanifold_root hB haB l hr⟩

end Delineation

/-! ### Lifting frontier-compatible partitions and open-slab intersections -/

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
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.val)) (𝓝 (θ B (σ i) x)))
    {E' E : Set (Fin (n + 1) → ℝ)} (hE' : E' ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    (hE : E ∈ ⋃ C ∈ ℬ, stackCells C (θ C)) (hne : (E' ∩ closure E).Nonempty) :
    E' ⊆ closure E := by
  obtain ⟨B, hB, hE'B⟩ := mem_iUnion₂.mp hE'
  obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.mp hE
  obtain ⟨v, hvE', hvcl⟩ := hne
  have hvB : Fin.tail v ∈ B := tail_mem_of_mem_stackCells hE'B hvE'
  have hvC_cl : Fin.tail v ∈ closure C :=
    tail_mem_closure_of_mem_closure_stackCells hEC hvcl
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
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.val)) (𝓝 (θ B (σ i) x)))
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
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.val)) (𝓝 (θ B (σ i) x)))
    {E' E : Set (Fin (n + 1) → ℝ)} (hE' : E' ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    (hE : E ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    (hE'_sub : IsAnalyticSubmanifold e' E') (hE_sub : IsAnalyticSubmanifold e E)
    (hsub : E' ⊆ closure E) (hne : E' ≠ E) : e' < e := by
  obtain ⟨B, hB, hE'B⟩ := mem_iUnion₂.mp hE'
  obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.mp hE
  obtain ⟨v, hvE'⟩ := hE'_sub.nonempty
  have hvB : Fin.tail v ∈ B := tail_mem_of_mem_stackCells hE'B hvE'
  have hvC_cl : Fin.tail v ∈ closure C :=
    tail_mem_closure_of_mem_closure_stackCells hEC (hsub hvE')
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
        ∀ i (x : B), Tendsto (θ C i) (comap Subtype.val (𝓝 x.val)) (𝓝 (θ B (σ i) x)))
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ ⋃ C ∈ ℬ, stackCells C (θ C))
    {v₀ : Fin (n + 1) → ℝ} (hv₀W : Fin.tail v₀ ∈ W) :
    IsPreconnectedApproachAt E v₀ := by
  by_cases hv₀_cl : v₀ ∈ closure E
  · obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.mp hE
    obtain ⟨B, hB, hvB⟩ := mem_sUnion.mp (hcover.symm ▸ hv₀W)
    have hvC_cl : Fin.tail v₀ ∈ closure C :=
      tail_mem_closure_of_mem_closure_stackCells hEC hv₀_cl
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
          (Fin.cons (AffineMap.lineMap (low p.1) (high p.1) p.2) p.1.val :
            Fin (n + 1) → ℝ)).continuousOn

end PartitionLifting

end TauCeti
