/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# A measure-free lattice-point packing and doubling engine

The Layer-0 engine gives measure-free cardinality estimates for an additive subgroup of
`ι → ℂ` in products of closed discs. The regions are stated directly with Mathlib's
`Set.pi Set.univ` and `Metric.closedBall`; there is no separate box or separation definition.

* `finite_and_ncard_le_of_subset_pi_closedBall_of_separated` bounds the cardinality of an
  `ε`-separated subset of the polydisc of radii `c * r i` by `(4*c/ε)^(2*#ι)`.
* `addSubgroup_inter_pi_closedBall_finite_and_ncard_le_of_separated` applies packing when
  every nonzero subgroup element escapes the polydisc of radii `ρ * r i`.
* `ncard_inter_pi_closedBall_two_le_pow_mul` bounds the count at radii `2 * r i` by
  `49^#ι` times the count at radii `r i`, assuming the first intersection is finite.
* `ncard_inter_pi_closedBall_two_le_pow_mul_of_discreteTopology` supplies that finiteness
  for a discrete `ℤ`-submodule, in particular for Mathlib's `IsZLattice ℝ` setting.

## Reconciliation with Mathlib's lattices

The core takes an arbitrary `AddSubgroup`, so no spanning or discreteness assumption is
hidden in its carrier. A `Submodule ℤ` enters through its existing `toAddSubgroup` map.
Compactness of the product of closed discs and closedness of a discrete subgroup supply
the lattice specialization. No new lattice, separation, box, or covolume convention is
introduced. The finite-grid maps below are private machinery for the cardinality proofs.

The estimates count points without a measure; Mathlib's covolume and convex-body results
remain the separate volumetric API. No count-to-covolume identity is assumed.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where the grid-pigeonhole core packed lattice points after projection to one
infinite place. The unit-distance application is dropped; only the reusable packing and
doubling bounds are migrated.
-/

public section

namespace TauCeti.GeometryOfNumbers

variable {ι : Type*}

section Packing

/-- Grid pigeonhole, axis bound: the cell index of a coordinate lying in the box is one of
the `⌊2√2·c/ε⌋ + 1` admissible values. -/
private theorem cell_index_mem {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri)
    {t : ℝ} (ht : |t| ≤ c * ri) :
    ⌊(t + c * ri) / (ε * ri / Real.sqrt 2)⌋ ∈
      Finset.Icc (0 : ℤ) ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℤ) := by
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hδ : 0 < ε * ri / Real.sqrt 2 := div_pos (mul_pos hε hri) hsqrt2
  -- `(2√2·c/ε)·(ε·ri/√2)` simplifies to `2·c·ri`, the diameter of the coordinate disc.
  have hq_eq : (2 * Real.sqrt 2 * c / ε) * (ε * ri / Real.sqrt 2) = 2 * c * ri := by
    field_simp
  have hstep : 2 * c * ri <
      ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℝ) + 1) * (ε * ri / Real.sqrt 2) := by
    rw [← hq_eq]
    exact mul_lt_mul_of_pos_right (Nat.lt_floor_add_one _) hδ
  rw [Finset.mem_Icc]
  refine ⟨Int.floor_nonneg.mpr (div_nonneg (by linarith [(abs_le.mp ht).1]) hδ.le),
    Int.le_of_lt_add_one (Int.floor_lt.mpr ?_)⟩
  rw [div_lt_iff₀ hδ]
  push_cast
  linarith [(abs_le.mp ht).2]

/-- A complex number whose real and imaginary parts are each `< d` in absolute value has
norm `< d·√2`. -/
private theorem norm_lt_of_re_im_bound {z : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hre : |z.re| < d) (him : |z.im| < d) : ‖z‖ < d * Real.sqrt 2 := by
  rw [Complex.norm_def, ← Real.sqrt_sq hd, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) ?_
  nlinarith [abs_lt.mp hre, abs_lt.mp him, Complex.normSq_apply z]

/-- The per-axis cell count `⌊2√2·c/ε⌋ + 1` is at most `4·c/ε` (using `ε ≤ c`). -/
private theorem cellCount_le {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) :
    ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℝ) + 1 ≤ 4 * c / ε := by
  have hc : 0 < c := hε.trans_le hεc
  have hnn : (0 : ℝ) ≤ 2 * Real.sqrt 2 * c / ε :=
    div_nonneg (mul_nonneg (by positivity) hc.le) hε.le
  have hfloor := Nat.floor_le hnn
  -- `⌊·⌋·ε ≤ 2√2·c` and `√2 ≤ 3/2`, so `(⌊·⌋ + 1)·ε ≤ 2√2·c + c ≤ 4·c`.
  have hme : (⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℝ) * ε ≤ 2 * Real.sqrt 2 * c := by
    have := mul_le_mul_of_nonneg_right hfloor hε.le
    rwa [div_mul_cancel₀ (2 * Real.sqrt 2 * c) hε.ne'] at this
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    have h32 : (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    rw [h32]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [le_div_iff₀ hε]
  nlinarith [hme, hεc, hc, hs]

/-- The cell-index map of scale `ε` for the polydisc of radii `c * r i`: a point maps to its
per-coordinate integer cell indices (of the real and imaginary parts), with cell side
`ε·rᵢ/√2`. -/
private noncomputable def cellIndexMap (r : ι → ℝ) (c ε : ℝ) : (ι → ℂ) → (ι → ℤ × ℤ) :=
  fun x i => (⌊((x i).re + c * r i) / (ε * r i / Real.sqrt 2)⌋,
    ⌊((x i).im + c * r i) / (ε * r i / Real.sqrt 2)⌋)

/-- The cell-index map is injective on a set whose distinct points are `ε`-separated in some
coordinate: two points sharing every cell index would differ by less than the cell diameter
`ε·rᵢ` in that coordinate, contradicting the separation. -/
private theorem injOn_cellIndexMap_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i) {c ε : ℝ}
    (hε : 0 < ε) {S : Set (ι → ℂ)} (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, ε * r i < ‖x i - y i‖) :
    Set.InjOn (cellIndexMap r c ε) S := by
  intro x hx y hy hxy
  by_contra hne
  obtain ⟨i, hi⟩ := hsep x hx y hy hne
  simp only [cellIndexMap, funext_iff, Prod.ext_iff] at hxy
  have hδ : 0 < ε * r i / Real.sqrt 2 :=
    div_pos (mul_pos hε (hr i)) (Real.sqrt_pos.2 (by norm_num))
  have hre : |(x i).re - (y i).re| < ε * r i / Real.sqrt 2 := by
    simpa [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos hδ, div_lt_iff₀ hδ] using
      Int.abs_sub_lt_one_of_floor_eq_floor (hxy i).1
  have him : |(x i).im - (y i).im| < ε * r i / Real.sqrt 2 := by
    simpa [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos hδ, div_lt_iff₀ hδ] using
      Int.abs_sub_lt_one_of_floor_eq_floor (hxy i).2
  have hlt : ‖x i - y i‖ < (ε * r i / Real.sqrt 2) * Real.sqrt 2 :=
    norm_lt_of_re_im_bound hδ.le (by rwa [Complex.sub_re]) (by rwa [Complex.sub_im])
  rw [div_mul_cancel₀ _ (by positivity : Real.sqrt 2 ≠ 0)] at hlt
  linarith

variable [Fintype ι]

/-- A subset of the polydisc of radii `c * r i` whose distinct points are `ε`-separated in
some coordinate is finite, of cardinality at most `(4*c/ε) ^ (2*#ι)`. -/
theorem finite_and_ncard_le_of_subset_pi_closedBall_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) {S : Set (ι → ℂ)} (hS : S ⊆ Set.pi Set.univ
        (fun i ↦ Metric.closedBall (0 : ℂ) (c * r i)))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, ε * r i < ‖x i - y i‖) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (4 * c / ε) ^ (2 * Fintype.card ι) := by
  classical
  -- The cell map sends a point to its tuple of cell indices — `⌊((x i).re + c·r i)/δ i⌋` and
  -- the analogous imaginary part, with cell side `δ i = ε·r i/√2` — landing in
  -- `ι → Icc 0 ⌊2√2·c/ε⌋ × Icc 0 ⌊2√2·c/ε⌋` and is injective on the separated set, because two
  -- points in the same cell of every coordinate differ by less than `ε·r i` there.
  set K : ℤ := (⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℤ) with hK
  set T : Finset (ι → ℤ × ℤ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc (0 : ℤ) K ×ˢ Finset.Icc (0 : ℤ) K) with hT
  -- The cell map, of cell side `ε·r i/√2` per coordinate.
  set g : (ι → ℂ) → (ι → ℤ × ℤ) := cellIndexMap r c ε
  have key : ∀ x ∈ S, ∀ i, |(x i).re| ≤ c * r i ∧ |(x i).im| ≤ c * r i := fun x hx i =>
    ⟨(Complex.abs_re_le_norm _).trans (by simpa using hS hx i (Set.mem_univ i)),
      (Complex.abs_im_le_norm _).trans (by simpa using hS hx i (Set.mem_univ i))⟩
  have hg : ∀ x ∈ S, g x ∈ T := by
    intro x hx
    rw [hT, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_product]
    exact ⟨cell_index_mem hε (hr i) (key x hx i).1, cell_index_mem hε (hr i) (key x hx i).2⟩
  -- The cell map is injective on `S`.
  have hg_inj : Set.InjOn g S := injOn_cellIndexMap_of_separated r hr hε hsep
  -- Finiteness and the cardinal bound follow from injectivity into the finite `T`.
  have hgsub : g '' S ⊆ (↑T : Set (ι → ℤ × ℤ)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Finset.mem_coe.mpr (hg x hx)
  have hfin : S.Finite := Set.Finite.of_finite_image (T.finite_toSet.subset hgsub) hg_inj
  refine ⟨hfin, ?_⟩
  have hcard : (S.ncard : ℝ) ≤ (T.card : ℝ) := by
    rw [← hg_inj.ncard_image]
    exact_mod_cast Set.ncard_le_ncard hgsub T.finite_toSet
  have hTeq : T.card = (Finset.Icc (0 : ℤ) K).card ^ (2 * Fintype.card ι) := by
    rw [hT, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Finset.card_product,
      ← pow_two, ← pow_mul]
  have haxis : ((Finset.Icc (0 : ℤ) K).card : ℝ) ≤ 4 * c / ε := by
    have hcard_eq : (Finset.Icc (0 : ℤ) K).card = ⌊2 * Real.sqrt 2 * c / ε⌋₊ + 1 := by
      rw [hK, Int.card_Icc]; omega
    rw [hcard_eq]; push_cast; exact cellCount_le hε hεc
  refine hcard.trans ?_
  rw [hTeq]
  push_cast
  exact pow_le_pow_left₀ (by positivity) haxis _

/-- If every nonzero element of `Λ` escapes the polydisc of radii `ρ * r i`, the subgroup
meets the polydisc of radii `2 * r i` in at most `(8/ρ) ^ (2*#ι)` points. -/
theorem addSubgroup_inter_pi_closedBall_finite_and_ncard_le_of_separated
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖) : ((Λ : Set (ι → ℂ)) ∩ Set.pi Set.univ
        (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))).Finite ∧
      (((Λ : Set (ι → ℂ)) ∩ Set.pi Set.univ
          (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))).ncard : ℝ) ≤
        (8 / ρ) ^ (2 * Fintype.card ι) := by
  -- Differences of distinct points in the subgroup's polydisc intersection are nonzero
  -- elements of the subgroup, so they satisfy the separation hypothesis.
  -- satisfy the separation hypothesis of the packing lemma with `c = 2`, `ε = ρ`.
  have hbound : (8 / ρ : ℝ) = 4 * 2 / ρ := by ring
  rw [hbound]
  refine finite_and_ncard_le_of_subset_pi_closedBall_of_separated r hr hρ0 hρ2
    Set.inter_subset_right ?_
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := hsep (x - y) (Λ.sub_mem hx.1 hy.1) (sub_ne_zero_of_ne hxy)
  exact ⟨i, by simpa using hi⟩

end Packing

section Doubling

/-- If two complex numbers share their coarse cell (side `2·ri/3`) in both the real and the
imaginary part, their distance is at most `ri`. -/
private theorem norm_sub_le_of_coarseCell_eq {ri : ℝ} (hri : 0 < ri) {z w : ℂ}
    (hre : ⌊z.re / (2 * ri / 3)⌋ = ⌊w.re / (2 * ri / 3)⌋)
    (him : ⌊z.im / (2 * ri / 3)⌋ = ⌊w.im / (2 * ri / 3)⌋) :
    ‖z - w‖ ≤ ri := by
  have hpos : (0 : ℝ) < 2 * ri / 3 := by positivity
  have hre' : |z.re - w.re| ≤ 2 * ri / 3 := by
    simpa [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos] using
      (Int.abs_sub_lt_one_of_floor_eq_floor hre).le
  have him' : |z.im - w.im| ≤ 2 * ri / 3 := by
    simpa [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos] using
      (Int.abs_sub_lt_one_of_floor_eq_floor him).le
  have hnorm : ‖z - w‖ ^ 2 ≤ ri ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [abs_le.mp hre', abs_le.mp him']
  nlinarith [norm_nonneg (z - w), hnorm, hri]

/-- A real of absolute value at most `2·ri` lands in one of the seven coarse cells
`Icc (-3) 3` of side `2·ri/3`. -/
private theorem coarseCell_mem_Icc {ri : ℝ} (hri : 0 < ri) {t : ℝ} (ht : |t| ≤ 2 * ri) :
    ⌊t / (2 * ri / 3)⌋ ∈ Finset.Icc (-3 : ℤ) 3 := by
  have hpos : (0 : ℝ) < 2 * ri / 3 := by positivity
  rw [Finset.mem_Icc]
  refine ⟨Int.le_floor.2 ?_, Int.le_of_lt_add_one (Int.floor_lt.2 ?_)⟩
  · rw [le_div_iff₀ hpos]; push_cast; nlinarith [abs_le.mp ht]
  · rw [div_lt_iff₀ hpos]; push_cast; nlinarith [abs_le.mp ht]

/-- The coarse cell index of `x` for the grid of side `2·r i/3`: per coordinate, the pair of
floor indices of the real and imaginary parts. -/
private noncomputable def coarseCellMap (r : ι → ℝ) (x : ι → ℂ) : ι → ℤ × ℤ :=
  fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)

/-- Two points sharing every coarse cell differ by at most `r i` in each coordinate. -/
private theorem sub_mem_pi_closedBall_one_of_coarseCellMap_eq {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) {y x : ι → ℂ}
    (h : coarseCellMap r y = coarseCellMap r x) : y - x ∈ Set.pi Set.univ
        (fun i ↦ Metric.closedBall (0 : ℂ) (r i)) := by
  intro i _
  simp only [Metric.mem_closedBall, dist_zero_right, Pi.sub_apply]
  have hc := congr_fun h i
  exact norm_sub_le_of_coarseCell_eq (hr i) (congr_arg Prod.fst hc) (congr_arg Prod.snd hc)

/-- A `g`-fibre of `sA` has at most `sB.card` elements when the difference of any two
same-fibre points of `sA` lies in `sB`: translating the fibre to a fixed representative
injects it into `sB`. -/
private theorem card_filter_le_of_sub_mem {G : Type*} [AddGroup G] {σ : Type*} [DecidableEq σ]
    {sA sB : Finset G} {g : G → σ} (h : ∀ y ∈ sA, ∀ x ∈ sA, g y = g x → y - x ∈ sB) (b : σ) :
    (sA.filter (fun a => g a = b)).card ≤ sB.card := by
  rcases (sA.filter (fun a => g a = b)).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · simp [he]
  · rw [Finset.mem_filter] at hx₀
    exact Finset.card_le_card_of_injOn (· - x₀)
      (fun y hy => h y (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1 x₀ hx₀.1
        ((Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2.trans hx₀.2.symm))
      (fun a _ c _ hac => by simpa using congrArg (· + x₀) hac)

variable [Fintype ι]

open scoped Classical in
/-- If `s` is in the polydisc of radii `2 * r i`, its coarse-cell image has at most `49 ^ #ι`
elements: each coordinate part lands in the seven cells `Icc (-3) 3`, so `49` cells per
coordinate and `49 ^ #ι` overall. -/
private theorem card_image_coarseCellMap_le {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {s : Finset (ι → ℂ)} (hs : ∀ x ∈ s, x ∈ Set.pi Set.univ
        (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))) :
    (s.image (coarseCellMap r)).card ≤ 49 ^ Fintype.card ι := by
  set T : Finset (ι → ℤ × ℤ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3) with hTdef
  have himage : s.image (coarseCellMap r) ⊆ T := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    rw [hTdef, Fintype.mem_piFinset]
    intro i
    have hy2 (i : ι) : ‖y i‖ ≤ 2 * r i := by
      simpa using hs y hy i (Set.mem_univ i)
    rw [Finset.mem_product]
    exact ⟨coarseCell_mem_Icc (hr i) ((Complex.abs_re_le_norm _).trans (hy2 i)),
      coarseCell_mem_Icc (hr i) ((Complex.abs_im_le_norm _).trans (hy2 i))⟩
  have hTeq : T.card = 49 ^ Fintype.card ι := by
    have hcard7 : (Finset.Icc (-3 : ℤ) 3).card = 7 := by rw [Int.card_Icc]; rfl
    rw [hTdef, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Finset.card_product, hcard7]
  exact hTeq ▸ Finset.card_le_card himage

/-- If the subgroup's intersection with the polydisc of radii `2 * r i` is finite, its
cardinality is at most `49 ^ #ι` times the count in the polydisc of radii `r i`. -/
theorem ncard_inter_pi_closedBall_two_le_pow_mul (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) (hfin : ((Λ : Set (ι → ℂ)) ∩ Set.pi Set.univ
        (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))).Finite) :
    (((Λ : Set (ι → ℂ)) ∩ Set.pi Set.univ
        (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))).ncard : ℝ) ≤
      49 ^ Fintype.card ι * ((Λ : Set (ι → ℂ)) ∩ Set.pi Set.univ
          (fun i ↦ Metric.closedBall (0 : ℂ) (r i))).ncard := by
  classical
  set A : Set (ι → ℂ) := (Λ : Set (ι → ℂ)) ∩ Set.pi Set.univ
      (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))
  set B : Set (ι → ℂ) := (Λ : Set (ι → ℂ)) ∩ Set.pi Set.univ
      (fun i ↦ Metric.closedBall (0 : ℂ) (r i))
  have hBfin : B.Finite := hfin.subset fun x hx ↦ ⟨hx.1, fun i hi ↦
    Metric.closedBall_subset_closedBall (by nlinarith [hr i]) (hx.2 i hi)⟩
  set sA : Finset (ι → ℂ) := hfin.toFinset with hsA
  set sB : Finset (ι → ℂ) := hBfin.toFinset with hsB
  -- Translating a coarse-cell fibre of `sA` to a representative injects it into `sB`.
  have hsub : ∀ y ∈ sA, ∀ x ∈ sA, coarseCellMap r y = coarseCellMap r x → y - x ∈ sB := by
    intro y hy x hx hyx
    rw [hsB, hBfin.mem_toFinset]
    exact ⟨Λ.sub_mem (hfin.mem_toFinset.mp hy).1 (hfin.mem_toFinset.mp hx).1,
      sub_mem_pi_closedBall_one_of_coarseCellMap_eq hr hyx⟩
  have hmul : sA.card ≤ sB.card * (sA.image (coarseCellMap r)).card :=
    Finset.card_le_mul_card_image sA sB.card fun b _ => card_filter_le_of_sub_mem hsub b
  have h49 : ((sA.image (coarseCellMap r)).card : ℝ) ≤ 49 ^ Fintype.card ι := by
    exact_mod_cast card_image_coarseCellMap_le hr fun z hz => (hfin.mem_toFinset.mp hz).2
  rw [Set.ncard_eq_toFinset_card A hfin, Set.ncard_eq_toFinset_card B hBfin, ← hsA, ← hsB]
  calc (sA.card : ℝ)
      ≤ (sB.card : ℝ) * ((sA.image (coarseCellMap r)).card : ℝ) := by exact_mod_cast hmul
    _ ≤ (sB.card : ℝ) * 49 ^ Fintype.card ι := mul_le_mul_of_nonneg_left h49 (by positivity)
    _ = 49 ^ Fintype.card ι * (sB.card : ℝ) := by ring

end Doubling

/-- Doubling for a discrete integral submodule, in particular a full `ZLattice`.
Compactness supplies the finiteness hypothesis of the measure-free subgroup estimate. -/
theorem ncard_inter_pi_closedBall_two_le_pow_mul_of_discreteTopology [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (L : Submodule ℤ (ι → ℂ)) [DiscreteTopology L] :
    (((L : Set (ι → ℂ)) ∩ Set.pi Set.univ
      (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))).ncard : ℝ) ≤
      49 ^ Fintype.card ι * ((L : Set (ι → ℂ)) ∩ Set.pi Set.univ
        (fun i ↦ Metric.closedBall (0 : ℂ) (r i))).ncard := by
  have hcompact : IsCompact (Set.pi Set.univ
      (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))) :=
    isCompact_univ_pi fun i ↦ isCompact_closedBall 0 _
  have hclosed : IsClosed (L : Set (ι → ℂ)) :=
    AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)
  have hfin : ((L : Set (ι → ℂ)) ∩ Set.pi Set.univ
      (fun i ↦ Metric.closedBall (0 : ℂ) (2 * r i))).Finite :=
    (hcompact.inter_left hclosed).finite
      ((isDiscrete_iff_discreteTopology.mpr ‹_›).mono Set.inter_subset_left)
  simpa only [Submodule.coe_toAddSubgroup] using
    ncard_inter_pi_closedBall_two_le_pow_mul r hr L.toAddSubgroup hfin

end TauCeti.GeometryOfNumbers
