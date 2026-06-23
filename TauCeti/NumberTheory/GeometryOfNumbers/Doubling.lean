/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval

/-!
# A measure-free lattice-point packing and doubling engine

This is the Layer-0 geometry-of-numbers engine of the effective-bounds roadmap: the two
*measure-free* cardinality estimates for an additive subgroup `Λ ≤ (ι → ℂ)` (`ι` finite)
inside the per-coordinate polydiscs `box r c = {x | ∀ i, ‖x i‖ ≤ c · r i}`. Both are proved
by grid pigeonhole alone — no Haar measure, no convex-body theorem, no covolume — so they
sit *upstream* of Mathlib's `ZLattice`/`MeasureTheory.Group.GeometryOfNumbers` machinery
rather than consuming it.

* **Packing** (`finite_and_ncard_le_of_subset_box_of_separated`): a subset of `box r c` whose
  distinct points are `ε`-separated in some coordinate is finite, with at most
  `(4·c/ε) ^ (2·#ι)` points.

* **Doubling** (`ncard_inter_box_two_le_pow_mul_ncard_inter_box_one`): passing from the unit
  box to the double box multiplies the lattice-point count by at most `64 ^ #ι`, i.e.
  `#(Λ ∩ box r 2) ≤ 64 ^ #ι · #(Λ ∩ box r 1)`, given that `Λ ∩ box r 2` is finite.

## Reconciliation with `ZLattice`

The roadmap asks that Layer 0 keep only the genuinely measure-free content. Accordingly:

* `box r c` is a *polydisc* — a product of per-coordinate closed discs with independent
  radii — not a ball, a fundamental domain, or any `ZLattice` notion; it is the natural
  counting region and is named only so the doubling statement can refer to it at two scales.
* `Λ` is an arbitrary `AddSubgroup (ι → ℂ)`: neither discreteness nor a covolume is used, so
  these bounds are strictly more general than the `ZLattice` API and do not duplicate it.
* The doubling bound takes the finiteness of `Λ ∩ box r 2` as a hypothesis. That is exactly
  what a `ZLattice`'s discreteness supplies (a discrete subgroup meets a bounded set in a
  finite set); the packing lemma here is one self-contained way to discharge it.

The doubling factor `64 ^ #ι` and the packing count are explicit and have no upstream
analogue: Mathlib's geometry of numbers is volumetric (Minkowski's convex-body theorem), not
a cardinal doubling estimate.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where the grid-pigeonhole core packed lattice points after projection to one
infinite place. The unit-distance application is dropped; only the reusable packing and
doubling bounds are migrated.
-/

public section

attribute [local instance] Classical.propDecidable

namespace TauCeti.GeometryOfNumbers

variable {ι : Type*}

/-- The closed polydisc of polyradius `c • r` in `ι → ℂ`: the points whose `i`-th
coordinate has norm at most `c · r i`. -/
def box (r : ι → ℝ) (c : ℝ) : Set (ι → ℂ) :=
  {x | ∀ i, ‖x i‖ ≤ c * r i}

/-- Membership in `box r c` unfolds to the coordinatewise norm bounds `‖x i‖ ≤ c · r i`. -/
@[simp] theorem mem_box {r : ι → ℝ} {c : ℝ} {x : ι → ℂ} :
    x ∈ box r c ↔ ∀ i, ‖x i‖ ≤ c * r i := Iff.rfl

/-- The polydisc `box r c` is monotone in the scale `c` when every coordinate radius `r i`
is nonnegative: enlarging the scale enlarges the box. -/
theorem box_mono {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {c c' : ℝ} (h : c ≤ c') :
    box r c ⊆ box r c' :=
  fun _ hx i => (hx i).trans (by have := hr i; nlinarith)

section Packing

variable [Fintype ι]

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

/-- Grid pigeonhole, cell-side bound: two coordinates in the same cell differ by less than
the cell side `ε·ri/√2`. -/
private theorem cell_index_diff {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri) {a b : ℝ}
    (h : ⌊(a + c * ri) / (ε * ri / Real.sqrt 2)⌋ = ⌊(b + c * ri) / (ε * ri / Real.sqrt 2)⌋) :
    |a - b| < ε * ri / Real.sqrt 2 := by
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hδ : 0 < ε * ri / Real.sqrt 2 := div_pos (mul_pos hε hri) hsqrt2
  set q := ε * ri / Real.sqrt 2
  have ha := Int.floor_le ((a + c * ri) / q)
  have ha' := Int.lt_floor_add_one ((a + c * ri) / q)
  have hb := Int.floor_le ((b + c * ri) / q)
  have hb' := Int.lt_floor_add_one ((b + c * ri) / q)
  rw [h] at ha ha'
  have hsub : (a + c * ri) / q - (b + c * ri) / q = (a - b) / q := by ring
  have hlt : (a - b) / q < 1 := by rw [← hsub]; linarith
  have hgt : -1 < (a - b) / q := by rw [← hsub]; linarith
  rw [abs_lt]
  exact ⟨by have := (lt_div_iff₀ hδ).mp hgt; linarith,
    by have := (div_lt_iff₀ hδ).mp hlt; linarith⟩

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

/-- **Grid pigeonhole / packing.** A subset of the polydisc `box r c` whose distinct points
are `ε`-separated in some coordinate (relative to `r`) is finite, of cardinality at most
`(4·c/ε) ^ (2·#ι)`. -/
theorem finite_and_ncard_le_of_subset_box_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) {S : Set (ι → ℂ)} (hS : S ⊆ box r c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, ε * r i < ‖x i - y i‖) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (4 * c / ε) ^ (2 * Fintype.card ι) := by
  -- The cell map sends a point to its tuple of cell indices — `⌊((x i).re + c·r i)/δ i⌋` and
  -- the analogous imaginary part, with cell side `δ i = ε·r i/√2` — landing in
  -- `ι → Icc 0 ⌊2√2·c/ε⌋ × Icc 0 ⌊2√2·c/ε⌋` and is injective on the separated set, because two
  -- points in the same cell of every coordinate differ by less than `ε·r i` there.
  set K : ℤ := (⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℤ) with hK
  set T : Finset (ι → ℤ × ℤ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc (0 : ℤ) K ×ˢ Finset.Icc (0 : ℤ) K) with hT
  -- The cell map, of cell side `ε·r i/√2` per coordinate.
  set g : (ι → ℂ) → (ι → ℤ × ℤ) :=
    fun x i => (⌊((x i).re + c * r i) / (ε * r i / Real.sqrt 2)⌋,
      ⌊((x i).im + c * r i) / (ε * r i / Real.sqrt 2)⌋)
  have key : ∀ x ∈ S, ∀ i, |(x i).re| ≤ c * r i ∧ |(x i).im| ≤ c * r i := fun x hx i =>
    ⟨(Complex.abs_re_le_norm _).trans (hS hx i), (Complex.abs_im_le_norm _).trans (hS hx i)⟩
  have hg : ∀ x ∈ S, g x ∈ T := by
    intro x hx
    rw [hT, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_product]
    exact ⟨cell_index_mem hε (hr i) (key x hx i).1, cell_index_mem hε (hr i) (key x hx i).2⟩
  -- The cell map is injective on `S`.
  have hg_inj : Set.InjOn g S := by
    intro x hx y hy hxy
    by_contra hne
    obtain ⟨i, hi⟩ := hsep x hx y hy hne
    have hdnn : (0 : ℝ) ≤ ε * r i / Real.sqrt 2 :=
      div_nonneg (mul_nonneg hε.le (hr i).le) (Real.sqrt_nonneg 2)
    have hre : |(x i).re - (y i).re| < ε * r i / Real.sqrt 2 :=
      cell_index_diff hε (hr i) (congr_arg Prod.fst (congr_fun hxy i))
    have him : |(x i).im - (y i).im| < ε * r i / Real.sqrt 2 :=
      cell_index_diff hε (hr i) (congr_arg Prod.snd (congr_fun hxy i))
    have hlt : ‖x i - y i‖ < (ε * r i / Real.sqrt 2) * Real.sqrt 2 :=
      norm_lt_of_re_im_bound hdnn
        (by rwa [Complex.sub_re]) (by rwa [Complex.sub_im])
    rw [div_mul_cancel₀ _ (by positivity : Real.sqrt 2 ≠ 0)] at hlt
    linarith
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

/-- **Lattice points in the box.** If every nonzero element of `Λ` escapes the small polydisc
`box r ρ` in some coordinate, then `Λ ∩ box r 2` is finite of cardinality at most
`(8/ρ) ^ (2·#ι)`. -/
theorem addSubgroup_inter_box_finite_and_ncard_le_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖) :
    ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite ∧
      (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤ (8 / ρ) ^ (2 * Fintype.card ι) := by
  -- Differences of distinct points of `Λ ∩ box r 2` are nonzero elements of `Λ`, so they
  -- satisfy the separation hypothesis of the packing lemma with `c = 2`, `ε = ρ`.
  have hbound : (8 / ρ : ℝ) = 4 * 2 / ρ := by ring
  rw [hbound]
  refine finite_and_ncard_le_of_subset_box_of_separated r hr hρ0 hρ2 Set.inter_subset_right ?_
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := hsep (x - y) (Λ.sub_mem hx.1 hy.1) (sub_ne_zero_of_ne hxy)
  exact ⟨i, by simpa using hi⟩

end Packing

section Doubling

variable [Fintype ι]

/-- Two reals lying in the same half-open floor-cell of positive width `q` (i.e.
`⌊a / q⌋ = ⌊b / q⌋`) differ by at most `q`. -/
private theorem abs_sub_le_of_floor_eq {a b q : ℝ} (hq : 0 < q) (h : ⌊a / q⌋ = ⌊b / q⌋) :
    |a - b| ≤ q := by
  rw [Int.floor_eq_iff] at h
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [h.1, h.2, Int.floor_le (b / q), Int.lt_floor_add_one (b / q), hq,
      mul_div_cancel₀ a hq.ne', mul_div_cancel₀ b hq.ne']

/-- If two complex numbers share their coarse cell (side `2·ri/3`) in both the real and the
imaginary part, their distance is at most `ri`. -/
private theorem norm_sub_le_of_coarseCell_eq {ri : ℝ} (hri : 0 < ri) {z w : ℂ}
    (hre : ⌊z.re / (2 * ri / 3)⌋ = ⌊w.re / (2 * ri / 3)⌋)
    (him : ⌊z.im / (2 * ri / 3)⌋ = ⌊w.im / (2 * ri / 3)⌋) :
    ‖z - w‖ ≤ ri := by
  have hpos : (0 : ℝ) < 2 * ri / 3 := by positivity
  have hre' : |z.re - w.re| ≤ 2 * ri / 3 := abs_sub_le_of_floor_eq hpos hre
  have him' : |z.im - w.im| ≤ 2 * ri / 3 := abs_sub_le_of_floor_eq hpos him
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

/-- **Doubling.** Assuming `Λ ∩ box r 2` is finite, counting lattice points in the double box
loses at most `64 ^ #ι` against the unit box:
`#(Λ ∩ box r 2) ≤ 64 ^ #ι · #(Λ ∩ box r 1)`. -/
theorem ncard_inter_box_two_le_pow_mul_ncard_inter_box_one (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite) :
    (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤
      64 ^ Fintype.card ι * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard := by
  set A : Set (ι → ℂ) := (Λ : Set (ι → ℂ)) ∩ box r 2
  set B : Set (ι → ℂ) := (Λ : Set (ι → ℂ)) ∩ box r 1
  have hBA : B ⊆ A := fun x hx => ⟨hx.1, box_mono (fun i => (hr i).le) one_le_two hx.2⟩
  have hBfin : B.Finite := hfin.subset hBA
  set sA : Finset (ι → ℂ) := hfin.toFinset with hsA
  set sB : Finset (ι → ℂ) := hBfin.toFinset with hsB
  set f : (ι → ℂ) → (ι → ℤ × ℤ) :=
    fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)
  have hfiber : ∀ b ∈ sA.image f, (sA.filter (fun a => f a = b)).card ≤ sB.card := by
    intro b hb
    obtain ⟨x₀, hx₀A, hx₀b⟩ := Finset.mem_image.mp hb
    have hmaps : ∀ y ∈ sA.filter (fun a => f a = b), y - x₀ ∈ sB := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have hyb : f y = f x₀ := hy.2.trans hx₀b.symm
      have hdiff : ∀ i, ‖(y - x₀) i‖ ≤ r i := by
        intro i
        have hcell := congr_fun hyb i
        rw [Pi.sub_apply]
        exact norm_sub_le_of_coarseCell_eq (hr i) (congr_arg Prod.fst hcell)
          (congr_arg Prod.snd hcell)
      have hyA : y ∈ A := (hfin.mem_toFinset).mp hy.1
      have hx₀A' : x₀ ∈ A := (hfin.mem_toFinset).mp hx₀A
      rw [hsB, hBfin.mem_toFinset]
      exact ⟨Λ.sub_mem hyA.1 hx₀A'.1, fun i => by rw [one_mul]; exact hdiff i⟩
    have hinj : Set.InjOn (fun y => y - x₀) ↑(sA.filter (fun a => f a = b)) :=
      fun a _ b _ h => by have h2 := congrArg (· + x₀) h; simpa using h2
    calc (sA.filter (fun a => f a = b)).card
        = ((sA.filter (fun a => f a = b)).image (fun y => y - x₀)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ sB.card := Finset.card_le_card (fun z hz => by
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz; exact hmaps y hy)
  set T : Finset (ι → ℤ × ℤ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3) with hTdef
  have himage : sA.image f ⊆ T := by
    intro b hb
    obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.mp hb
    have hyA' : y ∈ A := (hfin.mem_toFinset).mp hyA
    rw [hTdef, Fintype.mem_piFinset]
    intro i
    have hbre : |(y i).re| ≤ 2 * r i := (Complex.abs_re_le_norm _).trans (hyA'.2 i)
    have hbim : |(y i).im| ≤ 2 * r i := (Complex.abs_im_le_norm _).trans (hyA'.2 i)
    rw [Finset.mem_product]
    exact ⟨coarseCell_mem_Icc (hr i) hbre, coarseCell_mem_Icc (hr i) hbim⟩
  have hTcard : (T.card : ℝ) ≤ 64 ^ Fintype.card ι := by
    have hcard7 : (Finset.Icc (-3 : ℤ) 3).card = 7 := by rw [Int.card_Icc]; rfl
    have hTeq : T.card = 49 ^ Fintype.card ι := by
      rw [hTdef, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Finset.card_product, hcard7]
    rw [hTeq]; push_cast
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hmul : sA.card ≤ sB.card * (sA.image f).card :=
    Finset.card_le_mul_card_image sA sB.card hfiber
  have hAcard : A.ncard = sA.card := by rw [hsA]; exact Set.ncard_eq_toFinset_card A hfin
  have hBcard : B.ncard = sB.card := by rw [hsB]; exact Set.ncard_eq_toFinset_card B hBfin
  rw [hAcard, hBcard]
  have h64 : ((sA.image f).card : ℝ) ≤ 64 ^ Fintype.card ι :=
    le_trans (by exact_mod_cast Finset.card_le_card himage) hTcard
  calc (sA.card : ℝ)
      ≤ (sB.card : ℝ) * ((sA.image f).card : ℝ) := by exact_mod_cast hmul
    _ ≤ (sB.card : ℝ) * (64 ^ Fintype.card ι) := by
        exact mul_le_mul_of_nonneg_left h64 (by positivity)
    _ = 64 ^ Fintype.card ι * (sB.card : ℝ) := by ring

end Doubling

end TauCeti.GeometryOfNumbers
