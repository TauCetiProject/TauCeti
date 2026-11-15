/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import TauCeti.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Topology.MetricSpace.Kuratowski

/-!
# Grid step approximation on the unit square

Cutting `[0, 1]` into `n` equal cells, as `TauCeti.unitInterval.cellFin n` does, cuts the unit
square `I × I` into `n²` grid cells. A *grid step function* is a function of the pair of cell
indices `(cellFin n x, cellFin n y)`. This file proves that grid step functions are dense in
`Lᵖ (I × I)` for every finite exponent, both for functions with values in a real normed space and,
in the metric form of an `Lᵖ` discrepancy `‖(x, y) ↦ edist (κ (x, y)) (ω (i, j))‖_p`, for
functions with values in an arbitrary pseudometric space.

The metric form is what reads a measured kernel `κ : I × I → Z` as a limit of kernels on `n`
equally weighted points: the grid values are taken from any prescribed dense subset of `Z`, so
over a separable target they range over a countable set.

The normed statement approximates by a bounded continuous function and evaluates it at one point
of each cell; uniform continuity on the compact square controls the error. The metric statement
embeds `Z` isometrically in the Banach space `Z →ᵇ ℝ` by the Fréchet–Kuratowski embedding
`TauCeti.kuratowskiEmbedding`, approximates there, and returns to `Z` by choosing, for each grid
value, a nearly closest point of the embedded copy of `Z` and then a nearby point of the dense
subset. Neither separability nor completeness of `Z` is assumed.

## Main statements

* `TauCeti.unitInterval.dist_le_one_div_of_cellIdx_eq`: two points of the same cell of the
  `m`-fold equipartition are at distance at most `1 / m`.
* `TauCeti.unitInterval.measurePreserving_up_cellFin`: the cell index, lifted to any universe,
  carries `volume` to the uniform measure on `ULift (Fin n)`.
* `TauCeti.unitInterval.exists_dist_comp_cellFin_lt`: a continuous function on the unit square is
  uniformly approximated by grid step functions.
* `TauCeti.unitInterval.exists_eLpNorm_sub_comp_cellFin_lt`: for `p ≠ ∞`, every
  `f ∈ Lᵖ (I × I; E)` is `ε`-close in `Lᵖ` to a grid step function.
* `TauCeti.unitInterval.exists_eLpNorm_edist_comp_cellFin_lt`: for `p ≠ ∞`, every almost
  everywhere strongly measurable `κ : I × I → Z` into a pseudometric space, with finite `p`-th
  moment about a point, is `ε`-close in the `Lᵖ` discrepancy to a grid step function with values
  in a given dense set.

## References

* C. Kuratowski, *Quelques problèmes concernant les espaces métriques non-séparables*, Fund. Math.
  25 (1935), for the isometric embedding in a space of bounded functions.
-/

public section

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal unitInterval

namespace TauCeti

namespace unitInterval

universe u

variable {m : ℕ} {p : ℝ≥0∞}

/-- Two points of the same cell of the `m`-fold equipartition of `[0, 1]` are at distance at most
`1 / m`. -/
theorem dist_le_one_div_of_cellIdx_eq (hm : 0 < m) {x y : I} (h : cellIdx m x = cellIdx m y) :
    dist x y ≤ 1 / m := by
  have hx₁ := cellIdx_div_le m x
  have hx₂ := le_cellIdx_add_one_div hm x
  have hy₁ := cellIdx_div_le m y
  have hy₂ := le_cellIdx_add_one_div hm y
  rw [h] at hx₁ hx₂
  rw [add_div] at hx₂ hy₂
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  constructor <;> linarith

/-- A grid step function `(x, y) ↦ G (cellFin n x, cellFin n y)` is strongly measurable. -/
theorem stronglyMeasurable_comp_cellFin {β : Type*} [TopologicalSpace β] (n : ℕ) [NeZero n]
    (G : Fin n × Fin n → β) :
    StronglyMeasurable fun q : I × I ↦ G (cellFin n q.1, cellFin n q.2) :=
  StronglyMeasurable.of_discrete.comp_measurable
    ((measurable_cellFin.comp measurable_fst).prodMk (measurable_cellFin.comp measurable_snd))

/-- The cell index, lifted to any universe, carries `volume` on the unit interval to the uniform
measure on `ULift (Fin n)`. -/
theorem measurePreserving_up_cellFin (n : ℕ) [NeZero n] :
    MeasurePreserving (fun x : I ↦ ULift.up.{u} (cellFin n x)) volume
      (ProbabilityTheory.uniformOn univ) := by
  have hm : Measurable fun x : I ↦ ULift.up.{u} (cellFin n x) :=
    measurable_up.comp measurable_cellFin
  refine ⟨hm, Measure.ext_of_singleton fun i ↦ ?_⟩
  have hpre : (fun x : I ↦ ULift.up.{u} (cellFin n x)) ⁻¹' {i} = cellFin n ⁻¹' {i.down} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, ULift.ext_iff]
  rw [Measure.map_apply hm (measurableSet_singleton i), hpre,
    measurePreserving_cellFin.measure_preimage (measurableSet_singleton _).nullMeasurableSet,
    ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ, Measure.count_singleton,
    Measure.count_singleton, Fintype.card_ulift]

/-- A continuous function on the unit square is uniformly within any positive `r` of a grid step
function: its values at one chosen point of each cell, once the grid is fine enough. -/
theorem exists_dist_comp_cellFin_lt {E : Type*} [PseudoMetricSpace E] (F : I × I → E)
    (hF : Continuous F) {r : ℝ} (hr : 0 < r) :
    ∃ (n : ℕ) (_ : NeZero n) (G : Fin n × Fin n → E),
      ∀ q : I × I, dist (F q) (G (cellFin n q.1, cellFin n q.2)) < r := by
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hF) r hr
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have : NeZero (n + 1) := ⟨n.succ_ne_zero⟩
  -- `c i` is a point of the `i`-th cell.
  let c : Fin (n + 1) → I := Function.surjInv cellFin_surjective
  have hc : ∀ x : I, dist x (c (cellFin (n + 1) x)) < δ := fun x ↦ by
    refine (dist_le_one_div_of_cellIdx_eq n.succ_pos ?_).trans_lt (by exact_mod_cast hn)
    simpa using congrArg Fin.val (Function.surjInv_eq cellFin_surjective (cellFin (n + 1) x)).symm
  refine ⟨n + 1, inferInstance, fun ij ↦ F (c ij.1, c ij.2), fun q ↦ hFδ ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hc q.1, hc q.2⟩

/-- **Grid step functions are dense in `Lᵖ` of the unit square.** For a finite exponent `p`, every
`f ∈ Lᵖ (I × I; E)` is within any positive `ε` in `Lᵖ` of a grid step function
`(x, y) ↦ G (cellFin n x, cellFin n y)`. -/
theorem exists_eLpNorm_sub_comp_cellFin_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hp : p ≠ ∞) {f : I × I → E} (hf : MemLp f p) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (G : Fin n × Fin n → E),
      eLpNorm (fun q ↦ f q - G (cellFin n q.1, cellFin n q.2)) p volume < ε := by
  obtain ⟨η, hη, hhalf⟩ := exists_Lp_half E (volume : Measure (I × I)) p hε.ne'
  obtain ⟨r, -, hr₀, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  obtain ⟨F, hfF, -⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hp hη.ne'
  obtain ⟨n, hn, G, hG⟩ := exists_dist_comp_cellFin_lt F F.continuous (ENNReal.ofReal_pos.1 hr₀)
  refine ⟨n, hn, G, ?_⟩
  have hsplit : (fun q ↦ f q - G (cellFin n q.1, cellFin n q.2)) =
      (f - F) + fun q ↦ F q - G (cellFin n q.1, cellFin n q.2) := by
    ext q
    simp
  rw [hsplit]
  refine hhalf _ _ hfF ?_
  calc eLpNorm (fun q ↦ F q - G (cellFin n q.1, cellFin n q.2)) p volume
      ≤ volume (univ : Set (I × I)) ^ p.toReal⁻¹ * ENNReal.ofReal r :=
        eLpNorm_le_of_ae_bound (F.continuous.aestronglyMeasurable.sub
          (stronglyMeasurable_comp_cellFin n G).aestronglyMeasurable)
          (ae_of_all _ fun q ↦ by rw [← dist_eq_norm]; exact (hG q).le)
    _ ≤ η := by simpa using hrη.le

/-- For an isometry `ι : Z → E` of a nonempty space, every `y : E` has a point `z` of a dense set
`D ⊆ Z` with `dist s z ≤ 2 * dist (ι s) y + 2 * r` for every `s : Z`: an approximate nearest point
of the image of `ι`, moved slightly into `D`. -/
private theorem exists_mem_dist_le_two_mul_dist_add {Z E : Type*} [PseudoMetricSpace Z]
    [PseudoMetricSpace E] [Nonempty Z] {ι : Z → E} (hι : Isometry ι) {D : Set Z} (hD : Dense D)
    (y : E) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ D, ∀ s, dist s z ≤ 2 * dist (ι s) y + 2 * r := by
  obtain ⟨_, ⟨s₀, rfl⟩, hs₀⟩ :=
    (infDist_lt_iff (range_nonempty ι)).1 (lt_add_of_pos_right (infDist y (range ι)) hr)
  obtain ⟨z, hzD, hz⟩ := hD.exists_dist_lt s₀ hr
  refine ⟨z, hzD, fun s ↦ ?_⟩
  have h₁ := dist_triangle s s₀ z
  have h₂ := hι.dist_eq s s₀
  have h₃ := dist_triangle (ι s) y (ι s₀)
  have h₄ : infDist y (range ι) ≤ dist (ι s) y := by
    rw [dist_comm]
    exact infDist_le_dist_of_mem (mem_range_self s)
  linarith

/-- **Grid step approximation of metric-valued kernels.** Let `κ : I × I → Z` be almost everywhere
strongly measurable with values in a pseudometric space, with finite `p`-th moment
`‖(x, y) ↦ edist (κ (x, y)) z₀‖_p < ∞` about some point `z₀`, for a finite exponent `p`. Then for
every dense set `D ⊆ Z` and every positive `ε` there is a grid step function with values in `D`
whose `Lᵖ` discrepancy from `κ` is less than `ε`. The target `Z` need not be separable or
complete. -/
theorem exists_eLpNorm_edist_comp_cellFin_lt {Z : Type*} [PseudoMetricSpace Z] (hp : p ≠ ∞)
    {κ : I × I → Z} (hκ : AEStronglyMeasurable κ volume) {z₀ : Z}
    (hz₀ : MemLp (fun q ↦ edist (κ q) z₀) p volume) {D : Set Z} (hD : Dense D) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (ω : Fin n × Fin n → Z), (∀ ij, ω ij ∈ D) ∧
      eLpNorm (fun q ↦ edist (κ q) (ω (cellFin n q.1, cellFin n q.2))) p volume < ε := by
  -- Embed `Z` isometrically in the Banach space `Z →ᵇ ℝ`, approximate there, and return to `D`
  -- cell by cell.
  have : Nonempty Z := ⟨z₀⟩
  set ι := kuratowskiEmbedding z₀
  have hι : Isometry ι := isometry_kuratowskiEmbedding z₀
  have hι₀ : ι z₀ = 0 := by
    ext y
    simp [ι]
  have hfm : AEStronglyMeasurable (fun q ↦ ι (κ q)) volume :=
    hι.continuous.comp_aestronglyMeasurable hκ
  have hf : MemLp (fun q ↦ ι (κ q)) p volume := by
    refine (eLpNorm_mono_eNorm hfm fun q ↦ ?_).trans_lt hz₀
    rw [eNorm_eq_self, ← hι.edist_eq, hι₀, eDist_eq_eNorm_sub, sub_zero]
  obtain ⟨η, hη, hhalf⟩ := exists_Lp_half ℝ (volume : Measure (I × I)) p hε.ne'
  obtain ⟨r, -, hr₀, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.1 (ENNReal.half_pos hη.ne')
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr₀
  obtain ⟨n, hn, G, hG⟩ := exists_eLpNorm_sub_comp_cellFin_lt hp hf (ENNReal.half_pos hη.ne')
  choose ω hωD hω using fun ij ↦ exists_mem_dist_le_two_mul_dist_add hι hD (G ij) hr
  refine ⟨n, hn, ω, hωD, ?_⟩
  -- Pointwise, `dist (κ q) (ω ij) ≤ 2 ‖g q‖ + 2 r` on the cell `ij` of `q`.
  set g := fun q : I × I ↦ ι (κ q) - G (cellFin n q.1, cellFin n q.2)
  have hgm : AEStronglyMeasurable g volume :=
    hfm.sub (stronglyMeasurable_comp_cellFin n G).aestronglyMeasurable
  have hpt : ∀ q, ‖edist (κ q) (ω (cellFin n q.1, cellFin n q.2))‖ₑ ≤
      ‖((2 : ℝ) • fun q ↦ ‖g q‖) q + 2 * r‖ₑ := fun q ↦ by
    rw [eNorm_eq_self, edist_dist, Pi.smul_apply, smul_eq_mul,
      Real.eNorm_of_nonneg (by positivity), ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (hω _ _)
  refine (eLpNorm_mono_eNorm (by fun_prop) hpt).trans_lt (hhalf _ _ ?_ ?_)
  · rw [eLpNorm_const_smul, eLpNorm_norm _ hgm, show ‖(2 : ℝ)‖ₑ = 2 by
      simpa using Real.eNorm_natCast 2]
    calc 2 * eLpNorm g p volume ≤ 2 * (η / 2) := by gcongr
      _ = η := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  · calc eLpNorm (fun _ ↦ 2 * r) p volume
        ≤ volume (univ : Set (I × I)) ^ p.toReal⁻¹ * ENNReal.ofReal (2 * r) :=
          eLpNorm_le_of_ae_bound aestronglyMeasurable_const
            (ae_of_all _ fun _ ↦ (Real.norm_of_nonneg (by positivity)).le)
      _ = 2 * ENNReal.ofReal r := by simp [ENNReal.ofReal_mul]
      _ ≤ 2 * (η / 2) := by gcongr
      _ = η := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

end unitInterval

end TauCeti
