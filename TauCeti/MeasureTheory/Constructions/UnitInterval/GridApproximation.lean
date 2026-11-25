/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Topology.MetricSpace.HausdorffDistance
import TauCeti.Topology.MetricSpace.Kuratowski

/-!
# Grid step approximation on the unit square

Cutting `[0, 1]` into `n` equal cells, as `TauCeti.unitInterval.cellFin n` does, cuts the unit
square `I × I` into `n²` grid cells. A *grid step function* is a function of the pair of cell
indices `(cellFin n x, cellFin n y)`. This file proves that grid step functions are dense in
`Lᵖ (I × I)` for every finite exponent, both for functions with values in a seminormed group and,
in the metric form of an `Lᵖ` discrepancy `‖(x, y) ↦ edist (κ (x, y)) (ω (i, j))‖_p`, for
functions with values in an arbitrary pseudometric space.

The metric form is what reads a measured kernel `κ : I × I → Z` as a limit of kernels on `n`
equally weighted points: the grid values are taken from any prescribed dense subset of `Z`, so
over a separable target they range over a countable set.

In a real normed space, the proof approximates by a bounded continuous function and evaluates it
at one point of each cell; uniform continuity on the compact square controls the error. The metric
statement embeds `Z` isometrically in the Banach space `Z →ᵇ ℝ` by the Fréchet–Kuratowski
embedding `TauCeti.kuratowskiEmbedding`, approximates there, and returns to `Z` by choosing, for
each grid value, a nearly closest point of the embedded copy of `Z` and then a nearby point of the
dense subset. Neither separability nor completeness of `Z` is assumed. The statement for a
seminormed group is the metric one with basepoint `0`.

## Main statements

* `TauCeti.unitInterval.exists_dist_comp_prodMap_cellFin_lt`: a continuous function on the unit
  square is uniformly approximated by grid step functions.
* `TauCeti.unitInterval.exists_eLpNorm_edist_comp_prodMap_cellFin_lt`: for `p ≠ ∞`, every almost
  everywhere strongly measurable `κ : I × I → Z` into a pseudometric space, with finite `p`-th
  moment about a point, is `ε`-close in the `Lᵖ` discrepancy to a grid step function with values
  in a given dense set.
* `TauCeti.unitInterval.exists_eLpNorm_sub_comp_prodMap_cellFin_lt`: for `p ≠ ∞`, every
  `f ∈ Lᵖ (I × I; E)` with values in a seminormed group is `ε`-close in `Lᵖ` to a grid step
  function.

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

variable {p : ℝ≥0∞}

/-- A grid step function `(x, y) ↦ G (cellFin n x, cellFin n y)` is strongly measurable. -/
theorem stronglyMeasurable_comp_prodMap_cellFin {β : Type*} [TopologicalSpace β] (n : ℕ) [NeZero n]
    (G : Fin n × Fin n → β) :
    StronglyMeasurable fun q : I × I ↦ G (cellFin n q.1, cellFin n q.2) :=
  StronglyMeasurable.of_discrete.comp_measurable
    ((measurable_cellFin.comp measurable_fst).prodMk (measurable_cellFin.comp measurable_snd))

/-- A continuous function on the unit square is uniformly within any positive `r` of a grid step
function. -/
theorem exists_dist_comp_prodMap_cellFin_lt {E : Type*} [PseudoMetricSpace E] (F : I × I → E)
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

/-- Grid step approximation in `Lᵖ` for a real normed space; the general seminormed statement
`exists_eLpNorm_sub_comp_prodMap_cellFin_lt` is derived from the metric one below. -/
private theorem exists_eLpNorm_sub_comp_prodMap_cellFin_lt_of_normedSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hp : p ≠ ∞) {f : I × I → E} (hf : MemLp f p)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (G : Fin n × Fin n → E),
      eLpNorm (fun q ↦ f q - G (cellFin n q.1, cellFin n q.2)) p volume < ε := by
  obtain ⟨η, hη, hhalf⟩ := exists_Lp_half E (volume : Measure (I × I)) p hε.ne'
  obtain ⟨r, -, hr₀, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  obtain ⟨F, hfF, -⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hp hη.ne'
  obtain ⟨n, hn, G, hG⟩ :=
    exists_dist_comp_prodMap_cellFin_lt F F.continuous (ENNReal.ofReal_pos.1 hr₀)
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
          (stronglyMeasurable_comp_prodMap_cellFin n G).aestronglyMeasurable)
          (ae_of_all _ fun q ↦ by rw [← dist_eq_norm]; exact (hG q).le)
    _ ≤ η := by simpa using hrη.le

/-- **Grid step approximation of metric-valued kernels.** Let `κ : I × I → Z` be almost everywhere
strongly measurable with values in a pseudometric space, with finite `p`-th moment
`‖(x, y) ↦ edist (κ (x, y)) z₀‖_p < ∞` about some point `z₀`, for a finite exponent `p`. Then for
every dense set `D ⊆ Z` and every positive `ε` there is a grid step function with values in `D`
whose `Lᵖ` discrepancy from `κ` is less than `ε`. The target `Z` need not be separable or
complete. -/
theorem exists_eLpNorm_edist_comp_prodMap_cellFin_lt {Z : Type*} [PseudoMetricSpace Z]
    (hp : p ≠ ∞) {κ : I × I → Z} (hκ : AEStronglyMeasurable κ volume) {z₀ : Z}
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
    simp [← hι.edist_eq, hι₀]
  obtain ⟨η, hη, hhalf⟩ := exists_Lp_half ℝ (volume : Measure (I × I)) p hε.ne'
  obtain ⟨r, -, hr₀, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr₀
  obtain ⟨n, hn, G, hG⟩ :=
    exists_eLpNorm_sub_comp_prodMap_cellFin_lt_of_normedSpace hp hf (ENNReal.half_pos hη.ne')
  choose ω hωD hω using fun ij ↦ hι.exists_mem_dist_le_two_mul_dist_add hD (G ij) hr
  refine ⟨n, hn, ω, hωD, ?_⟩
  -- Pointwise, `dist (κ q) (ω ij) ≤ 2 ‖g q‖ + r` on the cell `ij` of `q`.
  set g := fun q : I × I ↦ ι (κ q) - G (cellFin n q.1, cellFin n q.2)
  have hgm : AEStronglyMeasurable g volume :=
    hfm.sub (stronglyMeasurable_comp_prodMap_cellFin n G).aestronglyMeasurable
  have hpt : ∀ q, ‖edist (κ q) (ω (cellFin n q.1, cellFin n q.2))‖ₑ ≤
      ‖((2 : ℝ) • fun q ↦ ‖g q‖) q + r‖ₑ := fun q ↦ by
    simpa [edist_dist, g, ← dist_eq_norm] using
      (ENNReal.ofReal_le_ofReal (hω (cellFin n q.1, cellFin n q.2) (κ q))).trans_eq
        (Real.eNorm_of_nonneg (by positivity)).symm
  refine (eLpNorm_mono_eNorm (by fun_prop) hpt).trans_lt (hhalf _ _ ?_ ?_)
  · rw [eLpNorm_const_smul, eLpNorm_norm _ hgm, show ‖(2 : ℝ)‖ₑ = 2 by
      simpa using Real.eNorm_natCast 2]
    calc 2 * eLpNorm g p volume ≤ 2 * (η / 2) := by gcongr
      _ = η := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  · calc eLpNorm (fun _ ↦ r) p volume
        ≤ volume (univ : Set (I × I)) ^ p.toReal⁻¹ * ENNReal.ofReal r :=
          eLpNorm_le_of_ae_bound aestronglyMeasurable_const
            (ae_of_all _ fun _ ↦ (Real.norm_of_nonneg hr.le).le)
      _ ≤ η := by simpa using hrη.le

/-- **Grid step functions are dense in `Lᵖ` of the unit square.** For a finite exponent `p`, every
`f ∈ Lᵖ (I × I; E)` with values in a seminormed group is within any positive `ε` in `Lᵖ` of a grid
step function `(x, y) ↦ G (cellFin n x, cellFin n y)`. -/
theorem exists_eLpNorm_sub_comp_prodMap_cellFin_lt {E : Type*} [SeminormedAddCommGroup E]
    (hp : p ≠ ∞) {f : I × I → E} (hf : MemLp f p) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (G : Fin n × Fin n → E),
      eLpNorm (fun q ↦ f q - G (cellFin n q.1, cellFin n q.2)) p volume < ε := by
  obtain ⟨n, hn, G, -, hG⟩ := exists_eLpNorm_edist_comp_prodMap_cellFin_lt hp
    hf.aestronglyMeasurable (z₀ := 0) (by simpa using hf.eNorm)
    dense_univ hε
  have hm : AEStronglyMeasurable (fun q ↦ f q - G (cellFin n q.1, cellFin n q.2)) volume :=
    hf.aestronglyMeasurable.sub (stronglyMeasurable_comp_prodMap_cellFin n G).aestronglyMeasurable
  exact ⟨n, hn, G, (eLpNorm_eNorm _ hm).symm.trans_lt
    (by simpa only [eDist_eq_eNorm_sub] using hG)⟩

end unitInterval

end TauCeti
