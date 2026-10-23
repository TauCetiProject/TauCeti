/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import TauCeti.MeasureTheory.MeasurableSpace.Embedding
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.TransportationDistance

/-!
# The Gromov–Prokhorov distance

Two measures `μ` on an extended pseudometric space `X` and `ν` on another such space `Y` are
compared by the *Gromov–Prokhorov distance*: the least Lévy–Prokhorov distance between isometric
copies of them in a common space. As for Sturm's transportation distance `TauCeti.sturmEDist`, the
common space can be taken to be the disjoint union `X ⊕ Y`, glued by a metric coupling `f`
(`TauCeti.IsMetricCoupling`), so

`d_GP (μ, ν) = ⨅ f, d_LP (inl_# μ, inr_# ν)`,

the Lévy–Prokhorov distance `MeasureTheory.levyProkhorovEDist` being computed for the glued
pseudometric `TauCeti.IsMetricCoupling.pseudoEMetricSpace`. Every other pair of a.e.-measurable
isometric embeddings into a common space with measurable open sets gives an upper bound
(`TauCeti.gromovProkhorovEDist_le_levyProkhorovEDist_map`), so allowing arbitrary common spaces
would not lower the infimum.

Placing the spaces side by side, the Lévy–Prokhorov condition only involves the cross distances:
`d_GP (μ, ν) ≤ δ` as soon as some metric coupling `f` satisfies
`μ A ≤ ν {y | ∃ x ∈ A, f x y < δ} + δ` and `ν C ≤ μ {x | ∃ y ∈ C, f x y < δ} + δ` for all
measurable `A` and `C` (`TauCeti.gromovProkhorovEDist_le_of_isMetricCoupling`), and conversely
`d_GP (μ, ν) < δ` provides such a coupling
(`TauCeti.exists_isMetricCoupling_of_gromovProkhorovEDist_lt`). Everything below is proved through
these two statements.

* The distance is symmetric (`TauCeti.gromovProkhorovEDist_comm`), at most the Lévy–Prokhorov
  distance on a single space (`TauCeti.gromovProkhorovEDist_le_levyProkhorovEDist`), and at most the
  larger of the two masses (`TauCeti.gromovProkhorovEDist_le_max_measure_univ`).
* It satisfies the triangle inequality whenever the open sets of the middle space are measurable
  (`TauCeti.gromovProkhorovEDist_triangle`): metric couplings glue along the middle space
  (`TauCeti.IsMetricCoupling.comp`), and the two Lévy–Prokhorov conditions compose. Unlike the
  transportation distance, no gluing of couplings of measures is needed, so there is no standard
  Borel hypothesis.
* It only depends on the isomorphism classes of metric-measure spaces: a measure and its image
  under an isometry are at distance `0` (`TauCeti.gromovProkhorovEDist_map_eq_zero`), replacing a
  measure by such an image does not change any distance (`TauCeti.gromovProkhorovEDist_map_left`),
  hence measure-preserving isometries preserve the distance
  (`TauCeti.MeasurePreservingIsometry.gromovProkhorovEDist_left`) and a metric-measure space may be
  replaced by its support (`TauCeti.MetricMeasureSpace.gromovProkhorovEDist_supportSpace`).
* It is controlled by Sturm's transportation distance. If a coupling `π` of the measures gives mass
  at most `δ` to the pairs at cross distance at least `δ`, then `d_GP (μ, ν) ≤ δ`
  (`TauCeti.gromovProkhorovEDist_le_of_isCoupling`), which is the easy half of Strassen's theorem.
  With Markov's inequality this gives `d_GP ≤ D_p ^ (p / (p + 1))` for `0 < p < ∞`
  (`TauCeti.gromovProkhorovEDist_le_sturmEDist_rpow`) and `d_GP ≤ D_∞`
  (`TauCeti.gromovProkhorovEDist_le_sturmEDist_top`). So convergence for `D_p` implies
  Gromov–Prokhorov convergence.

## Main definitions

* `TauCeti.gromovProkhorovEDist μ ν`: the infimum, over the metric couplings `f` of `X` and `Y`, of
  the Lévy–Prokhorov distance between the copies of `μ` and `ν` in `X ⊕ Y` glued by `f`.

## Implementation notes

The measures are raw `MeasureTheory.Measure`s, and the disjoint union carries its own measurable
structure, for which both inclusions are measurable embeddings (`MeasurableEmbedding.inl`). The
glued pseudometric is used only through the Lévy–Prokhorov distance, which needs no topology, so
it never meets the topology of the disjoint union.

## References

* A. Greven, P. Pfaffelhuber and A. Winter, *Convergence in distribution of random metric measure
  spaces (Λ-coalescent measure trees)*, Probab. Theory Related Fields 145 (2009), 285--322, §2, for
  the Gromov–Prokhorov metric as an infimum of Prokhorov distances over common isometric
  embeddings.
* V. Strassen, *The existence of probability measures with given marginals*, Ann. Math. Statist.
  36 (1965), 423--439, for the comparison of the Prokhorov distance with couplings.
* A. L. Gibbs and F. E. Su, *On choosing and bounding probability metrics*, Int. Stat. Rev. 70
  (2002), 419--435, Theorem 2, for the bound of the Prokhorov distance by the Wasserstein distance.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace TauCeti

variable {X X' Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace X'] [PseudoEMetricSpace Y]
  [PseudoEMetricSpace Z] [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Z] {μ : Measure X} {ν : Measure Y} {f : X → Y → ℝ≥0∞} {δ : ℝ≥0∞}

/-- The **Gromov–Prokhorov distance** of `μ` and `ν`: the infimum, over the metric couplings `f` of
`X` and `Y`, of the Lévy–Prokhorov distance between the copies of `μ` and `ν` in the disjoint union
`X ⊕ Y` with the pseudometric glued by `f`. This is the Gromov–Prokhorov distance of Greven,
Pfaffelhuber and Winter with the common ambient space taken to be the disjoint union; by
`TauCeti.gromovProkhorovEDist_le_levyProkhorovEDist_map`, a.e.-measurable isometric embeddings into
any other common space with measurable open sets give no smaller value. -/
def gromovProkhorovEDist (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨅ (f : X → Y → ℝ≥0∞) (hf : IsMetricCoupling f),
    letI := hf.pseudoEMetricSpace
    levyProkhorovEDist (μ.map Sum.inl) (ν.map Sum.inr)

/-- **Upper bounds.** If some metric coupling `f` moves every measurable set `A ⊆ X` into the set
of points of `Y` at cross distance less than `δ` from `A` up to mass `δ`, and symmetrically, then
the Gromov–Prokhorov distance is at most `δ`. -/
theorem gromovProkhorovEDist_le_of_isMetricCoupling (hf : IsMetricCoupling f)
    (h₁ : ∀ A, MeasurableSet A → μ A ≤ ν {y | ∃ x ∈ A, f x y < δ} + δ)
    (h₂ : ∀ C, MeasurableSet C → ν C ≤ μ {x | ∃ y ∈ C, f x y < δ} + δ) :
    gromovProkhorovEDist μ ν ≤ δ := by
  refine (iInf₂_le f hf).trans ?_
  let := hf.pseudoEMetricSpace
  refine levyProkhorovEDist_le_of_forall _ _ δ fun ε B hδε hε hB ↦ ⟨?_, ?_⟩
  · rw [MeasurableEmbedding.inl.map_apply, MeasurableEmbedding.inr.map_apply]
    refine (h₁ _ (measurable_inl hB)).trans (add_le_add (measure_mono ?_) hδε.le)
    rintro y ⟨x, hx, hxy⟩
    rw [mem_preimage, mem_thickening_iff_exists_edist_lt]
    refine ⟨.inl x, hx, ?_⟩
    rw [hf.pseudoEMetricSpace_edist_inr_inl, ENNReal.ofReal_toReal hε.ne]
    exact hxy.trans hδε
  · rw [MeasurableEmbedding.inl.map_apply, MeasurableEmbedding.inr.map_apply]
    refine (h₂ _ (measurable_inr hB)).trans (add_le_add (measure_mono ?_) hδε.le)
    rintro x ⟨y, hy, hxy⟩
    rw [mem_preimage, mem_thickening_iff_exists_edist_lt]
    refine ⟨.inr y, hy, ?_⟩
    rw [hf.pseudoEMetricSpace_edist_inl_inr, ENNReal.ofReal_toReal hε.ne]
    exact hxy.trans hδε

/-- **Lower bounds.** If the Gromov–Prokhorov distance is less than `δ`, some metric coupling `f`
moves every measurable set `A ⊆ X` into the set of points of `Y` at cross distance less than `δ`
from `A` up to mass `δ`, and symmetrically. -/
theorem exists_isMetricCoupling_of_gromovProkhorovEDist_lt (h : gromovProkhorovEDist μ ν < δ) :
    ∃ f : X → Y → ℝ≥0∞, IsMetricCoupling f ∧
      (∀ A, MeasurableSet A → μ A ≤ ν {y | ∃ x ∈ A, f x y < δ} + δ) ∧
      ∀ C, MeasurableSet C → ν C ≤ μ {x | ∃ y ∈ C, f x y < δ} + δ := by
  simp only [gromovProkhorovEDist, iInf_lt_iff] at h
  obtain ⟨f, hf, h⟩ := h
  let := hf.pseudoEMetricSpace
  refine ⟨f, hf, fun A hA ↦ ?_, fun C hC ↦ ?_⟩
  · have := left_measure_le_of_levyProkhorovEDist_lt h (hA.inl_image (β := Y))
    rw [MeasurableEmbedding.inl.map_apply, MeasurableEmbedding.inr.map_apply,
      Sum.inl_injective.preimage_image] at this
    refine this.trans (add_le_add_left (measure_mono ?_) _)
    intro y hy
    rw [mem_preimage, mem_thickening_iff_exists_edist_lt] at hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hy
    rw [hf.pseudoEMetricSpace_edist_inr_inl] at hxy
    exact ⟨x, hx, hxy.trans_le ENNReal.ofReal_toReal_le⟩
  · have := right_measure_le_of_levyProkhorovEDist_lt h (hC.inr_image (α := X))
    rw [MeasurableEmbedding.inl.map_apply, MeasurableEmbedding.inr.map_apply,
      Sum.inr_injective.preimage_image] at this
    refine this.trans (add_le_add_left (measure_mono ?_) _)
    intro x hx
    rw [mem_preimage, mem_thickening_iff_exists_edist_lt] at hx
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx
    rw [hf.pseudoEMetricSpace_edist_inl_inr] at hxy
    exact ⟨y, hy, hxy.trans_le ENNReal.ofReal_toReal_le⟩

/-- One half of `TauCeti.gromovProkhorovEDist_comm`. -/
private theorem gromovProkhorovEDist_swap_le (μ : Measure X) (ν : Measure Y) :
    gromovProkhorovEDist ν μ ≤ gromovProkhorovEDist μ ν :=
  le_of_forall_gt_imp_ge_of_dense fun _ hδ ↦
    let ⟨_, hf, h₁, h₂⟩ := exists_isMetricCoupling_of_gromovProkhorovEDist_lt hδ
    gromovProkhorovEDist_le_of_isMetricCoupling hf.swap h₂ h₁

/-- **Symmetry.** Exchanging the two measures does not change their Gromov–Prokhorov distance. -/
theorem gromovProkhorovEDist_comm (μ : Measure X) (ν : Measure Y) :
    gromovProkhorovEDist μ ν = gromovProkhorovEDist ν μ :=
  le_antisymm (gromovProkhorovEDist_swap_le ν μ) (gromovProkhorovEDist_swap_le μ ν)

/-- The Gromov–Prokhorov distance is at most the larger of the two total masses: the two spaces can
always be placed infinitely far apart. -/
theorem gromovProkhorovEDist_le_max_measure_univ (μ : Measure X) (ν : Measure Y) :
    gromovProkhorovEDist μ ν ≤ max (μ univ) (ν univ) :=
  gromovProkhorovEDist_le_of_isMetricCoupling isMetricCoupling_top
    (fun _ _ ↦ (measure_mono (subset_univ _)).trans (le_max_left _ _) |>.trans le_add_self)
    fun _ _ ↦ (measure_mono (subset_univ _)).trans (le_max_right _ _) |>.trans le_add_self

/-- Finite measures are at finite Gromov–Prokhorov distance. -/
theorem gromovProkhorovEDist_ne_top (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : gromovProkhorovEDist μ ν ≠ ∞ :=
  ne_top_of_le_ne_top (max_ne_top (measure_ne_top μ univ) (measure_ne_top ν univ))
    (gromovProkhorovEDist_le_max_measure_univ μ ν)

section Embedding

variable [OpensMeasurableSpace Z]

omit [PseudoEMetricSpace X] [PseudoEMetricSpace Y] in
/-- A Lévy–Prokhorov bound between images of `μ` and `ν` in a common space `Z` moves every set
`A ⊆ X` into the points of `Y` whose image is close to the image of `A`. -/
private theorem measure_le_of_levyProkhorovEDist_map_lt {T : X → Z} {S : Y → Z}
    (hT : AEMeasurable T μ) (hS : AEMeasurable S ν)
    (h : levyProkhorovEDist (μ.map T) (ν.map S) < δ) (hδ : δ ≠ ∞) (A : Set X) :
    μ A ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ :=
  calc μ A ≤ μ.map T (closure (T '' A)) :=
        (Measure.le_map_apply_image hT A).trans (measure_mono subset_closure)
    _ ≤ ν.map S (thickening δ.toReal (closure (T '' A))) + δ :=
        left_measure_le_of_levyProkhorovEDist_lt h isClosed_closure.measurableSet
    _ = ν (S ⁻¹' thickening δ.toReal (T '' A)) + δ := by
        rw [thickening_closure, Measure.map_apply_of_aemeasurable hS
          isOpen_thickening.measurableSet]
    _ ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ := by
        refine add_le_add_left (measure_mono fun y hy ↦ ?_) _
        rw [mem_preimage, mem_thickening_iff_exists_edist_lt] at hy
        obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hy
        rw [edist_comm, ENNReal.ofReal_toReal hδ] at hxy
        exact ⟨x, hx, hxy⟩

/-- **Common isometric embeddings.** The Gromov–Prokhorov distance is at most the Lévy–Prokhorov
distance between the images of `μ` and `ν` under a.e.-measurable isometric embeddings into any
common space whose open sets are measurable. -/
theorem gromovProkhorovEDist_le_levyProkhorovEDist_map {T : X → Z} {S : Y → Z}
    (hT : Isometry T) (hS : Isometry S) (hTm : AEMeasurable T μ) (hSm : AEMeasurable S ν) :
    gromovProkhorovEDist μ ν ≤ levyProkhorovEDist (μ.map T) (ν.map S) := by
  refine le_of_forall_gt_imp_ge_of_dense fun δ hδ ↦ ?_
  rcases eq_or_ne δ ∞ with rfl | hδtop
  · exact le_top
  refine gromovProkhorovEDist_le_of_isMetricCoupling (IsMetricCoupling.of_isometry hT hS)
    (fun A _ ↦ measure_le_of_levyProkhorovEDist_map_lt hTm hSm hδ hδtop A) fun C _ ↦ ?_
  rw [levyProkhorovEDist_comm] at hδ
  refine (measure_le_of_levyProkhorovEDist_map_lt hSm hTm hδ hδtop C).trans
    (add_le_add_left (measure_mono ?_) _)
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, hy, edist_comm (S y) (T x) ▸ hxy⟩

end Embedding

/-- On a single space, the Gromov–Prokhorov distance is at most the Lévy–Prokhorov distance. -/
theorem gromovProkhorovEDist_le_levyProkhorovEDist (μ ν : Measure X) :
    gromovProkhorovEDist μ ν ≤ levyProkhorovEDist μ ν := by
  refine le_of_forall_gt_imp_ge_of_dense fun δ hδ ↦ ?_
  rcases eq_or_ne δ ∞ with rfl | hδtop
  · exact le_top
  have hsub (A : Set X) : thickening δ.toReal A ⊆ {y | ∃ x ∈ A, edist y x < δ} := fun y hy ↦ by
    rwa [mem_thickening_iff_exists_edist_lt, ENNReal.ofReal_toReal hδtop] at hy
  refine gromovProkhorovEDist_le_of_isMetricCoupling isMetricCoupling_edist (fun A hA ↦ ?_)
    fun C hC ↦ (right_measure_le_of_levyProkhorovEDist_lt hδ hC).trans
      (add_le_add_left (measure_mono (hsub C)) _)
  simpa only [edist_comm] using (left_measure_le_of_levyProkhorovEDist_lt hδ hA).trans
    (add_le_add_left (measure_mono (hsub A)) _)

/-- The Gromov–Prokhorov distance from a measure to itself vanishes. -/
@[simp]
theorem gromovProkhorovEDist_self (μ : Measure X) :
    gromovProkhorovEDist μ μ = 0 :=
  nonpos_iff_eq_zero.mp ((gromovProkhorovEDist_le_levyProkhorovEDist μ μ).trans_eq
    (levyProkhorovEDist_self μ))

/-- **Isometric images are at distance zero.** A measure and its pushforward along an isometry are
at Gromov–Prokhorov distance `0`. -/
theorem gromovProkhorovEDist_map_eq_zero {T : X → Y} (hT : Isometry T) (hTm : AEMeasurable T μ) :
    gromovProkhorovEDist μ (μ.map T) = 0 := by
  refine nonpos_iff_eq_zero.mp <| le_of_forall_gt_imp_ge_of_dense fun δ hδ ↦ ?_
  refine gromovProkhorovEDist_le_of_isMetricCoupling (IsMetricCoupling.of_isometry hT isometry_id)
    (fun A _ ↦ ?_) fun C hC ↦ ?_
  · refine (Measure.le_map_apply_image hTm A).trans (le_add_right (measure_mono ?_))
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (edist_self (T x)).trans_lt hδ⟩
  · refine (Measure.map_apply_of_aemeasurable hTm hC).trans_le (le_add_right (measure_mono ?_))
    exact fun x hx ↦ ⟨T x, hx, (edist_self (T x)).trans_lt hδ⟩

section Triangle

variable [OpensMeasurableSpace Y]

/-- The quantitative triangle inequality: Gromov–Prokhorov distances less than `a` and `b` give a
distance at most `a + b`. -/
private theorem gromovProkhorovEDist_le_add_of_lt {ρ : Measure Z} {a b : ℝ≥0∞}
    (ha : gromovProkhorovEDist μ ν < a) (hb : gromovProkhorovEDist ν ρ < b) :
    gromovProkhorovEDist μ ρ ≤ a + b := by
  obtain ⟨f, hf, hf₁, hf₂⟩ := exists_isMetricCoupling_of_gromovProkhorovEDist_lt ha
  obtain ⟨g, hg, hg₁, hg₂⟩ := exists_isMetricCoupling_of_gromovProkhorovEDist_lt hb
  refine gromovProkhorovEDist_le_of_isMetricCoupling (hf.comp hg) (fun A hA ↦ ?_) fun C hC ↦ ?_
  · calc μ A ≤ ν {y | ∃ x ∈ A, f x y < a} + a := hf₁ A hA
      _ ≤ ρ {z | ∃ y ∈ {y | ∃ x ∈ A, f x y < a}, g y z < b} + b + a :=
        add_le_add_left (hg₁ _ (hf.isOpen_setOf_exists_lt A a).measurableSet) _
      _ ≤ ρ {z | ∃ x ∈ A, ⨅ y, f x y + g y z < a + b} + (a + b) := by
        rw [add_assoc, add_comm b a]
        refine add_le_add_left (measure_mono ?_) _
        rintro z ⟨y, ⟨x, hx, hxy⟩, hyz⟩
        exact ⟨x, hx, (iInf_le _ y).trans_lt (ENNReal.add_lt_add hxy hyz)⟩
  · calc ρ C ≤ ν {y | ∃ z ∈ C, g y z < b} + b := hg₂ C hC
      _ ≤ μ {x | ∃ y ∈ {y | ∃ z ∈ C, g y z < b}, f x y < a} + a + b :=
        add_le_add_left (hf₂ _ (hg.swap.isOpen_setOf_exists_lt C b).measurableSet) _
      _ ≤ μ {x | ∃ z ∈ C, ⨅ y, f x y + g y z < a + b} + (a + b) := by
        rw [add_assoc]
        refine add_le_add_left (measure_mono ?_) _
        rintro x ⟨y, ⟨z, hz, hyz⟩, hxy⟩
        exact ⟨z, hz, (iInf_le _ y).trans_lt (ENNReal.add_lt_add hxy hyz)⟩

/-- **The triangle inequality.** It holds whenever the open sets of the middle space are
measurable: the two metric couplings glue along the middle space. -/
theorem gromovProkhorovEDist_triangle (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) :
    gromovProkhorovEDist μ ρ ≤ gromovProkhorovEDist μ ν + gromovProkhorovEDist ν ρ := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos (by exact_mod_cast hε.ne') ENNReal.ofNat_ne_top
  have h₁ := ENNReal.lt_add_right (ENNReal.add_lt_top.1 hlt).1.ne hε2.ne'
  have h₂ := ENNReal.lt_add_right (ENNReal.add_lt_top.1 hlt).2.ne hε2.ne'
  calc gromovProkhorovEDist μ ρ
      ≤ gromovProkhorovEDist μ ν + ε / 2 + (gromovProkhorovEDist ν ρ + ε / 2) :=
        gromovProkhorovEDist_le_add_of_lt h₁ h₂
    _ = gromovProkhorovEDist μ ν + gromovProkhorovEDist ν ρ + ε := by
        rw [add_add_add_comm, ENNReal.add_halves]

end Triangle

/-- **Invariance under isometries.** Replacing a measure by its pushforward along an isometry does
not change its Gromov–Prokhorov distance to any measure. -/
theorem gromovProkhorovEDist_map_left [OpensMeasurableSpace X] [OpensMeasurableSpace X']
    {T : X → X'} (hT : Isometry T) (hTm : AEMeasurable T μ) (ν : Measure Y) :
    gromovProkhorovEDist (μ.map T) ν = gromovProkhorovEDist μ ν := by
  have h₀ := gromovProkhorovEDist_map_eq_zero hT hTm
  refine le_antisymm ?_ ?_
  · calc gromovProkhorovEDist (μ.map T) ν
        ≤ gromovProkhorovEDist (μ.map T) μ + gromovProkhorovEDist μ ν :=
          gromovProkhorovEDist_triangle _ _ _
      _ = gromovProkhorovEDist μ ν := by rw [gromovProkhorovEDist_comm, h₀, zero_add]
  · calc gromovProkhorovEDist μ ν
        ≤ gromovProkhorovEDist μ (μ.map T) + gromovProkhorovEDist (μ.map T) ν :=
          gromovProkhorovEDist_triangle _ _ _
      _ = gromovProkhorovEDist (μ.map T) ν := by rw [h₀, zero_add]

section Coupling

variable {π : Measure (X × Y)}

/-- **Couplings bound the Gromov–Prokhorov distance.** If, for a metric coupling `f`, some coupling
of the measures gives mass at most `δ` to the pairs at cross distance at least `δ`, then the
Gromov–Prokhorov distance is at most `δ`. -/
theorem gromovProkhorovEDist_le_of_isCoupling (hf : IsMetricCoupling f) (hπ : IsCoupling π μ ν)
    (h : π {z | δ ≤ f z.1 z.2} ≤ δ) : gromovProkhorovEDist μ ν ≤ δ :=
  gromovProkhorovEDist_le_of_isMetricCoupling hf (fun _ ↦ hπ.measure_le_of_measure_setOf_le h)
    fun _ ↦ hπ.swap.measure_le_of_measure_setOf_le (c := fun y x ↦ f x y)
      ((MeasurableEquiv.prodComm.map_apply _).trans_le h)

/-- For `0 < p < ∞`, the Gromov–Prokhorov distance is at most `‖f‖_{L^p (π)} ^ (p / (p + 1))` for
every metric coupling `f` and every coupling `π` of the measures, by Markov's inequality. -/
theorem gromovProkhorovEDist_le_eLpNorm_rpow {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (hf : IsMetricCoupling f) (hπ : IsCoupling π μ ν) :
    gromovProkhorovEDist μ ν ≤
      eLpNorm (fun z : X × Y ↦ f z.1 z.2) p π ^ (p.toReal / (p.toReal + 1)) := by
  set r := p.toReal
  have hr : 0 < r := ENNReal.toReal_pos hp₀ hp
  set E := eLpNorm (fun z : X × Y ↦ f z.1 z.2) p π
  refine le_of_forall_gt_imp_ge_of_dense fun ε hε ↦ ?_
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact le_top
  have hε₀ : ε ≠ 0 := (pos_of_gt hε).ne'
  refine gromovProkhorovEDist_le_of_isCoupling hf hπ ?_
  have hεr₀ : ε ^ r ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε₀) hεtop).ne'
  have hεrtop : ε ^ r ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr.le hεtop
  refine (ENNReal.mul_le_mul_iff_right hεr₀ hεrtop).1 ?_
  calc ε ^ r * π {z | ε ≤ f z.1 z.2} ≤ E ^ r := by
        simpa only [enorm_eq_self] using
          mul_meas_ge_le_pow_eLpNorm' π hp₀ hp ε (f := fun z : X × Y ↦ f z.1 z.2)
    _ = (E ^ (r / (r + 1))) ^ (r + 1) := by
        rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ (by positivity)]
    _ ≤ ε ^ (r + 1) := ENNReal.rpow_le_rpow hε.le (by positivity)
    _ = ε ^ r * ε := by rw [ENNReal.rpow_add _ _ hε₀ hεtop, ENNReal.rpow_one]

/-- The Gromov–Prokhorov distance is at most `‖f‖_{L^∞ (π)}` for every metric coupling `f` and every
coupling `π` of the measures. -/
theorem gromovProkhorovEDist_le_eLpNorm_top (hf : IsMetricCoupling f) (hπ : IsCoupling π μ ν) :
    gromovProkhorovEDist μ ν ≤ eLpNorm (fun z : X × Y ↦ f z.1 z.2) ∞ π := by
  refine le_of_forall_gt_imp_ge_of_dense fun ε hε ↦ gromovProkhorovEDist_le_of_isCoupling hf hπ ?_
  replace hε := eLpNormEssSup_le_eLpNorm_top.trans_lt hε
  calc π {z | ε ≤ f z.1 z.2}
      ≤ π {z | eLpNormEssSup (fun z : X × Y ↦ f z.1 z.2) π < ‖f z.1 z.2‖ₑ} :=
        measure_mono fun z (hz : ε ≤ f z.1 z.2) ↦ by
          rw [mem_ofPred_eq, enorm_eq_self]
          exact hε.trans_le hz
    _ = 0 := meas_eLpNormEssSup_lt
    _ ≤ ε := zero_le

/-- **Comparison with the transportation distance.** For `0 < p < ∞`, the Gromov–Prokhorov
distance is at most `D_p ^ (p / (p + 1))`, where `D_p` is Sturm's transportation distance. -/
theorem gromovProkhorovEDist_le_sturmEDist_rpow {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (μ : Measure X) (ν : Measure Y) :
    gromovProkhorovEDist μ ν ≤ sturmEDist p μ ν ^ (p.toReal / (p.toReal + 1)) := by
  have hq : 0 < p.toReal / (p.toReal + 1) := by
    have := ENNReal.toReal_pos hp₀ hp
    positivity
  rw [← ENNReal.rpow_inv_le_iff hq]
  exact le_sturmEDist fun f hf π hπ ↦ (ENNReal.rpow_inv_le_iff hq).2
    (gromovProkhorovEDist_le_eLpNorm_rpow hp₀ hp hf hπ)

/-- **Comparison with the transportation distance at `p = ∞`.** The Gromov–Prokhorov distance is at
most Sturm's transportation distance `D_∞`. -/
theorem gromovProkhorovEDist_le_sturmEDist_top (μ : Measure X) (ν : Measure Y) :
    gromovProkhorovEDist μ ν ≤ sturmEDist ∞ μ ν :=
  le_sturmEDist fun _ hf _ hπ ↦ gromovProkhorovEDist_le_eLpNorm_top hf hπ

end Coupling

namespace MeasurePreservingIsometry

variable {X Y Z : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [CompleteSpace Y]
  [SecondCountableTopology Y] [BorelSpace Y] [PseudoEMetricSpace Z] [MeasurableSpace Z]
  {M : MetricMeasureSpace X} {N : MetricMeasureSpace Y}

/-- Metric-measure spaces related by a measure-preserving isometry are at Gromov–Prokhorov
distance `0`. -/
theorem gromovProkhorovEDist_eq_zero (e : MeasurePreservingIsometry M N) :
    gromovProkhorovEDist M.reference N.reference = 0 := by
  rw [← e.measurePreserving.map_eq]
  exact gromovProkhorovEDist_map_eq_zero e.isometry e.measurePreserving.measurable.aemeasurable

/-- **The Gromov–Prokhorov distance is an isomorphism invariant.** Metric-measure spaces related by
a measure-preserving isometry are at the same Gromov–Prokhorov distance from every measure. -/
theorem gromovProkhorovEDist_left (e : MeasurePreservingIsometry M N) (ρ : Measure Z) :
    gromovProkhorovEDist N.reference ρ = gromovProkhorovEDist M.reference ρ := by
  rw [← e.measurePreserving.map_eq]
  exact gromovProkhorovEDist_map_left e.isometry e.measurePreserving.measurable.aemeasurable ρ

end MeasurePreservingIsometry

/-- A metric-measure space is at the same Gromov–Prokhorov distance as its support from every
measure. -/
theorem MetricMeasureSpace.gromovProkhorovEDist_supportSpace {X Z : Type*} [MetricSpace X]
    [MeasurableSpace X] [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]
    [PseudoEMetricSpace Z] [MeasurableSpace Z] (M : MetricMeasureSpace X) (ρ : Measure Z) :
    gromovProkhorovEDist M.supportSpace.reference ρ = gromovProkhorovEDist M.reference ρ :=
  (M.supportInclusion.gromovProkhorovEDist_left ρ).symm

end TauCeti
