/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Euclidean
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PopulationBarycenter
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FrechetMean
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel

/-!
# Quadratic Wasserstein barycenters on finite-dimensional inner product spaces

Let `E` be a finite-dimensional real inner product space, such as `ℝⁿ`. Every finite-dimensional
real normed space is proper, so by Le Gouic and Loubes's existence theorem
(`TauCeti.WassersteinSpace.exists_isFrechetBarycenter`), every probability law on the quadratic
Wasserstein space `P₂(E)` with finite second moment admits a quadratic Fréchet barycenter, and by
rescaling (or basepoint pinning when the total mass is infinite) the same holds for any nonzero
measure `P` on `P₂(E)` with finite second moment.

Combining existence with the Brenier-based uniqueness theorems in
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Euclidean` yields the
**Agueh–Carlier existence and uniqueness theorem** for quadratic Wasserstein barycenters, together
with its population counterpart: whenever a measure `P` on `P₂(E)` with finite second moment gives
positive outer measure to laws null on Lipschitz hyperplane graphs (for instance laws vanishing on
small sets of Hausdorff codimension at least `1`, or laws absolutely continuous with respect to
Lebesgue measure), `P` has a unique quadratic Fréchet barycenter. For finitely many laws `μ i` with
finite second moments and nonnegative weights `w i`, if some `μ j` with `w j ≠ 0` vanishes on small
sets, there is a unique Borel probability measure on `E` minimizing `ν ↦ ∑ i, w i * W₂(ν, μ i) ^ 2`
over *all* probability measures on `E` (not merely those pre-assumed to lie in `P₂(E)`), and any
minimizer automatically has finite second moment
(`TauCeti.hasFiniteMoment_of_isMinOn_sum_mul_wassersteinEDist_rpow`).

In dimension `0` (`Subsingleton E`), every measure vanishes on small sets
(`MeasureTheory.Measure.vanishesOnSmallSets_of_subsingleton`), so both the `VanishesOnSmallSets`
and `dimH ≤ finrank ℝ E - 1` formulations hold uniformly in every dimension `n ≥ 0`
(`TauCeti.existsUnique_isMinOn_sum_wassersteinEDist_sq_of_dimH_le`).

## Main statements

* `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_of_null_lipschitz_graphs`,
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_of_vanishesOnSmallSets`, and
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two` — population existence and
  uniqueness of quadratic Fréchet barycenters in `P₂(E)`.
* `WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs`,
  `WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_vanishesOnSmallSets`,
  and `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac` — Agueh–Carlier
  existence and uniqueness in `P₂(E)` for finitely many laws.
* `TauCeti.existsUnique_isMinOn_sum_wassersteinEDist_sq_of_null_lipschitz_graphs`,
  `TauCeti.existsUnique_isMinOn_sum_wassersteinEDist_sq_of_vanishesOnSmallSets`,
  `TauCeti.existsUnique_isMinOn_sum_wassersteinEDist_sq_of_dimH_le`, and
  `TauCeti.existsUnique_isMinOn_sum_wassersteinEDist_sq_of_absolutelyContinuous` — Agueh–Carlier
  existence and uniqueness over all Borel probability measures on `E`.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. **43**
  (2011), no. 2, 904–924, Proposition 3.5.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Related Fields **168** (2017), 901–917.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

section WassersteinSpaceBarycenters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace WassersteinSpace

/-- Any nonzero measure `P` on `P₂(E)` with finite second moment has a quadratic Fréchet
barycenter: for `P univ < ∞` we normalize `P` to a probability measure and apply
`exists_isFrechetBarycenter`, while for `P univ = ∞` the finite-moment anchor is the unique point
at which `frechetRadius 2 P` is finite. -/
private theorem exists_isFrechetBarycenter_two_of_ne_zero
    {P : Measure (WassersteinSpace 2 E)} (hP : HasFiniteMoment 2 P) (hP0 : P ≠ 0) :
    ∃ ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν := by
  have := borelSpace (X := E) (p := 2) ENNReal.ofNat_ne_top
  by_cases htop : P univ = ∞
  · obtain ⟨μ₀, hμ₀⟩ := hasFiniteMoment_def.1 hP
    have hfin₀ : frechetRadius 2 P μ₀ ≠ ∞ := by
      rw [frechetRadius_def]; exact hμ₀.eLpNorm_ne_top
    refine ⟨μ₀, isFrechetBarycenter_iff.2 ⟨hfin₀, isFrechetMinimizer_iff.2 fun z ↦ ?_⟩⟩
    rcases eq_or_ne z μ₀ with rfl | hz
    · exact le_rfl
    have hconst : eLpNorm (fun _ : WassersteinSpace 2 E ↦ edist μ₀ z) 2 P = ∞ := by
      rw [eLpNorm_const _ two_ne_zero hP0, htop, ENNReal.toReal_ofNat,
        ENNReal.top_rpow_of_pos (by positivity), eNorm_eq_self,
        ENNReal.mul_top (edist_pos.2 hz.symm).ne']
    have htri : eLpNorm (fun _ : WassersteinSpace 2 E ↦ edist μ₀ z) 2 P ≤
        frechetRadius 2 P μ₀ + frechetRadius 2 P z := by
      calc eLpNorm (fun _ : WassersteinSpace 2 E ↦ edist μ₀ z) 2 P
          ≤ eLpNorm ((fun y ↦ edist μ₀ y) + fun y ↦ edist z y) 2 P :=
            eLpNorm_mono_eNorm aestronglyMeasurable_const fun y ↦ by
              simpa [edist_comm y z] using edist_triangle μ₀ y z
        _ ≤ frechetRadius 2 P μ₀ + frechetRadius 2 P z := by
            rw [frechetRadius_def, frechetRadius_def]
            exact eLpNorm_add_le one_le_two
    have hztop : frechetRadius 2 P z = ∞ := by
      by_contra hzfin
      exact ENNReal.add_ne_top.2 ⟨hfin₀, hzfin⟩ (top_unique (hconst ▸ htri))
    exact hztop ▸ le_top
  · have hPuniv0 : P univ ≠ 0 := Measure.measure_univ_ne_zero.2 hP0
    set c : ℝ≥0∞ := (P univ)⁻¹
    have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 htop
    have hctop : c ≠ ∞ := ENNReal.inv_ne_top.2 hPuniv0
    let Q : Measure (WassersteinSpace 2 E) := c • P
    have : IsProbabilityMeasure Q :=
      ⟨by rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hPuniv0 htop]⟩
    obtain ⟨ν, hν⟩ := exists_isFrechetBarycenter ENNReal.ofNat_ne_top Q (hP.smul_measure hctop)
    obtain ⟨hνfin, hνmin⟩ := isFrechetBarycenter_iff.1 hν
    set a : ℝ≥0∞ := c ^ (1 / 2 : ℝ≥0∞).toReal
    have ha0 : a ≠ 0 := by positivity
    have hatop : a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hctop
    have hscale (z : WassersteinSpace 2 E) :
        frechetRadius 2 Q z = a * frechetRadius 2 P z := by
      rw [frechetRadius_def, frechetRadius_def, eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul]
    refine ⟨ν, isFrechetBarycenter_iff.2 ⟨fun h ↦ hνfin (by rw [hscale, h, ENNReal.mul_top ha0]),
      isFrechetMinimizer_iff.2 fun z ↦ ?_⟩⟩
    exact (ENNReal.mul_le_mul_iff_right ha0 hatop).1 <| by
      simpa only [hscale] using isFrechetMinimizer_iff.1 hνmin z

/-- **Existence and uniqueness of population quadratic Wasserstein barycenters (Lipschitz-graph
condition).** On a finite-dimensional real inner product space `E`, every measure `P` on `P₂(E)`
with finite second moment that gives positive outer measure to laws null on Lipschitz hyperplane
graphs has a unique quadratic Fréchet barycenter in `P₂(E)`. -/
theorem existsUnique_isFrechetBarycenter_two_of_null_lipschitz_graphs
    {P : Measure (WassersteinSpace 2 E)} (hP : HasFiniteMoment 2 P)
    (hPnull : P {m : WassersteinSpace 2 E | ∀ (v : E), ‖v‖ = 1 →
      ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
        ((m : ProbabilityMeasure E) : Measure E)
          {x | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} = 0} ≠ 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν := by
  obtain ⟨ν, hν⟩ :=
    exists_isFrechetBarycenter_two_of_ne_zero hP (fun h ↦ hPnull (by simp [h]))
  have hsub := subsingleton_frechetBarycenters_two_of_null_lipschitz_graphs hPnull
  exact ⟨ν, hν, fun ν' hν' ↦ hsub (mem_frechetBarycenters.2 hν') (mem_frechetBarycenters.2 hν)⟩

/-- **Existence and uniqueness of population quadratic Wasserstein barycenters under
`VanishesOnSmallSets`.** -/
theorem existsUnique_isFrechetBarycenter_two_of_vanishesOnSmallSets
    {P : Measure (WassersteinSpace 2 E)} (hP : HasFiniteMoment 2 P)
    (hPsmall : P {m : WassersteinSpace 2 E |
      ((m : ProbabilityMeasure E) : Measure E).VanishesOnSmallSets} ≠ 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν := by
  obtain ⟨ν, hν⟩ :=
    exists_isFrechetBarycenter_two_of_ne_zero hP (fun h ↦ hPsmall (by simp [h]))
  have hsub := subsingleton_frechetBarycenters_two_of_vanishesOnSmallSets hPsmall
  exact ⟨ν, hν, fun ν' hν' ↦ hsub (mem_frechetBarycenters.2 hν') (mem_frechetBarycenters.2 hν)⟩

/-- **Existence and uniqueness of population quadratic Wasserstein barycenters (Haar-absolutely
continuous laws).** -/
theorem existsUnique_isFrechetBarycenter_two {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {P : Measure (WassersteinSpace 2 E)} (hP : HasFiniteMoment 2 P)
    (hPac : P {m : WassersteinSpace 2 E | ((m : ProbabilityMeasure E) : Measure E) ≪ ρ} ≠ 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν := by
  obtain ⟨ν, hν⟩ :=
    exists_isFrechetBarycenter_two_of_ne_zero hP (fun h ↦ hPac (by simp [h]))
  have hsub := subsingleton_frechetBarycenters_two hPac
  exact ⟨ν, hν, fun ν' hν' ↦ hsub (mem_frechetBarycenters.2 hν') (mem_frechetBarycenters.2 hν)⟩

private theorem hasFiniteMoment_two_sum_smul_dirac {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ≥0) (μ : ι → WassersteinSpace 2 E) :
    HasFiniteMoment 2 (∑ i, w i • Measure.dirac (μ i)) := by
  have := borelSpace (X := E) (p := 2) ENNReal.ofNat_ne_top
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set P := ∑ i, w i • Measure.dirac (μ i)
  have hm : AEMeasurable (fun y ↦ edist (μ i₀) y) P :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  refine hasFiniteMoment_def.2 ⟨μ i₀, memLp_iff.2 (lt_top_iff_ne_top.2 fun htop ↦ ?_)⟩
  have hpow := frechetRadius_rpow_eq_frechetPower two_ne_zero ENNReal.ofNat_ne_top hm
  rw [frechetRadius_def, htop, ENNReal.toReal_ofNat, ENNReal.top_rpow_of_pos two_pos,
    frechetPower_sum_smul_dirac] at hpow
  exact sum_mul_wassersteinEDist_rpow_ne_top (w := w) μ (μ i₀) <| by
    simpa only [ENNReal.toReal_ofNat, edist_def, ENNReal.smul_def, smul_eq_mul] using hpow.symm

/-- **Agueh–Carlier existence and uniqueness in `P₂(E)` under the Lipschitz-graph condition.** -/
theorem existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} (μ : ι → WassersteinSpace 2 E)
    {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      ((μ j : ProbabilityMeasure E) : Measure E)
        {x | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} = 0) :
    ∃! ν : WassersteinSpace 2 E,
      IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν := by
  have : Nonempty ι := ⟨j⟩
  set S := {m : WassersteinSpace 2 E | ∀ (v : E), ‖v‖ = 1 →
    ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      ((m : ProbabilityMeasure E) : Measure E)
        {x | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} = 0}
  refine existsUnique_isFrechetBarycenter_two_of_null_lipschitz_graphs
    (hasFiniteMoment_two_sum_smul_dirac w μ) (ne_of_gt ?_)
  have hjS : μ j ∈ S := hμj
  calc (0 : ℝ≥0∞) < w j := ENNReal.coe_pos.2 (pos_iff_ne_zero.2 hj)
    _ = (w j • Measure.dirac (μ j)) S := by simp [Measure.dirac_apply_of_mem hjS]
    _ ≤ ∑ i, (w i • Measure.dirac (μ i)) S :=
        Finset.single_le_sum (f := fun i ↦ (w i • Measure.dirac (μ i)) S)
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)
    _ = (∑ i, w i • Measure.dirac (μ i)) S := by rw [FunLike.coe_sum, Finset.sum_apply]

/-- **Agueh–Carlier existence and uniqueness in `P₂(E)` under `VanishesOnSmallSets`.** -/
theorem existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_vanishesOnSmallSets
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} (μ : ι → WassersteinSpace 2 E)
    {j : ι} (hj : w j ≠ 0) (hμj : ((μ j : ProbabilityMeasure E) : Measure E).VanishesOnSmallSets) :
    ∃! ν : WassersteinSpace 2 E,
      IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν :=
  existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs μ hj
    fun _ hv _ _ hg ↦ hμj.measure_setOf_inner_eq_orthogonalProjectionOnto
      (ne_of_apply_ne norm (by simp [hv])) hg

/-- **Agueh–Carlier existence and uniqueness in `P₂(E)` for an absolutely continuous input law.** -/
theorem existsUnique_isFrechetBarycenter_two_sum_smul_dirac {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} (μ : ι → WassersteinSpace 2 E)
    {j : ι} (hj : w j ≠ 0) (hμj : ((μ j : ProbabilityMeasure E) : Measure E) ≪ ρ) :
    ∃! ν : WassersteinSpace 2 E,
      IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν :=
  existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_vanishesOnSmallSets μ hj
    (.of_absolutelyContinuous hμj)

end WassersteinSpace

end WassersteinSpaceBarycenters

section ProbabilityMeasureBarycenters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Agueh–Carlier existence and uniqueness over all Borel probability measures (Lipschitz-graph
condition).** Let `μ i` be finitely many Borel probability measures with finite second moments on a
finite-dimensional real inner product space `E`, and `w i` nonnegative weights. If some `μ j` with
`w j ≠ 0` assigns zero mass to every Lipschitz hyperplane graph, then there is a unique
`ν : ProbabilityMeasure E` minimizing `ν' ↦ ∑ i, w i * W₂(ν', μ i) ^ 2` over all Borel probability
measures on `E`. -/
theorem existsUnique_isMinOn_sum_wassersteinEDist_sq_of_null_lipschitz_graphs
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → ProbabilityMeasure E}
    (hmom : ∀ i, HasFiniteMoment 2 (μ i : Measure E)) {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      (μ j : Measure E) {x | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} = 0) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν' : ProbabilityMeasure E ↦ ∑ i, (w i : ℝ≥0∞) *
        wassersteinEDist 2 (ν' : Measure E) (μ i : Measure E) ^ 2) univ ν := by
  let m : ι → WassersteinSpace 2 E := fun i ↦ WassersteinSpace.mk (μ i) (hmom i)
  have hm (i : ι) : (m i : ProbabilityMeasure E) = μ i := WassersteinSpace.coe_mk _ _
  have hmj : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      ((m j : ProbabilityMeasure E) : Measure E)
        {x | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} = 0 := by
    simpa only [hm] using hμj
  obtain ⟨b, hb, huniq⟩ :=
    WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs
      m hj hmj
  refine ⟨(b : ProbabilityMeasure E), ?_, fun ν' hν' ↦ ?_⟩
  · have hmin := WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter
      ENNReal.ofNat_ne_top hb
    refine isMinOn_univ_iff.2 fun ν' ↦ ?_
    have h := isMinOn_iff.1 hmin (ν' : Measure E) (ν'.prop)
    simpa only [hm, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using h
  · have hν'rpow : IsMinOn (fun z : ProbabilityMeasure E ↦ ∑ i, (w i : ℝ≥0∞) *
        wassersteinEDist 2 (z : Measure E) (μ i : Measure E) ^ (2 : ℝ)) univ ν' := by
      simpa only [ENNReal.rpow_ofNat] using hν'
    have hmom' : HasFiniteMoment 2 (ν' : Measure E) :=
      hasFiniteMoment_of_isMinOn_sum_mul_wassersteinEDist_rpow measurable_edist two_pos hmom hj
        hν'rpow
    let b' : WassersteinSpace 2 E := WassersteinSpace.mk ν' hmom'
    have hb'coe : (b' : ProbabilityMeasure E) = ν' := WassersteinSpace.coe_mk _ _
    have hb' : IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (m i)) b' := by
      rw [WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn (p := 2)
        ENNReal.ofNat_ne_top, isMinOn_univ_iff]
      intro z
      simpa only [hb'coe, hm, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using
        isMinOn_univ_iff.1 hν' (z : ProbabilityMeasure E)
    exact hb'coe.symm.trans (congrArg (fun x : WassersteinSpace 2 E ↦ (x : ProbabilityMeasure E))
      (huniq b' hb'))

/-- **Agueh–Carlier existence and uniqueness over all Borel probability measures under
`VanishesOnSmallSets`** (valid in every dimension `n ≥ 0`, including `Subsingleton E`). -/
theorem existsUnique_isMinOn_sum_wassersteinEDist_sq_of_vanishesOnSmallSets
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → ProbabilityMeasure E}
    (hmom : ∀ i, HasFiniteMoment 2 (μ i : Measure E)) {j : ι} (hj : w j ≠ 0)
    (hμj : (μ j : Measure E).VanishesOnSmallSets) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν' : ProbabilityMeasure E ↦ ∑ i, (w i : ℝ≥0∞) *
        wassersteinEDist 2 (ν' : Measure E) (μ i : Measure E) ^ 2) univ ν :=
  existsUnique_isMinOn_sum_wassersteinEDist_sq_of_null_lipschitz_graphs hmom hj
    fun _ hv _ _ hg ↦ hμj.measure_setOf_inner_eq_orthogonalProjectionOnto
      (ne_of_apply_ne norm (by simp [hv])) hg

/-- **Agueh–Carlier existence and uniqueness of quadratic Wasserstein barycenters**
(Agueh–Carlier, Proposition 3.5). On a finite-dimensional real inner product space `E`, let `μ i`
be finitely many Borel probability measures with finite second moments and `w i` nonnegative
weights. If some `μ j` with `w j ≠ 0` vanishes on Borel sets of Hausdorff dimension at most
`finrank ℝ E - 1`, then there is a unique Borel probability measure minimizing
`ν' ↦ ∑ i, w i * W₂(ν', μ i) ^ 2` over all Borel probability measures on `E`. -/
theorem existsUnique_isMinOn_sum_wassersteinEDist_sq_of_dimH_le
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → ProbabilityMeasure E}
    (hmom : ∀ i, HasFiniteMoment 2 (μ i : Measure E)) {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ ⦃A : Set E⦄, MeasurableSet A →
      dimH A ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → (μ j : Measure E) A = 0) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν' : ProbabilityMeasure E ↦ ∑ i, (w i : ℝ≥0∞) *
        wassersteinEDist 2 (ν' : Measure E) (μ i : Measure E) ^ 2) univ ν := by
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · exact existsUnique_isMinOn_sum_wassersteinEDist_sq_of_vanishesOnSmallSets hmom hj
      (Measure.vanishesOnSmallSets_of_subsingleton _)
  · exact existsUnique_isMinOn_sum_wassersteinEDist_sq_of_vanishesOnSmallSets hmom hj
      (Measure.vanishesOnSmallSets_iff_dimH_le.2 hμj)

/-- **Agueh–Carlier existence and uniqueness over all Borel probability measures for an absolutely
continuous input law.** -/
theorem existsUnique_isMinOn_sum_wassersteinEDist_sq_of_absolutelyContinuous
    {ρ : Measure E} [ρ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] {w : ι → ℝ≥0}
    {μ : ι → ProbabilityMeasure E}
    (hmom : ∀ i, HasFiniteMoment 2 (μ i : Measure E)) {j : ι} (hj : w j ≠ 0)
    (hμj : (μ j : Measure E) ≪ ρ) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν' : ProbabilityMeasure E ↦ ∑ i, (w i : ℝ≥0∞) *
        wassersteinEDist 2 (ν' : Measure E) (μ i : Measure E) ^ 2) univ ν :=
  existsUnique_isMinOn_sum_wassersteinEDist_sq_of_vanishesOnSmallSets hmom hj
    (.of_absolutelyContinuous hμj)

end ProbabilityMeasureBarycenters

end TauCeti
