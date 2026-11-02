/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
public import TauCeti.Analysis.BoundedVariation.MinkowskiContent
import TauCeti.Analysis.BoundedVariation.Convex
import TauCeti.Analysis.Convex.Measure
import TauCeti.Analysis.BoundedVariation.ParallelVolume

/-!
# Steiner symmetrization, parallel sets and perimeter

Let `s` be a set in a finite-dimensional real inner product space and let `S s` be its Steiner
symmetral in a unit direction `e`. Symmetrization commutes with taking open neighbourhoods up to
an inclusion:

`thickening r (S s) ⊆ S (thickening r s)`

(`TauCeti.thickening_steinerSymmetrization_subset`), with no hypothesis on `s`. Symmetrization
preserves volume, so the open neighbourhoods of the symmetral are no larger than those of `s`
(`TauCeti.volume_thickening_steinerSymmetrization_le`). For a closed set with a neighbourhood
of finite volume, the closure of the symmetral differs from it only by a null set
(`TauCeti.closure_steinerSymmetrization_ae_eq`), so the outer shells
`thickening r (S s) \ closure (S s)` are no larger than the shells `thickening r s \ s`.
Since the perimeter of a closure is at most its lower outer Minkowski content
(`TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div`), the perimeter of the
symmetral of a closed set `s` of finite volume is at most the lower outer Minkowski content of `s`:

`P(S s) ≤ liminf_{ε → 0⁺} |thickening ε s \ s| / ε`

(`TauCeti.perimeter_steinerSymmetrization_le_liminf`). In particular, if the volume of the
parallel sets `K + t • closedBall 0 1` of a compact set `K` has right derivative `D` at `t = 0`,
then `P(S K) ≤ D` (`TauCeti.perimeter_steinerSymmetrization_le_of_hasDerivWithinAt`). For a
compact convex set with nonempty interior this derivative is the perimeter
(`Convex.hasDerivWithinAt_measureReal_add_smul_closedBall`), while a convex set with empty
interior is null. Since a bounded convex set agrees almost everywhere with its closure,
**Steiner symmetrization does not increase the perimeter of a bounded convex set**
(`TauCeti.perimeter_steinerSymmetrization_le_of_convex`).

The inclusion is proved line by line. If `p` lies in the symmetral and `x` is within `r` of `p`,
write `x - p = q + c • e` with `q` orthogonal to `e`. The section of `thickening r s` through
`x` contains a translate of the open `ρ`-neighbourhood of the section of `s` through `p`, where
`ρ = √(r² - ‖q‖²) > |c|`. By the one-dimensional Brunn–Minkowski inequality this neighbourhood
is longer than the section through `p` by at least `2 ρ`
(`TauCeti.Real.volume_add_le_volume_thickening`), which leaves room for the displacement `c`
along `e`.

## References

* G. Pólya, G. Szegő, *Isoperimetric Inequalities in Mathematical Physics*, Annals of
  Mathematics Studies **27**, Princeton University Press, 1951, for Steiner symmetrization of
  parallel sets and Minkowski's surface area.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 14, for
  Steiner symmetrization of sets of finite perimeter.
-/

public section

open MeasureTheory Metric Filter Set TopologicalSpace
open scoped ENNReal Pointwise RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The open `r`-neighbourhood of a Steiner symmetral lies in the symmetral of the open
`r`-neighbourhood. No measurability or finiteness hypothesis is needed. -/
theorem thickening_steinerSymmetrization_subset (e : E) (he : ‖e‖ = 1) (s : Set E) (r : ℝ) :
    thickening r (steinerSymmetrization e he s) ⊆
      steinerSymmetrization e he (thickening r s) := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.1 hx
  rw [mem_steinerSymmetrization_iff, mem_eball, edist_zero_right,
    Real.enorm_eq_ofReal_abs] at hp ⊢
  set A := {t : ℝ | p + t • e ∈ s}
  -- Split the displacement `x - p` into its components along and orthogonal to `e`.
  set c := ⟪e, x - p⟫
  set q := x - p - c • e
  have hqe : ⟪q, e⟫ = 0 := by
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, he, real_inner_comm]
    simp [c]
  have hnorm (σ : ℝ) : ‖q + σ • e‖ ^ 2 = ‖q‖ ^ 2 + σ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hqe, norm_smul, he]
    simp
  have hxp' : ‖q‖ ^ 2 + c ^ 2 < r ^ 2 := by
    rw [← hnorm c, show q + c • e = x - p by simp [q], ← dist_eq_norm]
    exact pow_lt_pow_left₀ hxp dist_nonneg two_ne_zero
  set ρ := √(r ^ 2 - ‖q‖ ^ 2)
  have hcρ : |c| < ρ := Real.lt_sqrt (abs_nonneg c) |>.2 (by rw [sq_abs]; linarith)
  have hρ : 0 < ρ := (abs_nonneg c).trans_lt hcρ
  have hA : A.Nonempty := nonempty_iff_ne_empty.2 fun h ↦ by simp [A, h] at hp
  -- A translate of the `ρ`-neighbourhood of the section through `p` lies in the section of the
  -- `r`-neighbourhood through `x`.
  have hsub : thickening ρ A ⊆ (· + -c) ⁻¹' {t : ℝ | x + t • e ∈ thickening r s} := by
    intro σ hσ
    obtain ⟨a, ha, hσa⟩ := mem_thickening_iff.1 hσ
    refine mem_thickening_iff.2 ⟨p + a • e, ha, ?_⟩
    have hsq : (σ - a) ^ 2 < ρ ^ 2 := by
      rw [← sq_abs, ← Real.dist_eq]
      exact pow_lt_pow_left₀ hσa dist_nonneg two_ne_zero
    rw [Real.sq_sqrt (by nlinarith [sq_nonneg c])] at hsq
    rw [dist_eq_norm, show x + (σ + -c) • e - (p + a • e) = q + (σ - a) • e by
      simp only [q]; module]
    have hr : 0 ≤ r := dist_nonneg.trans hxp.le
    exact lt_of_pow_lt_pow_left₀ 2 hr (by rw [hnorm]; linarith)
  calc ENNReal.ofReal |⟪e, x⟫|
      ≤ ENNReal.ofReal |⟪e, p⟫| + ENNReal.ofReal |c| := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show ⟪e, x⟫ = ⟪e, p⟫ + c by simp [c, inner_sub_right]]
        exact abs_add_le _ _
    _ < volume A / 2 + ENNReal.ofReal ρ :=
        ENNReal.add_lt_add hp ((ENNReal.ofReal_lt_ofReal_iff hρ).2 hcρ)
    _ = (volume A + ENNReal.ofReal (2 * ρ)) / 2 := by
        rw [ENNReal.add_div, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]
    _ ≤ volume (thickening ρ A) / 2 := by
        gcongr
        exact Real.volume_add_le_volume_thickening hA hρ
    _ ≤ volume {t : ℝ | x + t • e ∈ thickening r s} / 2 :=
        ENNReal.div_le_div_right ((measure_mono hsub).trans_eq
          (measure_preimage_add_right _ _ _)) 2

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Steiner symmetrization does not increase the volume of open `r`-neighbourhoods. No
measurability or finiteness hypothesis is needed. -/
theorem volume_thickening_steinerSymmetrization_le (e : E) (he : ‖e‖ = 1) (s : Set E) (r : ℝ) :
    volume (thickening r (steinerSymmetrization e he s)) ≤ volume (thickening r s) :=
  (measure_mono (thickening_steinerSymmetrization_subset e he s r)).trans_eq
    (volume_steinerSymmetrization e he isOpen_thickening.measurableSet.nullMeasurableSet)

/-- If some neighbourhood of a closed set `s` has finite volume, then the closure of a Steiner
symmetral of `s` agrees with the symmetral up to a null set. -/
theorem closure_steinerSymmetrization_ae_eq (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : IsClosed s) (hfin : ∃ R > 0, volume (thickening R s) ≠ ∞) :
    closure (steinerSymmetrization e he s) =ᵐ[volume] steinerSymmetrization e he s := by
  obtain ⟨R, hR, hRfin⟩ := hfin
  have hS : volume (steinerSymmetrization e he s) = volume s :=
    volume_steinerSymmetrization e he hs.measurableSet.nullMeasurableSet
  -- The closure lies in every neighbourhood of the symmetral, whose volume tends to that of `s`.
  have hle : volume (closure (steinerSymmetrization e he s)) ≤ volume s := by
    refine ge_of_tendsto (tendsto_measure_thickening_of_isClosed ⟨R, hR, hRfin⟩ hs) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (measure_mono (closure_subset_thickening hr _)).trans
      (volume_thickening_steinerSymmetrization_le e he s r)
  refine (ae_eq_of_subset_of_measure_ge subset_closure (hle.trans_eq hS.symm)
    (nullMeasurableSet_steinerSymmetrization e he hs.measurableSet.nullMeasurableSet) ?_).symm
  exact ne_top_of_le_ne_top hRfin (hle.trans (measure_mono (self_subset_thickening hR s)))

/-- The outer shells of the symmetral of a closed set with a finite-volume neighbourhood are no
larger than the outer shells of the set. -/
private theorem volume_thickening_steinerSymmetrization_sdiff_closure_le (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : IsClosed s) (hfin : ∃ R > 0, volume (thickening R s) ≠ ∞) (r : ℝ) :
    volume (thickening r (steinerSymmetrization e he s) \
        closure (steinerSymmetrization e he s)) ≤ volume (thickening r s \ s) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [thickening_of_nonpos hr]
  have hsfin : volume s ≠ ∞ := by
    obtain ⟨R, hR, h⟩ := hfin
    exact ne_top_of_le_ne_top h (measure_mono (self_subset_thickening hR s))
  have hcl : volume (closure (steinerSymmetrization e he s)) = volume s :=
    (measure_congr (closure_steinerSymmetrization_ae_eq e he hs hfin)).trans
      (volume_steinerSymmetrization e he hs.measurableSet.nullMeasurableSet)
  rw [measure_sdiff (closure_subset_thickening hr _)
      isClosed_closure.measurableSet.nullMeasurableSet (hcl ▸ hsfin), hcl,
    measure_sdiff (self_subset_thickening hr s) hs.measurableSet.nullMeasurableSet hsfin]
  exact tsub_le_tsub_right (volume_thickening_steinerSymmetrization_le e he s r) _

/-- **Steiner symmetrization and outer Minkowski content.** The perimeter of a Steiner symmetral
of a closed set `s` of finite volume is at most the lower outer Minkowski content of `s`,
`liminf_{ε → 0⁺} |thickening ε s \ s| / ε`. -/
theorem perimeter_steinerSymmetrization_le_liminf (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : IsClosed s) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ≤
      liminf (fun ε => volume (thickening ε s \ s) / ENNReal.ofReal ε) (𝓝[>] 0) := by
  by_cases hR : ∃ R > 0, volume (thickening R s) ≠ ∞
  · calc perimeter volume ⊤ (steinerSymmetrization e he s)
        = perimeter volume ⊤ (closure (steinerSymmetrization e he s)) := by
          exact perimeter_congr_ae
            (ae_restrict_of_ae (closure_steinerSymmetrization_ae_eq e he hs hR).symm)
      _ ≤ liminf (fun ε => volume ((thickening ε (steinerSymmetrization e he s) \
            closure (steinerSymmetrization e he s)) ∩ (⊤ : Opens E)) / ENNReal.ofReal ε)
            (𝓝[>] 0) :=
          perimeter_closure_le_liminf_measure_thickening_sdiff_div ⊤ _
      _ ≤ liminf (fun ε => volume (thickening ε s \ s) / ENNReal.ofReal ε) (𝓝[>] 0) := by
          refine liminf_le_liminf (.of_forall fun ε => ?_)
          rw [Opens.coe_top, inter_univ]
          exact ENNReal.div_le_div_right
            (volume_thickening_steinerSymmetrization_sdiff_closure_le e he hs hR ε) _
  · -- Every neighbourhood of `s` has infinite volume, so the right side is infinite.
    push Not at hR
    suffices h : liminf (fun ε => volume (thickening ε s \ s) / ENNReal.ofReal ε) (𝓝[>] 0) = ∞ by
      exact h ▸ le_top
    rw [← liminf_const (f := 𝓝[>] (0 : ℝ)) (∞ : ℝ≥0∞)]
    refine liminf_congr ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [measure_sdiff (self_subset_thickening hε s) hs.measurableSet.nullMeasurableSet hfin,
      hR ε hε, ENNReal.top_sub hfin, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]

/-- If the volume of the outer parallel sets `K + t • closedBall 0 1` of a compact set `K` has
right derivative `D` at `t = 0`, then every Steiner symmetral of `K` has perimeter at most `D`. -/
theorem perimeter_steinerSymmetrization_le_of_hasDerivWithinAt (e : E) (he : ‖e‖ = 1)
    {K : Set E} (hK : IsCompact K) {D : ℝ}
    (hD : HasDerivWithinAt (fun t : ℝ => volume.real (K + t • closedBall (0 : E) 1)) D (Ioi 0) 0) :
    perimeter volume ⊤ (steinerSymmetrization e he K) ≤ ENNReal.ofReal D :=
  calc perimeter volume ⊤ (steinerSymmetrization e he K)
      ≤ liminf (fun ε => volume (thickening ε K \ K) / ENNReal.ofReal ε) (𝓝[>] 0) :=
        perimeter_steinerSymmetrization_le_liminf e he hK.isClosed hK.measure_lt_top.ne
    _ ≤ liminf (fun ε => volume (cthickening ε K \ K) / ENNReal.ofReal ε) (𝓝[>] 0) :=
        liminf_le_liminf (.of_forall fun ε => ENNReal.div_le_div_right
          (measure_mono (sdiff_subset_sdiff_left (thickening_subset_cthickening ε K))) _)
    _ = ENNReal.ofReal D := (hK.tendsto_measure_cthickening_sdiff_div hD).liminf_eq

/-- **Steiner symmetrization does not increase the perimeter of a bounded convex set.** -/
theorem perimeter_steinerSymmetrization_le_of_convex (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hc : Convex ℝ s) (hb : Bornology.IsBounded s) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ≤ perimeter volume ⊤ s := by
  -- Both sides are unchanged when `s` is replaced by its compact convex closure.
  have hae : closure s =ᵐ[volume] s := closure_ae_eq_of_null_frontier (hc.addHaar_frontier volume)
  rw [← perimeter_congr_ae (ae_restrict_of_ae hae),
    ← perimeter_congr_ae (ae_restrict_of_ae (steinerSymmetrization_ae_eq e he hae))]
  have hKc : Convex ℝ (closure s) := hc.closure
  have hK : IsCompact (closure s) := hb.isCompact_closure
  rcases (interior (closure s)).eq_empty_or_nonempty with hKi | hKi
  · -- A convex set with empty interior is null, and so is its symmetral.
    have h0 : volume (steinerSymmetrization e he (closure s)) = 0 := by
      rw [volume_steinerSymmetrization e he isClosed_closure.measurableSet.nullMeasurableSet,
        hKc.addHaar_eq_zero_iff_interior_eq_empty]
      exact hKi
    rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 h0)), perimeter_empty]
    exact zero_le
  · have hP : perimeter volume ⊤ (closure s) ≠ ∞ := (hKc.perimeter_lt_top hK.isBounded).ne
    simpa [ENNReal.ofReal_toReal hP] using perimeter_steinerSymmetrization_le_of_hasDerivWithinAt
      e he hK ((hKc.hasDerivWithinAt_measureReal_add_smul_closedBall hK hKi).mono
        Ioi_subset_Ici_self)

end TauCeti
