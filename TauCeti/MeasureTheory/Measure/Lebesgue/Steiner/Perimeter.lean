/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
public import TauCeti.Analysis.BoundedVariation.MinkowskiContent
import TauCeti.Analysis.BoundedVariation.SmoothApproximation
import TauCeti.Analysis.Sobolev.W1p.LevelSet

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
then `P(S K) ≤ D` (`TauCeti.perimeter_steinerSymmetrization_le_of_hasDerivWithinAt`).

**Steiner symmetrization does not increase perimeter**: `P(S s) ≤ P(s)` for every null-measurable
set `s` of finite volume (`TauCeti.perimeter_steinerSymmetrization_le`). The closed regular
superlevel sets `{u ≥ t}` of compactly supported smooth functions have outer Minkowski content
equal to their perimeter (`ContDiff.tendsto_volume_thickening_sdiff_div`), so the bound above
gives `P(S F) ≤ P(F)` for them. Every set of finite volume is approximated by such sets in volume
and in perimeter (`MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`), and
regular levels are null. Steiner symmetrization contracts the volume of symmetric differences
(`TauCeti.volume_steinerSymmetrization_symmDiff_le`), so the symmetrals of the approximations
converge in measure to `S s`, and lower semicontinuity of the perimeter
(`TauCeti.perimeter_le_liminf`) concludes.

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
open scoped ENNReal Pointwise RealInnerProductSpace Topology symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Line sections of open neighbourhoods along a unit vector `e`: write `c = ⟪e, x - p⟫` for the
component of `x - p` along `e`. If `0 ≤ r` and `ρ ^ 2 + ‖x - p‖ ^ 2 ≤ r ^ 2 + c ^ 2`, then the
open `ρ`-neighbourhood of the line section of `s` through `p` lies in the preimage under
`t ↦ t - c` of the line section of `thickening r s` through `x`. In other words, its translate
by `-c` lies in the line section of `thickening r s` through `x`. -/
theorem thickening_lineSection_subset_preimage_sub_lineSection_thickening (e : E)
    (he : ‖e‖ = 1) (s : Set E) {x p : E} {r ρ : ℝ} (hr : 0 ≤ r)
    (hρ : ρ ^ 2 + ‖x - p‖ ^ 2 ≤ r ^ 2 + ⟪e, x - p⟫ ^ 2) :
    thickening ρ {t : ℝ | p + t • e ∈ s} ⊆
      (· - ⟪e, x - p⟫) ⁻¹' {t : ℝ | x + t • e ∈ thickening r s} := by
  -- Split the displacement `x - p` into its components along and orthogonal to `e`.
  set c := ⟪e, x - p⟫
  set q := x - p - c • e
  have hqe : ⟪q, e⟫ = 0 := by
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, he, real_inner_comm]
    simp [c]
  have hnorm (σ : ℝ) : ‖q + σ • e‖ ^ 2 = ‖q‖ ^ 2 + σ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hqe, norm_smul, he]
    simp
  have hxp : ‖x - p‖ ^ 2 = ‖q‖ ^ 2 + c ^ 2 := by
    rw [← hnorm c, show q + c • e = x - p by simp [q]]
  intro σ hσ
  obtain ⟨a, ha, hσa⟩ := mem_thickening_iff.1 hσ
  refine mem_thickening_iff.2 ⟨p + a • e, ha, ?_⟩
  have hsq : (σ - a) ^ 2 < ρ ^ 2 := by
    rw [← sq_abs, ← Real.dist_eq]
    exact pow_lt_pow_left₀ hσa dist_nonneg two_ne_zero
  rw [dist_eq_norm, show x + (σ - c) • e - (p + a • e) = q + (σ - a) • e by
    simp only [q]; module]
  exact lt_of_pow_lt_pow_left₀ 2 hr (by rw [hnorm]; linarith)

/-- The open `r`-neighbourhood of a Steiner symmetral lies in the symmetral of the open
`r`-neighbourhood. No measurability or finiteness hypothesis is needed. -/
theorem thickening_steinerSymmetrization_subset (e : E) (he : ‖e‖ = 1) (s : Set E) (r : ℝ) :
    thickening r (steinerSymmetrization e he s) ⊆
      steinerSymmetrization e he (thickening r s) := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.1 hx
  have hr : 0 ≤ r := dist_nonneg.trans hxp.le
  have hxp' : ‖x - p‖ ^ 2 < r ^ 2 := by
    rw [← dist_eq_norm]; exact pow_lt_pow_left₀ hxp dist_nonneg two_ne_zero
  set ρ := √(r ^ 2 - ‖x - p‖ ^ 2 + ⟪e, x - p⟫ ^ 2)
  have hρsq : ρ ^ 2 = r ^ 2 - ‖x - p‖ ^ 2 + ⟪e, x - p⟫ ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg ⟪e, x - p⟫])
  have hcρ : |⟪e, x - p⟫| < ρ := Real.lt_sqrt (abs_nonneg _) |>.2 (by rw [sq_abs]; linarith)
  have hsub := thickening_lineSection_subset_preimage_sub_lineSection_thickening e he s hr
    (ρ := ρ) (by linarith)
  rw [mem_steinerSymmetrization_iff, mem_eball, edist_zero_right,
    Real.enorm_eq_ofReal_abs] at hp ⊢
  have hρ : 0 < ρ := (abs_nonneg _).trans_lt hcρ
  have hA : {t : ℝ | p + t • e ∈ s}.Nonempty := nonempty_iff_ne_empty.2 fun h ↦ by simp [h] at hp
  calc ENNReal.ofReal |⟪e, x⟫|
      ≤ ENNReal.ofReal |⟪e, p⟫| + ENNReal.ofReal |⟪e, x - p⟫| := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show ⟪e, x⟫ = ⟪e, p⟫ + ⟪e, x - p⟫ by simp [inner_sub_right]]
        exact abs_add_le _ _
    _ < volume {t : ℝ | p + t • e ∈ s} / 2 + ENNReal.ofReal ρ :=
        ENNReal.add_lt_add hp ((ENNReal.ofReal_lt_ofReal_iff hρ).2 hcρ)
    _ = (volume {t : ℝ | p + t • e ∈ s} + ENNReal.ofReal (2 * ρ)) / 2 := by
        rw [ENNReal.add_div, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]
    _ ≤ volume (thickening ρ {t : ℝ | p + t • e ∈ s}) / 2 := by
        gcongr
        exact Real.volume_add_le_volume_thickening hA hρ
    _ ≤ volume {t : ℝ | x + t • e ∈ thickening r s} / 2 :=
        ENNReal.div_le_div_right ((measure_mono hsub).trans_eq <| by
          simpa only [sub_eq_add_neg] using measure_preimage_add_right _ _ _) 2

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

/-- **Steiner symmetrization does not increase perimeter.** For every null-measurable set `s` of
finite volume and every unit vector `e`, the Steiner symmetral of `s` in direction `e` has
perimeter at most that of `s`. No boundedness or regularity is assumed, and the perimeter of `s`
may be infinite. -/
theorem perimeter_steinerSymmetrization_le (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ≤ perimeter volume ⊤ s := by
  obtain ⟨u, t, hprop, hsymm, hP⟩ := hs.exists_smooth_perimeter_approximation hfin
  -- Approximate `s` by the closed regular superlevel sets `F k = {u k ≥ t k}`, which agree almost
  -- everywhere with the open ones `{u k > t k}` since regular levels are null.
  set F : ℕ → Set E := fun k => {x | t k ≤ u k x}
  have hreg (k : ℕ) (x : E) (hx : u k x = t k) : fderiv ℝ (u k) x ≠ 0 := fun h0 => by
    obtain ⟨v, hv⟩ := (hprop k).2.2.2.1 x hx 1
    simp [h0] at hv
  have hFae (k : ℕ) : F k =ᵐ[volume] {x | t k < u k x} := by
    have hnull := ((hprop k).1.of_le (by simp)).measure_setOf_eq_eq_zero_of_fderiv_ne_zero
      (mu := volume) (hreg k)
    have hF : F k = {x | t k < u k x} ∪ {x | u k x = t k} := by
      ext x
      simp [F, le_iff_lt_or_eq, eq_comm]
    rw [hF]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 hnull)
  have hFc (k : ℕ) : IsClosed (F k) := isClosed_le continuous_const (hprop k).1.continuous
  have hFm (k : ℕ) : NullMeasurableSet (F k) volume := (hFc k).measurableSet.nullMeasurableSet
  have hFfin (k : ℕ) : volume (F k) ≠ ∞ := by
    rw [measure_congr (hFae k)]
    exact ne_top_of_le_ne_top (hprop k).2.2.2.2.1.measure_lt_top.ne (measure_mono subset_closure)
  -- Each `F k` has outer Minkowski content `P(F k)`, which bounds the perimeter of its symmetral.
  have hstep (k : ℕ) : perimeter volume ⊤ (steinerSymmetrization e he (F k)) ≤
      perimeter volume ⊤ (F k) :=
    (perimeter_steinerSymmetrization_le_liminf e he (hFc k) (hFfin k)).trans_eq
      ((hprop k).1.tendsto_volume_thickening_sdiff_div (hprop k).2.1 (hprop k).2.2.1.1
        (hreg k)).liminf_eq
  have hPF : Tendsto (fun k => perimeter volume ⊤ (F k)) atTop (𝓝 (perimeter volume ⊤ s)) :=
    hP.congr fun k => (perimeter_congr_ae (ae_restrict_of_ae (hFae k))).symm
  -- The symmetrals converge in measure, and the perimeter is lower semicontinuous.
  have hconv : Tendsto (fun k => volume (steinerSymmetrization e he (F k) ∆
      steinerSymmetrization e he s)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsymm
      (fun _ => zero_le) fun k => ?_
    exact (volume_steinerSymmetrization_symmDiff_le e he (hFm k) hs).trans_eq
      (measure_congr ((hFae k).symmDiff .rfl))
  calc perimeter volume ⊤ (steinerSymmetrization e he s)
      ≤ liminf (fun k => perimeter volume ⊤ (steinerSymmetrization e he (F k))) atTop :=
        perimeter_le_liminf
          (.of_forall fun k => nullMeasurableSet_steinerSymmetrization e he (hFm k))
          (nullMeasurableSet_steinerSymmetrization e he hs) fun K _ _ =>
            tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
              (fun _ => zero_le) fun _ => measure_mono inter_subset_left
    _ ≤ liminf (fun k => perimeter volume ⊤ (F k)) atTop :=
        liminf_le_liminf (.of_forall hstep)
    _ = perimeter volume ⊤ s := hPF.liminf_eq

end TauCeti
