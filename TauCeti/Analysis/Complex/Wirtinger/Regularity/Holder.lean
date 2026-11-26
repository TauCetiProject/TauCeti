/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Complex.Pompeiu.Weak
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Complex.Pompeiu.Holder.Higher
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.Holder.Localization

/-!
# Interior Hölder regularity for the distributional `\bar∂` equation

Let `F` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open, `k : ℕ` and `0 < α < 1`.
If `u : ℂ → F` solves `\bar∂u = g` in the sense of distributions on `Ω`
(`TauCeti.HasWeakConjWirtingerDerivOn`), and `g` is `Cᵏ` on `Ω` with `k`-th derivative
`α`-Hölder on every compact subset of `Ω`, then `u` agrees almost everywhere on `Ω` with a map
`v` that is `C^{k+1}` on `Ω`, solves `\bar∂v = g` pointwise on `Ω`, and whose `(k + 1)`-th
derivative is `α`-Hölder on every compact subset of `Ω`
(`TauCeti.HasWeakConjWirtingerDerivOn.exists_contDiffOn_ae_eq_of_holderOnWith`). A continuous
solution is itself such a map (`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_of_holderOnWith`).
This is the interior Schauder estimate for `\bar∂` in qualitative form: the equation gains one
Hölder derivative, `g ∈ C^{k,α}_loc` gives `u ∈ C^{k+1,α}_loc`. The case `k = 0`, with the
hypothesis and conclusion stated for `g` and `Du` directly, is
`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_one_of_holderOnWith`: a continuous weak solution
with locally Hölder right-hand side is a classical `C¹` solution with locally Hölder derivative.
This is the regularity that upgrades distributional solutions with Hölder coefficients, such as
limits of solutions obtained by compactness, to classical ones.

Near each point the data are cut off to compactly supported `C^{k,α}` data `f` with `f = g` on a
smaller disc. The Cauchy transform of `f` is `C^{k+1,α}` near the point
(`TauCeti.exists_contDiffOn_holderOnWith_iteratedFDeriv_cauchyTransform`) and solves
`\bar∂ (T f) = f` distributionally (`TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform`), so
`u - T f` is a distributional solution of `\bar∂ = 0` on the smaller disc, holomorphic up to a
null set by Weyl's lemma (`TauCeti.HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq`).
The local representatives are continuous and agree almost everywhere on overlaps, hence agree, and
glue to one representative on `Ω`.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivOn.exists_contDiffOn_ae_eq_of_holderOnWith`: a distributional
  solution with `C^{k,α}_loc` right-hand side has a `C^{k+1,α}_loc` representative solving the
  equation classically.
* `TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_of_holderOnWith`: the same for a continuous
  solution itself.
* `TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_one_of_holderOnWith`: the case `k = 0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.4 and Theorem 4.6 (interior Hölder estimates for the Newtonian potential and for
  Poisson's equation).
-/

public section

open Complex Metric MeasureTheory Set Filter TopologicalSpace
open scoped NNReal Topology ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {Ω : Opens ℂ} {u g : ℂ → F} {k : ℕ} {α : ℝ≥0}

omit [FiniteDimensional ℂ F] in
/-- **Cutting off local `C^{k,α}` data.** Data that are `Cᵏ` on `ball z₀ r`, with derivatives
through order `k` bounded there and `k`-th derivative `α`-Hölder there, agree on `ball z₀ (r / 3)`
with `Cᵏ` data supported in `closedBall z₀ (2 * r / 3)` that are bounded with all derivatives
through order `k` and have globally `α`-Hölder `k`-th derivative. -/
private theorem exists_cutoff_eqOn {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {M H : ℝ≥0}
    (hg : ContDiffOn ℝ k g (ball z₀ r))
    (hM : ∀ j ≤ k, ∀ x ∈ ball z₀ r, ‖iteratedFDeriv ℝ j g x‖ ≤ M)
    (hH : HolderOnWith H α (iteratedFDeriv ℝ k g) (ball z₀ r)) (hα : α ≤ 1) :
    ∃ f : ℂ → F, ContDiff ℝ k f ∧ Function.support f ⊆ closedBall z₀ (2 * r / 3) ∧
      (∃ H' : ℝ≥0, HolderWith H' α (iteratedFDeriv ℝ k f)) ∧
      (∃ M' : ℝ≥0, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M') ∧ EqOn f g (ball z₀ (r / 3)) := by
  let χ : ContDiffBump z₀ := ⟨r / 3, 2 * r / 3, by positivity, by linarith⟩
  have hχ (m : ℕ) : ContDiff ℝ m χ := χ.contDiff.of_le (by exact_mod_cast le_top)
  obtain ⟨N, hN0, hN⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv_of_contDiff (hχ (k + 1))
  let N' : ℝ≥0 := ⟨N, hN0⟩
  have hrIn : χ.rIn = r / 3 := rfl
  have hrOut : χ.rOut = 2 * r / 3 := rfl
  let δ : ℝ≥0 := ⟨r / 3, by positivity⟩
  have hδr : (δ : ℝ) = r / 3 := rfl
  have hδ : 0 < δ := by rw [← NNReal.coe_pos, hδr]; positivity
  -- The `r / 3`-thickening of the support of the cutoff is the ball of radius `r`.
  have hthick : thickening (δ : ℝ) (tsupport χ) ⊆ ball z₀ r := by
    rw [χ.tsupport_eq, hrOut]
    refine (thickening_closedBall (by exact_mod_cast hδ) (by positivity) z₀).subset.trans ?_
    exact ball_subset_ball (by rw [hδr]; linarith)
  have hts : tsupport χ ⊆ ball z₀ r :=
    (self_subset_thickening (by exact_mod_cast hδ) _).trans hthick
  have hχb : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N' := fun i hi x ↦ hN i hi x
  refine ⟨fun x ↦ χ x • g x, ?_, ?_,
    ⟨_, holderWith_iteratedFDeriv_cutoff_smul_of_thickening_subset hg (hχ (k + 1)) isOpen_ball hδ
      hthick hα hM hχb hH⟩, ⟨2 ^ k * N' * M, fun j hj x ↦ ?_⟩, fun x hx ↦ ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball z₀ r
    · exact (hχ k).contDiffAt.smul (hg.contDiffAt (isOpen_ball.mem_nhds hx))
    · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hts h)] with y hy
      simp [hy]
  · refine (Function.support_smul_subset_left (⇑χ) g).trans ?_
    rw [χ.support_eq, hrOut]
    exact ball_subset_closedBall
  · refine (norm_iteratedFDeriv_cutoff_smul_le hg (hχ k) isOpen_ball hts hj hM
      (fun i hi x ↦ hχb i (by omega) x) x).trans ?_
    push_cast
    gcongr
    exact one_le_two
  · dsimp only
    rw [χ.one_of_mem_closedBall (by rw [hrIn]; exact ball_subset_closedBall hx), one_smul]

/-- **Local regularity.** Near each point of `Ω`, a distributional solution of `\bar∂u = g` with
`g ∈ C^{k,α}_loc(Ω)` agrees almost everywhere with a map that is `C^{k+1}` with `α`-Hölder
`(k + 1)`-th derivative on a ball about the point: the Cauchy transform of a cutoff of `g` plus a
holomorphic map. -/
private theorem exists_ball_contDiffOn_ae_eq (hα : 0 < α) (hα1 : α < 1)
    (h : HasWeakConjWirtingerDerivOn volume Ω u g) (hg : ContDiffOn ℝ k g Ω)
    (hgH : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ v : ℂ → F, ContDiffOn ℝ (k + 1 : ℕ) v (ball z₀ r) ∧
      u =ᵐ[volume.restrict (ball z₀ r)] v ∧
      ∃ C, HolderOnWith C α (iteratedFDeriv ℝ (k + 1) v) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  have hε2 : ball z₀ (ε / 2) ⊆ Ω :=
    (ball_subset_ball (half_le_self hε.le)).trans hεΩ
  obtain ⟨C, hC⟩ := hgH (closedBall z₀ (ε / 2))
    ((closedBall_subset_ball (half_lt_self hε)).trans hεΩ) (isCompact_closedBall _ _)
  -- Common bounds and a Hölder bound for the data on a ball `B(z₀, r)`.
  obtain ⟨r, hr, hrε, M, H, hM, hH⟩ :=
    (hg.mono hε2).exists_ball_bounds_and_holderOnWith_iteratedFDeriv
      (ball_mem_nhds z₀ (half_pos hε)) hα1.le (hC.mono ball_subset_closedBall)
  have hrΩ : ball z₀ r ⊆ Ω := hrε.trans hε2
  -- Cut the data off to `f`, equal to `g` on `B(z₀, r / 3)`.
  obtain ⟨f, hf, hfs, ⟨Hf, hHf⟩, ⟨Mf, hMf⟩, hfg⟩ :=
    exists_cutoff_eqOn hr (hg.mono hrΩ) hM (hH k le_rfl) hα1.le
  obtain ⟨A, hA⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_cauchyTransform (F := F) k hα
    hα1 z₀ (r := 2 * r / 3) (R := r / 3) (by positivity) (by positivity)
  obtain ⟨hTcd, hTH, -⟩ := hA hf hfs hHf hMf
  -- On `B(z₀, r / 3)`, `u - T f` solves `\bar∂ = 0`, so it is holomorphic up to a null set.
  let B : Opens ℂ := ⟨ball z₀ (r / 3), isOpen_ball⟩
  have hBΩ : B ≤ Ω := (ball_subset_ball (by linarith)).trans hrΩ
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hfs)
  have hgf : g =ᵐ[volume.restrict (B : Set ℂ)] f :=
    (ae_restrict_mem isOpen_ball.measurableSet).mono fun x hx ↦ (hfg hx).symm
  have hw := ((h.mono hBΩ).congr_ae_deriv hgf).sub
    (hasWeakConjWirtingerDerivOn_cauchyTransform hfi B)
  rw [sub_self] at hw
  obtain ⟨w, hwd, hwu⟩ := hw.exists_differentiableOn_ae_eq
  have hw' : ContDiffOn ℝ (k + 1 + 1 : ℕ) w (ball z₀ (r / 3)) :=
    (hwd.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hsub : ball z₀ (r / 6) ⊆ ball z₀ (r / 3) := ball_subset_ball (by linarith)
  have hsub' : ball z₀ (r / 6) ⊆ ball z₀ (r / 3 + 1) := ball_subset_ball (by linarith)
  obtain ⟨Cw, hCw⟩ := hw'.exists_holderOnWith_iteratedFDeriv isOpen_ball hα1.le
    (isCompact_closedBall z₀ (r / 6)) (closedBall_subset_ball (by linarith))
  refine ⟨r / 6, by positivity, hsub.trans hBΩ, cauchyTransform f + w,
    (hTcd.mono hsub').add ((hw'.of_le (by exact_mod_cast Nat.le_succ _)).mono hsub), ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hwu] with z hz
    rw [Pi.add_apply, ← hz, Pi.sub_apply, add_sub_cancel]
  · refine ⟨_, ((hTH.mono (hsub.trans ball_subset_closedBall)).add
      (hCw.mono ball_subset_closedBall)).congr fun x hx ↦ ?_⟩
    exact (iteratedFDeriv_add_apply (hTcd.contDiffAt (isOpen_ball.mem_nhds (hsub' hx)))
      ((hw'.of_le (by exact_mod_cast Nat.le_succ _)).contDiffAt
        (isOpen_ball.mem_nhds (hsub hx)))).symm

/-- **Interior Hölder regularity for `\bar∂`.** For `0 < α < 1`, a distributional solution of
`\bar∂u = g` on `Ω`, with `g` of class `Cᵏ` on `Ω` and `k`-th derivative `α`-Hölder on every
compact subset of `Ω`, agrees almost everywhere on `Ω` with a map `v` of class `C^{k+1}` on `Ω`
that solves `\bar∂v = g` at every point of `Ω` and whose `(k + 1)`-th derivative is `α`-Hölder on
every compact subset of `Ω`. -/
theorem HasWeakConjWirtingerDerivOn.exists_contDiffOn_ae_eq_of_holderOnWith (hα : 0 < α)
    (hα1 : α < 1) (h : HasWeakConjWirtingerDerivOn volume Ω u g) (hg : ContDiffOn ℝ k g Ω)
    (hgH : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K) :
    ∃ v : ℂ → F, ContDiffOn ℝ (k + 1 : ℕ) v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      (∀ z ∈ Ω, conjWirtingerDeriv v z 1 = g z) ∧
      ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ (k + 1) v) K := by
  have := FiniteDimensional.completeSpace ℂ F
  choose! r hr hrΩ v hv hvu hvH using fun z (hz : z ∈ (Ω : Set ℂ)) ↦
    exists_ball_contDiffOn_ae_eq hα hα1 h hg hgH hz
  -- The local representatives are continuous and agree almost everywhere on overlaps, hence
  -- agree there; so `V z = v z z` agrees with `v z` on the whole ball about `z`.
  let V : ℂ → F := fun z ↦ v z z
  have hV : ∀ z ∈ (Ω : Set ℂ), EqOn V (v z) (ball z (r z)) := fun z hz w hw ↦ by
    have hwΩ : w ∈ (Ω : Set ℂ) := hrΩ z hz hw
    have huw : u =ᵐ[volume.restrict (ball w (r w) ∩ ball z (r z))] v w :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hvu w hwΩ)
    have huz : u =ᵐ[volume.restrict (ball w (r w) ∩ ball z (r z))] v z :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hvu z hz)
    have hae := huw.symm.trans huz
    exact Measure.eqOn_open_of_ae_eq hae (isOpen_ball.inter isOpen_ball)
      ((hv w hwΩ).continuousOn.mono inter_subset_left)
      ((hv z hz).continuousOn.mono inter_subset_right) ⟨mem_ball_self (hr w hwΩ), hw⟩
  have hVcd : ContDiffOn ℝ (k + 1 : ℕ) V Ω := contDiffOn_of_locally_contDiffOn fun z hz ↦
    ⟨ball z (r z), isOpen_ball, mem_ball_self (hr z hz),
      ((hv z hz).congr (hV z hz)).mono inter_subset_right⟩
  -- Countably many of the balls cover `Ω`.
  have hVu : u =ᵐ[volume.restrict Ω] V := by
    obtain ⟨T, hTc, hTU⟩ := isOpen_iUnion_countable
      (fun z : (Ω : Set ℂ) ↦ ball (z : ℂ) (r z)) fun _ ↦ isOpen_ball
    have hΩT : (Ω : Set ℂ) = ⋃ z ∈ T, ball (z : ℂ) (r z) := by
      rw [hTU]
      exact Subset.antisymm (fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩)
        (iUnion_subset fun z ↦ hrΩ z z.property)
    rw [Filter.EventuallyEq, hΩT, ae_restrict_biUnion_iff _ hTc]
    intro z _
    filter_upwards [hvu z z.property, ae_restrict_mem measurableSet_ball] with x hx hxb
    rw [hx, hV z z.property hxb]
  have hV1 : ContDiffOn ℝ 1 V Ω := hVcd.of_le (by exact_mod_cast Nat.le_add_left 1 k)
  refine ⟨V, hVcd, hVu, fun z hz ↦ ?_, fun K hKΩ hK ↦ ?_⟩
  · -- The classical and distributional derivatives agree almost everywhere, and are continuous.
    have he := (h.congr_ae hVu).ae_eq (hasWeakConjWirtingerDerivOn_of_contDiffOn hV1)
    exact (Measure.eqOn_open_of_ae_eq he Ω.isOpen hg.continuousOn
      (hV1.conjWirtingerDeriv_apply_of_isOpen Ω.isOpen (m := 0) (by simp) 1).continuousOn hz).symm
  · obtain ⟨δ, hδ, L, -, hL, -⟩ := hK.exists_holderOnWith_thickening_and_norm_le
      (f := iteratedFDeriv ℝ (k + 1) V) fun z hz ↦ by
        obtain ⟨C, hC⟩ := hvH z (hKΩ hz)
        refine ⟨r z, hr z (hKΩ hz), C, hC.congr fun x hx ↦ ?_⟩
        exact (((hV z (hKΩ hz)).eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).iteratedFDeriv ℝ
          (k + 1)).eq_of_nhds.symm
    exact ⟨L, hL.mono (self_subset_thickening hδ K)⟩

/-- **Interior Hölder regularity for continuous solutions of `\bar∂`.** For `0 < α < 1`, a
continuous distributional solution of `\bar∂u = g` on `Ω`, with `g` of class `Cᵏ` on `Ω` and
`k`-th derivative `α`-Hölder on every compact subset of `Ω`, is of class `C^{k+1}` on `Ω`, solves
`\bar∂u = g` at every point of `Ω`, and its `(k + 1)`-th derivative is `α`-Hölder on every compact
subset of `Ω`. -/
theorem HasWeakConjWirtingerDerivOn.contDiffOn_of_holderOnWith (hα : 0 < α) (hα1 : α < 1)
    (h : HasWeakConjWirtingerDerivOn volume Ω u g) (hu : ContinuousOn u Ω)
    (hg : ContDiffOn ℝ k g Ω)
    (hgH : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k g) K) :
    ContDiffOn ℝ (k + 1 : ℕ) u Ω ∧ (∀ z ∈ Ω, conjWirtingerDeriv u z 1 = g z) ∧
      ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α (iteratedFDeriv ℝ (k + 1) u) K := by
  obtain ⟨v, hv, huv, hD, hH⟩ := h.exists_contDiffOn_ae_eq_of_holderOnWith hα hα1 hg hgH
  have he : EqOn u v Ω := Measure.eqOn_open_of_ae_eq huv Ω.isOpen hu hv.continuousOn
  have hn : ∀ z ∈ (Ω : Set ℂ), u =ᶠ[𝓝 z] v := fun z hz ↦
    he.eventuallyEq_of_mem (Ω.isOpen.mem_nhds hz)
  refine ⟨hv.congr he, fun z hz ↦ ?_, fun K hKΩ hK ↦ ?_⟩
  · rw [(hn z hz).conjWirtingerDeriv_eq]
    exact hD z hz
  · obtain ⟨C, hC⟩ := hH K hKΩ hK
    exact ⟨C, hC.congr fun x hx ↦ ((hn x (hKΩ hx)).iteratedFDeriv ℝ (k + 1)).eq_of_nhds.symm⟩

/-- **Hölder data give classical solutions of `\bar∂`.** For `0 < α < 1`, a continuous
distributional solution of `\bar∂u = g` on `Ω`, with `g` `α`-Hölder on every compact subset of
`Ω`, is of class `C¹` on `Ω`, solves `\bar∂u = g` at every point of `Ω`, and its derivative is
`α`-Hölder on every compact subset of `Ω`. -/
theorem HasWeakConjWirtingerDerivOn.contDiffOn_one_of_holderOnWith (hα : 0 < α) (hα1 : α < 1)
    (h : HasWeakConjWirtingerDerivOn volume Ω u g) (hu : ContinuousOn u Ω)
    (hgH : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α g K) :
    ContDiffOn ℝ 1 u Ω ∧ (∀ z ∈ Ω, conjWirtingerDeriv u z 1 = g z) ∧
      ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α (fderiv ℝ u) K := by
  -- Hölder bounds on the closed balls in `Ω` make `g` continuous on `Ω`.
  have hg : ContinuousOn g Ω := fun z hz ↦ by
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen z hz
    obtain ⟨C, hC⟩ := hgH (closedBall z (ε / 2))
      ((closedBall_subset_ball (half_lt_self hε)).trans hεΩ) (isCompact_closedBall z _)
    exact ((hC.continuousOn hα).continuousAt
      (closedBall_mem_nhds z (half_pos hε))).continuousWithinAt
  obtain ⟨h1, h2, h3⟩ := h.contDiffOn_of_holderOnWith (k := 0) hα hα1 hu
    (contDiffOn_zero.2 hg) fun K hKΩ hK ↦
      (hgH K hKΩ hK).imp fun _ hC ↦ holderOnWith_iteratedFDeriv_zero_iff.2 hC
  refine ⟨by simpa using h1, h2, fun K hKΩ hK ↦ (h3 K hKΩ hK).imp fun _ hC ↦ ?_⟩
  exact holderOnWith_iteratedFDeriv_zero_iff.1 (holderOnWith_iteratedFDeriv_succ_iff.1 hC)

end TauCeti
