/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
public import TauCeti.Topology.Covering.PowerSubstitution
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Constructions
import TauCeti.Analysis.Polynomial.Puiseux.PowerSubstitution
import TauCeti.Topology.ContinuousOn.Extension

/-!
# Analytic root branches after a power substitution

A separable polynomial family of constant degree on a product of a simply connected parameter
space and a punctured complex disc has finite root monodromy. A power substitution whose exponent
is divisible by the factorial of the degree kills that monodromy. The resulting continuous root
branches are analytic when the coefficients are analytic, since all roots on the punctured disc
are simple.

`TauCeti.Polynomial.exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution` gives a complete
factorization of a monic family into pairwise distinct analytic linear factors after substitution.
The functions are defined on the ambient normed space and are analytic on the punctured product;
no analyticity at the puncture is asserted. This is the input to removable-singularity arguments
that extend the factorization to the full disc, where roots may collide.

The parameter domain may be any open simply connected subset of a complex Banach space, including
a polydisc. The substituted disc has radius `R'`, with `R' ^ n ≤ R`; the exponent may be any
nonzero multiple of `d!`, in particular `d!` itself. Degree-zero monic families are included.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

noncomputable section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti.Polynomial

section Continuous

variable {E : Type*} [TopologicalSpace E]
  {U : Set E} {F : E × ℂ → ℂ[X]} {d n : ℕ} {R R' : ℝ}

/-- The finite root covering gives a continuous, pointwise injective list of roots after a power
substitution. The list is indexed by `Fin d`, using the cardinality of one fibre. -/
private theorem exists_continuousOn_isRoot_powerSubstitution
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (hR' : 0 < R') (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n)
    (hF : ∀ i ≤ d, ContinuousOn (fun b => (F b).coeff i) (U ×ˢ (ball 0 R \ {0})))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hsep : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).Separable) :
    ∃ r : Fin d → E × ℂ → ℂ,
      (∀ i, ContinuousOn (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
      ∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
        Injective (fun i => r i b) ∧ ∀ i, (F (b.1, b.2 ^ n)).IsRoot (r i b) := by
  -- Restrict the family to the punctured product, where the root covering is available.
  let incl : U × ↥(ball (0 : ℂ) R \ {0}) → E × ℂ := fun b => (b.1.1, b.2.1)
  have hincl : ∀ b, incl b ∈ U ×ˢ (ball 0 R \ {0}) := fun b => ⟨b.1.2, b.2.2⟩
  have hic : Continuous incl :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have : Nonempty (U × ↥(ball (0 : ℂ) R' \ {0})) := by
    obtain ⟨x, hx, hxR⟩ := NormedField.exists_norm_lt ℂ hR'
    exact ⟨(Classical.ofNonempty, ⟨x, mem_ball_zero_iff.2 hxR, norm_pos_iff.1 hx⟩)⟩
  obtain ⟨s, hs⟩ := exists_continuousMap_isRoot_powerSubstitution (F := F ∘ incl)
    (fun i hi => (hF i hi).comp_continuous hic hincl) (fun b => hdeg _ (hincl b))
    (fun b => hsep _ (hincl b)) hn hR hdvd
  let sub : U ×ˢ (ball (0 : ℂ) R' \ {0}) → U × ↥(ball (0 : ℂ) R' \ {0}) := fun b =>
    (⟨b.1.1, b.2.1⟩, ⟨b.1.2, b.2.2⟩)
  have hsub : Continuous sub := by fun_prop
  choose r hr hrs using fun i => ((s i).continuous.comp hsub).exists_continuousOn_eq
  refine ⟨r, hr, fun b hb => ?_⟩
  have hrb : ∀ i, r i b = s i (sub ⟨b, hb⟩) := fun i => hrs i ⟨b, hb⟩
  refine ⟨fun i j hij => (hs (sub ⟨b, hb⟩)).1 ((hrb i).symm.trans (hij.trans (hrb j))),
    fun i => ?_⟩
  rw [hrb i]
  simpa only [incl, comp_apply, powerSubstitution_apply_fst,
    coe_powerSubstitution_apply_snd] using (hs (sub ⟨b, hb⟩)).2 i

end Continuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {U : Set E} {F : E × ℂ → ℂ[X]} {d n : ℕ} {R R' : ℝ}

/-- **A power substitution splits a monic analytic family on a punctured disc.** On an open
simply connected parameter domain, let `F` be monic of constant degree `d`, with analytic
coefficients and separable fibres on the punctured product of radius `R`. For every nonzero
multiple `n` of `d!` and positive `R'` with `R' ^ n ≤ R`, there are `d` analytic branches on the
punctured product of radius `R'`. They are pointwise distinct and their linear factors multiply
to `F (x, t ^ n)`.

The branches are ambient functions, so they can be passed directly to analytic extension
results. Their values outside the punctured product are unconstrained. No regularity at `t = 0`
is required of the original family or asserted of the branches. -/
theorem exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution [CompleteSpace E]
    [SimplyConnectedSpace U]
    (hU : IsOpen U) (hR' : 0 < R') (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n)
    (hF : ∀ i < d, AnalyticOnNhd ℂ (fun b => (F b).coeff i) (U ×ˢ (ball 0 R \ {0})))
    (hmonic : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).Monic)
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hsep : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).Separable) :
    ∃ r : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
      ∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
        Injective (fun i => r i b) ∧ F (b.1, b.2 ^ n) = ∏ i, (X - C (r i b)) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  -- Monicity makes the remaining coefficient locally constant, so only lower coefficients
  -- need an analyticity hypothesis.
  have hFa : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b => (F b).coeff i)
      (U ×ˢ (ball 0 R \ {0})) := by
    intro i hi b hb
    rcases lt_or_eq_of_le hi with hlt | rfl
    · exact hF i hlt b hb
    · refine (analyticAt_const (v := (1 : ℂ))).congr ?_
      filter_upwards [(hU.prod (isOpen_ball.sdiff isClosed_singleton)).mem_nhds hb] with v hv
      exact (by simpa only [hdeg v hv] using (hmonic v hv).coeff_natDegree :
        (F v).coeff i = 1).symm
  obtain ⟨r, hrc, hr⟩ := exists_continuousOn_isRoot_powerSubstitution hR' hn hR hdvd
    (fun i hi => (hFa i hi).continuousOn) hdeg hsep
  let Q : E × ℂ → E × ℂ := fun b => (b.1, b.2 ^ n)
  let W := U ×ˢ (ball (0 : ℂ) R' \ {0})
  have hW : IsOpen W := hU.prod (isOpen_ball.sdiff isClosed_singleton)
  have hQ : ∀ b ∈ W, Q b ∈ U ×ˢ (ball 0 R \ {0}) := by
    intro b hb
    refine ⟨hb.1, ?_, pow_ne_zero n hb.2.2⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hb.2.1) (norm_nonneg _) hn).trans_le hR
  have hQa : ∀ b, AnalyticAt ℂ Q b := fun b =>
    analyticAt_fst.prod (analyticAt_snd.fun_pow n)
  refine ⟨r, fun i b hb => ?_, fun b hb => ⟨(hr b hb).1, ?_⟩⟩
  · have hcoeff : ∀ j ≤ d, AnalyticAt ℂ (fun b => (F (Q b)).coeff j) b :=
      fun j hj => (hFa j hj _ (hQ b hb)).comp (hQa b)
    have hdegree : ∀ᶠ v in 𝓝 b, (F (Q v)).natDegree ≤ d :=
      Filter.mem_of_superset (hW.mem_nhds hb) fun v hv => (hdeg _ (hQ v hv)).le
    have hroot : ∀ᶠ v in 𝓝 b, (F (Q v)).IsRoot (r i v) :=
      Filter.mem_of_superset (hW.mem_nhds hb) fun v hv => (hr v hv).2 i
    have hsimple : (derivative (F (Q b))).eval (r i b) ≠ 0 := by
      simpa only [eval₂_id] using
        (hsep _ (hQ b hb)).eval₂_derivative_ne_zero (RingHom.id ℂ) ((hr b hb).2 i)
    exact analyticAt_of_eventually_isRoot hcoeff hdegree
      ((hrc i b hb).continuousAt (hW.mem_nhds hb)) hroot hsimple
  · exact (Sym.toMonic_ofFn_eq_of_forall_isRoot (hmonic _ (hQ b hb))
      (hdeg _ (hQ b hb)) (hr b hb).1 (hr b hb).2).symm.trans (Sym.toMonic_ofFn _)

end TauCeti.Polynomial
