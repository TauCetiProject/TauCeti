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
  classical
  -- Restrict the family to the punctured product and form its root covering.
  let B := U × ↥(ball (0 : ℂ) R \ {0})
  let B' := U × ↥(ball (0 : ℂ) R' \ {0})
  let incl : B → E × ℂ := fun b => (b.1.1, b.2.1)
  let incl' : B' → E × ℂ := fun b => (b.1.1, b.2.1)
  let G : B → ℂ[X] := F ∘ incl
  let Z := {q : B × ℂ // (G q.1).IsRoot q.2}
  let p : Z → B := fun q => q.1.1
  have hincl : ∀ b, incl b ∈ U ×ˢ (ball 0 R \ {0}) := fun b => ⟨b.1.2, b.2.2⟩
  have hic : Continuous incl :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hp : IsCoveringMap p := isCoveringMap_fst_isRoot
    (fun i hi => (hF i hi).comp_continuous hic hincl)
    (fun b => hdeg _ (hincl b)) (fun b => hsep _ (hincl b))
  -- At one base point the fibre has exactly `d` points. Lift all of them and index by `Fin d`.
  let t : ℂ := (R' / 2 : ℝ)
  have ht : t ∈ ball (0 : ℂ) R' \ {0} := by
    constructor
    · simpa [t, mem_ball_zero_iff, abs_of_pos hR'] using half_lt_self hR'
    · simpa [t] using ne_of_gt (half_pos hR')
  let a : B' := (Classical.ofNonempty, ⟨t, ht⟩)
  let q := powerSubstitution U hn hR
  have hqa := hincl (q a)
  let : Finite (p ⁻¹' {q a}) := finite_preimage_fst_isRoot (hsep _ hqa).ne_zero
  have hcard : Nat.card (p ⁻¹' {q a}) = d :=
    natCard_preimage_fst_isRoot (hdeg _ hqa) (hsep _ hqa)
  obtain ⟨L, hL, hinj⟩ := hp.exists_continuousMap_lifts_powerSubstitution hn hR a
    (by rw [← hcard] at hdvd; exact hdvd)
  let : Fintype (p ⁻¹' {q a}) := Fintype.ofFinite _
  let e : Fin d ≃ p ⁻¹' {q a} :=
    (Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let s : Fin d → B' → ℂ := fun i b => (L (e i) b).1.2
  have hs : ∀ i, Continuous (s i) := fun i =>
    continuous_snd.comp (continuous_subtype_val.comp (L (e i)).continuous)
  -- Extend each root coordinate to an ambient function; only its restriction is used.
  let r : Fin d → E × ℂ → ℂ := fun i => extend incl' (s i) 0
  have hincl' : Injective incl' := fun _ _ h =>
    Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hr : ∀ i b, r i (incl' b) = s i b := fun i b => hincl'.extend_apply _ _ b
  have hbase : ∀ i b, p (L (e i) b) = q b := fun i b => congrFun (hL (e i)).2 b
  refine ⟨r, ?_, ?_⟩
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (U ×ˢ (ball 0 R' \ {0})).domRestrict (r i) =
        fun b => s i (⟨b.1.1, b.2.1⟩, ⟨b.1.2, b.2.2⟩) := by
      funext b
      exact hr i (⟨b.1.1, b.2.1⟩, ⟨b.1.2, b.2.2⟩)
    rw [heq]
    exact (hs i).comp (by fun_prop)
  · intro b hb
    let b' : B' := (⟨b.1, hb.1⟩, ⟨b.2, hb.2⟩)
    have hrb : ∀ i, r i b = s i b' := fun i => hr i b'
    refine ⟨fun i j hij => e.injective (hinj b' ?_), fun i => ?_⟩
    · refine Subtype.ext (Prod.ext ((hbase i b').trans (hbase j b').symm) ?_)
      exact (hrb i).symm.trans (hij.trans (hrb j))
    · -- Read the root equation through the projections defining the root space.
      have hz : (F (incl (p (L (e i) b')))).IsRoot (s i b') := (L (e i) b').2
      rw [hrb i]
      rw [hbase i b'] at hz
      simpa only [incl, q, b', powerSubstitution_apply_fst,
        coe_powerSubstitution_apply_snd] using hz

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
