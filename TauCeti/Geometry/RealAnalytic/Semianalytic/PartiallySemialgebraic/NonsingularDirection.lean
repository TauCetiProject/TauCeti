/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.NonsingularDirection
public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology

/-!
# Sets with a nonsingular vertical direction are partially semialgebraic

Write points of the cylinder `(ι → ℝ) × (Unit → ℝ)` as `(x, t)`, with base point `x` and height
`t`, and let `(0, 1)` be the vertical direction. If a function `f` analytic at `p` does not vanish
identically on the vertical line through `p`, the real Weierstrass preparation theorem writes it
near `p` as a monic polynomial in the height, with coefficients analytic in the base point, times a
nonvanishing analytic unit. Hence near `p` the function `f` has the same signs as a polynomial in
the height with analytic coefficients (`AnalyticAt.exists_isAnalyticCoeffPolynomialOn_sign_eq`),
and a set for which the vertical direction is nonsingular at `p` agrees near `p` with a Boolean
combination of analytic-coefficient polynomial sign conditions
(`TauCeti.IsNonsingularDirectionAt.exists_isAnalyticCoeffBooleanCombination`).

These descriptions only hold near a point, while partial semialgebraicity asks for a description
over the whole vertical cylinder above a neighbourhood of a base point. When the heights of the set
are bounded, finitely many of the local descriptions cover the relevant part of the cylinder above a
base point, by compactness of a bounded interval of heights, and they patch together into a single
description. This is Lemma 5 of Łojasiewicz's triangulation of semianalytic sets: a bounded set for
which the vertical direction is nonsingular is partially semialgebraic in the vertical coordinate
(`TauCeti.IsNonsingularDirection.isPartiallySemialgebraic`).

## Main results

* `AnalyticAt.exists_isAnalyticCoeffPolynomialOn_sign_eq`: an analytic function not vanishing
  identically on a vertical line has, near a point of that line, the signs of a polynomial in the
  height with analytic coefficients.
* `TauCeti.partiallySemialgebraicAt_of_isNonsingularDirectionAt`: a set with bounded heights is
  partially semialgebraic over a base point if the vertical direction is nonsingular for it at
  every point above that base point.
* `TauCeti.IsNonsingularDirection.isPartiallySemialgebraic`: a set with bounded heights for which
  the vertical direction is nonsingular is partially semialgebraic.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §2, Lemma 5.
-/

public section

open Filter MeasureTheory MvPolynomial Set Topology

variable {ι : Type} [Fintype ι]

/-- **Local polynomial signs along a nonsingular vertical direction.** Let `f` be analytic at a
point `p` of the cylinder `(ι → ℝ) × (Unit → ℝ)`, and not identically zero on the vertical line
through `p` near `p`. Then, near `p`, the function `f` has the same signs as a polynomial in the
height whose coefficients are analytic on a neighbourhood of the base point `p.1`. -/
theorem AnalyticAt.exists_isAnalyticCoeffPolynomialOn_sign_eq
    {f : (ι → ℝ) × (Unit → ℝ) → ℝ} {p : (ι → ℝ) × (Unit → ℝ)} (hf : AnalyticAt ℝ f p)
    (hv : ¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (p + ξ • (0, 1)) = 0) :
    ∃ U ∈ 𝓝 p.1, ∃ g, TauCeti.IsAnalyticCoeffPolynomialOn U g ∧
      ∀ᶠ q in 𝓝 p, SignType.sign (f q) = SignType.sign (g q) := by
  classical
  -- read `f` in the coordinates `(x, t)` of `(ι → ℝ) × ℝ`
  set t₀ := p.2 ()
  let e : (ι → ℝ) × ℝ → (ι → ℝ) × (Unit → ℝ) := fun q => (q.1, fun _ => q.2)
  have he (q : (ι → ℝ) × (Unit → ℝ)) : e (q.1, q.2 ()) = q := rfl
  have hF : AnalyticAt ℝ (f ∘ e) (p.1, t₀) :=
    hf.comp_of_eq (analyticAt_fst.prod (AnalyticAt.pi fun _ => analyticAt_snd)) (he p)
  -- the vertical slice of `f` through `p` vanishes to some finite order `d`
  have hd : analyticOrderAt (fun t => (f ∘ e) (p.1, t)) t₀ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    refine fun h => hv ?_
    have hT : Tendsto (fun ξ : ℝ => t₀ + ξ) (𝓝 0) (𝓝 t₀) := by
      simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ)))
    filter_upwards [hT.eventually h] with ξ hξ
    have hξe : p + ξ • ((0, 1) : (ι → ℝ) × (Unit → ℝ)) = e (p.1, t₀ + ξ) :=
      Prod.ext (by simp [e]) (funext fun _ => by simp [e, t₀])
    rwa [hξe]
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hd
  obtain ⟨c, u, hc, -, hu, hu0, hfac⟩ := hF.exists_weierstrassPreparation_real hd.symm
  -- the Weierstrass polynomial, multiplied by the value of the unit at the centre
  let Q : MvPolynomial (Fin d ⊕ Unit) ℝ := C (u (p.1, t₀)) *
    ((X (.inr ()) - C t₀) ^ d + ∑ i : Fin d, X (.inl i) * (X (.inr ()) - C t₀) ^ (i : ℕ))
  refine ⟨{x | ∀ i, AnalyticAt ℝ (c i) x}, eventually_all.2 fun i => (hc i).eventually_analyticAt,
    _, TauCeti.isAnalyticCoeffPolynomialOn_eval_sumElim (U := {x | ∀ i, AnalyticAt ℝ (c i) x})
      (c := fun x i => c i x) (fun i _ hx => hx i) Q, ?_⟩
  -- near the centre the unit has the sign of its value at the centre
  have hus : ∀ᶠ z in 𝓝 (p.1, t₀), SignType.sign (u z) = SignType.sign (u (p.1, t₀)) :=
    ((continuousAt_sign_of_ne_zero hu0).comp hu.continuousAt)
      ((isOpen_discrete _).mem_nhds (mem_singleton _))
  have hπ : Tendsto (fun q : (ι → ℝ) × (Unit → ℝ) => (q.1, q.2 ())) (𝓝 p) (𝓝 (p.1, t₀)) :=
    (continuous_fst.prodMk ((continuous_apply ()).comp continuous_snd)).tendsto p
  filter_upwards [hπ.eventually hfac, hπ.eventually hus] with q hq hqu
  rw [← he q, ← Function.comp_apply (f := f), hq, sign_mul, hqu]
  simp [Q, e, TauCeti.Polynomial.eval_monicOfCoeff, sign_mul, mul_comm]

namespace TauCeti

/-- Near a point `p` of the cylinder `(ι → ℝ) × (Unit → ℝ)` at which the vertical direction is
nonsingular for `s`, the set `s` agrees with a Boolean combination of polynomial sign conditions in
the height, with coefficients analytic on a neighbourhood of the base point `p.1`. -/
theorem IsNonsingularDirectionAt.exists_isAnalyticCoeffBooleanCombination
    {s : Set ((ι → ℝ) × (Unit → ℝ))} {p : (ι → ℝ) × (Unit → ℝ)}
    (hs : IsNonsingularDirectionAt s (0, 1) p) :
    ∃ U ∈ 𝓝 p.1, ∃ t, IsAnalyticCoeffBooleanCombination U t ∧ s =ᶠ[𝓝 p] t := by
  obtain ⟨t, ht, hst⟩ := isNonsingularDirectionAt_def.1 hs
  -- the sets with such a description near `p` form an algebra of sets
  let ℬ : Set (Set ((ι → ℝ) × (Unit → ℝ))) :=
    {t | ∃ U ∈ 𝓝 p.1, ∃ t', IsAnalyticCoeffBooleanCombination U t' ∧ t =ᶠ[𝓝 p] t'}
  have hℬ : IsSetAlgebra ℬ :=
    { empty_mem := ⟨univ, univ_mem, ∅, isAnalyticCoeffBooleanCombination_empty _,
        EventuallyEqSet.rfl⟩
      compl_mem := fun _ ⟨U, hU, t', ht', h⟩ => ⟨U, hU, t'ᶜ, ht'.compl, h.compl⟩
      union_mem := fun _ _ ⟨U, hU, t', ht', h⟩ ⟨V, hV, u', hu', h'⟩ =>
        ⟨U ∩ V, inter_mem hU hV, t' ∪ u',
          (ht'.mono inter_subset_left).union (hu'.mono inter_subset_right), h.union h'⟩ }
  suffices htℬ : t ∈ ℬ by
    obtain ⟨U, hU, t', ht', h⟩ := htℬ
    exact ⟨U, hU, t', ht', hst.trans h⟩
  -- each generating sign condition has such a description, by Weierstrass preparation
  refine hℬ.generateSetAlgebra_subset ?_ ht
  rintro _ (⟨f, hf, hv, rfl⟩ | ⟨f, hf, hv, rfl⟩) <;>
    obtain ⟨U, hU, g, hg, hfg⟩ := hf.exists_isAnalyticCoeffPolynomialOn_sign_eq hv
  · refine ⟨U, hU, _, hg.isAnalyticCoeffBooleanCombination_setOf_eq_zero,
      eventuallyEqSet_iff.2 (hfg.mono fun q hq => ?_)⟩
    rw [mem_ofPred_eq, mem_ofPred_eq, ← sign_eq_zero_iff, hq, sign_eq_zero_iff]
  · refine ⟨U, hU, _, hg.isAnalyticCoeffBooleanCombination_setOf_pos,
      eventuallyEqSet_iff.2 (hfg.mono fun q hq => ?_)⟩
    rw [mem_ofPred_eq, mem_ofPred_eq, ← sign_eq_one_iff, hq, sign_eq_one_iff]

/-- **Łojasiewicz's Lemma 5, over a base point.** Let `s` be a subset of the cylinder
`(ι → ℝ) × (Unit → ℝ)` with bounded heights. If the vertical direction is nonsingular for `s` at
every point above the base point `x₀`, then `s` is partially semialgebraic over `x₀`. -/
theorem partiallySemialgebraicAt_of_isNonsingularDirectionAt {s : Set ((ι → ℝ) × (Unit → ℝ))}
    {x₀ : ι → ℝ} (hb : Bornology.IsBounded (Prod.snd '' s))
    (hs : ∀ y, IsNonsingularDirectionAt s (0, 1) (x₀, y)) : PartiallySemialgebraicAt s x₀ := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  -- above each height `y`, a local description valid on a box of size `ε y` around `(x₀, y)`
  choose U hU t ht hst using fun y => (hs y).exists_isAnalyticCoeffBooleanCombination
  choose ε hε hεs using fun y => Metric.eventually_nhds_iff.1 (eventuallyEqSet_iff.1 (hst y))
  -- finitely many of these boxes cover the bounded heights
  obtain ⟨T, -, hT⟩ := (isCompact_closedBall (0 : Unit → ℝ) R).elim_nhds_subcover
    (fun y => Metric.ball y (ε y)) fun y _ => Metric.ball_mem_nhds y (hε y)
  refine partiallySemialgebraicAt_def.2 ⟨⋂ y ∈ T, U y ∩ Metric.ball x₀ (ε y),
    (biInter_finset_mem T).2 fun y _ => inter_mem (hU y) (Metric.ball_mem_nhds x₀ (hε y)),
    ⋃ y ∈ T, t y ∩ Prod.snd ⁻¹' Metric.ball y (ε y), ?_, ?_⟩
  · exact .biUnion T.finite_toSet fun y hy =>
      ((ht y).mono ((biInter_subset_of_mem hy).trans inter_subset_left)).inter
        ((isSemialgebraic_ball y (ε y)).isAnalyticCoeffBooleanCombination_preimage_snd _)
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_iInter, Metric.mem_ball, exists_prop]
  have key (y) (h₁ : dist q.1 x₀ < ε y) (h₂ : dist q.2 y < ε y) : q ∈ s ↔ q ∈ t y :=
    hεs y (by rw [Prod.dist_eq]; exact max_lt h₁ h₂)
  constructor
  · rintro ⟨hqs, hqV⟩
    obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.1 (hT (hR ⟨q, hqs, rfl⟩))
    exact ⟨⟨y, hyT, (key y (hqV y hyT).2 hy).1 hqs, hy⟩, hqV⟩
  · rintro ⟨⟨y, hyT, hqt, hy⟩, hqV⟩
    exact ⟨(key y (hqV y hyT).2 hy).2 hqt, hqV⟩

/-- **Łojasiewicz's Lemma 5.** A subset of the cylinder `(ι → ℝ) × (Unit → ℝ)` with bounded heights,
for which the vertical direction is nonsingular, is partially semialgebraic. This applies in
particular to bounded sets, by `Bornology.IsBounded.image_snd`. -/
theorem IsNonsingularDirection.isPartiallySemialgebraic {s : Set ((ι → ℝ) × (Unit → ℝ))}
    (hs : IsNonsingularDirection s (0, 1)) (hb : Bornology.IsBounded (Prod.snd '' s)) :
    IsPartiallySemialgebraic s :=
  isPartiallySemialgebraic_iff.2 fun _ =>
    partiallySemialgebraicAt_of_isNonsingularDirectionAt hb fun _ =>
      isNonsingularDirection_iff.1 hs _

end TauCeti
