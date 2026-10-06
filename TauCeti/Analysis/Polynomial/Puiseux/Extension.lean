/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Monic.OfCoeff
public import TauCeti.Analysis.Complex.RemovableSingularity
import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# Extending analytic polynomial root branches across a hyperplane

An analytic root branch of a monic polynomial family on `U × (s \ {c₀})`
extends analytically to `U × s` when the lower coefficients are continuous there.
A complete factorization extends with all factors, so multiplicities are retained.
The extension still solves the polynomial equation, including on the hyperplane.
For a nonmonic family of fixed degree off the hyperplane, with continuous coefficients
and analytic leading coefficient, multiplying a root branch by the leading coefficient
gives an analytic extension. In particular, if that
coefficient is `(z - c₀)^a` times a nowhere-zero analytic function, the branch
has a Laurent form with pole order at most `a`.

These results supply the extension step in Puiseux arguments with parameters;
they start with single-valued analytic branches on the punctured domain. No
simplicity or distinctness of the roots is required at the hyperplane.

The proofs use Mathlib's `Polynomial.integralNormalization` to scale a root
by the leading coefficient, Cauchy's root bound in coefficient coordinates,
and `TauCeti.exists_analyticOnNhd_prod_eqOn` for joint analytic extension.

Reference: S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's
method for CAD construction*, J. Symbolic Comput. 92 (2019), §4.
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti.Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {U : Set V} {s : Set ℂ} {c₀ : ℂ} {d : ℕ}

/-- An analytic root branch of a monic family extends across `z = c₀`, and its
extension remains a root. The coefficients need only be continuous on the full
domain. The extension is unique there by
`TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton`. -/
theorem exists_analyticOnNhd_isRoot_monicOfCoeff
    (c : V × ℂ → Fin d → ℂ) {r : V × ℂ → ℂ} (hU : IsOpen U) (hs : IsOpen s)
    (hc : ContinuousOn c (U ×ˢ s)) (hr : AnalyticOnNhd ℂ r (U ×ˢ (s \ {c₀})))
    (hroot : ∀ x ∈ U ×ˢ (s \ {c₀}), (monicOfCoeff (c x)).IsRoot (r x)) :
    ∃ g : V × ℂ → ℂ, AnalyticOnNhd ℂ g (U ×ˢ s) ∧
      EqOn g r (U ×ˢ (s \ {c₀})) ∧ ∀ x ∈ U ×ˢ s, (monicOfCoeff (c x)).IsRoot (g x) := by
  have hb : c₀ ∈ s → ∀ w ∈ U,
      ∃ t ∈ 𝓝 c₀, BddAbove (norm ∘ (fun z => r (w, z)) '' (t \ {c₀})) := by
    intro hc₀ w hw
    have hcw : ContinuousAt (fun z => c (w, z)) c₀ :=
      ((hc (w, c₀) ⟨hw, hc₀⟩).continuousAt ((hU.prod hs).mem_nhds ⟨hw, hc₀⟩)).comp
        (continuousAt_const.prodMk continuousAt_id)
    have hbound : ∀ᶠ z in 𝓝 c₀, ‖c (w, z)‖ < ‖c (w, c₀)‖ + 1 :=
      hcw.norm.eventually (gt_mem_nhds (by linarith))
    refine ⟨{z | z ∈ s ∧ ‖c (w, z)‖ < ‖c (w, c₀)‖ + 1},
      inter_mem (hs.mem_nhds hc₀) hbound, ‖c (w, c₀)‖ + 2, ?_⟩
    rintro _ ⟨z, ⟨⟨hz, hzc⟩, hne⟩, rfl⟩
    exact (norm_lt_of_isRoot_monicOfCoeff _ (hroot (w, z) ⟨hw, hz, hne⟩)).le.trans
      (by linarith)
  obtain ⟨g, hg, hgr⟩ := TauCeti.exists_analyticOnNhd_prod_eqOn hU hs hr hb
  refine ⟨g, hg, hgr, ?_⟩
  have heval := continuousOn_eval_monicOfCoeff c hc hg.continuousOn
  have hzero : EqOn (fun x => (monicOfCoeff (c x)).eval (g x)) (fun _ => 0)
      (U ×ˢ (s \ {c₀})) := by
    intro x hx
    dsimp only
    rw [hgr hx]
    exact hroot x hx
  exact TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton hs heval continuousOn_const hzero

/-- A complete analytic factorization of a monic family on the punctured domain
extends to a factorization on the full domain, even when roots collide at `z = c₀`.
The indexing retains all factors, including repetitions. -/
theorem exists_analyticOnNhd_monicOfCoeff_eq_prod_X_sub_C
    (c : V × ℂ → Fin d → ℂ) (r : Fin d → V × ℂ → ℂ) (hU : IsOpen U) (hs : IsOpen s)
    (hc : ContinuousOn c (U ×ˢ s))
    (hr : ∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (s \ {c₀})))
    (hfac : ∀ x ∈ U ×ˢ (s \ {c₀}), monicOfCoeff (c x) = ∏ i, (X - C (r i x))) :
    ∃ g : Fin d → V × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (g i) (U ×ˢ s) ∧ EqOn (g i) (r i) (U ×ˢ (s \ {c₀}))) ∧
      ∀ x ∈ U ×ˢ s, monicOfCoeff (c x) = ∏ i, (X - C (g i x)) := by
  have hroot : ∀ i x, x ∈ U ×ˢ (s \ {c₀}) → (monicOfCoeff (c x)).IsRoot (r i x) := by
    intro i x hx
    rw [hfac x hx, isRoot_prod]
    exact ⟨i, Finset.mem_univ _, by simp⟩
  choose g hg hgr _ using fun i =>
    exists_analyticOnNhd_isRoot_monicOfCoeff c hU hs hc (hr i) (hroot i)
  refine ⟨g, fun i => ⟨hg i, hgr i⟩, fun x hx => Polynomial.funext fun z => ?_⟩
  have hleft := continuousOn_eval_monicOfCoeff c hc continuousOn_const (r := fun _ => z)
  have hright : ContinuousOn (fun x => (∏ i, (X - C (g i x))).eval z) (U ×ˢ s) := by
    simp_rw [eval_prod, eval_sub, eval_X, eval_C]
    exact continuousOn_finsetProd _ fun i _ => continuousOn_const.sub (hg i).continuousOn
  refine TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton hs hleft hright (c := c₀) ?_ hx
  intro y hy
  simp only [hfac y hy, eval_prod, eval_sub, eval_X, eval_C, hgr _ hy]

/-- For a polynomial family with continuous coefficients and fixed degree off
`z = c₀`, multiplying an analytic root branch by the degree-`d` coefficient removes
its singularity. That coefficient may vanish on the hyperplane. -/
theorem exists_analyticOnNhd_coeff_mul_of_isRoot
    (F : V × ℂ → ℂ[X]) {r : V × ℂ → ℂ} (hU : IsOpen U) (hs : IsOpen s)
    (hF : ∀ i ≤ d, ContinuousOn (fun x => (F x).coeff i) (U ×ˢ s))
    (hl : AnalyticOnNhd ℂ (fun x => (F x).coeff d) (U ×ˢ (s \ {c₀})))
    (hd : ∀ x ∈ U ×ˢ (s \ {c₀}), (F x).natDegree = d)
    (hne : ∀ x ∈ U ×ˢ (s \ {c₀}), F x ≠ 0)
    (hr : AnalyticOnNhd ℂ r (U ×ˢ (s \ {c₀})))
    (hroot : ∀ x ∈ U ×ˢ (s \ {c₀}), (F x).IsRoot (r x)) :
    ∃ g : V × ℂ → ℂ, AnalyticOnNhd ℂ g (U ×ˢ s) ∧
      EqOn g (fun x => (F x).coeff d * r x) (U ×ˢ (s \ {c₀})) := by
  let c : V × ℂ → Fin d → ℂ := fun x i =>
    (F x).coeff i * (F x).coeff d ^ (d - 1 - i.val)
  have hc : ContinuousOn c (U ×ˢ s) := continuousOn_pi.2 fun i =>
    (hF i (by omega)).mul ((hF d le_rfl).pow _)
  have ha : AnalyticOnNhd ℂ (fun x => (F x).coeff d * r x) (U ×ˢ (s \ {c₀})) :=
    hl.mul hr
  have hscaled : ∀ x ∈ U ×ˢ (s \ {c₀}),
      (monicOfCoeff (c x)).IsRoot ((F x).coeff d * r x) := by
    intro x hx
    have hlc : (F x).coeff d = (F x).leadingCoeff := by rw [← hd x hx, coeff_natDegree]
    have hc' : monicOfCoeff (c x) = (F x).integralNormalization := by
      rw [← monicOfCoeff_coeff (monic_integralNormalization (hne x hx))
        (by simpa using hd x hx)]
      congr 1
      funext i
      simp only [c, integralNormalization_coeff_ne_natDegree (by rw [hd x hx]; exact i.isLt.ne),
        hd x hx, hlc]
    rw [hc', hlc]
    exact integralNormalization_eval₂_eq_zero (RingHom.id ℂ) (hroot x hx) (fun _ h => h)
  obtain ⟨g, hg, hgr, _⟩ := exists_analyticOnNhd_isRoot_monicOfCoeff c hU hs hc ha hscaled
  exact ⟨g, hg, hgr⟩

/-- If the leading coefficient is `(z - c₀)^a` times a nowhere-zero analytic
function, an analytic root branch has a Laurent form with pole order at most `a`:
`(z - c₀)^a * r` extends analytically to the full domain. -/
theorem exists_analyticOnNhd_pow_mul_of_isRoot
    (F : V × ℂ → ℂ[X]) {r u : V × ℂ → ℂ} {a : ℕ} (hU : IsOpen U) (hs : IsOpen s)
    (hF : ∀ i ≤ d, ContinuousOn (fun x => (F x).coeff i) (U ×ˢ s))
    (hd : ∀ x ∈ U ×ˢ (s \ {c₀}), (F x).natDegree = d)
    (hu : AnalyticOnNhd ℂ u (U ×ˢ s)) (hu0 : ∀ x ∈ U ×ˢ s, u x ≠ 0)
    (hlc : ∀ x ∈ U ×ˢ (s \ {c₀}), (F x).coeff d = (x.2 - c₀) ^ a * u x)
    (hr : AnalyticOnNhd ℂ r (U ×ˢ (s \ {c₀})))
    (hroot : ∀ x ∈ U ×ˢ (s \ {c₀}), (F x).IsRoot (r x)) :
    ∃ g : V × ℂ → ℂ, AnalyticOnNhd ℂ g (U ×ˢ s) ∧
      EqOn g (fun x => (x.2 - c₀) ^ a * r x) (U ×ˢ (s \ {c₀})) := by
  have hne : ∀ x ∈ U ×ˢ (s \ {c₀}), F x ≠ 0 := by
    intro x hx hzero
    have hcoef : (F x).coeff d ≠ 0 := by
      rw [hlc x hx]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hx.2.2))
        (hu0 x (prod_mono subset_rfl sdiff_subset hx))
    exact hcoef (by simp [hzero])
  have hl : AnalyticOnNhd ℂ (fun x => (F x).coeff d) (U ×ˢ (s \ {c₀})) := by
    intro x hx
    refine (((analyticAt_snd.sub (analyticAt_const (v := c₀))).pow a).mul (hu x
      (prod_mono subset_rfl sdiff_subset hx))).congr ?_
    filter_upwards [(hU.prod (hs.sdiff isClosed_singleton)).mem_nhds hx] with y hy
    exact (hlc y hy).symm
  obtain ⟨g, hg, hgr⟩ := exists_analyticOnNhd_coeff_mul_of_isRoot F hU hs hF hl hd hne hr hroot
  refine ⟨fun x => g x / u x, hg.div hu hu0, ?_⟩
  intro x hx
  dsimp only
  simp only [hgr hx, hlc x hx]
  field_simp [hu0 x (prod_mono subset_rfl sdiff_subset hx)]

end TauCeti.Polynomial
