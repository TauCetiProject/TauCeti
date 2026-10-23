/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
public import TauCeti.Topology.Covering.PowerSubstitution
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Analytic roots after a power substitution

A monic polynomial family of degree `d` with analytic coefficients and simple roots on
`U × (ball 0 R \ {0})` admits single-valued analytic root functions after the substitution
`(w, t) ↦ (w, t ^ n)`, provided `d ! ∣ n` and the substituted disc fits inside the original disc.
Here `U` is open and simply connected. The root functions are pointwise distinct and give a
complete linear factorization. The degree-zero case gives the empty factorization.

The continuous and analytic splitting theorems give the single-valued root functions needed for
Puiseux factorization with parameters. These functions are defined on the punctured domain only;
extension across the missing hyperplane requires a separate removable-singularity argument.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

noncomputable section

open Function Filter Metric Polynomial Set Topology

namespace TauCeti.Polynomial

/-- A continuous monic family of degree `d`, separable over a punctured disc, splits into `d`
pointwise distinct continuous linear factors after a power substitution of exponent divisible by
`d !`. The parameter space can be any simply connected, locally path connected space. -/
theorem exists_continuousMap_prod_X_sub_C_powerSubstitution
    {U : Type*} [TopologicalSpace U] [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    {d n : ℕ} {R R' : ℝ} {F : U × ↥(ball (0 : ℂ) R \ {0}) → ℂ[X]}
    (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hmonic : ∀ b, (F b).Monic) (hdeg : ∀ b, (F b).natDegree = d)
    (hsep : ∀ b, (F b).Separable) (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n) :
    ∃ r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ), ∀ b,
      Injective (fun i => r i b) ∧
      F (powerSubstitution U hn hR b) = ∏ i, (X - C (r i b)) := by
  classical
  obtain hempty | ⟨⟨a⟩⟩ := isEmpty_or_nonempty (U × ↥(ball (0 : ℂ) R' \ {0}))
  · let := hempty
    exact ⟨fun _ => 0, fun b => isEmptyElim b⟩
  let B := U × ↥(ball (0 : ℂ) R \ {0})
  let Z := {q : B × ℂ // (F q.1).IsRoot q.2}
  let p : Z → B := fun q => q.1.1
  let q := powerSubstitution U hn hR
  -- Lift all points of one fibre, then use their root coordinates as the global labels.
  have hp : IsCoveringMap p := isCoveringMap_fst_isRoot hF hdeg hsep
  let : Finite (p ⁻¹' {q a}) := finite_preimage_fst_isRoot (hmonic (q a)).ne_zero
  have hcard : Nat.card (p ⁻¹' {q a}) = d := natCard_preimage_fst_isRoot (hdeg _) (hsep _)
  obtain ⟨L, hL, hinj⟩ := hp.exists_continuousMap_lifts_powerSubstitution hn hR a
    (by rwa [hcard])
  let := Fintype.ofFinite (p ⁻¹' {q a})
  let e : Fin d ≃ p ⁻¹' {q a} :=
    (Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])).symm
  let r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ) := fun i =>
    ⟨fun b => (L (e i) b).1.2,
      ((continuous_snd : Continuous (Prod.snd : B × ℂ → ℂ)).comp
        (continuous_subtype_val : Continuous (Subtype.val : Z → B × ℂ))).comp (L (e i)).continuous⟩
  have hbase : ∀ i b, p (L (e i) b) = q b := fun i b => congrFun (hL (e i)).2 b
  have hroot : ∀ b i, (F (q b)).IsRoot (r i b) := by
    intro b i
    exact (hbase i b) ▸ (L (e i) b).2
  refine ⟨r, fun b => ?_⟩
  have hrinj : Injective (fun i => r i b) := by
    intro i j hij
    apply e.injective
    apply hinj b
    exact Subtype.ext (Prod.ext ((hbase i b).trans (hbase j b).symm) hij)
  exact ⟨hrinj, (Sym.toMonic_ofFn_eq_of_forall_isRoot (hmonic _) (hdeg _)
    hrinj (hroot b)).symm.trans (Sym.toMonic_ofFn _)⟩

/-- A monic family with analytic coefficients and simple roots on an open simply connected
parameter domain times a punctured disc splits into pointwise distinct analytic linear factors
there after `t ↦ t ^ n`, for any nonzero `n` divisible by `d !`. The functions in the conclusion
are ambient functions, analytic on the punctured product; nothing is asserted at `t = 0`. -/
theorem exists_analyticOnNhd_prod_X_sub_C_powerSubstitution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) [SimplyConnectedSpace U]
    {F : E × ℂ → ℂ[X]} {d n : ℕ} {R R' : ℝ}
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b => (F b).coeff i)
      (U ×ˢ (ball (0 : ℂ) R \ {0})))
    (hmonic : ∀ b ∈ U ×ˢ (ball (0 : ℂ) R \ {0}), (F b).Monic)
    (hdeg : ∀ b ∈ U ×ˢ (ball (0 : ℂ) R \ {0}), (F b).natDegree = d)
    (hsep : ∀ b ∈ U ×ˢ (ball (0 : ℂ) R \ {0}), (F b).Separable)
    (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n) :
    ∃ r : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball (0 : ℂ) R' \ {0}))) ∧
      ∀ b ∈ U ×ˢ (ball (0 : ℂ) R' \ {0}), Injective (fun i => r i b) ∧
        F (b.1, b.2 ^ n) = ∏ i, (X - C (r i b)) := by
  classical
  let D := ball (0 : ℂ) R \ {0}
  let D' := ball (0 : ℂ) R' \ {0}
  let Ω := U ×ˢ D'
  let f : U × D → ℂ[X] := fun b => F (b.1, b.2)
  let q : E × ℂ → E × ℂ := fun b => (b.1, b.2 ^ n)
  have hΩ : IsOpen Ω := hU.prod (isOpen_ball.sdiff isClosed_singleton)
  let : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  -- First split the family continuously on the product of subtypes.
  have hf : ∀ i ≤ d, Continuous fun b => (f b).coeff i := by
    intro i hi
    exact (hF i hi).continuousOn.comp_continuous (by fun_prop) (fun b => ⟨b.1.2, b.2.2⟩)
  obtain ⟨s, hs⟩ := exists_continuousMap_prod_X_sub_C_powerSubstitution hf
    (fun b => hmonic _ ⟨b.1.2, b.2.2⟩) (fun b => hdeg _ ⟨b.1.2, b.2.2⟩)
    (fun b => hsep _ ⟨b.1.2, b.2.2⟩) hn hR hdvd
  -- Ambient representatives let us state analyticity without an analytic structure on a subtype.
  let r : Fin d → E × ℂ → ℂ := fun i =>
    extend Subtype.val (fun b : Ω => s i (Homeomorph.Set.prod U D' b)) (fun _ => 0)
  have hr : ∀ i (b : Ω), r i b = s i (Homeomorph.Set.prod U D' b) := fun i b =>
    Subtype.val_injective.extend_apply _ _ b
  have hrc : ∀ i, ContinuousOn (r i) Ω := by
    intro i
    apply continuousOn_iff_continuous_domRestrict.2
    exact ((s i).continuous.comp (Homeomorph.Set.prod U D').continuous).congr fun b => (hr i b).symm
  have hqmem : ∀ b ∈ Ω, q b ∈ U ×ˢ D := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    simpa only [q, coe_powerSubstitution_apply_snd] using
      (powerSubstitution U hn hR (⟨b.1, hb.1⟩, ⟨b.2, hb.2⟩)).2.2
  have hprod : ∀ b ∈ Ω, Injective (fun i => r i b) ∧
      F (q b) = ∏ i, (X - C (r i b)) := by
    intro b hb
    have hbprod : Homeomorph.Set.prod U D' ⟨b, hb⟩ =
        (⟨b.1, hb.1⟩, ⟨b.2, hb.2⟩) := Homeomorph.Set.prod_apply U D' ⟨b, hb⟩
    have hri : ∀ i, r i b = s i (⟨b.1, hb.1⟩, ⟨b.2, hb.2⟩) := fun i =>
      (hr i ⟨b, hb⟩).trans (congrArg (s i) hbprod)
    simpa only [hri, f, q, powerSubstitution_apply_fst, coe_powerSubstitution_apply_snd] using
      hs (⟨b.1, hb.1⟩, ⟨b.2, hb.2⟩)
  have hroot : ∀ i b, b ∈ Ω → (F (q b)).IsRoot (r i b) := by
    intro i b hb
    rw [(hprod b hb).2, isRoot_prod]
    exact ⟨i, Finset.mem_univ i, by simp⟩
  -- Every continuous branch agrees locally with the analytic implicit root at its simple root.
  refine ⟨r, fun i b hb => ?_, hprod⟩
  have hqa : AnalyticAt ℂ q b := analyticAt_fst.prod (analyticAt_snd.pow n)
  apply analyticAt_of_eventually_isRoot (d := d)
  · intro k hk
    exact (hF k hk _ (hqmem b hb)).comp hqa
  · filter_upwards [hΩ.mem_nhds hb] with x hx
    exact (hdeg _ (hqmem x hx)).le
  · exact (hrc i).continuousAt (hΩ.mem_nhds hb)
  · filter_upwards [hΩ.mem_nhds hb] with x hx
    exact hroot i x hx
  · exact (hsep _ (hqmem b hb)).eval₂_derivative_ne_zero (RingHom.id ℂ) (hroot i b hb)

end TauCeti.Polynomial
