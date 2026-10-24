/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Topology.Instances.Sign

/-!
# Local signs of real analytic functions

A real analytic function has constant sign on each side of a point, sufficiently close to
that point. The same interval can be chosen for a finite family. Thus the three cells cut out
by the center give a simultaneous local sign decomposition, including identically zero germs.

The proof uses Mathlib's `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` and
`IsPreconnected.sign_eq_of_continuousOn`: isolated zeros and connectedness make the sign
constant on each side.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- Near a point of analyticity, a real function has the same sign at any two points on the
same side of the center. The center is its own cell. -/
theorem exists_Ioo_sign_eq_of_analyticAt {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    ∃ a b, x ∈ Ioo a b ∧ ∀ y ∈ Ioo a b, ∀ z ∈ Ioo a b,
      SignType.sign (y - x) = SignType.sign (z - x) →
        SignType.sign (f y) = SignType.sign (f z) := by
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · obtain ⟨a, b, hx, hab⟩ := hzero.exists_Ioo_subset
    exact ⟨a, b, hx, fun y hy z hz _ => by rw [hab hy, hab hz]⟩
  · have hloc := hf.eventually_analyticAt.and (eventually_nhdsWithin_iff.1 hne)
    obtain ⟨a, b, hx, hab⟩ := hloc.exists_Ioo_subset
    have hc : ContinuousOn f (Ioo a b) :=
      fun y hy => (hab hy).1.continuousAt.continuousWithinAt
    have hn : ∀ y ∈ Ioo a b, y ≠ x → f y ≠ 0 :=
      fun y hy hyx => (hab hy).2 hyx
    refine ⟨a, b, hx, fun y hy z hz hsign => ?_⟩
    rcases lt_trichotomy y x with hyx | hyx | hxy
    · have hzx : z < x := sub_neg.1 <| sign_eq_neg_one_iff.1 <|
        hsign.symm.trans (sign_neg (sub_neg.2 hyx))
      exact isPreconnected_Ioo.sign_eq_of_continuousOn
        (hc.mono fun w hw => ⟨hw.1, hw.2.trans hx.2⟩)
        (fun w hw => hn w ⟨hw.1, hw.2.trans hx.2⟩ hw.2.ne)
        ⟨hy.1, hyx⟩ ⟨hz.1, hzx⟩
    · have hzx : z = x := sub_eq_zero.1 <| sign_eq_zero_iff.1 <| by
        simpa [hyx] using hsign.symm
      rw [hyx, hzx]
    · have hxz : x < z := sub_pos.1 <| sign_eq_one_iff.1 <|
        hsign.symm.trans (sign_pos (sub_pos.2 hxy))
      exact isPreconnected_Ioo.sign_eq_of_continuousOn
        (hc.mono fun w hw => ⟨hx.1.trans hw.1, hw.2⟩)
        (fun w hw => hn w ⟨hx.1.trans hw.1, hw.2⟩ hw.1.ne')
        ⟨hxy, hy.2⟩ ⟨hxz, hz.2⟩

/-- A finite family of real analytic germs has a simultaneous constant-sign decomposition
into a left interval, the center point, and a right interval, inside any prescribed
neighborhood of the center. Empty families are allowed. -/
theorem exists_Ioo_sign_eq_of_finite_analyticAt {ι : Type*} [Finite ι]
    {f : ι → ℝ → ℝ} {x : ℝ} (hf : ∀ i, AnalyticAt ℝ (f i) x)
    {U : Set ℝ} (hU : U ∈ 𝓝 x) :
    ∃ a b, x ∈ Ioo a b ∧ Ioo a b ⊆ U ∧
      ∀ i, ∀ y ∈ Ioo a b, ∀ z ∈ Ioo a b,
        SignType.sign (y - x) = SignType.sign (z - x) →
          SignType.sign (f i y) = SignType.sign (f i z) := by
  choose a b hx hab using fun i => exists_Ioo_sign_eq_of_analyticAt (hf i)
  obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (inter_mem hU <|
    (Filter.iInter_mem.2 fun i => Ioo_mem_nhds (hx i).1 (hx i).2))
  refine ⟨l, u, hxu, fun y hy => (hsub hy).1, fun i y hy z hz =>
    hab i y (mem_iInter.1 (hsub hy).2 i) z (mem_iInter.1 (hsub hz).2 i)⟩

end TauCeti
