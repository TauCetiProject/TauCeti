/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.Decomposition
public import TauCeti.Analysis.Contour.Crossing.ExitWindow
public import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.Crossing.Windows

/-!
# The winding decomposition of an immersed contour

This file completes Hungerbühler--Wasem Proposition 2.2.  A closed piecewise-`C¹` immersion
meets a point `s` at finitely many parameter values.  Provided the basepoint avoids `s`, we choose
one common parameter radius around those crossings and then one common spatial exit radius.  The
corresponding first-exit windows are pairwise disjoint.  Replacing each window by its circular cap
produces a closed piecewise-`C¹` curve avoiding `s`, and

`n_s(γ) = n_s(excised γ) + ∑ₜ crossingAngle γ t / (2π)`.

The construction combines the finite-window accounting theorem in `Crossing.Decomposition` with
the canonical equal-radius windows and their local principal-value calculation from
`Crossing.ExitWindow`.  The point-avoiding curve in the conclusion is the curve denoted
`\tilde{Λ}` by Hungerbühler and Wasem.

## Main results

* `TauCeti.Contour.IsPwC1ImmersionOn.exists_crossingDecomposition` -- HW Proposition 2.2,
  including an explicit closed, piecewise-`C¹`, point-avoiding excised curve.
* `TauCeti.Contour.IsPwC1ImmersionOn.exists_avoiding_curve_windingNumber_eq` -- curve existence form
  of Hungerbühler--Wasem Proposition 2.2.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.2.

## Provenance

Independently reconstructed from Tau Ceti's exit-window and finite-excision APIs.  No external
formalization is vendored.  The `ContourIntegration` roadmap designates the AINTLIB
`LeanModularForms` development (Apache-2.0) as the existing source for this area; its
`ForMathlib/HungerbuhlerWasem/Crossing.lean` was consulted at revision `340875a` for the
mathematical decomposition statement.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- **Choosing the crossing windows.** For a finite set `T` of the crossings of an immersion `γ`
with `s`, there are a common parameter radius `δ`, a common spatial exit radius `ε` and one-sided
derivative limits `L_R t`, `L_L t` at each crossing `t ∈ T`, such that the windows of
`TauCeti.Contour.exitCapWindows` lie inside `(a, b)`, are separated, contain their crossings and
have the Cauchy principal value of `(z - s)⁻¹` computed by `TauCeti.Contour.exitCapWindow`. -/
private theorem exists_exitCapWindows_data {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b) (hclosed : γ a = γ b) (hbase : γ a ≠ s)
    {T : Finset ℝ} (hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s) :
    ∃ (δ ε : ℝ) (L_R L_L : ℝ → ℂ), 0 < δ ∧ 0 < ε ∧
      (∀ t ∈ T, a + δ < t ∧ t < b - δ) ∧ (∀ t ∈ T, ∀ t' ∈ T, t' ≠ t → 2 * δ < |t - t'|) ∧
      (∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ))) ∧
      (∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ ∧ ε ≤ ‖γ (t + δ) - s‖) ∧
      (∀ t ∈ T, t ∈ Ioo (exitCapWindow γ s t δ ε (L_R t) (L_L t)).lower
        (exitCapWindow γ s t δ ε (L_R t) (L_L t)).upper) ∧
      (∀ t ∈ T, L_R t ≠ 0 ∧ L_L t ≠ 0 ∧ Tendsto (deriv γ) (𝓝[>] t) (𝓝 (L_R t)) ∧
        Tendsto (deriv γ) (𝓝[<] t) (𝓝 (L_L t))) ∧
      (∀ t ∈ T, ∀ W, W = exitCapWindow γ s t δ ε (L_R t) (L_L t) →
        HasCauchyPVAt γ W.lower W.upper (fun z ↦ (z - s)⁻¹) s
          (((((-L_L t) / (γ W.lower - s)).arg + ((γ W.upper - s) / L_R t).arg : ℝ) : ℂ) *
            Complex.I)) := by
  have hcomplete : ∀ t ∈ Icc a b, γ t = s → t ∈ T :=
    fun t ht heq => hT_mem.mpr ⟨ht, heq⟩
  have hinterior : ∀ t ∈ T, t ∈ Ioo a b := by
    intro t ht
    have ht' := hT_mem.mp ht
    refine ⟨lt_of_le_of_ne ht'.1.1 ?_, lt_of_le_of_ne ht'.1.2 ?_⟩
    · exact fun hta => hbase (hta ▸ ht'.2)
    · exact fun htb => hbase (hclosed.trans (htb ▸ ht'.2))
  choose! R hR_pos L_R L_L hL_R hL_L h_R h_L hspec using
    fun t (ht : t ∈ T) =>
      exists_radius_hasCauchyPVAt_exitCapWindow h_imm (hinterior t ht) (hT_mem.mp ht).2
  obtain ⟨δ, hδ, hendpoints, hseparated, hδR⟩ :=
    exists_common_window_radius_le hinterior R hR_pos
  have hunique : ∀ t₀ ∈ T, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), γ t = s → t = t₀ := by
    intro t₀ ht₀ t ht heq
    exact eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (hendpoints t₀ ht₀)
      (hseparated t₀ ht₀) hcomplete ht heq
  have hendpoint_ne : ∀ t ∈ T, γ (t - δ) ≠ s ∧ γ (t + δ) ≠ s := by
    intro t ht
    constructor
    · intro heq
      have := hunique t ht (t - δ) (by constructor <;> linarith) heq
      linarith
    · intro heq
      have := hunique t ht (t + δ) (by constructor <;> linarith) heq
      linarith
  have hγ_window : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ)) := by
    intro t ht
    exact h_imm.continuousOn.mono (by
      rw [uIcc_of_le hab.le]
      exact Icc_subset_Icc (by linarith [(hendpoints t ht).1])
        (by linarith [(hendpoints t ht).2]))
  obtain ⟨ε, hε, hεends, hcrossing_inside⟩ :=
    exists_common_exitCapWindows_radius (L_R := L_R) (L_L := L_L) hδ hγ_window
      (fun t ht => (hT_mem.mp ht).2) hendpoint_ne
  exact ⟨δ, ε, L_R, L_L, hδ, hε, hendpoints, hseparated, hγ_window, hεends, hcrossing_inside,
    fun t ht => ⟨hL_R t ht, hL_L t ht, h_R t ht, h_L t ht⟩, fun t ht W hW =>
      hW ▸ hspec t ht δ hδ (hδR t ht) (by linarith [(hendpoints t ht).1])
        (by linarith [(hendpoints t ht).2]) (hunique t ht) ε hε (hεends t ht).1
        (hεends t ht).2⟩

/-- **Geometry of the exit windows.** The windows of `TauCeti.Contour.exitCapWindows` built from
radii `δ`, `ε` as in `exists_exitCapWindows_data` are ordered, lie inside `(a, b)` with
nonempty interior, have nonzero radius, and cover every parameter at which `γ` meets `s`. -/
private theorem exitCapWindows_geometry {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} (hδ : 0 < δ) (hε : 0 < ε) (hat : ∀ t ∈ T, γ t = s)
    (hcomplete : ∀ t ∈ Icc a b, γ t = s → t ∈ T) (hend : ∀ t ∈ T, a + δ < t ∧ t < b - δ)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t' ≠ t → 2 * δ < |t - t'|)
    (hγ_window : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ)))
    (hεends : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ ∧ ε ≤ ‖γ (t + δ) - s‖)
    (hcrossing_inside : ∀ t ∈ T, t ∈ Ioo (exitCapWindow γ s t δ ε (L_R t) (L_L t)).lower
      (exitCapWindow γ s t δ ε (L_R t) (L_L t)).upper) :
    (exitCapWindows γ s T δ ε L_R L_L).Pairwise (fun W V => W.upper < V.lower) ∧
    (∀ W ∈ exitCapWindows γ s T δ ε L_R L_L, a < W.lower ∧ W.lower < W.upper ∧ W.upper < b) ∧
    (∀ W ∈ exitCapWindows γ s T δ ε L_R L_L, W.radius ≠ 0) ∧
    (∀ t ∈ Icc a b, (∀ W ∈ exitCapWindows γ s T δ ε L_R L_L, t ∉ Ioo W.lower W.upper) →
      γ t ≠ s) := by
  have hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ := fun t ht => (hεends t ht).1
  have hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖ := fun t ht => (hεends t ht).2
  refine ⟨pairwise_upper_lt_lower_exitCapWindows hδ.le hεL hεR
      (fun t ht t' ht' hne => hsep t ht t' ht' hne.symm), fun W hW => ?_, fun W hW => ?_,
    fun t ht houtside heq => ?_⟩
  · exact ⟨lt_lower_of_mem_exitCapWindows hδ.le
        (fun t ht => by linarith [(hend t ht).1]) hεL hW,
      lower_lt_upper_of_mem_exitCapWindows hδ hε hγ_window hat hεL hεR hW,
      upper_lt_of_mem_exitCapWindows hδ.le
        (fun t ht => by linarith [(hend t ht).2]) hεR hW⟩
  · rw [radius_eq_of_mem_exitCapWindows hW]
    exact hε.ne'
  · have htT := hcomplete t ht heq
    exact houtside _ (mem_exitCapWindows_iff.mpr ⟨t, htT, rfl⟩) (hcrossing_inside t htT)

/-- **Local contributions of the exit windows.** The Cauchy principal values over the windows of
`TauCeti.Contour.exitCapWindows` exist, and their local contributions sum to the crossing angles
divided by `2π`. -/
private theorem exitCapWindows_localContribution_sum {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    {T : Finset ℝ} {δ ε : ℝ} {L_R L_L : ℝ → ℂ} (hδ : 0 < δ) (hε : 0 < ε)
    (hat : ∀ t ∈ T, γ t = s) (hγ_window : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ)))
    (hεends : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ ∧ ε ≤ ‖γ (t + δ) - s‖)
    (hlim : ∀ t ∈ T, L_R t ≠ 0 ∧ L_L t ≠ 0 ∧ Tendsto (deriv γ) (𝓝[>] t) (𝓝 (L_R t)) ∧
      Tendsto (deriv γ) (𝓝[<] t) (𝓝 (L_L t)))
    (hpv : ∀ t ∈ T, ∀ W, W = exitCapWindow γ s t δ ε (L_R t) (L_L t) →
      HasCauchyPVAt γ W.lower W.upper (fun z ↦ (z - s)⁻¹) s
        (((((-L_L t) / (γ W.lower - s)).arg + ((γ W.upper - s) / L_R t).arg : ℝ) : ℂ) *
          Complex.I))
    (hinside : ∀ W ∈ exitCapWindows γ s T δ ε L_R L_L,
      a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (hradius : ∀ W ∈ exitCapWindows γ s T δ ε L_R L_L, W.radius ≠ 0) :
    (∀ W ∈ exitCapWindows γ s T δ ε L_R L_L,
      CauchyPVExistsAt γ W.lower W.upper (fun z => (z - s)⁻¹) s) ∧
    ((exitCapWindows γ s T δ ε L_R L_L).map fun W => W.localContribution γ s).sum =
      ((∑ t ∈ T, crossingAngle γ t : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  refine ⟨fun W hW => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
    exact CauchyPVExistsAt.intro (hpv t ht _ rfl)
  · have hlocal : ∀ t ∈ T,
        (exitCapWindow γ s t δ ε (L_R t) (L_L t)).localContribution γ s =
          (crossingAngle γ t : ℂ) / (2 * (Real.pi : ℂ)) := by
      intro t ht
      have hW : exitCapWindow γ s t δ ε (L_R t) (L_L t) ∈ exitCapWindows γ s T δ ε L_R L_L :=
        mem_exitCapWindows_iff.mpr ⟨t, ht, rfl⟩
      rw [CircularCapWindow.localContribution_eq_sub_windingNumber_cap _ γ s (hradius _ hW)
        (hinside _ hW).2.1.ne]
      exact windingNumber_sub_cap_exitCapWindow_eq_crossingAngle_div_two_pi hδ hε
        (hat t ht) (hγ_window t ht) (hεends t ht).1 (hεends t ht).2 (hlim t ht).1
        (hlim t ht).2.1 (hlim t ht).2.2.1 (hlim t ht).2.2.2 (hpv t ht _ rfl)
    rw [sum_exitCapWindows, Finset.sum_congr rfl hlocal, ← Finset.sum_div]
    push_cast
    rfl

/-- **Hungerbühler--Wasem Proposition 2.2 (winding decomposition).**  Let `γ` be a closed
piecewise-`C¹` immersion on `[a, b]`, with a basepoint away from `s`.  There is a finite ordered
family of disjoint crossing windows whose circular-cap excision is again piecewise `C¹`, is
closed, and avoids `s`.  Its winding number accounts for the integer part of the original winding
number; each crossing contributes its geometric angle divided by `2π`.

The sum is indexed by the canonical finite crossing set supplied by
`IsPwC1ImmersionOn.finite_crossings`. -/
theorem IsPwC1ImmersionOn.exists_crossingDecomposition
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b)
    (hclosed : γ a = γ b) (hbase : γ a ≠ s) :
    ∃ windows : List CircularCapWindow,
      windows.Pairwise (fun W V => W.upper < V.lower) ∧
      IsPiecewiseC1On (exciseCrossings γ s windows) a b ∧
      exciseCrossings γ s windows a = exciseCrossings γ s windows b ∧
      (∀ t ∈ Icc a b, exciseCrossings γ s windows t ≠ s) ∧
      windingNumber γ a b s = windingNumber (exciseCrossings γ s windows) a b s +
        ((∑ t ∈ (h_imm.finite_crossings (z₀ := s)).toFinset,
          crossingAngle γ t : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  classical
  set T : Finset ℝ := (h_imm.finite_crossings (z₀ := s)).toFinset with hT_def
  have hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := fun {_} => by
    rw [hT_def, h_imm.mem_toFinset_finite_crossings_of_le hab.le]
  have hcomplete : ∀ t ∈ Icc a b, γ t = s → t ∈ T :=
    fun t ht heq => hT_mem.mpr ⟨ht, heq⟩
  have hat : ∀ t ∈ T, γ t = s := fun t ht => (hT_mem.mp ht).2
  obtain ⟨δ, ε, L_R, L_L, hδ, hε, hend, hsep, hγ_window, hεends, hcrossing_inside, hlim, hpv⟩ :=
    exists_exitCapWindows_data h_imm hab hclosed hbase hT_mem
  obtain ⟨hordered, hinside, hradius, havoid⟩ := exitCapWindows_geometry hδ hε hat hcomplete hend
    hsep hγ_window hεends hcrossing_inside
  obtain ⟨hpv_exists, hlocal_sum⟩ := exitCapWindows_localContribution_sum hδ hε hat hγ_window
    hεends hlim hpv hinside hradius
  set windows := exitCapWindows γ s T δ ε L_R L_L with hwindows
  have hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ := fun t ht => (hεends t ht).1
  have hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖ := fun t ht => (hεends t ht).2
  have hregular : IsPiecewiseC1On (exciseCrossings γ s windows) a b :=
    h_imm.isPiecewiseC1On.exciseCrossings
      (pairwise_disjoint_interval_of_pairwise_upper_lt_lower hordered) hinside
      (fun W hW => eq_circleMap_startAngle_of_mem_exitCapWindows hδ.le hε.le
        (fun t ht => (hγ_window t ht).mono (Icc_subset_Icc le_rfl (by linarith)))
        hat hεL hW)
      (fun W hW => eq_circleMap_endAngle_of_mem_exitCapWindows hδ.le hε.le hγ_window
        hat hεL hεR (fun t ht => (hlim t ht).1) (fun t ht => (hlim t ht).2.1)
        (fun t ht => (hlim t ht).2.2.1) (fun t ht => (hlim t ht).2.2.2) hW)
  have hclosed_excised :
      exciseCrossings γ s windows a = exciseCrossings γ s windows b :=
    exciseCrossings_closed hclosed fun W hW => ⟨
      fun haW => by rw [CircularCapWindow.mem_interval_iff] at haW; linarith [(hinside W hW).1],
      fun hbW => by rw [CircularCapWindow.mem_interval_iff] at hbW; linarith [(hinside W hW).2.2]⟩
  have havoids_excised : ∀ t ∈ Icc a b, exciseCrossings γ s windows t ≠ s :=
    exciseCrossings_ne_center
      (fun W hW _ => hradius W hW)
      (fun t ht heq => by
        let W := exitCapWindow γ s t δ ε (L_R t) (L_L t)
        have htW : t ∈ W.interval := by
          rw [CircularCapWindow.mem_interval_iff]
          exact Ioo_subset_Icc_self (hcrossing_inside t (hcomplete t ht heq))
        exact ⟨W, mem_exitCapWindows_iff.mpr ⟨t, hcomplete t ht heq, rfl⟩, htW⟩)
  refine ⟨windows, hordered, hregular, hclosed_excised, havoids_excised, ?_⟩
  rw [hT_def]
  exact (windingNumber_eq_exciseCrossings_add_sum h_imm.isPiecewiseC1On hordered hinside
    hradius havoid hpv_exists).trans
      (congrArg (windingNumber (exciseCrossings γ s windows) a b s + ·) hlocal_sum)

/-- **Hungerbühler--Wasem Proposition 2.2 (winding decomposition, curve existence form).**
For a closed piecewise-`C¹` immersion `γ` based away from `s`, there exists an avoiding closed
piecewise-`C¹` curve `γ₀` whose winding number differs from `γ`'s by the canonical finite sum of
crossing angles divided by `2π`. -/
theorem IsPwC1ImmersionOn.exists_avoiding_curve_windingNumber_eq
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b)
    (hclosed : γ a = γ b) (hbase : γ a ≠ s) :
    ∃ γ₀ : ℝ → ℂ,
      IsPiecewiseC1On γ₀ a b ∧
      γ₀ a = γ₀ b ∧
      (∀ t ∈ Icc a b, γ₀ t ≠ s) ∧
      windingNumber γ a b s = windingNumber γ₀ a b s +
        ((∑ t ∈ (h_imm.finite_crossings (z₀ := s)).toFinset,
          crossingAngle γ t : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  obtain ⟨windows, -, hregular, hclosed_excised, havoids_excised, hwinding⟩ :=
    h_imm.exists_crossingDecomposition hab hclosed hbase
  exact ⟨exciseCrossings γ s windows, hregular, hclosed_excised, havoids_excised, hwinding⟩

end TauCeti.Contour

end
