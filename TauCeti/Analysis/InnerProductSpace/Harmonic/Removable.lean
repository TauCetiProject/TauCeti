/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.PDE.PoissonIntegral.Ball

/-!
# Removable singularities of harmonic functions

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 3`, and let `u` be a
real function harmonic on a punctured neighbourhood `s \ {c}` of a point `c`. If `u` grows more
slowly than the fundamental solution near `c`, that is `u = o(‖x - c‖ ^ (2 - n))` as `x → c`,
then the singularity is removable: `u` has a limit at `c`, and redefining `u` at `c` as this
limit gives a function harmonic on all of `s`
(`TauCeti.harmonicOnNhd_update_limUnder_of_isLittleO`). In particular a function harmonic on a
punctured neighbourhood of `c` that tends to `a` at `c` extends harmonically by the value `a`
(`TauCeti.harmonicOnNhd_update_of_tendsto`). The growth condition is sharp: the fundamental
solution `‖x - c‖ ^ (2 - n)` itself is harmonic off `c` and does not extend.

These are the higher-dimensional analogues of Riemann's removable singularity theorem
`Complex.differentiableOn_update_limUnder_of_isLittleO`. Combined with the Kelvin transform
(`TauCeti.harmonicOnNhd_update_kelvinTransform`) they show that a harmonic function `f` on an
exterior region `‖x‖ > R` for which `‖x‖ ^ (n - 2) f(x)` has a limit at infinity is the Kelvin
transform of a function harmonic on a full ball about the origin; this is how a harmonically flat
end is closed off by adding a point at infinity.

## The argument

Choose `ρ > 0` with `closedBall c ρ ⊆ s`, and let `v` be the harmonic function on `ball c ρ`,
continuous on `closedBall c ρ`, with the boundary values of `u` on `sphere c ρ`
(`TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`). Put
`Φ x = ‖x - c‖ ^ (2 - n) - ρ ^ (2 - n)`, which is harmonic off `c`, vanishes on `sphere c ρ` and
dominates `‖x - c‖ ^ (2 - n) / 2` near `c`. Since `v` is bounded near `c`, the growth hypothesis
gives, for each `ε > 0`, a radius `δ` such that `|u - v| ≤ ε Φ` on `sphere c δ`. The comparison
principle on the annulus `δ < ‖x - c‖ < ρ` then gives `|u - v| ≤ ε Φ` throughout the annulus, and
letting `ε → 0` shows `u = v` on the punctured ball.

## Main declarations

* `TauCeti.harmonicOnNhd_update_limUnder_of_isLittleO`: a harmonic function on a punctured
  neighbourhood that is `o(‖x - c‖ ^ (2 - n))` at the puncture extends harmonically.
* `TauCeti.harmonicOnNhd_update_of_tendsto`: a harmonic function on a punctured neighbourhood with
  a limit at the puncture extends harmonically by that limit.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137, 2001,
  Chapter 2 (bounded isolated singularities) and Chapter 10 (isolated singularities).
-/

public section

namespace TauCeti

open Asymptotics Filter InnerProductSpace Metric Module Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- In dimension at least three the exponent `2 - n` of the fundamental solution is negative. -/
private theorem two_sub_finrank_neg (hn : 3 ≤ finrank ℝ E) : (2 - finrank ℝ E : ℝ) < 0 := by
  have : (3 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hn
  linarith

omit [FiniteDimensional ℝ E] in
/-- In dimension at least three, constants are `o(‖x - c‖ ^ (2 - n))` at `c`. -/
private theorem isLittleO_one_norm_sub_rpow (hn : 3 ≤ finrank ℝ E) (c : E) :
    (fun _ ↦ (1 : ℝ)) =o[𝓝[≠] c] fun y : E ↦ ‖y - c‖ ^ (2 - finrank ℝ E : ℝ) :=
  (isLittleO_one_left_iff ℝ).2 (tendsto_norm_atTop_atTop.comp
    (tendsto_norm_sub_rpow_nhdsNE_atTop (two_sub_finrank_neg hn) c))

/-- The comparison step of the removable singularity theorem. Let `v` be harmonic on `ball c ρ`,
continuous on `closedBall c ρ`, with the boundary values of `u` on `sphere c ρ`, and let
`u - v = o(‖x - c‖ ^ (2 - n))` at `c`. Then for every `ε > 0` the difference `|u - v|` is bounded
on the punctured ball by `ε (‖x - c‖ ^ (2 - n) - ρ ^ (2 - n))`. -/
private theorem abs_sub_le_mul_of_isLittleO (hn : 3 ≤ finrank ℝ E) {u v : E → ℝ} {c : E}
    {ρ : ℝ} (hρ : 0 < ρ) (hu : HarmonicOnNhd u (closedBall c ρ \ {c}))
    (hv : HarmonicOnNhd v (ball c ρ)) (hvc : ContinuousOn v (closedBall c ρ))
    (hvu : EqOn v u (sphere c ρ))
    (huv : (fun y ↦ u y - v y) =o[𝓝[≠] c] fun y ↦ ‖y - c‖ ^ (2 - finrank ℝ E : ℝ))
    {ε : ℝ} (hε : 0 < ε) {x : E} (hx : x ∈ ball c ρ \ {c}) :
    |u x - v x| ≤ ε * (‖x - c‖ ^ (2 - finrank ℝ E : ℝ) - ρ ^ (2 - finrank ℝ E : ℝ)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  borelize E
  set p : ℝ := 2 - finrank ℝ E
  have hxc : 0 < dist x c := dist_pos.2 hx.2
  -- The comparison function `ε Φ`, with `Φ = ‖x - c‖ ^ p - ρ ^ p` harmonic off `c`.
  set Φ : E → ℝ := fun y ↦ ‖y - c‖ ^ p - ρ ^ p
  have hΦ : HarmonicOnNhd (fun y ↦ ε * Φ y) {c}ᶜ := fun y hy ↦ by
    convert ((harmonicAt_norm_sub_rpow_two_sub_finrank hy).sub
      (harmonicAt_const (ρ ^ p))).const_smul (c := ε) using 1
  -- Near `c`, `|u - v| ≤ ε Φ`; fix such a radius `δ < dist x c`.
  have hg := tendsto_norm_sub_rpow_nhdsNE_atTop (two_sub_finrank_neg hn) c
  have hnear : ∀ᶠ y in 𝓝[≠] c, |u y - v y| ≤ ε * Φ y := by
    filter_upwards [huv.def (half_pos hε), hg.eventually_ge_atTop (2 * ρ ^ p)] with y hy hy'
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by linarith [Real.rpow_nonneg hρ.le p])] at hy
    simp only [Φ]
    nlinarith
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hnear)
  set δ := min δ₀ (dist x c) / 2
  have hδ : 0 < δ := half_pos (lt_min hδ₀ hxc)
  have hδsph : ∀ y ∈ sphere c δ, |u y - v y| ≤ ε * Φ y := fun y hy ↦ by
    have hyc : dist y c = δ := mem_sphere.1 hy
    refine hδ₀' ?_ (fun h ↦ hδ.ne' (by rwa [h, dist_self, eq_comm] at hyc))
    rw [hyc]
    exact (half_lt_self (lt_min hδ₀ hxc)).trans_le (min_le_left _ _)
  -- Compare `±(u - v)` with `ε Φ` on the annulus `δ < ‖y - c‖ < ρ`.
  have hann : ball c ρ \ closedBall c δ ⊆ ball c ρ \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_closedBall_self hδ.le))
  have hann' : closedBall c ρ \ ball c δ ⊆ closedBall c ρ \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_ball_self hδ))
  have huvH : HarmonicOnNhd (fun y ↦ u y - v y) (ball c ρ \ closedBall c δ) :=
    ((hu.mono (sdiff_subset_sdiff_left ball_subset_closedBall)).sub (hv.mono sdiff_subset)).mono
      hann
  have huvC : ContinuousOn (fun y ↦ u y - v y) (closedBall c ρ \ ball c δ) :=
    (hu.continuousOn.mono hann').sub (hvc.mono sdiff_subset)
  have hΦH := hΦ.mono (hann.trans fun y hy ↦ hy.2)
  have hΦC := hΦ.continuousOn.mono (hann'.trans fun y hy ↦ hy.2)
  have hxA : x ∈ ball c ρ \ closedBall c δ :=
    ⟨hx.1, by simpa using (half_lt_self (lt_min hδ₀ hxc)).trans_le (min_le_right _ _)⟩
  have hρsph : ∀ y ∈ sphere c ρ, u y - v y = 0 ∧ Φ y = 0 := fun y hy ↦
    ⟨sub_eq_zero.2 (hvu hy).symm, by simp [Φ, ← dist_eq_norm, mem_sphere.1 hy]⟩
  have h₁ := huvH.subharmonicOn.le_of_le_sphere_of_le_sphere huvC hΦH hΦC
    (fun y hy ↦ by simp [(hρsph y hy).1, (hρsph y hy).2])
    (fun y hy ↦ (le_abs_self _).trans (hδsph y hy)) x hxA
  have h₂ := huvH.neg.subharmonicOn.le_of_le_sphere_of_le_sphere huvC.neg hΦH hΦC
    (fun y hy ↦ by simp [(hρsph y hy).1, (hρsph y hy).2])
    (fun y hy ↦ (neg_le_abs _).trans (hδsph y hy)) x hxA
  simp only [Pi.neg_apply] at h₂
  exact abs_le.2 ⟨by linarith, h₁⟩

/-- **The removable singularity theorem on a closed ball.** In dimension at least three, a
function harmonic near `closedBall c ρ` minus its centre and `o(‖x - c‖ ^ (2 - n))` at `c` agrees
on the punctured open ball with a function harmonic on the whole open ball. -/
private theorem exists_harmonicOnNhd_ball_eqOn_of_isLittleO (hn : 3 ≤ finrank ℝ E) {u : E → ℝ}
    {c : E} {ρ : ℝ} (hρ : 0 < ρ) (hu : HarmonicOnNhd u (closedBall c ρ \ {c}))
    (ho : u =o[𝓝[≠] c] fun x ↦ ‖x - c‖ ^ (2 - finrank ℝ E : ℝ)) :
    ∃ v : E → ℝ, HarmonicOnNhd v (ball c ρ) ∧ EqOn v u (ball c ρ \ {c}) := by
  set p : ℝ := 2 - finrank ℝ E
  have hp : p ≤ 0 := (two_sub_finrank_neg hn).le
  have hsph : sphere c ρ ⊆ closedBall c ρ \ {c} := fun y hy ↦
    ⟨sphere_subset_closedBall hy, fun h ↦ by simp_all⟩
  obtain ⟨v, hv, hvc, hvu⟩ :=
    exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere (hu.continuousOn.mono hsph)
  refine ⟨v, hv, fun x hx ↦ ?_⟩
  -- `u - v` is `o(‖x - c‖ ^ p)` at `c`, because `v` is bounded there and `‖x - c‖ ^ p → ∞`.
  have hvO : v =O[𝓝[≠] c] (fun _ ↦ (1 : ℝ)) :=
    ((hvc.continuousAt (closedBall_mem_nhds c hρ)).tendsto.mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  have huv : (fun y ↦ u y - v y) =o[𝓝[≠] c] fun y ↦ ‖y - c‖ ^ p :=
    ho.sub (hvO.trans_isLittleO (isLittleO_one_norm_sub_rpow hn c))
  -- `|u x - v x| ≤ ε Φ x` for every `ε > 0`, with `Φ x = ‖x - c‖ ^ p - ρ ^ p ≥ 0`.
  set Φx := ‖x - c‖ ^ p - ρ ^ p
  have hΦx : 0 ≤ Φx :=
    sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos (by rw [← dist_eq_norm, dist_pos]; exact hx.2)
      (by rw [← dist_eq_norm]; exact hx.1.le) hp)
  have key : |u x - v x| ≤ 0 := le_of_forall_pos_le_add fun ε hε ↦ by
    calc |u x - v x| ≤ ε / (Φx + 1) * Φx :=
          abs_sub_le_mul_of_isLittleO hn hρ hu hv hvc hvu huv (div_pos hε (by linarith)) hx
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      _ = 0 + ε := (zero_add ε).symm
  exact (sub_eq_zero.1 (abs_nonpos_iff.1 key)).symm

/-- **Removable singularities of harmonic functions.** In dimension at least three, let `u` be
harmonic on `s \ {c}` for a neighbourhood `s` of `c`, with `u = o(‖x - c‖ ^ (2 - n))` as `x → c`.
Then `u` has a limit at `c`, and redefining `u` at `c` as this limit gives a function harmonic on
`s`. -/
theorem harmonicOnNhd_update_limUnder_of_isLittleO [DecidableEq E] (hn : 3 ≤ finrank ℝ E)
    {u : E → ℝ} {s : Set E} {c : E} (hs : s ∈ 𝓝 c) (hu : HarmonicOnNhd u (s \ {c}))
    (ho : u =o[𝓝[≠] c] fun x ↦ ‖x - c‖ ^ (2 - finrank ℝ E : ℝ)) :
    HarmonicOnNhd (Function.update u c (limUnder (𝓝[≠] c) u)) s := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨ρ, hρ, hρs⟩ := nhds_basis_closedBall.mem_iff.1 hs
  obtain ⟨v, hv, hvu⟩ :=
    exists_harmonicOnNhd_ball_eqOn_of_isLittleO hn hρ (hu.mono (sdiff_subset_sdiff_left hρs)) ho
  -- The harmonic function `v` is continuous at `c`, so its value there is the limit of `u`.
  have hev : v =ᶠ[𝓝[≠] c] u := by
    filter_upwards [inter_mem_nhdsWithin {c}ᶜ (ball_mem_nhds c hρ)] with y hy
    exact hvu ⟨hy.2, hy.1⟩
  have hlim : limUnder (𝓝[≠] c) u = v c :=
    (((hv c (mem_ball_self hρ)).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      hev).limUnder_eq
  intro x hx
  rcases eq_or_ne x c with rfl | hxc
  · refine (harmonicAt_congr_nhds ?_).2 (hv x (mem_ball_self hρ))
    filter_upwards [ball_mem_nhds x hρ] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · simp [hlim]
    · rw [Function.update_of_ne hyx]
      exact (hvu ⟨hy, hyx⟩).symm
  · refine (harmonicAt_congr_nhds ?_).2 (hu x ⟨hx, hxc⟩)
    filter_upwards [eventually_ne_nhds hxc] with y hy
    exact Function.update_of_ne hy _ _

/-- **Bounded singularities of harmonic functions are removable.** In dimension at least three,
a function harmonic on `s \ {c}`, for a neighbourhood `s` of `c`, that tends to `a` at `c` is
harmonic on `s` once its value at `c` is set to `a`. -/
theorem harmonicOnNhd_update_of_tendsto [DecidableEq E] (hn : 3 ≤ finrank ℝ E) {u : E → ℝ}
    {s : Set E} {c : E} {a : ℝ} (hs : s ∈ 𝓝 c) (hu : HarmonicOnNhd u (s \ {c}))
    (ha : Tendsto u (𝓝[≠] c) (𝓝 a)) :
    HarmonicOnNhd (Function.update u c a) s := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have ho : u =o[𝓝[≠] c] fun x ↦ ‖x - c‖ ^ (2 - finrank ℝ E : ℝ) :=
    (ha.isBigO_one ℝ).trans_isLittleO (isLittleO_one_norm_sub_rpow hn c)
  simpa only [ha.limUnder_eq] using harmonicOnNhd_update_limUnder_of_isLittleO hn hs hu ho

end TauCeti
