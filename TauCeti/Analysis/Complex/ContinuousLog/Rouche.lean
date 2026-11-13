/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.Complex.ContinuousLog.Circle
public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import TauCeti.Topology.Sym.Metric
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Data.Multiset.Filter
import TauCeti.Data.Multiset.Rel
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Rouché's and Hurwitz's theorems for functions with local power factorizations

Let `f : ℂ → ℂ` have finitely many zeros, with multiplicities given by a multiset `D`: near every
point `z` it factors as `f w = (w - z) ^ (count z D) * v w` with `v` continuous at `z` and nonzero
there (`TauCeti.IsZeroMultiplicity f (D.count ·)`). No holomorphy is assumed; this is the local
form that the similarity principle gives for solutions of `∂bar f = a f`, such as the section of a
plane vortex. This file proves the two classical consequences of the argument principle for such
functions.

* **Rouché's theorem.** If `g` is another such function, with zero divisor `E`, and
  `‖f w - g w‖ < ‖f w‖ + ‖g w‖` on the circle of radius `r` about `c`, then `f` and `g` have the
  same number of zeros, counted with multiplicity, in the open disc bounded by that circle
  (`TauCeti.IsZeroMultiplicity.countP_dist_lt_eq_of_norm_sub_lt_add`). The classical hypothesis
  `‖g w - f w‖ < ‖f w‖` implies this one
  (`TauCeti.IsZeroMultiplicity.countP_dist_lt_eq_of_norm_sub_lt`).
* **Hurwitz's theorem.** If a family `g i` of such functions, with zero divisors `E i` of the same
  cardinality as `D`, converges to `f` locally uniformly, then the divisors `E i` converge to `D`:
  for every `ε > 0` their points are eventually matched one-to-one with those of `D`, matched points
  being at distance less than `ε`
  (`TauCeti.IsZeroMultiplicity.eventually_rel_dist_lt_of_tendstoLocallyUniformly`). For divisors
  of degree `m`, read as points of the symmetric power `Sym ℂ m`, this is convergence in its
  quotient topology (`TauCeti.IsZeroMultiplicity.tendsto_of_tendstoLocallyUniformly`).

For the section of a framed degree-`m` plane vortex the divisor has `m` points
(`TauCeti.IsZeroMultiplicity.card_eq_of_tendsto_mul_inv_pow`), so Hurwitz's theorem says that the
zero divisor in `Sym ℂ m` depends continuously on the section, for the topology of locally uniform
convergence.

## Proof

The zeros of `f` are finite, so `f w = exp (L w) * ∏ z ∈ s, (w - z) ^ n z` for a continuous `L`
(`TauCeti.IsZeroMultiplicity.exists_continuous_eq_exp_mul_prod_pow`). On a circle about `c`
avoiding `s`, each factor `w - z` with `z` outside the circle has a continuous logarithm, and each
factor with `z` inside is `w - c` times a function with a continuous logarithm; so the product is
`(w - c) ^ N` times a function with a continuous logarithm, where `N` counts the zeros inside
(`TauCeti.hasContinuousLogOn_prod_pow_div_pow_sphere`). Under the hypothesis of Rouché's theorem,
`g / f` takes values in the slit plane (`TauCeti.div_mem_slitPlane_of_norm_sub_lt_add`), hence
has the principal logarithm, so
`(w - c) ^ (N' - N)` has a continuous logarithm on the circle. That forces `N' = N`
(`TauCeti.not_hasContinuousLogOn_zpow_sub_sphere`).

For Hurwitz's theorem, choose `ρ ≤ ε` below half the distance between distinct points of `D`
(`TauCeti.exists_pos_closedBall_subset_and_lt_dist`).
On the circles of radius `ρ` about the points of `D`, `|f|` is bounded below by some `δ > 0`, and
locally uniform convergence makes `‖g i - f‖ < δ` there eventually. Rouché's theorem then puts
exactly `count z D` points of `E i` in the disc of radius `ρ` about each `z ∈ D`; since the discs
are disjoint and `E i` has as many points as `D`, no point of `E i` lies outside them
(`Multiset.rel_of_forall_countP_eq_count_of_card_eq`).

## References

* L. V. Ahlfors, *Complex Analysis*, third edition, McGraw–Hill, 1979, Chapter 4, §5.2 and
  Chapter 5, §1.1 (Rouché's and Hurwitz's theorems for analytic functions).
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

open Complex Filter Metric Set Topology

namespace TauCeti

/-! ### Rouché's theorem -/

namespace IsZeroMultiplicity

variable {f : ℂ → ℂ} {D : Multiset ℂ}

/-- **Rouché's theorem for functions with local power factorizations**, symmetric form. Let `f`
and `g` have finitely many zeros, with multiplicities the counts of multisets `D` and `E`. If
`‖f w - g w‖ < ‖f w‖ + ‖g w‖` on the circle of radius `r` about `c`, then `f` and `g` have the
same number of zeros in the open disc bounded by that circle, counted with multiplicity. -/
theorem countP_dist_lt_eq_of_norm_sub_lt_add {g : ℂ → ℂ} {E : Multiset ℂ}
    (hf : IsZeroMultiplicity f fun z ↦ D.count z) (hg : IsZeroMultiplicity g fun z ↦ E.count z)
    {c : ℂ} {r : ℝ} (hlt : ∀ w ∈ sphere c r, ‖f w - g w‖ < ‖f w‖ + ‖g w‖) :
    (E.countP fun z ↦ dist z c < r) = D.countP fun z ↦ dist z c < r := by
  rcases le_or_gt r 0 with hr | hr
  · have hball : ∀ z, ¬ dist z c < r := fun z hz ↦ (dist_nonneg.trans_lt hz).not_ge hr
    rw [Multiset.countP_eq_zero.2 fun z _ ↦ hball z, Multiset.countP_eq_zero.2 fun z _ ↦ hball z]
  -- neither `f` nor `g` vanishes on the circle
  have hf0 : ∀ w ∈ sphere c r, f w ≠ 0 := fun w hw h0 ↦ by simpa [h0] using hlt w hw
  have hg0 : ∀ w ∈ sphere c r, g w ≠ 0 := fun w hw h0 ↦ by simpa [h0] using hlt w hw
  have hD : ∀ z ∈ D.toFinset, dist z c ≠ r := fun z hz h ↦
    hf0 z (mem_sphere.2 h) (hf.pos_iff.1 (Multiset.count_pos.2 (Multiset.mem_toFinset.1 hz)))
  have hE : ∀ z ∈ E.toFinset, dist z c ≠ r := fun z hz h ↦
    hg0 z (mem_sphere.2 h) (hg.pos_iff.1 (Multiset.count_pos.2 (Multiset.mem_toFinset.1 hz)))
  obtain ⟨L, hLc, hL⟩ := hf.exists_continuous_eq_exp_mul_prod_pow
  obtain ⟨L', hL'c, hL'⟩ := hg.exists_continuous_eq_exp_mul_prod_pow
  rw [← Multiset.sum_filter_count_eq_countP, ← Multiset.sum_filter_count_eq_countP]
  set N := ∑ z ∈ D.toFinset with dist z c < r, D.count z
  set N' := ∑ z ∈ E.toFinset with dist z c < r, E.count z
  -- `g / f` takes values in the slit plane, so it has the principal logarithm
  have hgf : HasContinuousLogOn (fun w ↦ g w / f w) (sphere c r) :=
    hasContinuousLogOn_of_mapsTo_slitPlane
      (hg.continuous.continuousOn.div hf.continuous.continuousOn hf0) fun w hw ↦
        div_mem_slitPlane_of_norm_sub_lt_add (hlt w hw)
  have hexp : HasContinuousLogOn (fun w ↦ exp (L w - L' w)) (sphere c r) :=
    hasContinuousLogOn_iff.2 ⟨fun w ↦ L w - L' w, (hLc.sub hL'c).continuousOn, fun _ _ ↦ rfl⟩
  -- hence so does `(w - c) ^ (N' - N)`
  have hlog : HasContinuousLogOn (fun w ↦ (w - c) ^ ((N' : ℤ) - N)) (sphere c r) := by
    refine (((hgf.mul hexp).mul
      (hasContinuousLogOn_prod_pow_div_pow_sphere D.toFinset (fun z ↦ D.count z) hD)).div
      (hasContinuousLogOn_prod_pow_div_pow_sphere E.toFinset (fun z ↦ E.count z) hE)).congr
      fun w hw ↦ ?_
    have hw0 : w - c ≠ 0 := by
      rw [← norm_ne_zero_iff, ← dist_eq_norm, mem_sphere.1 hw]
      exact hr.ne'
    have hP : ∏ z ∈ D.toFinset, (w - z) ^ D.count z ≠ 0 := fun h ↦
      hf0 w hw (by rw [hL w, h, mul_zero])
    have hP' : ∏ z ∈ E.toFinset, (w - z) ^ E.count z ≠ 0 := fun h ↦
      hg0 w hw (by rw [hL' w, h, mul_zero])
    simp only [hL w, hL' w, exp_sub]
    rw [zpow_sub₀ hw0, zpow_natCast, zpow_natCast]
    field_simp
    simp only [N, N']
    ring
  by_contra hne
  exact not_hasContinuousLogOn_zpow_sub_sphere hr.le c
    (sub_ne_zero.2 fun h ↦ hne (by exact_mod_cast h)) hlog

/-- **Rouché's theorem for functions with local power factorizations.** Let `f` and `g` have
finitely many zeros, with multiplicities the counts of multisets `D` and `E`. If
`‖g w - f w‖ < ‖f w‖` on the circle of radius `r` about `c`, then `f` and `g` have the same number
of zeros in the open disc bounded by that circle, counted with multiplicity. -/
theorem countP_dist_lt_eq_of_norm_sub_lt {g : ℂ → ℂ} {E : Multiset ℂ}
    (hf : IsZeroMultiplicity f fun z ↦ D.count z) (hg : IsZeroMultiplicity g fun z ↦ E.count z)
    {c : ℂ} {r : ℝ} (hlt : ∀ w ∈ sphere c r, ‖g w - f w‖ < ‖f w‖) :
    (E.countP fun z ↦ dist z c < r) = D.countP fun z ↦ dist z c < r :=
  countP_dist_lt_eq_of_norm_sub_lt_add hf hg fun w hw ↦ by
    rw [norm_sub_rev]
    exact (hlt w hw).trans_le (le_add_of_nonneg_right (norm_nonneg _))

/-! ### Hurwitz's theorem -/

/-- **Hurwitz's theorem for functions with local power factorizations**, matching form. Let `f`
have finitely many zeros, with multiplicities the counts of a multiset `D`, and let `g i` be
functions with zero multiplicities the counts of multisets `E i` with as many points as `D`. If
`g i → f` locally uniformly, then for every `ε > 0` the points of `E i` are eventually matched
one-to-one with those of `D`, matched points being at distance less than `ε`. -/
theorem eventually_rel_dist_lt_of_tendstoLocallyUniformly {ι : Type*} {l : Filter ι}
    {g : ι → ℂ → ℂ} {E : ι → Multiset ℂ} (hf : IsZeroMultiplicity f fun z ↦ D.count z)
    (hg : ∀ᶠ i in l, IsZeroMultiplicity (g i) fun z ↦ (E i).count z)
    (hcard : ∀ᶠ i in l, Multiset.card (E i) = Multiset.card D)
    (hgf : TendstoLocallyUniformly g f l) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, Multiset.Rel (fun a b ↦ dist a b < ε) D (E i) := by
  classical
  obtain ⟨ρ₀, hρ₀, -, hsep₀⟩ :=
    exists_pos_closedBall_subset_and_lt_dist (T := D.toFinset) (U := fun _ ↦ univ)
      fun _ _ ↦ univ_mem
  set ρ := min ρ₀ ε
  have hρ : 0 < ρ := lt_min hρ₀ hε
  have hρε : ρ ≤ ε := min_le_right _ _
  have hsep : ∀ z ∈ D, ∀ w ∈ D, z ≠ w → 2 * ρ < dist z w := fun z hz w hw hzw ↦
    (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le_two).trans_lt
      (hsep₀ z (Multiset.mem_toFinset.2 hz) w (Multiset.mem_toFinset.2 hw) hzw)
  -- the circles of radius `ρ` about the points of `D`, on which `f` is bounded away from zero
  set K := ⋃ z ∈ D.toFinset, sphere z ρ
  have hK : IsCompact K := D.toFinset.isCompact_biUnion fun z _ ↦ isCompact_sphere z ρ
  have hmemK : ∀ z ∈ D, ∀ w ∈ sphere z ρ, w ∈ K := fun z hz w hw ↦
    mem_iUnion₂.2 ⟨z, Multiset.mem_toFinset.2 hz, hw⟩
  have hfK : ∀ w ∈ K, f w ≠ 0 := by
    intro w hw h0
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.1 hw
    have hwD : w ∈ D := Multiset.count_pos.1 (hf.pos_iff.2 h0)
    rcases eq_or_ne z w with rfl | hzw
    · simp only [mem_sphere, dist_self] at hwz
      exact hρ.ne hwz
    · have := hsep z (Multiset.mem_toFinset.1 hz) w hwD hzw
      rw [mem_sphere, dist_comm] at hwz
      linarith
  obtain ⟨δ, hδ, hfδ⟩ : ∃ δ > 0, ∀ w ∈ K, δ ≤ ‖f w‖ := by
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨1, one_pos, by simp [hK0]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ :=
        hK.exists_isMinOn hKne (continuous_norm.comp hf.continuous).continuousOn
      exact ⟨‖f w₀‖, norm_pos_iff.2 (hfK w₀ hw₀), fun w hw ↦ hmin hw⟩
  have hunif := tendstoLocallyUniformly_iff_forall_isCompact.1 hgf K hK
  filter_upwards [hg, hcard, Metric.tendstoUniformlyOn_iff.1 hunif δ hδ] with i hgi hci hδi
  refine (Multiset.rel_of_forall_countP_eq_count_of_card_eq (r := fun a b ↦ dist a b < ρ)
    (fun b _ a ha a' ha' hab ha'b ↦ ?_) (fun z hz ↦ ?_) hci).mono
      fun _ _ _ _ h ↦ h.trans_le hρε
  · -- a point is within `ρ` of at most one point of `D`
    exact eq_of_dist_lt_of_dist_lt (hsep a ha a' ha') (by rwa [dist_comm]) (by rwa [dist_comm])
  · -- Rouché's theorem on the circle of radius `ρ` about `z`
    have hR := countP_dist_lt_eq_of_norm_sub_lt hf hgi (c := z) (r := ρ) fun w hw ↦ by
      have h := hδi w (hmemK z hz w hw)
      rw [dist_eq_norm, norm_sub_rev] at h
      exact h.trans_le (hfδ w (hmemK z hz w hw))
    calc (E i).countP (fun b ↦ dist z b < ρ) = (E i).countP fun b ↦ dist b z < ρ :=
          Multiset.countP_congr rfl fun b _ ↦ by rw [dist_comm]
      _ = D.countP fun b ↦ dist b z < ρ := hR
      _ = D.count z := by
        rw [Multiset.count_eq_card_filter_eq, ← Multiset.countP_eq_card_filter]
        exact Multiset.countP_congr rfl fun b hb ↦ propext
          ⟨fun h ↦ eq_of_dist_lt_of_dist_lt (hsep z hz b hb) h (by simpa using hρ),
            fun h ↦ by simp [← h, hρ]⟩

/-- **Hurwitz's theorem for functions with local power factorizations.** Let `f` and `g i` have
finitely many zeros, with multiplicities the counts of `D` and `E i` in the symmetric power
`Sym ℂ m`. If `g i → f` locally uniformly, then `E i → D` in `Sym ℂ m`: the zero divisor depends
continuously on the function, for the topology of locally uniform convergence. -/
theorem tendsto_of_tendstoLocallyUniformly {m : ℕ} {ι : Type*} {l : Filter ι}
    {g : ι → ℂ → ℂ} {D : Sym ℂ m} {E : ι → Sym ℂ m}
    (hf : IsZeroMultiplicity f fun z ↦ (D : Multiset ℂ).count z)
    (hg : ∀ᶠ i in l, IsZeroMultiplicity (g i) fun z ↦ (E i : Multiset ℂ).count z)
    (hgf : TendstoLocallyUniformly g f l) : Tendsto E l (𝓝 D) :=
  Sym.tendsto_nhds_iff_rel_dist_lt.2 fun _ hε ↦
    eventually_rel_dist_lt_of_tendstoLocallyUniformly hf hg (.of_forall fun i ↦ by simp) hgf hε

end IsZeroMultiplicity

end TauCeti
