/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowSubstitution
public import TauCeti.Analysis.Complex.Wirtinger.Regularity.Linear
public import TauCeti.Analysis.Complex.Wirtinger.Root.Normalization
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Regularity of the root branches of the Newton coefficient equation at a collision

Let `b₁, …, b_m` be `C¹` on a disc `ball x r`, with `b_j(y) = e_j(R(y))` for the multiset `R(y)` of
the `m` roots of `P_y(W) = Wᵐ - b₁(y) W^(m-1) + ⋯ + (-1)ᵐ b_m(y)`, simple for `y ≠ x`, and suppose
that they solve the equation of the elementary symmetric functions of `m` solutions of
`D_C = \bar∂ + ν W + μ \bar W`. Near the collision `x` the root multigraph is normalized by local
branches `t ↦ (x + t^(kₐ), vₐ(t))` with multiplicities `kₐ` summing to `m`
(`TauCeti.exists_eq_sum_map_nthRoots_hasWeakConjWirtingerDerivOn`); each `vₐ` is continuous, `C¹`
off `t = 0`, and solves the pulled-back equation

`\bar∂v + \overline{k t^(k-1)} (v ν(x + tᵏ) + \bar v μ(x + tᵏ)) = 0`

there classically and across `t = 0` only in the sense of distributions.

This file shows that when the forms `ν` and `μ` are Hölder continuous, the branches are `C¹` across
the collision as well, and solve the pulled-back equation at every point, centre included
(`TauCeti.exists_eq_sum_map_nthRoots_contDiffOn`). The pulled-back coefficients
`\overline{k t^(k-1)} ν(x + tᵏ)` and `\overline{k t^(k-1)} μ(x + tᵏ)` are Hölder on compact sets,
so this is the regularity of continuous weak solutions of linear Cauchy–Riemann equations with
Hölder coefficients
(`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_one_of_linear_of_holderOnWith`), applied to one
branch at a time
(`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_and_conjWirtingerDeriv_add_smul_eq_zero`). So the
root multigraph near `x` is the union of the images of finitely many `C¹` maps of discs, the
normalization of the limiting curve across a collision of its branches.

Consequently the derivatives of the branches are bounded near the centre, and every branch `V`
of the roots over a region of `y`, `V(x + tᵏ) = v(t)` on an open sheet `s` of the substitution
with closure in the disc, has `‖dV‖ ∈ L^{p_m}` on `x + sᵏ` for `p_m = 2 + 2 / m`: since `k ≤ m`,
the singularity `‖dV(y)‖ ≍ ‖y - x‖^(1 / k - 1)` keeps the margin `p_m (1 - 1 / k) < 2`
(`TauCeti.memLp_norm_fderiv_image_add_pow_two_add_two_div`). This is the integrability of the
branch derivatives through a collision at the exponent `p_m` of the coefficient estimates.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Finset Metric Polynomial Set MeasureTheory TopologicalSpace
open scoped NNReal ComplexConjugate

namespace TauCeti

/-- The pulled-back coefficient `t ↦ \overline{k t^(k-1)} f(x + tᵏ)(1)` of a form `f` that is
`α`-Hölder on the compact subsets of `U`, `0 < α ≤ 1`, is `α`-Hölder on every compact set that
`t ↦ x + tᵏ` maps into `U`. -/
private theorem exists_holderOnWith_conj_mul_apply_add_pow {x : ℂ} {k : ℕ} {U K : Set ℂ}
    {f : ℂ → ℂ →L⋆[ℂ] ℂ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α f K) (hK : IsCompact K)
    (hKU : MapsTo (fun t ↦ x + t ^ k) K U) :
    ∃ C, HolderOnWith C α (fun t ↦ conj ((k : ℂ) * t ^ (k - 1)) * f (x + t ^ k) 1) K := by
  set φ : ℂ → ℂ := fun t ↦ x + t ^ k
  have hφ : ContDiff ℝ 1 φ := contDiff_const.add (contDiff_id.pow k)
  -- the form is `α`-Hölder on the compact image of `K`, and `φ` is Lipschitz on `K`
  obtain ⟨C, hC⟩ := hf (φ '' K) (image_subset_iff.2 hKU) (hK.image hφ.continuous)
  obtain ⟨L, hL⟩ := hφ.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  have hfφ := hC.comp hL.holderOnWith (mapsTo_image φ K)
  rw [mul_one] at hfφ
  have hf1 := (ContinuousLinearMap.lipschitzWith_apply (σ₁₂ := starRingEnd ℂ) (F := ℂ)
    (1 : ℂ)).comp_holderOnWith hfφ
  -- the smooth factor `\overline{k t^(k-1)}` is `α`-Hölder on `K`
  have hc : ContDiff ℝ 1 fun t : ℂ ↦ conj ((k : ℂ) * t ^ (k - 1)) :=
    Complex.conjCLE.contDiff.comp (contDiff_const.mul (contDiff_id.pow (k - 1)))
  obtain ⟨_, hCc⟩ := hc.locallyLipschitz.locallyLipschitzOn.exists_holderOnWith_of_isCompact
    (s := univ) hα1 hK (subset_univ K)
  obtain ⟨_, hprod⟩ := (ContinuousLinearMap.mul ℂ ℂ).exists_holderOnWith_comp₂_of_isCompact hK hα
    hCc hf1
  exact ⟨_, hprod.congr fun t _ ↦ by simp [φ]⟩

/-- **A branch through a power substitution is a classical solution.** Let `v` be continuous on an
open set `Ω` and solve the pulled-back equation

`\bar∂v + \overline{k t^(k-1)} (v ν(x + tᵏ) + \bar v μ(x + tᵏ)) = 0`

in the sense of distributions on `Ω`, where `t ↦ x + tᵏ` maps `Ω` into a set `U` on whose compact
subsets the forms `ν` and `μ` are `α`-Hölder for some `α > 0`. Then `v` is `C¹` on `Ω` and solves
the equation at every point of `Ω`, including the branch point `t = 0`. -/
theorem HasWeakConjWirtingerDerivOn.contDiffOn_and_conjWirtingerDeriv_add_smul_eq_zero
    {Ω : Opens ℂ} {U : Set ℂ} {x : ℂ} {k : ℕ} {v : ℂ → ℂ} {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ} {α : ℝ≥0}
    (hα : 0 < α)
    (h : HasWeakConjWirtingerDerivOn volume Ω v fun t ↦
      -(conj ((k : ℂ) * t ^ (k - 1)) * (v t * ν (x + t ^ k) 1 + conj (v t) * μ (x + t ^ k) 1)))
    (hv : ContinuousOn v Ω) (hmaps : MapsTo (fun t ↦ x + t ^ k) Ω U)
    (hν : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α ν K)
    (hμ : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α μ K) :
    ContDiffOn ℝ 1 v Ω ∧ ∀ t ∈ Ω, conjWirtingerDeriv v t + conj ((k : ℂ) * t ^ (k - 1)) •
      (v t • ν (x + t ^ k) + conj (v t) • μ (x + t ^ k)) = 0 := by
  set a : ℂ → ℂ := fun t ↦ conj ((k : ℂ) * t ^ (k - 1)) * ν (x + t ^ k) 1
  set b : ℂ → ℂ := fun t ↦ conj ((k : ℂ) * t ^ (k - 1)) * μ (x + t ^ k) 1
  have h' : HasWeakConjWirtingerDerivOn volume Ω v fun t ↦ -(a t * v t + b t * conj (v t)) := by
    convert h using 2 with t
    simp only [a, b]
    ring
  -- the forms are also `min α 1`-Hölder on compact sets, an exponent at most `1`
  have hlow {f : ℂ → ℂ →L⋆[ℂ] ℂ} (hf : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α f K) :
      ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C (min α 1) f K := fun K hKU hK ↦
    HolderOnWith.exists_holderOnWith_of_le (hf K hKU hK) (min_le_left _ _) hK.isBounded
  have hα' : 0 < min α 1 := lt_min hα one_pos
  obtain ⟨h1, h2, -⟩ := h'.contDiffOn_one_of_linear_of_holderOnWith hα' hv
    (fun K hKΩ hK ↦ exists_holderOnWith_conj_mul_apply_add_pow hα' (min_le_right _ _) (hlow hν)
      hK (hmaps.mono_left hKΩ))
    (fun K hKΩ hK ↦ exists_holderOnWith_conj_mul_apply_add_pow hα' (min_le_right _ _) (hlow hμ)
      hK (hmaps.mono_left hKΩ))
  refine ⟨h1, fun t ht ↦ ContinuousLinearMap.coe_injective (LinearMap.ext_ring ?_)⟩
  have h2t := h2 t ht
  simp only [a, b] at h2t
  simp only [ContinuousLinearMap.coe_coe, add_apply, smul_apply,
    ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply, smul_eq_mul]
  linear_combination h2t

variable {m : ℕ} {b : ℕ → ℂ → ℂ} {x : ℂ} {r : ℝ} {R : ℂ → Multiset ℂ}

/-- **Normalization of the root multigraph across a collision by `C¹` branches.** Let
`b₁, …, b_m` be `C¹` on the disc `ball x r`, `r > 0`, with `b_j(y) = e_j(R(y))` for multisets
`R(y)` of `m` points, simple for `y ≠ x`, and let them solve the equation of the elementary
symmetric functions of `m` solutions of `D_C = \bar∂ + ν W + μ \bar W`, with forms `ν`, `μ` that
are `α`-Hölder on the compact subsets of the disc for some `α > 0`. Then near `x` the root
multigraph `{(y, w) : w ∈ R(y)}` is parametrized by finitely many local branches
`t ↦ (x + t^(kₐ), vₐ(t))` on a disc `ball 0 δ`, with multiplicities `kₐ ≥ 1` summing to `m`:

* for `s` in a disc `ball 0 ε`, `R(x + s)` is, with multiplicity, the multiset of the values
  `vₐ(t)` at the `kₐ`-th roots `t` of `s`, over all branches `a`, and these roots lie in `ball 0 δ`;
* each branch parametrization `t ↦ (t^(kₐ), vₐ(t))` is injective on `ball 0 δ`, the
  parametrizations of distinct branches meet only over `s = 0`, and `t ↦ x + t^(kₐ)` maps
  `ball 0 δ` into `ball x r`;
* each `vₐ` is `C¹` on `ball 0 δ` and solves the pulled-back equation
  `\bar∂v + \overline{kₐ t^(kₐ-1)} (v ν(x + t^(kₐ)) + \bar v μ(x + t^(kₐ))) = 0` at every point,
  centre included;
* the derivative of each branch over a region of `y` is `L^{p_m}`, `p_m = 2 + 2 / m`: if `s` is
  open with closure in `ball 0 δ` and `V(x + t^(kₐ)) = vₐ(t)` for `t ∈ s`, then `‖dV‖` is
  `L^{p_m}` on `x + s^(kₐ)`. -/
theorem exists_eq_sum_map_nthRoots_contDiffOn (hr : 0 < r)
    (hb : ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ 1 (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Finset.Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ} {α : ℝ≥0}
    (hα : 0 < α) (hν : ∀ K ⊆ ball x r, IsCompact K → ∃ C, HolderOnWith C α ν K)
    (hμ : ∀ K ⊆ ball x r, IsCompact K → ∃ C, HolderOnWith C α μ K)
    (heq : ∀ y ∈ ball x r, ∀ j ∈ Finset.Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (k : ι → ℕ) (v : ι → ℂ → ℂ), ∃ ε > 0, ∃ δ > 0,
      (∀ a, 0 < k a) ∧ ∑ a, k a = m ∧
      (∀ s ∈ ball (0 : ℂ) ε, R (x + s) = ∑ a, (nthRoots (k a) s).map (v a)) ∧
      (∀ a, ∀ s ∈ ball (0 : ℂ) ε, ∀ t ∈ nthRoots (k a) s, t ∈ ball (0 : ℂ) δ) ∧
      (∀ a, Set.InjOn (fun t ↦ (t ^ k a, v a t)) (ball 0 δ)) ∧
      (∀ a a', a ≠ a' → ∀ t ∈ ball (0 : ℂ) δ, ∀ t' ∈ ball (0 : ℂ) δ, t ≠ 0 →
        (t ^ k a, v a t) ≠ (t' ^ k a', v a' t')) ∧
      (∀ a, Set.MapsTo (fun t ↦ x + t ^ k a) (ball 0 δ) (ball x r)) ∧
      (∀ a, ContDiffOn ℝ 1 (v a) (ball 0 δ)) ∧
      (∀ a, ∀ t ∈ ball (0 : ℂ) δ, conjWirtingerDeriv (v a) t + conj (k a * t ^ (k a - 1)) •
        (v a t • ν (x + t ^ k a) + conj (v a t) • μ (x + t ^ k a)) = 0) ∧
      ∀ a, ∀ s : Set ℂ, IsOpen s → closure s ⊆ ball 0 δ → ∀ V : ℂ → ℂ,
        (∀ t ∈ s, V (x + t ^ k a) = v a t) →
        MemLp (fun y ↦ ‖fderiv ℝ V y‖) (ENNReal.ofReal (2 + 2 / m))
          (volume.restrict ((fun t ↦ x + t ^ k a) '' s)) := by
  obtain ⟨ι, _, k, v, ε, hε, δ, hδ, hk, hsum, hroots, hnth, hinj, hdisj, hmaps, hvc, -, hweak⟩ :=
    exists_eq_sum_map_nthRoots_hasWeakConjWirtingerDerivOn hr hb hR hsimple
      (continuousOn_of_forall_isCompact_holderOnWith isOpen_ball hα hν)
      (continuousOn_of_forall_isCompact_holderOnWith isOpen_ball hα hμ) heq
  -- each branch is a classical solution across the centre
  have hreg (a : ι) := (hweak a).contDiffOn_and_conjWirtingerDeriv_add_smul_eq_zero hα (hvc a)
    (hmaps a) hν hμ
  refine ⟨ι, inferInstance, k, v, ε, hε, δ, hδ, hk, hsum, hroots, hnth, hinj, hdisj, hmaps,
    fun a ↦ (hreg a).1, fun a ↦ (hreg a).2, fun a s hs hsδ V hV ↦ ?_⟩
  -- the derivative of `vₐ` is bounded on the compact closure of `s`
  have hcs : IsCompact (closure s) :=
    (isCompact_closedBall (0 : ℂ) δ).of_isClosed_subset isClosed_closure
      (hsδ.trans ball_subset_closedBall)
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuousOn
    (((hreg a).1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hsδ)
  have hsb : s ⊆ ball 0 δ := subset_closure.trans hsδ
  have hkm : k a ≤ m := hsum ▸ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
  have hφ : Continuous fun t : ℂ ↦ x + t ^ k a := by fun_prop
  exact memLp_norm_fderiv_image_add_pow_two_add_two_div hkm hs
    (fun t ht ↦ ((hreg a).1.differentiableOn one_ne_zero t (hsb ht)).differentiableAt
      (isOpen_ball.mem_nhds (hsb ht))) hV
    (fun t ht ↦ by simpa using hM t (subset_closure ht))
    ((hcs.image hφ).isBounded.subset (image_mono subset_closure))

end TauCeti
