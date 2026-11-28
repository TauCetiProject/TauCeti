/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Root.Collision
public import TauCeti.Analysis.Complex.Wirtinger.Root.Regularity
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Model

/-!
# The root multigraph of the Newton coefficient equation is a `J_N`-holomorphic curve

Let `b₁, …, b_m` be `C¹` functions on an open set `U` of the base `ℂ`, with `b_j(y) = e_j(R(y))`
for the multiset `R(y)` of the `m` roots of

`P_y(W) = Wᵐ - b₁(y) W^(m-1) + ⋯ + (-1)ᵐ b_m(y)`,

and suppose that they solve the equation of the elementary symmetric functions of `m` solutions of
the real Cauchy–Riemann operator `D_C = \bar∂ + ν W + μ \bar W`,

`\bar∂ b_j + j ν b_j + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ = 0`,  `1 ≤ j ≤ m`.

In Taubes's analysis of Seiberg–Witten solutions concentrating along a pseudoholomorphic curve
`C`, the `b_j` are the limits of the Newton coefficients of the normal moments of the curvature
current, and the root multigraph `{(y, w) : w ∈ R(y)}` in the normal bundle is the candidate for
the limiting curve. This file shows that it is a curve for the almost complex structure
`J_N = TauCeti.normalModelStructure` of the linear normal model, whose holomorphic sections are
the solutions of `D_C`, and normalizes it by `J_N`-holomorphic discs across the collisions of its
branches, with multiplicities.

* **Branches as discs.** For the substitution `y = x + tᵏ`, a branch `t ↦ (x + tᵏ, v(t))` is
  `J_N`-holomorphic at `t` exactly when `v` is differentiable at `t` and solves the pulled-back
  equation `\bar∂v + \overline{k t^(k-1)} (v ν(x + tᵏ) + \bar v μ(x + tᵏ)) = 0` there
  (`TauCeti.isJHolomorphicAt_add_pow_normalModelStructure_iff`). This is the equation that the
  branches of the root multigraph at a collision solve.
* **Normalization at a collision.** If the roots are simple on a punctured disc about `x` and the
  forms `ν`, `μ` are Hölder continuous, then near `x` the root multigraph is the union of the
  images of finitely many `J_N`-holomorphic discs `t ↦ (x + t^(kₐ), vₐ(t))`, `C¹` and injective,
  meeting one another only over `x`, with multiplicities `kₐ` summing to `m`; when the roots are
  simple at `x` as well, every multiplicity is one
  (`TauCeti.exists_eq_sum_map_nthRoots_isJHolomorphicOn`).
* **The whole multigraph.** On a connected open set `U` on which the roots are simple at one
  point, they are simple off a discrete set, so the root multigraph has such a normalization by
  `J_N`-holomorphic discs at every point of `U`
  (`TauCeti.exists_eq_sum_map_nthRoots_isJHolomorphicOn_of_isPreconnected`).

The analytic content is the regularity of the root branches across a collision
(`TauCeti.exists_eq_sum_map_nthRoots_contDiffOn`) and the isolation of collisions
(`TauCeti.setOf_nodup_mem_codiscreteWithin`); the link with `J_N` is the characterization of
`J_N`-holomorphic curves `t ↦ (f t, v t)` with holomorphic base component
(`TauCeti.isJHolomorphicAt_prodMk_normalModelStructure_iff`). Here the `(0,1)`-forms `ν`, `μ` of
`D_C` enter `J_N` through their values `ν(y) 1`, `μ(y) 1` on the unit vector of the base.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Complex Filter Metric Polynomial Set Topology
open scoped ComplexConjugate NNReal

namespace TauCeti

variable {m : ℕ} {b : ℕ → ℂ → ℂ} {R : ℂ → Multiset ℂ} {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ} {x : ℂ}

/-- **Branches of the root multigraph are `J_N`-holomorphic discs.** For the substitution
`y = x + tᵏ` of the base, the curve `t ↦ (x + tᵏ, v(t))` in the normal model is
`J_N`-holomorphic at `t` exactly when `v` is differentiable at `t` and solves the pulled-back
normal equation

`\bar∂v + \overline{k t^(k-1)} (v ν(x + tᵏ) + \bar v μ(x + tᵏ)) = 0`

there, where `J_N` is built from the values of the `(0,1)`-forms `ν`, `μ` on `1`. -/
theorem isJHolomorphicAt_add_pow_normalModelStructure_iff {v : ℂ → ℂ} {k : ℕ} {t : ℂ} :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
        (normalModelStructure (ν · 1) (μ · 1)) (fun t ↦ (x + t ^ k, v t)) t ↔
      DifferentiableAt ℝ v t ∧ conjWirtingerDeriv v t + conj ((k : ℂ) * t ^ (k - 1)) •
        (v t • ν (x + t ^ k) + conj (v t) • μ (x + t ^ k)) = 0 := by
  have hf : DifferentiableAt ℂ (fun t ↦ x + t ^ k) t := by fun_prop
  have hderiv : deriv (fun t ↦ x + t ^ k) t = k * t ^ (k - 1) := by simp
  rw [isJHolomorphicAt_prodMk_normalModelStructure_iff, hderiv]
  refine and_iff_right_of_imp (fun _ ↦ hf) |>.trans (and_congr_right fun _ ↦ ?_)
  -- an antilinear map on `ℂ` vanishes exactly when its value on `1` does
  refine ⟨fun h ↦ ContinuousLinearMap.coe_injective (LinearMap.ext_ring ?_), fun h ↦ ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, add_apply, smul_apply,
      ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply, smul_eq_mul]
    linear_combination h
  · have h₁ := congrArg (fun L : ℂ →L⋆[ℂ] ℂ ↦ L 1) h
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply] at h₁
    linear_combination h₁

/-- **Normalization of the root multigraph at a collision by `J_N`-holomorphic discs.** Let
`b₁, …, b_m` be `C¹` on the disc `ball x r`, `r > 0`, with `b_j(y) = e_j(R(y))` for multisets
`R(y)` of `m` points, simple for `y ≠ x`, and let them solve the equation of the elementary
symmetric functions of `m` solutions of `D_C = \bar∂ + ν W + μ \bar W`, with forms `ν`, `μ` that
are `α`-Hölder on the compact subsets of the disc for some `α > 0`. Then near `x` the root
multigraph `{(y, w) : w ∈ R(y)}` is the union of the images of finitely many discs
`uₐ(t) = (x + t^(kₐ), vₐ(t))`, `t ∈ ball 0 δ`, with multiplicities `kₐ ≥ 1` summing to `m`:

* for `s` in a disc `ball 0 ε`, `R(x + s)` is, with multiplicity, the multiset of the values
  `vₐ(t)` at the `kₐ`-th roots `t` of `s`, over all branches `a`, and these roots lie in `ball 0 δ`;
* each `uₐ` is injective on `ball 0 δ`, distinct discs meet only over `x`, and `uₐ` lies over
  `ball x r`;
* each `vₐ` is `C¹` and each `uₐ` is `J_N`-holomorphic on `ball 0 δ`, for the structure `J_N` of
  `D_C`;
* if the roots are also simple at `x`, every multiplicity `kₐ` is one, so that each disc
  `t ↦ (x + t, vₐ(t))` is a graph over `ball x δ`. -/
theorem exists_eq_sum_map_nthRoots_isJHolomorphicOn {r : ℝ} (hr : 0 < r)
    (hb : ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ 1 (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Finset.Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) {α : ℝ≥0} (hα : 0 < α)
    (hν : ∀ K ⊆ ball x r, IsCompact K → ∃ C, HolderOnWith C α ν K)
    (hμ : ∀ K ⊆ ball x r, IsCompact K → ∃ C, HolderOnWith C α μ K)
    (heq : ∀ y ∈ ball x r, ∀ j ∈ Finset.Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (k : ι → ℕ) (v : ι → ℂ → ℂ), ∃ ε > 0, ∃ δ > 0,
      (∀ a, 0 < k a) ∧ ∑ a, k a = m ∧
      (∀ s ∈ ball (0 : ℂ) ε, R (x + s) = ∑ a, (nthRoots (k a) s).map (v a)) ∧
      (∀ a, ∀ s ∈ ball (0 : ℂ) ε, ∀ t ∈ nthRoots (k a) s, t ∈ ball (0 : ℂ) δ) ∧
      (∀ a, InjOn (fun t ↦ (x + t ^ k a, v a t)) (ball 0 δ)) ∧
      (∀ a a', a ≠ a' → ∀ t ∈ ball (0 : ℂ) δ, ∀ t' ∈ ball (0 : ℂ) δ, t ≠ 0 →
        (x + t ^ k a, v a t) ≠ (x + t' ^ k a', v a' t')) ∧
      (∀ a, MapsTo (fun t ↦ x + t ^ k a) (ball 0 δ) (ball x r)) ∧
      (∀ a, ContDiffOn ℝ 1 (v a) (ball 0 δ)) ∧
      (∀ a, IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
        (normalModelStructure (ν · 1) (μ · 1)) (fun t ↦ (x + t ^ k a, v a t)) (ball 0 δ)) ∧
      ((R x).Nodup → ∀ a, k a = 1) := by
  obtain ⟨ι, _, k, v, ε, hε, δ, hδ, hk, hsum, hroots, hnth, hinj, hdisj, hmaps, hvc, hveq, -⟩ :=
    exists_eq_sum_map_nthRoots_contDiffOn hr hb hR hsimple hα hν hμ heq
  -- the discs `uₐ` differ from the maps `t ↦ (t^(kₐ), vₐ(t))` by a translation of the base
  have hpair {p q w w' : ℂ} : ((x + p, w) = (x + q, w')) ↔ ((p, w) = (q, w')) := by
    simp only [Prod.mk.injEq, add_right_inj]
  refine ⟨ι, inferInstance, k, v, ε, hε, δ, hδ, hk, hsum, hroots, hnth,
    fun a t ht t' ht' h ↦ hinj a ht ht' (hpair.1 h),
    fun a a' haa' t ht t' ht' ht0 h ↦ hdisj a a' haa' t ht t' ht' ht0 (hpair.1 h), hmaps, hvc,
    fun a ↦ (isJHolomorphicOn_iff _ _ _ _).2 fun t ht ↦ ?_, fun hnd a ↦ ?_⟩
  · -- each branch solves the pulled-back equation, so its disc is `J_N`-holomorphic
    have hvt : DifferentiableAt ℝ (v a) t :=
      ((hvc a).differentiableOn one_ne_zero t ht).differentiableAt (isOpen_ball.mem_nhds ht)
    exact (isJHolomorphicAt_add_pow_normalModelStructure_iff.2
      ⟨hvt, hveq a t ht⟩).isJHolomorphicWithinAt
  · -- at a simple point the summand `(nthRoots kₐ 0).map vₐ`, which repeats `vₐ(0)` `kₐ` times,
    -- is part of `R x`, which repeats nothing
    have hx := hroots 0 (mem_ball_self hε)
    rw [add_zero] at hx
    have hle : Multiset.replicate (k a) (v a 0) ≤ R x := by
      rw [hx]
      simpa [nthRoots_zero_right, Multiset.map_replicate] using
        Finset.single_le_sum (f := fun a ↦ (nthRoots (k a) (0 : ℂ)).map (v a))
          (fun _ _ ↦ Multiset.zero_le _) (Finset.mem_univ a)
    exact le_antisymm ((Multiset.le_count_iff_replicate_le.2 hle).trans
      (Multiset.nodup_iff_count_le_one.1 hnd _)) (hk a)

/-- **The root multigraph is a `J_N`-holomorphic curve.** Let `b₁, …, b_m` be `C¹` on a connected
open set `U ⊆ ℂ`, with `b_j(y) = e_j(R(y))` for multisets `R(y)` of `m` points, solving the
equation of the elementary symmetric functions of `m` solutions of `D_C = \bar∂ + ν W + μ \bar W`
with forms `ν`, `μ` that are `α`-Hölder on the compact subsets of `U`, `α > 0`, and suppose that the
roots are simple at one point of `U`. Then at every point `x ∈ U` the root multigraph
`{(y, w) : y ∈ U, w ∈ R(y)}` is normalized by finitely many injective `C¹` discs
`t ↦ (x + t^(kₐ), vₐ(t))` lying over `U`, `J_N`-holomorphic for the structure `J_N` of `D_C`,
meeting one another only over `x`, with multiplicities `kₐ ≥ 1` summing to `m`, all equal to one
where the roots are simple, as in `TauCeti.exists_eq_sum_map_nthRoots_isJHolomorphicOn`. -/
theorem exists_eq_sum_map_nthRoots_isJHolomorphicOn_of_isPreconnected {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hb : ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ 1 (b j) U)
    (hR : ∀ y ∈ U, Multiset.card (R y) = m ∧ ∀ j ∈ Finset.Icc 1 m, b j y = (R y).esymm j)
    {α : ℝ≥0} (hα : 0 < α) (hν : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α ν K)
    (hμ : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α μ K)
    (heq : ∀ y ∈ U, ∀ j ∈ Finset.Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0)
    (hne : ∃ y ∈ U, (R y).Nodup) (hx : x ∈ U) :
    ∃ (ι : Type) (_ : Fintype ι) (k : ι → ℕ) (v : ι → ℂ → ℂ), ∃ ε > 0, ∃ δ > 0,
      (∀ a, 0 < k a) ∧ ∑ a, k a = m ∧
      (∀ s ∈ ball (0 : ℂ) ε, R (x + s) = ∑ a, (nthRoots (k a) s).map (v a)) ∧
      (∀ a, ∀ s ∈ ball (0 : ℂ) ε, ∀ t ∈ nthRoots (k a) s, t ∈ ball (0 : ℂ) δ) ∧
      (∀ a, InjOn (fun t ↦ (x + t ^ k a, v a t)) (ball 0 δ)) ∧
      (∀ a a', a ≠ a' → ∀ t ∈ ball (0 : ℂ) δ, ∀ t' ∈ ball (0 : ℂ) δ, t ≠ 0 →
        (x + t ^ k a, v a t) ≠ (x + t' ^ k a', v a' t')) ∧
      (∀ a, MapsTo (fun t ↦ x + t ^ k a) (ball 0 δ) U) ∧
      (∀ a, ContDiffOn ℝ 1 (v a) (ball 0 δ)) ∧
      (∀ a, IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
        (normalModelStructure (ν · 1) (μ · 1)) (fun t ↦ (x + t ^ k a, v a t)) (ball 0 δ)) ∧
      ((R x).Nodup → ∀ a, k a = 1) := by
  -- the forms are continuous, hence locally bounded, on `U`
  have hbdd {f : ℂ → ℂ →L⋆[ℂ] ℂ} (hf : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α f K)
      (z : ℂ) (hz : z ∈ U) : ∃ M, ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ M :=
    ⟨‖f z‖ + 1, (((continuousOn_of_forall_isCompact_holderOnWith hU hα hf).continuousAt
      (hU.mem_nhds hz)).norm.eventually (eventually_le_nhds (lt_add_one _)))⟩
  -- the collisions of the roots are isolated in `U`, so a disc about `x` contains no other one
  have hev : ∀ᶠ y in 𝓝[≠] x, (R y).Nodup ∨ y ∉ U :=
    mem_codiscreteWithin_iff_forall_mem_nhdsNE.1
      (setOf_nodup_mem_codiscreteWithin hU hUc hb hR (hbdd hν) (hbdd hμ) heq hne) x hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (eventually_nhdsWithin_iff.1 hev) (hU.mem_nhds hx))
  have hrU : ball x r ⊆ U := fun y hy ↦ (hball hy).2
  have hsimple (y : ℂ) (hy : y ∈ ball x r) (hyx : y ≠ x) : (R y).Nodup :=
    ((hball hy).1 hyx).resolve_right fun hyU ↦ hyU (hball hy).2
  obtain ⟨ι, _, k, v, ε, hε, δ, hδ, hk, hsum, hroots, hnth, hinj, hdisj, hmaps, hvc, hJ, hone⟩ :=
    exists_eq_sum_map_nthRoots_isJHolomorphicOn hr (fun j hj ↦ (hb j hj).mono hrU)
      (fun y hy ↦ hR y (hrU hy)) hsimple hα (fun K hK ↦ hν K (hK.trans hrU))
      (fun K hK ↦ hμ K (hK.trans hrU)) fun y hy ↦ heq y (hrU hy)
  exact ⟨ι, inferInstance, k, v, ε, hε, δ, hδ, hk, hsum, hroots, hnth, hinj, hdisj,
    fun a ↦ (hmaps a).mono_right hrU, hvc, hJ, hone⟩

end TauCeti
