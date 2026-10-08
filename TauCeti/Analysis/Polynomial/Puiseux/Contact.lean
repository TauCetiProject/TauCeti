/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Rotation
public import TauCeti.Analysis.Polynomial.Puiseux.Multiplicity
import TauCeti.Topology.Connected.FiniteFamily
import TauCeti.Topology.Homotopy.PuncturedStarConvex
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Capped contacts of Puiseux branches

A complete analytic splitting after `y = t ^ N` is permuted by `t ↦ ζ * t`
for a primitive `N`th root of unity. If its discriminant is a power of `t`
times an analytic unit, the orders of differences between distinct labels are
locally constant. Rotation then shows that the orders of contact with each
branch's value at `t = 0`, capped at `N`, are locally constant too.

The capped contacts with any labelled root on the hyperplane are also locally
constant, including when several labels coincide there. These are the summands
in the Puiseux formula for ambient polynomial order at a root section.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti

/-- Rotation permutes a complete continuous splitting of a power-substituted polynomial
family. The permutation is unique even if roots collide at `t = 0`; distinctness is
required only on the punctured disc. -/
theorem existsUnique_root_rotation_perm {E : Type*} [TopologicalSpace E]
    {U : Set E} {R : ℝ} {N n : ℕ} {ζ : ℂ}
    {P : E × ℂ → ℂ[X]} {r : Fin n → E × ℂ → ℂ}
    (hU : IsPreconnected U) (hR : 0 < R) (hζ : ζ ^ N = 1) (hζnorm : ‖ζ‖ = 1)
    (hr : ∀ i, ContinuousOn (r i) (U ×ˢ ball 0 R))
    (hinj : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), Injective (fun i ↦ r i b))
    (hP : ∀ b ∈ U ×ˢ ball 0 R, P (b.1, b.2 ^ N) = ∏ i, (X - C (r i b)))
    (x₀ : U) :
    ∃! σ : Equiv.Perm (Fin n), ∀ i b, b ∈ U ×ˢ ball 0 R →
      r (σ i) b = r i (b.1, ζ * b.2) := by
  classical
  let S := U ×ˢ (ball (0 : ℂ) R \ {0})
  let T := U ×ˢ ball (0 : ℂ) R
  let κ : E × ℂ → E × ℂ := fun b ↦ (b.1, ζ * b.2)
  have hζ0 : ζ ≠ 0 := by intro hz; simp [hz] at hζnorm
  have hκ : Continuous κ := by fun_prop
  have hκT : MapsTo κ T T := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    simpa only [κ, mem_ball_zero_iff, norm_mul, hζnorm, one_mul] using hb.2
  have hκS : MapsTo κ S S := fun b hb ↦
    ⟨(hκT ⟨hb.1, hb.2.1⟩).1, (hκT ⟨hb.1, hb.2.1⟩).2, mul_ne_zero hζ0 hb.2.2⟩
  let := pathConnectedSpace_ball_diff_singleton (0 : ℂ) hR
  have hSc : IsPreconnected S :=
    hU.prod (isPreconnected_iff_preconnectedSpace.2 inferInstance)
  let := Subtype.preconnectedSpace hSc
  have hroot (b : E × ℂ) (hb : b ∈ T) (z : ℂ) :
      (P (b.1, b.2 ^ N)).IsRoot z ↔ ∃ i, r i b = z := by
    rw [hP b hb, isRoot_prod]
    simp [sub_eq_zero, eq_comm]
  have hmem (i : Fin n) (b : S) : r i (κ b) ∈ range (fun j ↦ r j b) := by
    have hz := (hroot (κ b) (hκT ⟨b.property.1, b.property.2.1⟩) _).2 ⟨i, rfl⟩
    have hp : P ((κ b).1, (κ b).2 ^ N) = P (b.val.1, b.val.2 ^ N) := by
      simp only [κ, mul_pow, hζ, one_mul]
    rw [hp] at hz
    exact (hroot b ⟨b.property.1, b.property.2.1⟩ _).1 hz
  obtain ⟨t₀⟩ : Nonempty ↥(ball (0 : ℂ) R \ {0}) := inferInstance
  let b₀ : S := ⟨(x₀, t₀), x₀.property, t₀.property⟩
  -- Distinctness makes each rotated root choose one label on the punctured product.
  choose p hp using fun i ↦ hmem i b₀
  have hall (i : Fin n) (b : S) : r (p i) b = r i (κ b) := by
    have hsub : S ⊆ T := prod_mono subset_rfl sdiff_subset
    exact congrFun (eq_of_continuous_mem_range
      (fun j ↦ ((hr j).mono hsub).domRestrict)
      (((hr i).comp hκ.continuousOn hκT).mono hsub).domRestrict
      (fun b ↦ hinj b b.property) (hmem i) b₀ (hp i)) b
  have hpinj : Injective p := by
    intro i j hij
    apply hinj (κ b₀) (hκS b₀.property)
    exact (hall i b₀).symm.trans ((congrArg (fun k ↦ r k b₀) hij).trans (hall j b₀))
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective p ((Finite.injective_iff_bijective).1 hpinj)
  -- Continuity extends the label identities through collisions at the hyperplane.
  have hdense : T ⊆ closure S := by
    rw [closure_prod_eq, Set.sdiff_eq]
    exact prod_mono subset_closure
      ((dense_compl_singleton (0 : ℂ)).open_subset_closure_inter isOpen_ball)
  have heq (i : Fin n) : EqOn (r (σ i)) (fun b ↦ r i (κ b)) T := by
    have heqS : EqOn (r (σ i)) (fun b ↦ r i (κ b)) S := fun b hb ↦ hall i ⟨b, hb⟩
    exact heqS.of_subset_closure (hr _) ((hr i).comp hκ.continuousOn hκT)
      (prod_mono subset_rfl sdiff_subset) hdense
  refine ⟨σ, heq, ?_⟩
  intro σ' hσ'
  apply Equiv.ext
  intro i
  exact hinj b₀ b₀.property
    ((hσ' i b₀ ⟨b₀.property.1, b₀.property.2.1⟩).trans (hall i b₀).symm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {U : Set E} {R : ℝ} {N n a : ℕ}
  {P : E × ℂ → ℂ[X]} {r : Fin n → E × ℂ → ℂ} {u : E × ℂ → ℂ} {x₀ : E}

/-- The contact of each ramified branch with its own value on the hyperplane,
capped at the ramification exponent, is locally constant in the parameter.
Neither that contact order nor a permutation of branches is assumed. -/
private theorem eventually_min_analyticOrderAt_root_sub_self_eq
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx₀ : x₀ ∈ U) (hR : 0 < R)
    (hN : N ≠ 0)
    (hr : ∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ ball 0 R))
    (hP : ∀ b ∈ U ×ˢ ball 0 R, P (b.1, b.2 ^ N) = ∏ i, (X - C (r i b)))
    (hu : AnalyticAt ℂ u (x₀, 0)) (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hdiscr : ∀ b ∈ U ×ˢ ball 0 R, (P (b.1, b.2 ^ N)).discr = b.2 ^ a * u b) :
    ∀ᶠ x in 𝓝 x₀, ∀ i,
      min (N : ℕ∞) (analyticOrderAt (fun t ↦ r i (x, t) - r i (x, 0)) 0) =
        min (N : ℕ∞) (analyticOrderAt (fun t ↦ r i (x₀, t) - r i (x₀, 0)) 0) := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN
  have hsub : U ×ˢ (ball (0 : ℂ) R \ {0}) ⊆ U ×ˢ ball 0 R :=
    prod_mono subset_rfl sdiff_subset
  have hinj : ∀ b ∈ U ×ˢ (ball (0 : ℂ) R \ {0}), Injective (fun i ↦ r i b) := by
    intro b hb
    apply separable_prod_X_sub_C_iff.1
    apply (monic_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C (r i b))).discr_ne_zero_iff.1
    rw [← hP b (hsub hb), hdiscr b (hsub hb)]
    exact mul_ne_zero (pow_ne_zero _ hb.2.2) (hu0 b (hsub hb))
  obtain ⟨σ, hσ, -⟩ := existsUnique_root_rotation_perm hUc hR hζ.pow_eq_one
    (hζ.norm'_eq_one hN) (fun i ↦ (hr i).continuousOn) hinj hP ⟨x₀, hx₀⟩
  have hcap (x : E) (hx : x ∈ U) (i : Fin n) :
      min (N : ℕ∞) (analyticOrderAt (fun t ↦ r (σ i) (x, t) - r i (x, t)) 0) =
        min (N : ℕ∞) (analyticOrderAt (fun t ↦ r i (x, t) - r i (x, 0)) 0) := by
    have hi : AnalyticAt ℂ (fun t ↦ r i (x, t)) 0 :=
      (hr i (x, 0) ⟨hx, mem_ball_self hR⟩).curry_right
    have heq : (fun t ↦ r (σ i) (x, t) - r i (x, t)) =ᶠ[𝓝 0]
        (fun t ↦ r i (x, ζ * t) - r i (x, t)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with t ht
      rw [hσ i (x, t) ⟨hx, ht⟩]
    rw [analyticOrderAt_congr heq]
    exact hi.min_analyticOrderAt_comp_mul_sub hζ
  have hmem : ∀ᶠ b in 𝓝 (x₀, (0 : ℂ)), b ∈ U ×ˢ ball 0 R :=
    (hU.prod isOpen_ball).mem_nhds ⟨hx₀, mem_ball_self hR⟩
  -- The discriminant supplies constant orders for moved labels. Fixed labels have
  -- identically zero rotation difference and therefore contribute the cap itself.
  have hpair : ∀ᶠ x in 𝓝 x₀, ∀ i,
      analyticOrderAt (fun t ↦ r (σ i) (x, t) - r i (x, t)) 0 =
        analyticOrderAt (fun t ↦ r (σ i) (x₀, t) - r i (x₀, t)) 0 := by
    rw [eventually_all]
    intro i
    by_cases hi : σ i = i
    · simp [hi]
    · obtain ⟨b, v, hv, hv0, heq⟩ := exists_root_sub_eq_pow_mul_unit
        (fun j ↦ hr j (x₀, 0) ⟨hx₀, mem_ball_self hR⟩)
        (hmem.mono hP) hu (hu0 _ ⟨hx₀, mem_ball_self hR⟩)
        (by simpa only [sub_zero] using hmem.mono hdiscr) hi
      have hG := (hr (σ i) (x₀, 0) ⟨hx₀, mem_ball_self hR⟩).sub
        (hr i (x₀, 0) ⟨hx₀, mem_ball_self hR⟩)
      have horder := hG.eventually_analyticOrderAt_eq_natCast_iff.2
        ⟨v, hv, hv0, by simpa only [smul_eq_mul, Pi.sub_apply] using heq⟩
      exact horder.mono fun x hx ↦ hx.trans horder.self_of_nhds.symm
  filter_upwards [hU.mem_nhds hx₀, hpair] with x hx hp i
  rw [← hcap x hx i, ← hcap x₀ hx₀ i, hp i]

/-- All capped contacts of ramified branches with labelled roots on the hyperplane
are locally constant, including contacts between labels colliding there. Analyticity,
splitting, and the power-times-unit discriminant identity are only required as germs
at the central point. -/
theorem eventually_min_analyticOrderAt_root_sub_eq
    (hr : ∀ i, AnalyticAt ℂ (r i) (x₀, 0))
    (hP : ∀ᶠ b in 𝓝 (x₀, (0 : ℂ)), P (b.1, b.2 ^ N) = ∏ i, (X - C (r i b)))
    (hu : AnalyticAt ℂ u (x₀, 0)) (hu0 : u (x₀, 0) ≠ 0)
    (hdiscr : ∀ᶠ b in 𝓝 (x₀, (0 : ℂ)),
      (P (b.1, b.2 ^ N)).discr = b.2 ^ a * u b) :
    ∀ᶠ x in 𝓝 x₀, ∀ i j,
      min (N : ℕ∞) (analyticOrderAt (fun t ↦ r j (x, t) - r i (x, 0)) 0) =
        min (N : ℕ∞) (analyticOrderAt (fun t ↦ r j (x₀, t) - r i (x₀, 0)) 0) := by
  by_cases hN : N = 0
  · simp [hN]
  -- Shrink all germ hypotheses to one connected cylinder preserved by rotation.
  have hlocal : ∀ᶠ b in 𝓝 (x₀, (0 : ℂ)),
      (∀ i, AnalyticAt ℂ (r i) b) ∧
      P (b.1, b.2 ^ N) = ∏ i, (X - C (r i b)) ∧
      (P (b.1, b.2 ^ N)).discr = b.2 ^ a * u b ∧ u b ≠ 0 := by
    filter_upwards [eventually_all.2 (fun i ↦ (hr i).eventually_analyticAt),
      hP, hdiscr, hu.continuousAt.eventually_ne hu0] with b hb hPb hdb hub
    exact ⟨hb, hPb, hdb, hub⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hlocal
  rw [← ball_prod_same] at hball
  have hrel := eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    eventually_root_eq_iff_on_hyperplane hr hP hu hu0
      (by simpa only [sub_zero] using hdiscr) i j
  have hself := eventually_min_analyticOrderAt_root_sub_self_eq
    isOpen_ball (convex_ball x₀ ε).isPreconnected (mem_ball_self hε) hε hN
    (fun i b hb ↦ (hball b hb).1 i) (fun b hb ↦ (hball b hb).2.1) hu
    (fun b hb ↦ (hball b hb).2.2.2) (fun b hb ↦ (hball b hb).2.2.1)
  -- Persistent collisions reduce to self-contact; distinct central values have order zero.
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε), hrel, hself]
    with x hx hrelx hself i j
  by_cases hij : r i (x₀, 0) = r j (x₀, 0)
  · simp only [hrelx i j |>.2 hij, hij]
    exact hself j
  · have hxij : r i (x, 0) ≠ r j (x, 0) := (hrelx i j).not.2 hij
    have hi : AnalyticAt ℂ (fun t ↦ r j (x, t) - r i (x, 0)) 0 :=
      ((hball (x, 0) ⟨hx, mem_ball_self hε⟩).1 j).curry_right.sub analyticAt_const
    have hi₀ : AnalyticAt ℂ (fun t ↦ r j (x₀, t) - r i (x₀, 0)) 0 :=
      (hr j).curry_right.sub analyticAt_const
    rw [hi.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hxij.symm),
      hi₀.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (Ne.symm hij))]

end TauCeti
