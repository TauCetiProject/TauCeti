/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Root.Branch
public import TauCeti.Analysis.Complex.Wirtinger.Weak
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Polynomial.Puiseux.PowerSubstitution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# Root branches of the Newton coefficient equation through a collision

Let `b₁, …, b_m` be `C¹` complex functions on a disc `ball x r` in `ℂ`, with `b_j(y) = e_j(R(y))`
for the multiset `R(y)` of the `m` roots of

`P_y(W) = Wᵐ - b₁(y) W^(m-1) + ⋯ + (-1)ᵐ b_m(y)`,

and suppose that they solve the equation of the elementary symmetric functions of `m` solutions of
`D_C = \bar∂ + ν W + μ \bar W`,

`\bar∂ b_j + j ν b_j + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ = 0`,  `1 ≤ j ≤ m`,

with continuous `(0,1)`-forms `ν`, `μ`. Where the roots are simple, the root multigraph
`{(y, w) : P_y(w) = 0}` is a union of graphs of solutions of `D_C`
(`TauCeti.exists_root_branch_conjWirtingerDeriv_add_add_eq_zero`). This file treats a point `x`
where roots may collide, assuming the roots are simple on the rest of the disc, and parametrizes
the roots there by continuous weak solutions of the pulled-back equation.

After the substitution `y = x + ζⁿ`, `n = m!`, the roots become `m` continuous functions `u_i` on a
disc about `ζ = 0` (`TauCeti.exists_root_branches_hasWeakConjWirtingerDerivOn`):

* `R(x + ζⁿ) = {u₁(ζ), …, u_m(ζ)}` with multiplicity, for every `ζ` in the disc, including `ζ = 0`,
  where the `u_i(0)` are the roots of `P_x` with their multiplicities;
* off `ζ = 0` each `u_i` is `C¹` and solves the pulled-back equation
  `\bar∂u + \overline{n ζ^(n-1)} (u ν(x + ζⁿ) + \bar u μ(x + ζⁿ)) = 0`;
* across `ζ = 0` each `u_i` is a continuous distributional solution of the same equation
  (`TauCeti.HasWeakConjWirtingerDerivOn`), whose coefficient is continuous on the whole disc.

So near the collision the root multigraph is the union of the images of finitely many continuous
maps `ζ ↦ (x + ζⁿ, u_i(ζ))` of a disc, each a distributional solution of a real-linear
Cauchy–Riemann equation with continuous coefficients, the kind of equation treated by the
similarity principle (`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn`). Grouping the
branches into orbits of the rotation `ζ ↦ e^(2πi/n) ζ`, and the regularity of the branches at the
centre beyond the distributional equation, are not treated here.

The proof first extends continuous roots over the punctured disc across the centre
(`TauCeti.Polynomial.exists_continuousOn_prod_X_sub_C_add_pow`). Off the centre a branch agrees
with the `C¹` branch through a simple root given by the implicit function theorem
(`TauCeti.exists_root_branch_conjWirtingerDeriv_add_add_eq_zero`), and the chain rule
`TauCeti.conjWirtingerDeriv_comp_eq_conj_smul` pulls its equation back along `ζ ↦ x + ζⁿ`.
The continuous branch acquires no point mass at the centre
(`TauCeti.HasWeakConjWirtingerDerivOn.of_diff_singleton`).

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Finset Filter Metric Polynomial Topology ComplexConjugate MeasureTheory

namespace TauCeti

variable {m : ℕ} {b : ℕ → ℂ → ℂ} {x : ℂ} {r : ℝ} {R : ℂ → Multiset ℂ}

/-- The coefficients of `∏_{w ∈ R(y)} (X - w)` are `±b_j(y)` or `±1`, hence continuous where the
`b_j` are. -/
private theorem continuousOn_coeff_prod_X_sub_C
    (hb : ∀ j ∈ Icc 1 m, ContinuousOn (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    {k : ℕ} (hk : k ≤ m) :
    ContinuousOn (fun y ↦ ((R y).map fun w ↦ X - C w).prod.coeff k) (ball x r) := by
  by_cases hmk : m - k = 0
  · refine continuousOn_const (c := (-1 : ℂ) ^ (m - k)).congr fun y hy ↦ ?_
    obtain ⟨hcard, -⟩ := hR y hy
    rw [Multiset.prod_X_sub_C_coeff (R y) (hcard ▸ hk), hcard, hmk]
    simp [Multiset.esymm]
  · refine ((continuousOn_const (c := (-1 : ℂ) ^ (m - k))).mul
      (hb (m - k) (mem_Icc.2 ⟨by omega, by omega⟩))).congr fun y hy ↦ ?_
    obtain ⟨hcard, hbR⟩ := hR y hy
    rw [Pi.mul_apply, Multiset.prod_X_sub_C_coeff (R y) (hcard ▸ hk), hcard,
      hbR (m - k) (mem_Icc.2 ⟨by omega, by omega⟩)]

/-- **A root branch off the collision solves the pulled-back equation.** Let `u` be continuous at
`ζ ≠ 0`, with `u(z)` a root of `P_(x + zⁿ)` for `z` near `ζ`, and let the roots be simple at
`x + ζⁿ ∈ ball x r`. Then `u` is `C¹` at `ζ` and solves
`\bar∂u + \overline{n ζ^(n-1)} (u ν(x + ζⁿ) + \bar u μ(x + ζⁿ)) = 0` there, the pullback of
`D_C u = 0` along `ζ ↦ x + ζⁿ`. -/
private theorem contDiffAt_and_conjWirtingerDeriv_add_smul_eq_zero {n : ℕ}
    (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) (ν μ : ℂ → ℂ →L⋆[ℂ] ℂ)
    (heq : ∀ y ∈ ball x r, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0)
    {u : ℂ → ℂ} {ζ : ℂ} (hζ : x + ζ ^ n ∈ ball x r) (hζ0 : ζ ≠ 0) (hu : ContinuousAt u ζ)
    (hroot : ∀ᶠ z in 𝓝 ζ, u z ∈ R (x + z ^ n)) :
    ContDiffAt ℝ 1 u ζ ∧ conjWirtingerDeriv u ζ +
      conj (n * ζ ^ (n - 1)) • (u ζ • ν (x + ζ ^ n) + conj (u ζ) • μ (x + ζ ^ n)) = 0 := by
  classical
  set h : ℂ → ℂ := fun z ↦ x + z ^ n
  have hnhds : ball x r ∈ 𝓝 (h ζ) := isOpen_ball.mem_nhds hζ
  have hne : h ζ ≠ x := by simpa [h] using pow_ne_zero n hζ0
  have hcount : (R (h ζ)).count (u ζ) = 1 :=
    Multiset.count_eq_one_of_mem (hsimple _ hζ hne) hroot.self_of_nhds
  -- the `C¹` branch through the simple root `u ζ` of `P_(h ζ)`
  obtain ⟨v, -, hvc, hgraph, hveq⟩ := exists_root_branch_conjWirtingerDeriv_add_add_eq_zero
    one_ne_zero (fun j hj ↦ (hb j hj).contDiffAt hnhds) (eventually_of_mem hnhds hR) hcount ν μ
    (eventually_of_mem hnhds heq)
  have hhc : Continuous h := by fun_prop
  -- near `ζ`, the root `u` is that branch composed with `h`
  have huv : u =ᶠ[𝓝 ζ] v ∘ h := by
    have hpair : Tendsto (fun z ↦ (h z, u z)) (𝓝 ζ) (𝓝 (h ζ, u ζ)) :=
      (hhc.tendsto ζ).prodMk_nhds hu
    filter_upwards [hpair.eventually hgraph, hroot, hhc.continuousAt.preimage_mem_nhds hnhds] with
      z hz hzR hzb
    refine (hz.1 ?_).symm
    obtain ⟨hcard, hbR⟩ := hR _ hzb
    rw [sum_congr rfl fun j hj ↦ by rw [hbR j hj],
      ← Multiset.prod_map_sub_eq_pow_add_sum_esymm hcard]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨u z, hzR, sub_self _⟩)
  have hderiv : HasDerivAt h (n * ζ ^ (n - 1)) ζ := (hasDerivAt_pow n ζ).const_add x
  refine ⟨(hvc.comp ζ (by fun_prop)).congr_of_eventuallyEq huv, ?_⟩
  -- the chain rule pulls `\bar∂v` back along `h`
  have hpull : conjWirtingerDeriv u ζ = conj (n * ζ ^ (n - 1)) • conjWirtingerDeriv v (h ζ) := by
    rw [huv.conjWirtingerDeriv_eq]
    exact conjWirtingerDeriv_comp_eq_conj_smul (hvc.differentiableAt one_ne_zero) hderiv
  -- the equation of `v` at `h ζ`, where `v (h ζ) = u ζ`
  have hv : conjWirtingerDeriv v (h ζ) = -(u ζ • ν (h ζ) + conj (u ζ) • μ (h ζ)) := by
    rw [huv.self_of_nhds, Function.comp_apply]
    exact eq_neg_of_add_eq_zero_left ((add_assoc _ _ _).symm.trans hveq.self_of_nhds)
  rw [hpull, hv]
  module

/-- The roots of `∏_{w ∈ R(y)} (X - w)` continue across the collision at `x` after the substitution
`y = x + ζⁿ`, `m! ∣ n`, as `m` continuous branches listing them with multiplicity. -/
private theorem exists_continuousOn_root_branches {n : ℕ} {R' : ℝ}
    (hb : ∀ j ∈ Icc 1 m, ContinuousOn (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) (hn : n ≠ 0) (hR'n : R' ^ n ≤ r)
    (hdvd : m.factorial ∣ n) :
    ∃ u : Fin m → ℂ → ℂ, (∀ i, ContinuousOn (u i) (ball 0 R')) ∧
      ∀ ζ ∈ ball (0 : ℂ) R', R (x + ζ ^ n) = univ.val.map fun i ↦ u i ζ := by
  have hmonic (y : ℂ) : ((R y).map fun w ↦ X - C w).prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun w _ ↦ monic_X_sub_C w
  obtain ⟨u, huc, huF, -⟩ := Polynomial.exists_continuousOn_prod_X_sub_C_add_pow
    (F := fun y ↦ ((R y).map fun w ↦ X - C w).prod) (c := x) (d := m)
    (fun k hk ↦ continuousOn_coeff_prod_X_sub_C hb hR hk) (fun y _ ↦ hmonic y)
    (fun y hy ↦ by
      rw [natDegree_multiset_prod_of_monic _ (by simp [monic_X_sub_C]), Multiset.map_map]
      simp [(hR y hy).1])
    (fun y hy hyx ↦ by
      rw [← nodup_roots_iff_of_splits (hmonic y).ne_zero (IsAlgClosed.splits _),
        roots_multiset_prod_X_sub_C]
      exact hsimple y hy hyx)
    hn hR'n hdvd
  refine ⟨u, huc, fun ζ hζ ↦ ?_⟩
  have h := congrArg Polynomial.roots (huF ζ hζ)
  have hmap : (univ.val.map fun i ↦ X - C (u i ζ)) =
      (univ.val.map fun i ↦ u i ζ).map fun w ↦ X - C w := by
    simp only [Multiset.map_map, Function.comp_def]
  rwa [roots_multiset_prod_X_sub_C, Finset.prod_eq_multiset_prod, hmap,
    roots_multiset_prod_X_sub_C] at h

/-- A continuous function on `ball 0 R'` that solves the pulled-back equation classically off the
centre solves it distributionally on `ball 0 (R' / 2)`, centre included: there its coefficient is
bounded and the centre is removable. -/
private theorem hasWeakConjWirtingerDerivOn_ball_half {n : ℕ} {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hν : ContinuousOn ν (ball x r)) (hμ : ContinuousOn μ (ball x r)) {R' : ℝ} (hR' : 0 < R')
    (hpow : Set.MapsTo (fun ζ : ℂ ↦ x + ζ ^ n) (ball 0 R') (ball x r)) {u : ℂ → ℂ}
    (hu : ContinuousOn u (ball 0 R'))
    (hcl : ∀ ζ ∈ ball (0 : ℂ) R', ζ ≠ 0 → ContDiffAt ℝ 1 u ζ ∧ conjWirtingerDeriv u ζ +
      conj (n * ζ ^ (n - 1)) • (u ζ • ν (x + ζ ^ n) + conj (u ζ) • μ (x + ζ ^ n)) = 0) :
    HasWeakConjWirtingerDerivOn volume ⟨ball 0 (R' / 2), isOpen_ball⟩ u fun ζ ↦
      -(conj (n * ζ ^ (n - 1)) * (u ζ * ν (x + ζ ^ n) 1 + conj (u ζ) * μ (x + ζ ^ n) 1)) := by
  set g : ℂ → ℂ := fun ζ ↦ -(conj (n * ζ ^ (n - 1)) * (u ζ * ν (x + ζ ^ n) 1 +
    conj (u ζ) * μ (x + ζ ^ n) 1))
  have hρ : ball (0 : ℂ) (R' / 2) ⊆ ball 0 R' := ball_subset_ball (half_le_self hR'.le)
  -- the coefficient is continuous on `ball 0 R'`, hence bounded on the closed half disc
  have hgc : ContinuousOn g (ball 0 R') := by
    have hν' := (continuous_eval_const 1).comp_continuousOn
      (hν.comp (Continuous.continuousOn (by fun_prop)) hpow)
    have hμ' := (continuous_eval_const 1).comp_continuousOn
      (hμ.comp (Continuous.continuousOn (by fun_prop)) hpow)
    exact ((Continuous.continuousOn (by fun_prop)).mul ((hu.mul hν').add
      ((Complex.continuous_conj.comp_continuousOn hu).mul hμ'))).neg
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (R' / 2)).exists_bound_of_continuousOn
    (hgc.mono (closedBall_subset_ball (half_lt_self hR')))
  have hg : MemLp g ⊤ (volume.restrict (ball 0 (R' / 2))) :=
    memLp_top_of_bound ((hgc.mono hρ).aestronglyMeasurable measurableSet_ball) M
      (ae_restrict_of_forall_mem measurableSet_ball fun z hz ↦ hM z (ball_subset_closedBall hz))
  refine HasWeakConjWirtingerDerivOn.of_diff_singleton (Ω := ⟨ball 0 (R' / 2), isOpen_ball⟩)
    (z₀ := 0) (p := ⊤) (q := 1) isBounded_ball (by norm_num) (hu.mono hρ) hg ?_
  -- off the centre, the classical equation is the distributional one
  refine (hasWeakConjWirtingerDerivOn_of_contDiffOn
    (Ω := ⟨ball (0 : ℂ) (R' / 2) \ {0}, isOpen_ball.sdiff isClosed_singleton⟩) fun z hz ↦
      (hcl z (hρ hz.1) hz.2).1.contDiffWithinAt).congr_ae_deriv
    ((ae_restrict_iff' ((isOpen_ball.sdiff isClosed_singleton).measurableSet)).2
      (Eventually.of_forall fun z (hz : z ∈ ball (0 : ℂ) (R' / 2) \ {0}) ↦ ?_))
  have h1 := congrArg (fun L : ℂ →L⋆[ℂ] ℂ ↦ L 1) (hcl z (hρ hz.1) hz.2).2
  simp only [add_apply, smul_apply, zero_apply, smul_eq_mul] at h1
  simp only [g]
  linear_combination h1

/-- **Normalization of the root multigraph across a collision.** Let `b₁, …, b_m` be `C¹` on the
disc `ball x r`, `r > 0`, with `b_j(y) = e_j(R(y))` for multisets `R(y)` of `m` points, simple
for `y ≠ x`, and let them solve the equation of the elementary symmetric functions of `m` solutions
of `D_C = \bar∂ + ν W + μ \bar W` with continuous `ν`, `μ`. Put `n = m!`. Then there are `ρ > 0`
and functions `u₁, …, u_m`, continuous on `ball 0 ρ`, such that

* `R(x + ζⁿ) = {u₁(ζ), …, u_m(ζ)}` for `ζ ∈ ball 0 ρ`;
* for `ζ ≠ 0` each `u_i` is `C¹` at `ζ` and solves the pulled-back equation
  `\bar∂u + \overline{n ζ^(n-1)} (u ν(x + ζⁿ) + \bar u μ(x + ζⁿ)) = 0`;
* each `u_i` solves the same equation distributionally on the whole disc `ball 0 ρ`, centre
  included, in the normalized form `\bar∂u(1) = -\overline{n ζ^(n-1)} (u ν(x + ζⁿ)(1) + \bar u
  μ(x + ζⁿ)(1))`. -/
theorem exists_root_branches_hasWeakConjWirtingerDerivOn (hr : 0 < r)
    (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hν : ContinuousOn ν (ball x r)) (hμ : ContinuousOn μ (ball x r))
    (heq : ∀ y ∈ ball x r, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ∃ ρ > 0, ∃ u : Fin m → ℂ → ℂ,
      (∀ ζ ∈ ball (0 : ℂ) ρ, R (x + ζ ^ m.factorial) = univ.val.map fun i ↦ u i ζ) ∧
      (∀ i, ContinuousOn (u i) (ball 0 ρ)) ∧
      (∀ i, ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → ContDiffAt ℝ 1 (u i) ζ ∧
        conjWirtingerDeriv (u i) ζ + conj (m.factorial * ζ ^ (m.factorial - 1)) •
          (u i ζ • ν (x + ζ ^ m.factorial) + conj (u i ζ) • μ (x + ζ ^ m.factorial)) = 0) ∧
      ∀ i, HasWeakConjWirtingerDerivOn volume ⟨ball 0 ρ, isOpen_ball⟩ (u i) fun ζ ↦
        -(conj (m.factorial * ζ ^ (m.factorial - 1)) * (u i ζ * ν (x + ζ ^ m.factorial) 1 +
          conj (u i ζ) * μ (x + ζ ^ m.factorial) 1)) := by
  set n := m.factorial
  have hn : n ≠ 0 := m.factorial_ne_zero
  -- a disc `ball 0 R'` mapped into `ball x r` by `ζ ↦ x + ζⁿ`
  set R' := min 1 r
  have hR' : 0 < R' := lt_min one_pos hr
  have hR'n : R' ^ n ≤ r :=
    (pow_le_of_le_one hR'.le (min_le_left _ _) hn).trans (min_le_right _ _)
  have hpow : Set.MapsTo (fun ζ : ℂ ↦ x + ζ ^ n) (ball 0 R') (ball x r) := fun ζ hζ ↦ by
    simpa [mem_ball_iff_norm] using mapsTo_pow_ball_zero hn hR'n hζ
  obtain ⟨u, huc, hroots⟩ := exists_continuousOn_root_branches
    (fun j hj ↦ (hb j hj).continuousOn) hR hsimple hn hR'n dvd_rfl
  -- off the centre, each branch solves the pulled-back equation classically
  have hcl (i : Fin m) (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) R') (hζ0 : ζ ≠ 0) :=
    contDiffAt_and_conjWirtingerDeriv_add_smul_eq_zero hb hR hsimple ν μ heq (hpow hζ) hζ0
      ((huc i).continuousAt (isOpen_ball.mem_nhds hζ))
      (eventually_of_mem (isOpen_ball.mem_nhds hζ) fun z hz ↦ by
        rw [hroots z hz]
        exact Multiset.mem_map_of_mem _ (mem_univ_val i))
  have hρ : ball (0 : ℂ) (R' / 2) ⊆ ball 0 R' := ball_subset_ball (half_le_self hR'.le)
  exact ⟨R' / 2, half_pos hR', u, fun ζ hζ ↦ hroots ζ (hρ hζ), fun i ↦ (huc i).mono hρ,
    fun i ζ hζ hζ0 ↦ hcl i ζ (hρ hζ) hζ0,
    fun i ↦ hasWeakConjWirtingerDerivOn_ball_half hν hμ hR' hpow (huc i) (hcl i)⟩

end TauCeti
