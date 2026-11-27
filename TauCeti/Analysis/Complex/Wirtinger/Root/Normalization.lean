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
import TauCeti.Analysis.Complex.RootsOfUnity.Descent
import TauCeti.Analysis.Complex.RootsOfUnity.Quotient
import TauCeti.Analysis.Polynomial.Puiseux.Contact
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex

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
similarity principle (`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn`).

**Branch multiplicities.** The rotation `ζ ↦ c ζ` by a primitive `n`-th root of unity `c` fixes
`x + ζⁿ`, so it permutes the branches: `u_(σ i)(ζ) = u_i(c ζ)` for a permutation `σ` of the labels,
the same on the whole disc because the roots are distinct off the centre
(`TauCeti.existsUnique_root_rotation_perm`). Along a cycle of `σ` of length `k`, the branch `u_a`
is invariant under the rotations by the `(n / k)`-th roots of unity, so it factors as
`u_a(ζ) = v(ζ^(n / k))` through its descent `v = TauCeti.descendPow (n / k) u_a`, which is
continuous because `ζ ↦ ζ^(n / k)` is an open map (`TauCeti.continuousOn_descendPow`). These
functions are the local branches of the
root multigraph at `x`, with the cycle lengths `k` as multiplicities
(`TauCeti.exists_eq_sum_map_nthRoots_hasWeakConjWirtingerDerivOn`):

* the multiplicities sum to `m`, and for `s` near `0` the roots `R(x + s)` are, with multiplicity,
  the values `v(t)` at the `k`-th roots `t` of `s` (`Polynomial.nthRoots`), over all branches;
* each branch `t ↦ (x + tᵏ, v(t))` is injective on its disc, and distinct branches meet only over
  `y = x`;
* each `v` is `C¹` off `t = 0` and solves `\bar∂v + \overline{k t^(k-1)} (v ν(x + tᵏ) +
  \bar v μ(x + tᵏ)) = 0` there, and it solves the same equation distributionally across `t = 0`.

So near the collision the root multigraph is the union of the images of finitely many injective
continuous maps `t ↦ (x + tᵏ, v(t))` of discs, disjoint off the fibre over `x`: its normalization
there. The regularity of the branches at the centre beyond the distributional equation is not
treated here.

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

/-! ### The branches grouped into orbits of the rotation -/

section Orbits

variable {n : ℕ} {ρ : ℝ} {c : ℂ} {u : Fin m → ℂ → ℂ} {σ : Equiv.Perm (Fin m)}

/-- Rotation by a primitive `n`-th root of unity `c` permutes continuous branches listing the roots
after the substitution `y = x + ζⁿ`, when they are distinct off the centre: there is a permutation
`σ` of the labels with `u_(σʲ i)(ζ) = u_i(cʲ ζ)` on the whole disc, centre included. -/
private theorem exists_perm_pow_apply_eq (hρ : 0 < ρ) (hc : IsPrimitiveRoot c n) (hn : n ≠ 0)
    (huc : ∀ i, ContinuousOn (u i) (ball 0 ρ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ)
    (hroots : ∀ ζ ∈ ball (0 : ℂ) ρ, R (x + ζ ^ n) = univ.val.map fun i ↦ u i ζ) :
    ∃ σ : Equiv.Perm (Fin m), ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ) := by
  classical
  have hcn : ‖c‖ = 1 := hc.norm'_eq_one hn
  obtain ⟨σ, hσ, -⟩ := existsUnique_root_rotation_perm (U := (Set.univ : Set Unit)) (N := n)
    (P := fun b ↦ ((R (x + b.2)).map fun w ↦ X - C w).prod) (r := fun i b ↦ u i b.2)
    isPreconnected_univ hρ hc.pow_eq_one hcn
    (fun i ↦ (huc i).comp continuous_snd.continuousOn fun b hb ↦ hb.2)
    (fun b hb ↦ hinj b.2 hb.2.1 hb.2.2)
    (fun b hb ↦ by
      simp only [hroots b.2 hb.2, Multiset.map_map, Function.comp_def, prod_eq_multiset_prod])
    ⟨(), Set.mem_univ _⟩
  refine ⟨σ, fun j ↦ ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    intro i ζ hζ
    have hcζ : c ^ j * ζ ∈ ball (0 : ℂ) ρ := by simpa [hcn] using hζ
    have h1 : u (σ i) (c ^ j * ζ) = u i (c * (c ^ j * ζ)) := hσ i ((), c ^ j * ζ) ⟨trivial, hcζ⟩
    rw [pow_succ, Equiv.Perm.mul_apply, ih (σ i) ζ hζ, h1, pow_succ', mul_assoc]

/-- Under a rotation of the labels as in `exists_perm_pow_apply_eq`, every label comes back to
itself after `n` rotations: the length `k` of its cycle divides `n`, and `k` and `n / k` are
positive. -/
private theorem minimalPeriod_dvd_and_pos (hρ : 0 < ρ) (hc : IsPrimitiveRoot c n) (hn : n ≠ 0)
    (hσ : ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ) (i : Fin m) :
    Function.minimalPeriod σ i ∣ n ∧ 0 < Function.minimalPeriod σ i ∧
      n / Function.minimalPeriod σ i ≠ 0 := by
  have hζ : ((ρ / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hk : Function.minimalPeriod σ i ∣ n :=
    (MulAction.pow_smul_eq_iff_minimalPeriod_dvd (a := σ) (b := i)).1 <|
    hinj _ hζ (by simpa using hρ.ne') (a₁ := (σ ^ n) i) (a₂ := i) (by
      simp only
      rw [hσ n i _ hζ, hc.pow_eq_one, one_mul])
  have hk0 := Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hn)
  exact ⟨hk, hk0, (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hk) hk0).ne'⟩

/-- Two parameters `ζ ≠ 0` and `ζ'` with the same `n`-th power differ by a rotation `cʲ`; if the
labels `a` and `a'` carry the same value at them, then `σʲ` carries `a'` to `a`. -/
private theorem exists_pow_apply_eq_of_apply_eq (hc : IsPrimitiveRoot c n) (hn : n ≠ 0)
    (hσ : ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ) {a a' : Fin m}
    {ζ ζ' : ℂ} (hζ : ζ ∈ ball (0 : ℂ) ρ) (hζ0 : ζ ≠ 0) (hpow : ζ' ^ n = ζ ^ n)
    (h : u a' ζ' = u a ζ) :
    ∃ j, (σ ^ j) a' = a ∧ ζ' = c ^ j * ζ := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨j, -, hj⟩ := hc.eq_pow_of_pow_eq_one (ξ := ζ' / ζ)
    (by rw [div_pow, hpow, div_self (pow_ne_zero _ hζ0)])
  have hζ' : ζ' = c ^ j * ζ := by rw [hj, div_mul_cancel₀ _ hζ0]
  refine ⟨j, hinj ζ hζ hζ0 (a₁ := (σ ^ j) a') (a₂ := a) ?_, hζ'⟩
  simp only
  rw [hσ j a' ζ hζ, ← hζ', h]

/-- **The branch of an orbit is invariant.** With `k` the length of the cycle of `a`, the branch
`u_a` is invariant under the rotations by the `(n / k)`-th roots of unity: they are the powers of
`cᵏ`, and `σᵏ` fixes `a`. So `u_a` descends through `ζ ↦ ζ^(n / k)` (`TauCeti.descendPow`). -/
private theorem apply_rootsOfUnity_smul_eq (hρ : 0 < ρ) (hc : IsPrimitiveRoot c n) (hn : n ≠ 0)
    (hσ : ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ) (a : Fin m)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) ρ) (ξ : rootsOfUnity (n / Function.minimalPeriod σ a) ℂ) :
    u a (ξ • ζ) = u a ζ := by
  obtain ⟨hk, -, hd⟩ := minimalPeriod_dvd_and_pos hρ hc hn hσ hinj a
  have : NeZero (n / Function.minimalPeriod σ a) := ⟨hd⟩
  -- `ξ` is a power of the primitive `(n / k)`-th root of unity `cᵏ`
  obtain ⟨j, -, hj⟩ := (hc.pow (Nat.pos_of_ne_zero hn) (Nat.mul_div_cancel' hk).symm)
    |>.eq_pow_of_pow_eq_one (ξ := ((ξ : ℂˣ) : ℂ))
    (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ξ.prop, Units.val_one])
  rw [Subgroup.smul_def, Units.smul_def, smul_eq_mul, ← hj, ← pow_mul, ← hσ _ _ _ hζ,
    ← Equiv.Perm.smul_def, (MulAction.pow_smul_eq_iff_minimalPeriod_dvd (a := σ) (b := a)
      (n := Function.minimalPeriod σ a * j)).2 (dvd_mul_right _ j)]

/-- The descended branch of `a` reads `u_a` on the disc `ball 0 ρⁿ`: each `t` there is `ζᵈ` for
some `ζ ∈ ball 0 ρ`, `d = n / k` with `k` the length of the cycle of `a`, and then `tᵏ = ζⁿ` and
the descended branch takes the value `u_a(ζ)` at `t`. -/
private theorem exists_pow_eq_descendPow (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : IsPrimitiveRoot c n)
    (hn : n ≠ 0) (hσ : ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ) (a : Fin m)
    [NeZero (n / Function.minimalPeriod σ a)] {t : ℂ} (ht : t ∈ ball (0 : ℂ) (ρ ^ n)) :
    ∃ ζ ∈ ball (0 : ℂ) ρ, ζ ^ (n / Function.minimalPeriod σ a) = t ∧
      t ^ Function.minimalPeriod σ a = ζ ^ n ∧
      descendPow (n / Function.minimalPeriod σ a) (u a) t = u a ζ := by
  have ht' : t ∈ (· ^ (n / Function.minimalPeriod σ a)) '' ball (0 : ℂ) ρ := by
    rw [image_pow_ball hρ.le]
    exact ball_subset_ball (pow_le_pow_of_le_one hρ.le hρ1 (Nat.div_le_self n _)) ht
  obtain ⟨ζ, hζ, rfl⟩ := ht'
  refine ⟨ζ, hζ, rfl, ?_, descendPow_pow (apply_rootsOfUnity_smul_eq hρ hc hn hσ hinj a hζ)⟩
  rw [← pow_mul, Nat.div_mul_cancel (minimalPeriod_dvd_and_pos hρ hc hn hσ hinj a).1]

/-- **The descended branches solve the pulled-back equation.** Let `u_i` be continuous branches
on `ball 0 ρ`, `0 < ρ ≤ min 1 r`, listing the roots `R(x + ζⁿ)` of the Newton coefficient
equation, with the roots simple off `x` and the labels rotated by `σ`. Then the descent `v` of
`u_a` through `ζ ↦ ζ^(n / k)`, for a label `a` whose cycle has length `k`, is continuous on
`ball 0 ρⁿ`; off `t = 0` it is `C¹` and solves
`\bar∂v + \overline{k t^(k-1)} (v ν(x + tᵏ) + \bar v μ(x + tᵏ)) = 0`, and it solves the same
equation distributionally on `ball 0 (ρⁿ / 2)`, centre included. -/
private theorem descendPow_hasWeakConjWirtingerDerivOn
    (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hν : ContinuousOn ν (ball x r)) (hμ : ContinuousOn μ (ball x r))
    (heq : ∀ y ∈ ball x r, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρr : ρ ≤ r) (hc : IsPrimitiveRoot c n) (hn : n ≠ 0)
    (huc : ∀ i, ContinuousOn (u i) (ball 0 ρ))
    (hroots : ∀ ζ ∈ ball (0 : ℂ) ρ, R (x + ζ ^ n) = univ.val.map fun i ↦ u i ζ)
    (hσ : ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ) (a : Fin m)
    [NeZero (n / Function.minimalPeriod σ a)] :
    letI v := descendPow (n / Function.minimalPeriod σ a) (u a)
    letI k := Function.minimalPeriod σ a
    ContinuousOn v (ball 0 (ρ ^ n)) ∧
      (∀ t ∈ ball (0 : ℂ) (ρ ^ n), t ≠ 0 → ContDiffAt ℝ 1 v t ∧
        conjWirtingerDeriv v t + conj (k * t ^ (k - 1)) •
          (v t • ν (x + t ^ k) + conj (v t) • μ (x + t ^ k)) = 0) ∧
      HasWeakConjWirtingerDerivOn volume ⟨ball 0 (ρ ^ n / 2), isOpen_ball⟩ v
        fun t ↦ -(conj (k * t ^ (k - 1)) *
          (v t * ν (x + t ^ k) 1 + conj (v t) * μ (x + t ^ k) 1)) := by
  obtain ⟨-, hk0, -⟩ := minimalPeriod_dvd_and_pos hρ hc hn hσ hinj a
  -- continuity: the branch `u_a` descends along the quotient map `ζ ↦ ζᵈ`
  have hvc :
      ContinuousOn (descendPow (n / Function.minimalPeriod σ a) (u a)) (ball 0 (ρ ^ n)) := by
    have := continuousOn_descendPow isOpen_ball (huc a) fun ζ hζ ↦
      apply_rootsOfUnity_smul_eq hρ hc hn hσ hinj a hζ
    rw [image_pow_ball hρ.le] at this
    exact this.mono (ball_subset_ball (pow_le_pow_of_le_one hρ.le hρ1 (Nat.div_le_self n _)))
  -- each value of the descended branch is a root
  have hmem : ∀ t ∈ ball (0 : ℂ) (ρ ^ n), descendPow (n / Function.minimalPeriod σ a) (u a) t ∈
      R (x + t ^ Function.minimalPeriod σ a) := fun t ht ↦ by
    obtain ⟨ζ, hζ, -, htk, hvζ⟩ := exists_pow_eq_descendPow hρ hρ1 hc hn hσ hinj a ht
    rw [hvζ, htk, hroots ζ hζ]
    exact Multiset.mem_map_of_mem _ (mem_univ_val a)
  have hpow : Set.MapsTo (fun t : ℂ ↦ x + t ^ Function.minimalPeriod σ a) (ball 0 (ρ ^ n))
      (ball x r) := fun t ht ↦ by
    have hle : (ρ ^ n) ^ Function.minimalPeriod σ a ≤ r :=
      (pow_le_of_le_one (by positivity) (pow_le_one₀ hρ.le hρ1) hk0.ne').trans
        ((pow_le_of_le_one hρ.le hρ1 hn).trans hρr)
    simpa [mem_ball_iff_norm] using mapsTo_pow_ball_zero hk0.ne' hle ht
  have hcl := fun t (ht : t ∈ ball (0 : ℂ) (ρ ^ n)) (ht0 : t ≠ 0) ↦
    contDiffAt_and_conjWirtingerDeriv_add_smul_eq_zero hb hR hsimple ν μ heq
      (hpow ht) ht0 (hvc.continuousAt (isOpen_ball.mem_nhds ht))
      (eventually_of_mem (isOpen_ball.mem_nhds ht) hmem)
  exact ⟨hvc, hcl, hasWeakConjWirtingerDerivOn_ball_half hν hμ (by positivity) hpow hvc hcl⟩

/-- **Distinct descended branches do not meet off the centre, and each is injective.** If the
descended branches of labels `a` and `a'` take the same value at points `t ≠ 0` and `t'` of
`ball 0 ρⁿ` with `tᵏ = t'ᵏ'`, for the cycle lengths `k` and `k'`, then `a` and `a'` lie on the
same cycle of `σ`, and if `a = a'` then `t = t'`. -/
private theorem sameCycle_and_eq_of_descendPow_eq (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hc : IsPrimitiveRoot c n) (hn : n ≠ 0)
    (hσ : ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ)
    [∀ i, NeZero (n / Function.minimalPeriod σ i)] {a a' : Fin m}
    {t t' : ℂ} (ht : t ∈ ball (0 : ℂ) (ρ ^ n)) (ht' : t' ∈ ball (0 : ℂ) (ρ ^ n)) (ht0 : t ≠ 0)
    (hpow : t' ^ Function.minimalPeriod σ a' = t ^ Function.minimalPeriod σ a)
    (h : descendPow (n / Function.minimalPeriod σ a') (u a') t' =
      descendPow (n / Function.minimalPeriod σ a) (u a) t) :
    σ.SameCycle a' a ∧ (a' = a → t' = t) := by
  obtain ⟨ζ, hζ, hζt, htζ, hvζ⟩ := exists_pow_eq_descendPow hρ hρ1 hc hn hσ hinj a ht
  obtain ⟨ζ', -, hζt', htζ', hvζ'⟩ := exists_pow_eq_descendPow hρ hρ1 hc hn hσ hinj a' ht'
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    exact ht0 ((pow_eq_zero_iff (minimalPeriod_dvd_and_pos hρ hc hn hσ hinj a).2.1.ne').1
      (htζ.trans (zero_pow hn)))
  obtain ⟨j, hj, hζ'⟩ := exists_pow_apply_eq_of_apply_eq hc hn hσ hinj hζ hζ0
    (by rw [← htζ', hpow, htζ]) (by rw [← hvζ', ← hvζ, h])
  refine ⟨⟨j, by simpa using hj⟩, fun haa ↦ ?_⟩
  subst haa
  -- `σʲ` fixes `a`, so `j` is a multiple of the cycle length `k` and `cʲ` is a `d`-th root of 1
  obtain ⟨l, rfl⟩ : Function.minimalPeriod σ a' ∣ j :=
    (MulAction.pow_smul_eq_iff_minimalPeriod_dvd (a := σ) (b := a')).1 hj
  set k := Function.minimalPeriod σ a'
  have hcl : (c ^ (k * l) * ζ) ^ (n / k) = (c ^ (k * (n / k))) ^ l * ζ ^ (n / k) := by ring
  rw [← hζt', ← hζt, hζ', hcl,
    Nat.mul_div_cancel' (minimalPeriod_dvd_and_pos hρ hc hn hσ hinj a').1, hc.pow_eq_one,
    one_pow, one_mul]

/-- **The descended branches list the roots.** For `ζ ∈ ball 0 ρ`, the roots `R(x + ζⁿ)` are,
with multiplicity, the values of the descended branches at the `k`-th roots of `ζⁿ`, over the
cycles of `σ` with representatives `q.out` and lengths `k`. -/
private theorem eq_sum_map_nthRoots_descendPow
    [Fintype (Quotient (Equiv.Perm.SameCycle.setoid σ))]
    (hρ : 0 < ρ) (hc : IsPrimitiveRoot c n) (hn : n ≠ 0)
    (hroots : ∀ ζ ∈ ball (0 : ℂ) ρ, R (x + ζ ^ n) = univ.val.map fun i ↦ u i ζ)
    (hσ : ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ))
    (hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ)
    [∀ i, NeZero (n / Function.minimalPeriod σ i)] {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) ρ) :
    R (x + ζ ^ n) = ∑ q : Quotient (Equiv.Perm.SameCycle.setoid σ),
      (nthRoots (Function.minimalPeriod σ q.out) (ζ ^ n)).map
        (descendPow (n / Function.minimalPeriod σ q.out) (u q.out)) := by
  have hsum {ι : Type} (s : Finset ι) (f : ι → ℂ) :
      ∑ i ∈ s, ({f i} : Multiset ℂ) = s.val.map f := by
    rw [sum_eq_multiset_sum, ← Multiset.sum_map_singleton (s.val.map f), Multiset.map_map,
      Function.comp_def]
  rw [hroots ζ hζ, ← hsum, ← σ.sum_quotient_sameCycle_sum_range]
  refine sum_congr rfl fun q _ ↦ ?_
  have hk := (minimalPeriod_dvd_and_pos hρ hc hn hσ hinj q.out).1
  set k := Function.minimalPeriod σ q.out
  have hnk : n = n / k * k := (Nat.div_mul_cancel hk).symm
  rw [(hc.pow (Nat.pos_of_ne_zero hn) hnk).nthRoots_eq (α := ζ ^ (n / k))
    (by rw [← pow_mul, ← hnk]), Multiset.map_map, hsum, range_val]
  refine Multiset.map_congr rfl fun j _ ↦ ?_
  have hcζ : c ^ j * ζ ∈ ball (0 : ℂ) ρ := by simpa [hc.norm'_eq_one hn] using hζ
  have hpow : (c ^ (n / k)) ^ j * ζ ^ (n / k) = (c ^ j * ζ) ^ (n / k) := by ring
  rw [Function.comp_apply, hpow,
    descendPow_pow (apply_rootsOfUnity_smul_eq hρ hc hn hσ hinj _ hcζ), hσ j _ ζ hζ]

/-- The setting of the orbit branches: for `n = m!` there are continuous branches `u_i` on
`ball 0 ρ`, `0 < ρ ≤ min 1 r`, listing the roots `R(x + ζⁿ)`, distinct off the centre, and a
permutation `σ` of their labels through which the rotation `ζ ↦ c ζ` by a primitive `n`-th root of
unity `c` acts: `u_(σʲ i)(ζ) = u_i(cʲ ζ)`. -/
private theorem exists_perm_root_branches (hr : 0 < r)
    (hb : ∀ j ∈ Icc 1 m, ContinuousOn (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) :
    ∃ ρ > 0, ρ ≤ 1 ∧ ρ ≤ r ∧ ∃ c : ℂ, IsPrimitiveRoot c m.factorial ∧
      ∃ (u : Fin m → ℂ → ℂ) (σ : Equiv.Perm (Fin m)), (∀ i, ContinuousOn (u i) (ball 0 ρ)) ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ, R (x + ζ ^ m.factorial) = univ.val.map fun i ↦ u i ζ) ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ) ∧
      ∀ j i, ∀ ζ ∈ ball (0 : ℂ) ρ, u ((σ ^ j) i) ζ = u i (c ^ j * ζ) := by
  set n := m.factorial
  have hn : n ≠ 0 := m.factorial_ne_zero
  set ρ := min 1 r
  have hρ : 0 < ρ := lt_min one_pos hr
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρn : ρ ^ n ≤ r := (pow_le_of_le_one hρ.le hρ1 hn).trans (min_le_right _ _)
  obtain ⟨u, huc, hroots⟩ := exists_continuousOn_root_branches hb hR hsimple hn hρn dvd_rfl
  -- the roots are simple off the centre, so the branches take distinct values there
  have hinj : ∀ ζ ∈ ball (0 : ℂ) ρ, ζ ≠ 0 → Function.Injective fun i ↦ u i ζ := by
    intro ζ hζ hζ0 i j hij
    have hy : x + ζ ^ n ∈ ball x r := by
      simpa [mem_ball_iff_norm] using mapsTo_pow_ball_zero hn hρn hζ
    have hnd := hsimple _ hy (by simpa using pow_ne_zero n hζ0)
    rw [hroots ζ hζ] at hnd
    exact Multiset.inj_on_of_nodup_map hnd i (mem_univ_val i) j (mem_univ_val j) hij
  have hc := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨σ, hσ⟩ := exists_perm_pow_apply_eq hρ hc hn huc hinj hroots
  exact ⟨ρ, hρ, hρ1, min_le_right _ _, _, hc, u, σ, huc, hroots, hinj, hσ⟩

/-- **Normalization of the root multigraph across a collision, with branch multiplicities.** Let
`b₁, …, b_m` be `C¹` on the disc `ball x r`, `r > 0`, with `b_j(y) = e_j(R(y))` for multisets
`R(y)` of `m` points, simple for `y ≠ x`, and let them solve the equation of the elementary
symmetric functions of `m` solutions of `D_C = \bar∂ + ν W + μ \bar W` with continuous `ν`, `μ`.
Then near `x` the root multigraph `{(y, w) : w ∈ R(y)}` is parametrized by finitely many local
branches `t ↦ (x + t^(kₐ), vₐ(t))` on a disc `ball 0 δ`, with multiplicities `kₐ ≥ 1` summing
to `m`:

* for `s` in a disc `ball 0 ε`, `R(x + s)` is, with multiplicity, the multiset of the values
  `vₐ(t)` at the `kₐ`-th roots `t` of `s`, over all branches `a`, and these roots lie in `ball 0 δ`;
* each branch parametrization `t ↦ (t^(kₐ), vₐ(t))` is injective on `ball 0 δ`, and the
  parametrizations of distinct branches meet only over `s = 0`;
* each `vₐ` is continuous on `ball 0 δ`, and off `t = 0` it is `C¹` and solves the pulled-back
  equation `\bar∂v + \overline{kₐ t^(kₐ-1)} (v ν(x + t^(kₐ)) + \bar v μ(x + t^(kₐ))) = 0`;
* each `vₐ` solves the same equation distributionally on the whole disc `ball 0 δ`, centre
  included.

The branches are the orbits of the rotation `ζ ↦ e^(2πi/m!) ζ` on the `m` branches of
`TauCeti.exists_root_branches_hasWeakConjWirtingerDerivOn`, and `kₐ` is the length of an orbit:
the number of sheets of the root multigraph over `ball x ε` that come together at `x` along the
branch `a`. -/
theorem exists_eq_sum_map_nthRoots_hasWeakConjWirtingerDerivOn (hr : 0 < r)
    (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) (ball x r))
    (hR : ∀ y ∈ ball x r, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hsimple : ∀ y ∈ ball x r, y ≠ x → (R y).Nodup) {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hν : ContinuousOn ν (ball x r)) (hμ : ContinuousOn μ (ball x r))
    (heq : ∀ y ∈ ball x r, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (k : ι → ℕ) (v : ι → ℂ → ℂ), ∃ ε > 0, ∃ δ > 0,
      (∀ a, 0 < k a) ∧ ∑ a, k a = m ∧
      (∀ s ∈ ball (0 : ℂ) ε, R (x + s) = ∑ a, (nthRoots (k a) s).map (v a)) ∧
      (∀ a, ∀ s ∈ ball (0 : ℂ) ε, ∀ t ∈ nthRoots (k a) s, t ∈ ball (0 : ℂ) δ) ∧
      (∀ a, Set.InjOn (fun t ↦ (t ^ k a, v a t)) (ball 0 δ)) ∧
      (∀ a a', a ≠ a' → ∀ t ∈ ball (0 : ℂ) δ, ∀ t' ∈ ball (0 : ℂ) δ, t ≠ 0 →
        (t ^ k a, v a t) ≠ (t' ^ k a', v a' t')) ∧
      (∀ a, ContinuousOn (v a) (ball 0 δ)) ∧
      (∀ a, ∀ t ∈ ball (0 : ℂ) δ, t ≠ 0 → ContDiffAt ℝ 1 (v a) t ∧
        conjWirtingerDeriv (v a) t + conj (k a * t ^ (k a - 1)) •
          (v a t • ν (x + t ^ k a) + conj (v a t) • μ (x + t ^ k a)) = 0) ∧
      ∀ a, HasWeakConjWirtingerDerivOn volume ⟨ball 0 δ, isOpen_ball⟩ (v a) fun t ↦
        -(conj (k a * t ^ (k a - 1)) * (v a t * ν (x + t ^ k a) 1 +
          conj (v a t) * μ (x + t ^ k a) 1)) := by
  classical
  have hn : m.factorial ≠ 0 := m.factorial_ne_zero
  obtain ⟨ρ, hρ, hρ1, hρr, c, hc, u, σ, huc, hroots, hinj, hσ⟩ :=
    exists_perm_root_branches hr (fun j hj ↦ (hb j hj).continuousOn) hR hsimple
  set n := m.factorial
  -- the descended branches on `ball 0 δ`, `δ = ρⁿ / 2`
  have hper (i : Fin m) := minimalPeriod_dvd_and_pos hρ hc hn hσ hinj i
  have (i : Fin m) : NeZero (n / Function.minimalPeriod σ i) := ⟨(hper i).2.2⟩
  set δ := ρ ^ n / 2
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := (half_le_self (by positivity)).trans (pow_le_one₀ hρ.le hρ1)
  have hδρ : ball (0 : ℂ) δ ⊆ ball 0 (ρ ^ n) := ball_subset_ball (half_le_self (by positivity))
  have hbr (a : Fin m) := descendPow_hasWeakConjWirtingerDerivOn hb hR hsimple hν hμ heq hρ hρ1
    hρr hc hn huc hroots hσ hinj a
  refine ⟨Quotient (Equiv.Perm.SameCycle.setoid σ), inferInstance,
    fun q ↦ Function.minimalPeriod σ q.out,
    fun q ↦ descendPow (n / Function.minimalPeriod σ q.out) (u q.out),
    δ ^ (m + 1), by positivity, δ, hδ, fun q ↦ (hper q.out).2.1, ?_,
    fun s hs ↦ ?_, fun q s hs t ht ↦ ?_, fun q t ht t' ht' htt' ↦ ?_,
    fun q q' hqq' t ht t' ht' ht0 htt' ↦ ?_, fun q ↦ (hbr q.out).1.mono hδρ,
    fun q t ht ↦ (hbr q.out).2.1 t (hδρ ht), fun q ↦ (hbr q.out).2.2⟩
  · -- the multiplicities are the lengths of the cycles of `σ`, which partition the `m` labels
    simpa using σ.sum_quotient_sameCycle_sum_range fun _ ↦ (1 : ℕ)
  · -- each `s` near `0` is `ζⁿ` for some `ζ ∈ ball 0 ρ`
    have hs' : s ∈ (· ^ n) '' ball (0 : ℂ) ρ := by
      have : NeZero n := ⟨hn⟩
      rw [image_pow_ball hρ.le]
      refine ball_subset_ball ?_ hs
      exact (pow_le_of_le_one hδ.le hδ1 (Nat.succ_ne_zero m)).trans (half_le_self (by positivity))
    obtain ⟨ζ, hζ, rfl⟩ := hs'
    exact eq_sum_map_nthRoots_descendPow hρ hc hn hroots hσ hinj hζ
  · -- a `k`-th root of `s ∈ ball 0 δ^(m + 1)`, `k ≤ m`, lies in `ball 0 δ`
    have hk0 := (hper q.out).2.1
    rw [mem_nthRoots hk0] at ht
    rw [mem_ball_zero_iff] at hs ⊢
    rw [← ht, norm_pow] at hs
    exact (pow_lt_pow_iff_left₀ (norm_nonneg t) hδ.le hk0.ne').1
      (hs.trans_le (pow_le_pow_of_le_one hδ.le hδ1
        (Function.minimalPeriod_le_card.trans_eq (Fintype.card_fin m) |>.trans m.le_succ)))
  · -- injectivity of a single branch: off the centre by the cycle structure
    obtain ⟨hpow, hv⟩ := Prod.ext_iff.1 htt'
    rcases eq_or_ne t 0 with rfl | ht0
    · have hk0 := (hper q.out).2.1
      exact ((pow_eq_zero_iff hk0.ne').1 (hpow.symm.trans (zero_pow hk0.ne'))).symm
    exact ((sameCycle_and_eq_of_descendPow_eq hρ hρ1 hc hn hσ hinj (hδρ ht) (hδρ ht') ht0
      hpow.symm hv.symm).2 rfl).symm
  · -- distinct branches lie over distinct cycles
    obtain ⟨hpow, hv⟩ := Prod.ext_iff.1 htt'
    exact hqq' (Quotient.out_equiv_out.1 (sameCycle_and_eq_of_descendPow_eq hρ hρ1 hc hn hσ hinj
      (hδρ ht) (hδρ ht') ht0 hpow.symm hv.symm).1.symm)

end Orbits

end TauCeti
