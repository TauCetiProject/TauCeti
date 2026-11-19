/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
public import TauCeti.Analysis.Complex.Wirtinger.Root.Branch
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Analysis.Polynomial.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Collisions of the roots of the Newton coefficient equation are isolated

Let `b₁, …, b_m` be complex functions on an open set `U`, and let `R(y)` be the multiset of the `m`
roots of `P_y(W) = Wᵐ - b₁(y) W^(m-1) + ⋯ + (-1)ᵐ b_m(y)`, so that `b_j(y) = e_j(R(y))`. Suppose
the `b_j` solve the equation of the elementary symmetric functions of `m` solutions of a real
Cauchy–Riemann operator `D_C = \bar∂ + ν W + μ \bar W`,

`\bar∂ b_j + j ν b_j + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ = 0`,  `1 ≤ j ≤ m`,

the equation that `TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton` derives, up to a
remainder, for the Newton coefficients of the normal moments of a current concentrating along a
pseudoholomorphic curve. Where the roots are simple, they are the values of root branches solving
`D_C v = 0` (`TauCeti.exists_root_branch_conjWirtingerDeriv_add_add_eq_zero`). This file controls
the *collisions*, the points where two roots coincide.

The collisions are the zeros of the discriminant `Δ(y)` of `P_y`
(`Multiset.discr_prod_X_sub_C_ne_zero_iff`). Near a point with simple roots, `Δ` is, up to sign,
the product of the differences `v - v'` of distinct root branches
(`Multiset.prod_map_prod_map_sub_erase_eq_neg_one_pow_mul_discr`). The equation `D_C` is real
linear, so these differences solve it as well, and each satisfies
`|\bar∂ (v - v')| ≤ (‖ν‖ + ‖μ‖) |v - v'|`. Hence

`‖\bar∂ Δ‖ ≤ m (m - 1) (‖ν‖ + ‖μ‖) |Δ|`

at every point with simple roots (`TauCeti.norm_conjWirtingerDeriv_discr_le_of_nodup`). The
discriminant is a polynomial in the `b_j`, so it is `C¹` when they are
(`TauCeti.contDiffOn_discr_prod_X_sub_C`), and the inequality extends by continuity to the
collisions, where both sides vanish (`TauCeti.norm_conjWirtingerDeriv_discr_le`).

On a domain of the plane, a `C¹` function with `|\bar∂ Δ| ≤ C |Δ|` solves a linear Cauchy–Riemann
equation with a bounded coefficient, so by the similarity principle its zeros are isolated unless
it vanishes identically
(`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_norm_conjWirtingerDeriv_le`). Therefore, **if
the roots are simple at one point of a connected open set `U ⊆ ℂ`, they are simple off a discrete
subset of `U`** (`TauCeti.setOf_nodup_mem_codiscreteWithin`). Away from that discrete set the
root multigraph of `P` is a union of graphs of solutions of `D_C`, and the remaining collisions are
isolated points across which the branches are to be normalized. When two of the roots coincide on
all of `U`, for instance along a multiply covered component, the discriminant vanishes identically
and the statement is empty.

## Main results

* `TauCeti.norm_conjWirtingerDeriv_discr_le_of_nodup`,
  `TauCeti.norm_conjWirtingerDeriv_discr_le`: the differential inequality for the discriminant.
* `TauCeti.setOf_nodup_mem_codiscreteWithin`: the collisions are isolated.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle).
-/

public section

open Finset Filter Topology ComplexConjugate Polynomial MeasureTheory

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The differential inequality for the discriminant -/

/-- A difference of two solutions of `\bar∂ v + v ν + \bar v μ = 0` at `x` satisfies
`‖\bar∂ (v - v')(x)‖ ≤ (‖ν‖ + ‖μ‖) |v(x) - v'(x)|`. -/
private theorem norm_conjWirtingerDeriv_sub_le {v v' : V → ℂ} {x : V}
    (hv : DifferentiableAt ℝ v x) (hv' : DifferentiableAt ℝ v' x) (ν μ : V →L⋆[ℂ] ℂ)
    (hD : conjWirtingerDeriv v x + v x • ν + conj (v x) • μ = 0)
    (hD' : conjWirtingerDeriv v' x + v' x • ν + conj (v' x) • μ = 0) :
    ‖conjWirtingerDeriv (fun y ↦ v y - v' y) x‖ ≤ (‖ν‖ + ‖μ‖) * ‖v x - v' x‖ := by
  have h : conjWirtingerDeriv (fun y ↦ v y - v' y) x =
      -((v x - v' x) • ν + conj (v x - v' x) • μ) := by
    rw [conjWirtingerDeriv_fun_sub hv hv', map_sub]
    linear_combination (norm := module) hD - hD'
  rw [h, norm_neg]
  calc ‖(v x - v' x) • ν + conj (v x - v' x) • μ‖
      ≤ ‖v x - v' x‖ * ‖ν‖ + ‖v x - v' x‖ * ‖μ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Complex.norm_conj]
    _ = (‖ν‖ + ‖μ‖) * ‖v x - v' x‖ := by ring

/-- **The differential inequality for the discriminant at simple roots.** Let `b₁, …, b_m` be `C¹`
at `x`, with `b_j(y) = e_j(R(y))` for multisets `R(y)` of `m` points near `x`, and suppose that
near `x` the `b_j` solve the equation of the elementary symmetric functions of `m` solutions of
`D_C = \bar∂ + ν W + μ \bar W`. If the roots `R(x)` are simple, the discriminant
`Δ(y) = discr ∏_{w ∈ R(y)} (X - w)` satisfies

`‖\bar∂ Δ(x)‖ ≤ m (m - 1) (‖ν(x)‖ + ‖μ(x)‖) |Δ(x)|`. -/
theorem norm_conjWirtingerDeriv_discr_le_of_nodup [CompleteSpace V] {m : ℕ} {b : ℕ → V → ℂ}
    {R : V → Multiset ℂ} {x : V} (hb : ∀ j ∈ Icc 1 m, ContDiffAt ℝ 1 (b j) x)
    (hR : ∀ᶠ y in 𝓝 x, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hx : (R x).Nodup) (ν μ : V → V →L⋆[ℂ] ℂ)
    (heq : ∀ᶠ y in 𝓝 x, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ‖conjWirtingerDeriv (fun y ↦ ((R y).map fun w ↦ X - C w).prod.discr) x‖ ≤
      ((m * (m - 1) : ℕ) * (‖ν x‖ + ‖μ x‖)) * ‖((R x).map fun w ↦ X - C w).prod.discr‖ := by
  classical
  obtain ⟨v, hv, hRv⟩ :=
    exists_root_branches_conjWirtingerDeriv_add_add_eq_zero_of_nodup one_ne_zero hb hR hx ν μ heq
  set s : Finset ℂ := (R x).toFinset
  have hsval : s.val = R x := by rw [Multiset.toFinset_val, hx.dedup]
  have hcard : #s = m := by rw [← Finset.card_val, hsval, hR.self_of_nhds.1]
  have hv' : ∀ w ∈ s, _ := fun w hw ↦ hv w (by rwa [← Finset.mem_val, hsval] at hw)
  -- Near `x` the discriminant is, up to the sign `σ`, the product `F` of the differences of
  -- the branches.
  set σ : ℂ := (-1) ^ (m * (m - 1) / 2) with hσ
  set F : V → ℂ := fun y ↦ ∏ w ∈ s, ∏ u ∈ s.erase w, (v w y - v u y)
  have hΔ : (fun y ↦ ((R y).map fun w ↦ X - C w).prod.discr) =ᶠ[𝓝 x] σ • F := by
    filter_upwards [hRv] with y hRy
    have h := Finset.prod_prod_erase_sub_eq_neg_one_pow_mul_discr s fun w ↦ v w y
    rw [hcard, Finset.prod_eq_multiset_prod (f := fun w ↦ X - C (v w y))] at h
    rw [Pi.smul_apply, smul_eq_mul, hRy, ← hsval, Multiset.map_map, Function.comp_def]
    simp only [F]
    rw [h, ← mul_assoc, hσ, ← mul_pow]
    simp
  have hΔx : ((R x).map fun w ↦ X - C w).prod.discr = σ * F x := by
    simpa using hΔ.self_of_nhds
  -- Each difference `v w - v u` solves `D_C`, so the logarithmic derivative bound applies.
  have hvd : ∀ w ∈ s, DifferentiableAt ℝ (v w) x :=
    fun w hw ↦ ((hv' w hw).2.1).differentiableAt one_ne_zero
  have hdiff : ∀ w ∈ s, ∀ u ∈ s.erase w, DifferentiableAt ℝ (fun y ↦ v w y - v u y) x :=
    fun w hw u hu ↦ (hvd w hw).sub (hvd u (Finset.mem_of_mem_erase hu))
  have hinner : ∀ w ∈ s, DifferentiableAt ℝ (fun y ↦ ∏ u ∈ s.erase w, (v w y - v u y)) x :=
    fun w hw ↦ (HasFDerivAt.finsetProd fun u hu ↦ (hdiff w hw u hu).hasFDerivAt).differentiableAt
  set K : ℝ := ‖ν x‖ + ‖μ x‖
  have hinnerb : ∀ w ∈ s,
      ‖conjWirtingerDeriv (fun y ↦ ∏ u ∈ s.erase w, (v w y - v u y)) x‖ ≤
        ((m - 1 : ℕ) * K) * ‖∏ u ∈ s.erase w, (v w x - v u x)‖ := by
    intro w hw
    rw [← hcard, ← Finset.card_erase_of_mem hw]
    exact norm_conjWirtingerDeriv_finsetProd_le (hdiff w hw) fun u hu ↦
      norm_conjWirtingerDeriv_sub_le (hvd w hw) (hvd u (Finset.mem_of_mem_erase hu)) (ν x) (μ x)
        (hv' w hw).2.2.self_of_nhds (hv' u (Finset.mem_of_mem_erase hu)).2.2.self_of_nhds
  have hFb : ‖conjWirtingerDeriv F x‖ ≤ (#s * ((m - 1 : ℕ) * K)) * ‖F x‖ :=
    norm_conjWirtingerDeriv_finsetProd_le hinner hinnerb
  have hσn : ‖σ‖ = 1 := by rw [hσ, norm_pow, norm_neg, norm_one, one_pow]
  rw [hΔ.conjWirtingerDeriv_eq, conjWirtingerDeriv_const_smul, norm_smul, hσn, one_mul, hΔx,
    norm_mul, hσn, one_mul]
  calc ‖conjWirtingerDeriv F x‖ ≤ (m * ((m - 1 : ℕ) * K)) * ‖F x‖ := by rwa [hcard] at hFb
    _ = ((m * (m - 1) : ℕ) * K) * ‖F x‖ := by push_cast; ring

/-- **The differential inequality for the discriminant.** Let `U` be open, let `b₁, …, b_m` be
`C¹` on `U` with `b_j(y) = e_j(R(y))` for multisets `R(y)` of `m` points, and suppose that on `U`
the `b_j` solve the equation of the elementary symmetric functions of `m` solutions of
`D_C = \bar∂ + ν W + μ \bar W`, with `ν` and `μ` locally bounded. Then at every point `x` of `U`
the discriminant `Δ(y) = discr ∏_{w ∈ R(y)} (X - w)` satisfies

`‖\bar∂ Δ(x)‖ ≤ m (m - 1) (‖ν(x)‖ + ‖μ(x)‖) |Δ(x)|`.

At a collision both sides vanish: `\bar∂ Δ` is continuous and is bounded by a multiple of `|Δ|`
at the nearby points with simple roots. -/
theorem norm_conjWirtingerDeriv_discr_le [CompleteSpace V] {U : Set V} (hU : IsOpen U) {m : ℕ}
    {b : ℕ → V → ℂ} {R : V → Multiset ℂ} (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) U)
    (hR : ∀ y ∈ U, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    {ν μ : V → V →L⋆[ℂ] ℂ} (hν : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝 z, ‖ν w‖ ≤ M)
    (hμ : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝 z, ‖μ w‖ ≤ M)
    (heq : ∀ y ∈ U, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0)
    {x : V} (hx : x ∈ U) :
    ‖conjWirtingerDeriv (fun y ↦ ((R y).map fun w ↦ X - C w).prod.discr) x‖ ≤
      ((m * (m - 1) : ℕ) * (‖ν x‖ + ‖μ x‖)) * ‖((R x).map fun w ↦ X - C w).prod.discr‖ := by
  set Δ : V → ℂ := fun y ↦ ((R y).map fun w ↦ X - C w).prod.discr
  have hpt : ∀ y ∈ U, (R y).Nodup → ‖conjWirtingerDeriv Δ y‖ ≤
      ((m * (m - 1) : ℕ) * (‖ν y‖ + ‖μ y‖)) * ‖Δ y‖ := fun y hy hnd ↦
    norm_conjWirtingerDeriv_discr_le_of_nodup (fun j hj ↦ (hb j hj).contDiffAt (hU.mem_nhds hy))
      (eventually_of_mem (hU.mem_nhds hy) hR) hnd ν μ (eventually_of_mem (hU.mem_nhds hy) heq)
  by_cases hnd : (R x).Nodup
  · exact hpt x hx hnd
  -- At a collision `Δ(x) = 0`, and `\bar∂ Δ(x) = 0`.
  have hΔ0 : ∀ y, ¬ (R y).Nodup → Δ y = 0 := fun y hy ↦
    not_not.1 fun h ↦ hy ((Multiset.discr_prod_X_sub_C_ne_zero_iff (R y)).1 h)
  suffices h0 : conjWirtingerDeriv Δ x = 0 by
    rw [h0, norm_zero]
    positivity
  by_cases hloc : ∀ᶠ y in 𝓝 x, ¬ (R y).Nodup
  · have hΔe : Δ =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := hloc.mono fun y hy ↦ hΔ0 y hy
    rw [hΔe.conjWirtingerDeriv_eq]
    exact (differentiableAt_const _).conjWirtingerDeriv_eq_zero
  -- Otherwise points with simple roots accumulate at `x`, where `\bar∂ Δ = O(|Δ|)`.
  rw [not_eventually] at hloc
  simp only [not_not] at hloc
  obtain ⟨M₁, hM₁⟩ := hν x hx
  obtain ⟨M₂, hM₂⟩ := hμ x hx
  have hΔc : ContDiffOn ℝ 1 Δ U := contDiffOn_discr_prod_X_sub_C hb hR
  ext v
  by_contra hv
  set N : ℝ := (m * (m - 1) : ℕ) * (M₁ + M₂)
  have hcont : ContinuousAt (fun y ↦ ‖conjWirtingerDeriv Δ y v‖) x :=
    ((hΔc.conjWirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) v).continuousOn.continuousAt
      (hU.mem_nhds hx)).norm
  have hcontΔ : ContinuousAt (fun y ↦ N * ‖Δ y‖ * ‖v‖) x :=
    ((continuous_const.mul continuous_norm).continuousAt.comp
      (hΔc.continuousOn.continuousAt (hU.mem_nhds hx))).mul continuousAt_const
  have hlt : N * ‖Δ x‖ * ‖v‖ < ‖conjWirtingerDeriv Δ x v‖ := by
    rw [hΔ0 x hnd, norm_zero, mul_zero, zero_mul]
    exact norm_pos_iff.2 hv
  obtain ⟨y, hy, hylt, hyU, hy₁, hy₂⟩ :=
    (hloc.and_eventually ((hcontΔ.eventually_lt hcont hlt).and
      ((hU.eventually_mem hx).and (hM₁.and hM₂)))).exists
  have hle : ‖conjWirtingerDeriv Δ y v‖ ≤ N * ‖Δ y‖ * ‖v‖ :=
    calc ‖conjWirtingerDeriv Δ y v‖ ≤ ‖conjWirtingerDeriv Δ y‖ * ‖v‖ :=
          (conjWirtingerDeriv Δ y).le_opNorm v
      _ ≤ (((m * (m - 1) : ℕ) * (‖ν y‖ + ‖μ y‖)) * ‖Δ y‖) * ‖v‖ := by
          gcongr; exact hpt y hyU hy
      _ ≤ N * ‖Δ y‖ * ‖v‖ := by
          gcongr
          exact mul_le_mul_of_nonneg_left (add_le_add hy₁ hy₂) (Nat.cast_nonneg _)
  exact (hylt.trans_le hle).false

/-- **Collisions of roots are isolated.** Let `U ⊆ ℂ` be a connected open set, let
`b₁, …, b_m` be `C¹` on `U` with `b_j(y) = e_j(R(y))` for multisets `R(y)` of `m` points, and
suppose that on `U` the `b_j` solve the equation of the elementary symmetric functions of `m`
solutions of `D_C = \bar∂ + ν W + μ \bar W`,

`\bar∂ b_j + j ν b_j + (∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)) μ = 0`,  `1 ≤ j ≤ m`,

with `ν` and `μ` locally bounded. If the roots `R(y₀)` are simple at one point `y₀ ∈ U`, then
they are simple at every point of `U` outside a discrete subset. -/
theorem setOf_nodup_mem_codiscreteWithin {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {m : ℕ} {b : ℕ → ℂ → ℂ} {R : ℂ → Multiset ℂ} (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ 1 (b j) U)
    (hR : ∀ y ∈ U, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ} (hν : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝 z, ‖ν w‖ ≤ M)
    (hμ : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝 z, ‖μ w‖ ≤ M)
    (heq : ∀ y ∈ U, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0)
    (hne : ∃ y ∈ U, (R y).Nodup) :
    {y | (R y).Nodup} ∈ codiscreteWithin U := by
  obtain ⟨y₀, hy₀, hnd⟩ := hne
  have hiso := setOf_ne_zero_mem_codiscreteWithin_of_norm_conjWirtingerDeriv_le hU hUc
    (contDiffOn_discr_prod_X_sub_C hb hR) (K := fun z ↦ (m * (m - 1) : ℕ) * (‖ν z‖ + ‖μ z‖))
    (fun z hz ↦ ?_) (fun z hz ↦ norm_conjWirtingerDeriv_discr_le hU hb hR hν hμ heq hz)
    ⟨y₀, hy₀, (Multiset.discr_prod_X_sub_C_ne_zero_iff (R y₀)).2 hnd⟩
  · filter_upwards [hiso] with y hy
    exact (Multiset.discr_prod_X_sub_C_ne_zero_iff (R y)).1 hy
  obtain ⟨M₁, hM₁⟩ := hν z hz
  obtain ⟨M₂, hM₂⟩ := hμ z hz
  exact ⟨(m * (m - 1) : ℕ) * (M₁ + M₂), (hM₁.and hM₂).mono fun w hw ↦
    mul_le_mul_of_nonneg_left (add_le_add hw.1 hw.2) (Nat.cast_nonneg _)⟩

end TauCeti
