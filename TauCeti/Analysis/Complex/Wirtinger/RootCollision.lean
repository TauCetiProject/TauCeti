/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
public import TauCeti.Analysis.Complex.Wirtinger.RootBranch
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Analysis.Calculus.ContDiff.Matrix
import TauCeti.Analysis.Complex.Wirtinger.FinsetProd
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Vieta

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
isolated points across which the branches are to be normalized. When the roots coincide
everywhere, as for a multiply covered curve, the discriminant vanishes identically and the
statement is empty.

## Main results

* `TauCeti.contDiffOn_discr_prod_X_sub_C`: the discriminant is as regular as the coefficients.
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

/-! ### Regularity of the discriminant -/

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An entry of the Sylvester matrix of two families of polynomials whose coefficients are `C^n`
on a set is `C^n` there. -/
private theorem contDiffOn_sylvester_apply {n : WithTop ℕ∞} {s : Set E} {f g : E → ℂ[X]}
    (hf : ∀ k, ContDiffOn ℝ n (fun y ↦ (f y).coeff k) s)
    (hg : ∀ k, ContDiffOn ℝ n (fun y ↦ (g y).coeff k) s) (p q : ℕ) (i j : Fin (p + q)) :
    ContDiffOn ℝ n (fun y ↦ sylvester (f y) (g y) p q i j) s := by
  induction j using Fin.addCases with
  | left j =>
    by_cases h : (i : ℕ) ∈ Set.Icc (j : ℕ) (j + q)
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_left, h, ↓reduceIte] using hg _
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_left, h, ↓reduceIte] using
        contDiffOn_const
  | right j =>
    by_cases h : (i : ℕ) ∈ Set.Icc (j : ℕ) (j + p)
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_right, h, ↓reduceIte] using hf _
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_right, h, ↓reduceIte] using
        contDiffOn_const

/-- **Regularity of the discriminant.** If `b₁, …, b_m` are `C^n` on `s` and `b_j(y) = e_j(R(y))`
for a multiset `R(y)` of `m` points, then the discriminant of `∏_{w ∈ R(y)} (X - w)` is `C^n` on
`s`. It is a polynomial in the coefficients of that product, which are `±b_j` and `1`. -/
theorem contDiffOn_discr_prod_X_sub_C {n : WithTop ℕ∞} {s : Set E} {m : ℕ} {b : ℕ → E → ℂ}
    {R : E → Multiset ℂ} (hb : ∀ j ∈ Icc 1 m, ContDiffOn ℝ n (b j) s)
    (hR : ∀ y ∈ s, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j) :
    ContDiffOn ℝ n (fun y ↦ ((R y).map fun w ↦ X - C w).prod.discr) s := by
  set P : E → ℂ[X] := fun y ↦ ((R y).map fun w ↦ X - C w).prod with hP
  -- The coefficients of `P y`, read off Vieta's formulas.
  set c : ℕ → E → ℂ := fun k y ↦
    if k < m then (-1) ^ (m - k) * b (m - k) y else if k = m then 1 else 0 with hc
  have hcd : ∀ k, ContDiffOn ℝ n (c k) s := by
    intro k
    by_cases hk : k < m
    · simpa only [hc, hk, ↓reduceIte] using
        contDiffOn_const.mul (hb (m - k) (mem_Icc.2 ⟨by omega, by omega⟩))
    · by_cases hk' : k = m
      · simpa only [hc, hk, hk', ↓reduceIte, lt_irrefl] using contDiffOn_const
      · simpa only [hc, hk, hk', ↓reduceIte] using contDiffOn_const
  have hPc : ∀ y ∈ s, ∀ k, (P y).coeff k = c k y := by
    intro y hy k
    obtain ⟨hcard, hbR⟩ := hR y hy
    by_cases hk : k ≤ m
    · rw [hP, Multiset.prod_X_sub_C_coeff _ (hcard ▸ hk), hcard]
      rcases hk.lt_or_eq with hk | rfl
      · simp only [hc, hk, ↓reduceIte, hbR (m - k) (mem_Icc.2 ⟨by omega, by omega⟩)]
      · simp [hc]
    · rw [coeff_eq_zero_of_natDegree_lt (by
        rw [hP, natDegree_multiset_prod_X_sub_C_eq_card, hcard]; omega)]
      simp [hc, show ¬k < m by omega, show k ≠ m by omega]
  have hPd : ∀ k, ContDiffOn ℝ n (fun y ↦ (P y).coeff k) s :=
    fun k ↦ (hcd k).congr fun y hy ↦ hPc y hy k
  have hP'd : ∀ k, ContDiffOn ℝ n (fun y ↦ (P y).derivative.coeff k) s := fun k ↦ by
    simpa only [coeff_derivative] using (hPd (k + 1)).mul contDiffOn_const
  -- The discriminant of the monic `P y` is a sign times the resultant of `P y` and its derivative.
  have hdiscr : ∀ y ∈ s, (P y).discr =
      (-1) ^ (m * (m - 1) / 2) * (sylvester (P y) (P y).derivative m (m - 1)).det := by
    intro y hy
    have hmon : (P y).Monic := monic_multisetProd_X_sub_C (R y)
    have hdeg : (P y).natDegree = m := by
      rw [hP, natDegree_multiset_prod_X_sub_C_eq_card, (hR y hy).1]
    have h := hmon.resultant_deriv
    rw [hdeg] at h
    have hsq : ((-1 : ℂ) ^ (m * (m - 1) / 2)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    calc (P y).discr = ((-1 : ℂ) ^ (m * (m - 1) / 2)) ^ 2 * (P y).discr := by rw [hsq, one_mul]
      _ = (-1) ^ (m * (m - 1) / 2) * ((-1) ^ (m * (m - 1) / 2) * (P y).discr) := by ring
      _ = _ := by rw [← h, resultant]
  exact (contDiffOn_const.mul (ContDiffOn.matrix_det fun i j ↦
    contDiffOn_sylvester_apply hPd hP'd m (m - 1) i j)).congr hdiscr

end Regularity

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
    rw [show (fun y ↦ v y - v' y) = v - v' from rfl, conjWirtingerDeriv_sub hv hv', map_sub]
    linear_combination (norm := module) hD - hD'
  rw [h, norm_neg]
  calc ‖(v x - v' x) • ν + conj (v x - v' x) • μ‖
      ≤ ‖v x - v' x‖ * ‖ν‖ + ‖v x - v' x‖ * ‖μ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Complex.norm_conj]
    _ = (‖ν‖ + ‖μ‖) * ‖v x - v' x‖ := by ring

/-- **Root branches near simple roots.** Let `b₁, …, b_m` be `C¹` at `x`, with `b_j(y) = e_j(R(y))`
for multisets `R(y)` of `m` points near `x`, solving near `x` the equation of the elementary
symmetric functions of `m` solutions of `D_C = \bar∂ + ν W + μ \bar W`. If `R(x)` has no repeated
point, there are functions `v w`, one through each root `w ∈ R(x)`, which are `C¹` at `x`, solve
`D_C (v w) = 0` near `x`, and list the roots near `x`: `R(y) = {v w (y) | w ∈ R(x)}`. -/
private theorem exists_root_branches_of_nodup [CompleteSpace V] {m : ℕ} {b : ℕ → V → ℂ}
    {R : V → Multiset ℂ} {x : V} (hb : ∀ j ∈ Icc 1 m, ContDiffAt ℝ 1 (b j) x)
    (hR : ∀ᶠ y in 𝓝 x, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j)
    (hx : (R x).Nodup) (ν μ : V → V →L⋆[ℂ] ℂ)
    (heq : ∀ᶠ y in 𝓝 x, ∀ j ∈ Icc 1 m, conjWirtingerDeriv (b j) y + (j * b j y) • ν y +
      ((R y).map fun w ↦ conj w * ((R y).erase w).esymm (j - 1)).sum • μ y = 0) :
    ∃ v : ℂ → V → ℂ, (∀ w ∈ R x, v w x = w ∧ ContDiffAt ℝ 1 (v w) x ∧
      ∀ᶠ y in 𝓝 x, conjWirtingerDeriv (v w) y + v w y • ν y + conj (v w y) • μ y = 0) ∧
      ∀ᶠ y in 𝓝 x, R y = (R x).map fun w ↦ v w y := by
  classical
  -- Through each root `w` passes a root branch `v w` solving `D_C (v w) = 0` near `x`.
  have hbr : ∀ w ∈ R x, ∃ v : V → ℂ, v x = w ∧ ContDiffAt ℝ 1 v x ∧
      (∀ᶠ p in 𝓝 (x, w),
        p.2 ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j p.1 * p.2 ^ (m - j) = 0 ↔ v p.1 = p.2) ∧
      ∀ᶠ y in 𝓝 x, conjWirtingerDeriv v y + v y • ν y + conj (v y) • μ y = 0 :=
    fun w hw ↦ exists_root_branch_conjWirtingerDeriv_add_add_eq_zero one_ne_zero hb hR
      (Multiset.count_eq_one_of_mem hx hw) ν μ heq
  choose! v hvx hvc hgraph hvD using hbr
  refine ⟨v, fun w hw ↦ ⟨hvx w hw, hvc w hw, hvD w hw⟩, ?_⟩
  set s : Finset ℂ := (R x).toFinset
  have hsval : s.val = R x := by rw [Multiset.toFinset_val, hx.dedup]
  -- Near `x`, every branch value is a root.
  have hall : ∀ w ∈ s, ∀ᶠ y in 𝓝 x,
      v w y ^ m + ∑ j ∈ Icc 1 m, (-1) ^ j * b j y * v w y ^ (m - j) = 0 := fun w hw ↦ by
    rw [← Finset.mem_val, hsval] at hw
    have hc : Tendsto (v w) (𝓝 x) (𝓝 w) := by
      simpa only [hvx w hw] using (hvc w hw).continuousAt.tendsto
    exact ((tendsto_id.prodMk_nhds hc).eventually (hgraph w hw)).mono fun y hy ↦ hy.2 rfl
  -- Near `x`, distinct branches take distinct values.
  have hdist : ∀ w ∈ s, ∀ u ∈ s, ∀ᶠ y in 𝓝 x, w ≠ u → v w y ≠ v u y := by
    intro w hw u hu
    rw [← Finset.mem_val, hsval] at hw hu
    by_cases hwu : w = u
    · exact .of_forall fun _ h ↦ absurd hwu h
    · have hne : v w x ≠ v u x := by rw [hvx w hw, hvx u hu]; exact hwu
      exact (((hvc w hw).continuousAt.sub (hvc u hu).continuousAt).eventually_ne
        (sub_ne_zero.2 hne)).mono fun y hy _ ↦ sub_ne_zero.1 hy
  -- Hence near `x` the roots are exactly the branch values.
  filter_upwards [hR, (eventually_all_finset s).2 hall,
    (eventually_all_finset s).2 fun w hw ↦ (eventually_all_finset s).2 (hdist w hw)] with
    y hy hroot hdisty
  rw [← hsval]
  have hnd : (s.val.map fun w ↦ v w y).Nodup :=
    Multiset.Nodup.map_on (fun w hw u hu h ↦ by_contra fun hwu ↦ hdisty w hw u hu hwu h) s.nodup
  refine (Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun z hz ↦ ?_)
    (by rw [hy.1, Multiset.card_map, hsval, hR.self_of_nhds.1])).symm
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hz
  have h := hroot w hw
  rw [Finset.sum_congr rfl fun j hj ↦ by rw [hy.2 j hj],
    ← Multiset.prod_map_sub_eq_pow_add_sum_esymm hy.1] at h
  exact Multiset.prod_map_sub_eq_zero_iff.1 h

/-- The discriminant of `∏_{w ∈ s} (X - g w)`, for a finite set `s` and values `g w`, is
`(-1)^(#s (#s - 1) / 2) ∏_{w ∈ s} ∏_{u ∈ s ∖ w} (g w - g u)`. -/
private theorem discr_prod_X_sub_C_map_eq (s : Finset ℂ) (g : ℂ → ℂ) :
    ((s.val.map g).map fun w ↦ X - C w).prod.discr =
      (-1) ^ (#s * (#s - 1) / 2) * ∏ w ∈ s, ∏ u ∈ s.erase w, (g w - g u) := by
  classical
  have h := Multiset.prod_map_prod_map_sub_erase_eq_neg_one_pow_mul_discr (s.val.map g)
  rw [Multiset.card_map, Finset.card_val] at h
  have hprod : ((s.val.map g).map fun w ↦ (((s.val.map g).erase w).map fun u ↦ w - u).prod).prod =
      ∏ w ∈ s, ∏ u ∈ s.erase w, (g w - g u) := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun w hw ↦ ?_)
    rw [Function.comp_apply, ← Multiset.map_erase_of_mem _ _ hw, Multiset.map_map,
      Finset.prod_eq_multiset_prod, Finset.erase_val, Function.comp_def]
  have hσ : ((-1 : ℂ) ^ (#s * (#s - 1) / 2)) * (-1) ^ (#s * (#s - 1) / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hprod] at h
  rw [h, ← mul_assoc, hσ, one_mul]

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
  obtain ⟨v, hv, hRv⟩ := exists_root_branches_of_nodup hb hR hx ν μ heq
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
    rw [Pi.smul_apply, smul_eq_mul, hRy, ← hsval, discr_prod_X_sub_C_map_eq, hcard]
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
