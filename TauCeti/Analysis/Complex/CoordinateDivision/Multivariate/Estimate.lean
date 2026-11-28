/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Pi
import TauCeti.Algebra.Polynomial.Degree.CoordinateLine
import TauCeti.Analysis.Complex.CoordinateDivision.Estimate
import TauCeti.Analysis.Complex.PartialDeriv.Degree

/-!
# Polydisc supremum bounds for multivariate coordinate polynomial division

For a finite linearly ordered index type `ι`, a family of monic polynomials `P : ι → ℂ[X]` whose
roots lie in `closedBall (c i) r`, and an entire multivariate coordinate division

  `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)`

with triangular degree bounds (`deg_{z_j} f₀ < deg (P j)` for all `j`, and
`deg_{z_j} g_i < deg (P j)` for all `i < j`), if `0 < R`, `5 * r ≤ R`, and `‖f‖ ≤ M` on
`closedBall c R`, then both `f₀` and `R ^ deg (P i) * g_i` are bounded on `closedBall c R` by
`3 ^ (∑ j, deg (P j)) * M`, and hence by `9 ^ (Fintype.card ι * p) * M` whenever every
`deg (P j) ≤ p`.

## Main results

* `TauCeti.norm_le_of_eq_add_sum_mul_eval_of_monic`: polydisc supremum bounds with factor
  `3 ^ (∑ j, deg (P j))`.
* `TauCeti.norm_le_nine_pow_of_eq_add_sum_mul_eval_of_monic`: polydisc supremum bounds with
  Waldschmidt's factor `9 ^ (Fintype.card ι * p)`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Lemma 4.8, pp. 123–128.
-/

public section

open Finset Function Metric Nat Polynomial

namespace TauCeti

section MultivariateEstimate

variable {ι : Type*}

/-- Combines the univariate head bounds and tail induction bounds at a `cons` step of
`norm_le_of_eq_add_sum_mul_eval_of_list`. -/
private theorem norm_cons_of_norm_tail {P : ι → ℂ[X]} {i : ι} {l' : List ι}
    {f₀ : (ι → ℂ) → ℂ} {g : ι → (ι → ℂ) → ℂ} {R M : ℝ} {z : ι → ℂ}
    (hR : 0 < R) (hM0 : 0 ≤ M)
    (hf₀_z :
      ‖f₀ z‖ ≤ 3 ^ (P i).natDegree * ((3 : ℝ) ^ (l'.map fun j ↦ (P j).natDegree).sum * M))
    (hgi_z :
      ‖g i z‖ ≤ (3 / R) ^ (P i).natDegree * ((3 : ℝ) ^ (l'.map fun j ↦ (P j).natDegree).sum * M))
    (htail : ∀ m ∈ l', ‖g m z‖ ≤
      3 ^ (l'.map fun j ↦ (P j).natDegree).sum / R ^ (P m).natDegree * M) :
    ‖f₀ z‖ ≤ 3 ^ ((i :: l').map fun j ↦ (P j).natDegree).sum * M ∧
      ∀ m ∈ i :: l', ‖g m z‖ ≤
        3 ^ ((i :: l').map fun j ↦ (P j).natDegree).sum / R ^ (P m).natDegree * M := by
  set S' : ℕ := (l'.map fun j ↦ (P j).natDegree).sum
  have hpow_sum : (3 : ℝ) ^ (P i).natDegree * (3 : ℝ) ^ S' =
      (3 : ℝ) ^ ((i :: l').map fun j ↦ (P j).natDegree).sum := by simp [S', pow_add]
  refine ⟨?_, fun m hm ↦ ?_⟩
  · calc ‖f₀ z‖ ≤ (3 : ℝ) ^ (P i).natDegree * ((3 : ℝ) ^ S' * M) := hf₀_z
      _ = (3 : ℝ) ^ ((i :: l').map fun j ↦ (P j).natDegree).sum * M := by
        rw [← mul_assoc, hpow_sum]
  · rcases List.mem_cons.mp hm with rfl | hml'
    · simpa only [div_pow, ← hpow_sum] using hgi_z.trans_eq (by ring)
    · refine (htail m hml').trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right ?_ (by positivity)) hM0)
      simpa only [List.map_cons, List.sum_cons] using
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_add_left S' (P i).natDegree)

variable [LinearOrder ι]

/-- Polydisc supremum bounds for any entire multivariate coordinate division along a strictly
increasing list `l : List ι`. -/
private theorem norm_le_of_eq_add_sum_mul_eval_of_list [Fintype ι]
    {f : (ι → ℂ) → ℂ} {P : ι → ℂ[X]} (hP : ∀ i, (P i).Monic)
    {c : ι → ℂ} {r R M : ℝ} (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hroots : ∀ i ζ, (P i).IsRoot ζ → ζ ∈ closedBall (c i) r)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) :
    ∀ (l : List ι), l.Pairwise (· < ·) →
      ∀ {f₀ : (ι → ℂ) → ℂ} {g : ι → (ι → ℂ) → ℂ},
        Differentiable ℂ f₀ → (∀ i ∈ l, Differentiable ℂ (g i)) →
        (∀ z, f z = f₀ z + ∑ i ∈ l.toFinset, g i z * (P i).eval (z i)) →
        (∀ j ∈ l, ∀ z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w) →
        (∀ i ∈ l, ∀ j ∈ l, i < j → ∀ z,
          ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w) →
        ∀ z ∈ closedBall c R,
          ‖f₀ z‖ ≤ 3 ^ (l.map fun j ↦ (P j).natDegree).sum * M ∧
          ∀ i ∈ l, ‖g i z‖ ≤
            3 ^ (l.map fun j ↦ (P j).natDegree).sum / R ^ (P i).natDegree * M := by
  intro l hsort
  induction l with
  | nil =>
    intro f₀ g _ _ hdiv _ _ z hz
    have hf₀ : f₀ z = f z := by simpa using (hdiv z).symm
    exact ⟨by simpa [hf₀] using hM z hz, fun _ hi ↦ by simp at hi⟩
  | cons i l' ih =>
    intro f₀ g hf₀ hg hdiv hdeg₀ hdeg_g z hz
    obtain ⟨hilt, hsort'⟩ := List.pairwise_cons.mp hsort
    have hi_not : i ∉ l'.toFinset := by simpa using fun h ↦ lt_irrefl i (hilt i h)
    -- Phase 1: fold the `i`-th term into `r'` and apply the induction hypothesis on `l'`.
    let r' : (ι → ℂ) → ℂ := fun w ↦ f₀ w + g i w * (P i).eval (w i)
    have hr' : Differentiable ℂ r' :=
      hf₀.add ((hg i List.mem_cons_self).mul ((P i).differentiable.comp (differentiable_apply i)))
    have hdiv' (w : ι → ℂ) : f w = r' w + ∑ m ∈ l'.toFinset, g m w * (P m).eval (w m) := by
      have h := hdiv w
      rw [List.toFinset_cons, sum_insert hi_not] at h
      linear_combination h
    have hdeg_r' (j : ι) (hjl' : j ∈ l') :
        ∀ w, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ u, r' (update w j u) = Q.eval u :=
      exists_degree_lt_and_add_mul_eval_eq_eval i j (hilt j hjl').ne
        (hdeg₀ j (List.mem_cons_of_mem i hjl'))
        (hdeg_g i List.mem_cons_self j (List.mem_cons_of_mem i hjl') (hilt j hjl'))
    have hnorm' := fun w hw ↦ ih hsort' hr' (fun m hm ↦ hg m (List.mem_cons_of_mem i hm))
      hdiv' hdeg_r' (fun a ha b hb ↦ hdeg_g a (List.mem_cons_of_mem i ha) b
        (List.mem_cons_of_mem i hb)) w hw
    -- Phase 2: identify `f₀` and `g i` as the univariate remainder and quotient of `r'` by `P i`.
    have hdeg_f₀ : (partialDeriv i)^[(P i).natDegree] f₀ = 0 :=
      (iterate_partialDeriv_eq_zero_iff_exists_degree_lt hf₀ i (P i).natDegree).mpr
        (by simpa only [degree_eq_natDegree (hP i).ne_zero] using hdeg₀ i List.mem_cons_self)
    have hr'_eq (w : ι → ℂ) : r' w = f₀ w + (P i).eval (w i) • g i w := by
      simp only [r', smul_eq_mul, mul_comm]
    have hf₀_eq : f₀ = partialModByMonic i r' (P i) :=
      eq_partialModByMonic (hP i) hf₀ (hg i List.mem_cons_self).continuous hdeg_f₀ hr'_eq
    have hgi_eq : g i = partialDivByMonic i r' (P i) :=
      eq_partialDivByMonic (hP i) hf₀ (hg i List.mem_cons_self).continuous hdeg_f₀ hr'_eq
    -- Phase 3: combine the univariate `P i` bounds with the `3 ^ _` tail bounds.
    have hroots_i : ∀ ζ ∈ (P i).roots, ζ ∈ closedBall (c i) r :=
      fun ζ hζ ↦ hroots i ζ ((mem_roots (hP i).ne_zero).mp hζ)
    have hf₀_z := hf₀_eq ▸ norm_partialModByMonic_le_of_five_mul_le (hP i) hr' hroots_i hR hrR
      (fun w hw ↦ (hnorm' w hw).1) hz
    have hgi_z := hgi_eq ▸ norm_partialDivByMonic_le_of_five_mul_le hr' hroots_i hR hrR
      (fun w hw ↦ (hnorm' w hw).1) hz
    exact norm_cons_of_norm_tail hR ((norm_nonneg (f z)).trans (hM z hz)) hf₀_z hgi_z
      (hnorm' z hz).2

/-- **Polydisc supremum bounds for multivariate coordinate division.**
For any entire decomposition `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` with `P i` monic and
triangular degree bounds, if `0 < R`, `5 * r ≤ R`, every root of `P i` lies in `closedBall (c i) r`,
and `‖f‖ ≤ M` on `closedBall c R`, then for every `z ∈ closedBall c R`,
`‖f₀ z‖ ≤ 3 ^ (∑ j, (P j).natDegree) * M` and
`‖g i z‖ ≤ 3 ^ (∑ j, (P j).natDegree) / R ^ (P i).natDegree * M`. -/
theorem norm_le_of_eq_add_sum_mul_eval_of_monic [Fintype ι]
    {f f₀ : (ι → ℂ) → ℂ} {g : ι → (ι → ℂ) → ℂ} {P : ι → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀) (hg : ∀ i, Differentiable ℂ (g i)) (hP : ∀ i, (P i).Monic)
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hdeg_g : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w)
    {c : ι → ℂ} {r R M : ℝ} (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hroots : ∀ i ζ, (P i).IsRoot ζ → ζ ∈ closedBall (c i) r)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : ι → ℂ} (hz : z ∈ closedBall c R) :
    ‖f₀ z‖ ≤ 3 ^ (∑ j, (P j).natDegree) * M ∧
    ∀ i, ‖g i z‖ ≤ 3 ^ (∑ j, (P j).natDegree) / R ^ (P i).natDegree * M := by
  have hsum_eq : (univ.sort.map fun j ↦ (P j).natDegree).sum = ∑ j, (P j).natDegree :=
    ((univ.sort_perm_toList _).map _).sum_eq.trans (univ.sum_map_toList _)
  obtain ⟨h0, hgi⟩ := norm_le_of_eq_add_sum_mul_eval_of_list hP hR hrR hroots hM (univ.sort)
    (Finset.sortedLT_sort univ).pairwise hf₀ (fun i _ ↦ hg i)
    (by simpa only [Finset.sort_toFinset] using hdiv) (fun j _ ↦ hdeg₀ j)
    (fun i _ j _ hij ↦ hdeg_g i j hij) z hz
  rw [hsum_eq] at h0 hgi
  exact ⟨h0, fun i ↦ hgi i ((Finset.mem_sort _).mpr (mem_univ i))⟩

/-- **Polydisc supremum bounds with Waldschmidt's `9 ^ (Fintype.card ι * p)` factor (Lemma 4.8).**
Under the hypotheses of `norm_le_of_eq_add_sum_mul_eval_of_monic`, if `(P i).natDegree ≤ p` for
every `i`, then `‖f₀ z‖ ≤ 9 ^ (Fintype.card ι * p) * M` and
`‖g i z‖ ≤ 9 ^ (Fintype.card ι * p) / R ^ (P i).natDegree * M` for every `z ∈ closedBall c R`. -/
theorem norm_le_nine_pow_of_eq_add_sum_mul_eval_of_monic [Fintype ι]
    {f f₀ : (ι → ℂ) → ℂ} {g : ι → (ι → ℂ) → ℂ} {P : ι → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀) (hg : ∀ i, Differentiable ℂ (g i)) (hP : ∀ i, (P i).Monic)
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hdeg_g : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w)
    {p : ℕ} (hp : ∀ i, (P i).natDegree ≤ p)
    {c : ι → ℂ} {r R M : ℝ} (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hroots : ∀ i ζ, (P i).IsRoot ζ → ζ ∈ closedBall (c i) r)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : ι → ℂ} (hz : z ∈ closedBall c R) :
    ‖f₀ z‖ ≤ 9 ^ (Fintype.card ι * p) * M ∧
    ∀ i, ‖g i z‖ ≤ 9 ^ (Fintype.card ι * p) / R ^ (P i).natDegree * M := by
  obtain ⟨h0, hgi⟩ := norm_le_of_eq_add_sum_mul_eval_of_monic hf₀ hg hP hdiv hdeg₀ hdeg_g
    hR hrR hroots hM hz
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hz)
  have hsum_le : ∑ j : ι, (P j).natDegree ≤ Fintype.card ι * p := by
    calc ∑ j : ι, (P j).natDegree
        ≤ ∑ _ : ι, p := sum_le_sum fun j _ ↦ hp j
      _ = Fintype.card ι * p := by simp
  have hpow : (3 : ℝ) ^ (∑ j, (P j).natDegree) ≤ 9 ^ (Fintype.card ι * p) := by
    calc (3 : ℝ) ^ (∑ j, (P j).natDegree)
        ≤ (3 : ℝ) ^ (Fintype.card ι * p) := pow_le_pow_right₀ (by norm_num) hsum_le
      _ ≤ (9 : ℝ) ^ (Fintype.card ι * p) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  exact ⟨h0.trans (mul_le_mul_of_nonneg_right hpow hM0), fun i ↦
    (hgi i).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hpow (by positivity)) hM0)⟩

end MultivariateEstimate

end TauCeti
