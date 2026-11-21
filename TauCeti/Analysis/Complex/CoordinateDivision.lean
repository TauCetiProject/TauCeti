/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.PartialDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.DividedDifference
import TauCeti.Topology.Algebra.Polynomial.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Pi

/-!
# Division of entire functions by coordinate polynomials

Let `f : (ι → ℂ) → ℂ` be an entire function and let `P : ι → ℂ[X]` be a family of nonzero
polynomials in one variable. Iterating the coordinate divided difference `TauCeti.partialDslope`
along the roots of a single polynomial `P` in coordinate `k` produces Newton's division with
remainder

  `f(z) = f₀(z) + f_k(z) P(z_k)`,

where `f₀` and `f_k` are entire and `z_k ↦ f₀(update z k z_k)` is a polynomial of degree strictly
less than `deg P` for every `z`. The pair `(f₀, f_k)` is uniquely determined among all
decompositions with `f_k` continuous and `deg_{z_k} f₀ < deg P`, and any coordinate polynomial
degree bound on `f` transfers to both `f₀` and `f_k`. When `P` is monic and all its roots lie in
`closedBall (c k) r` with `5 r ≤ R` and `0 < R`, any bound `‖f‖ ≤ M` on the closed polydisc
`closedBall c R` propagates to `‖f₀‖ ≤ 3 ^ deg P * M` and `‖f_k‖ ≤ (3 / R) ^ deg P * M` on
`closedBall c R`. Moreover, if at every root `ζ` of `P` the partial derivatives `∂_k^m f` of order
`m < P.rootMultiplicity ζ` vanish along the hyperplane `z_k = ζ`, then `f₀ = 0`.

For any finite linearly ordered index type `ι`, applying univariate coordinate division backwards
across the coordinates yields Waldschmidt's multivariate polynomial division
(Waldschmidt 2000, §4.3, Lemma 4.8):

  `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)`,

where `f₀` has polynomial degree `< deg (P j)` in every coordinate `z_j`, each `g_i` has polynomial
degree `< deg (P j)` in every coordinate `z_j` with `i < j`, and when each `P i` is monic, on
`closedBall c R` both `f₀` and `R ^ deg (P i) * g_i` are bounded by `3 ^ (∑ j, deg (P j)) * M`
(hence in particular by `9 ^ (Fintype.card ι * p) * M` for any `p` bounding every `deg (P j)`).

## Main results

* `TauCeti.iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity`: derivatives of order
  below `P.rootMultiplicity (z k)` annihilate `y ↦ g y * P.eval (y k)`.
* `TauCeti.eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero`,
  `TauCeti.eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero`: vanishing of a univariate
  polynomial coordinate slice (and hence of the univariate division remainder) under
  root-multiplicity derivative conditions.
* `TauCeti.eq_of_eq_add_mul_eval`: uniqueness of univariate coordinate division for continuous
  quotients.
* `TauCeti.exists_eq_add_mul_eval_of_ne_zero`: univariate coordinate division by a nonzero
  polynomial `P`.
* `TauCeti.norm_le_of_eq_add_mul_eval_of_monic`,
  `TauCeti.exists_degree_lt_of_eq_add_mul_eval`,
  `TauCeti.exists_natDegree_le_of_eq_add_mul_eval`: polydisc supremum bounds and coordinate degree
  preservation for univariate coordinate division.
* `TauCeti.eq_of_eq_add_sum_mul_eval`: uniqueness of multivariate coordinate division under
  triangular degree bounds and continuous quotients.
* `TauCeti.exists_eq_add_sum_mul_eval_of_ne_zero`: multivariate coordinate division by nonzero
  polynomials with triangular degree bounds.
* `TauCeti.norm_le_of_eq_add_sum_mul_eval_of_monic`,
  `TauCeti.norm_le_nine_pow_of_eq_add_sum_mul_eval_of_monic`: polydisc supremum bounds with factors
  `3 ^ (∑ j, deg (P j))` and `9 ^ (Fintype.card ι * p)`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Lemma 4.8, pp. 123–128.
-/

public section

open Finset Function Metric Nat Polynomial

namespace TauCeti

/-! ### Closure helpers for coordinate polynomial degree bounds -/

section DegreeHelpers

private lemma exists_degree_lt_zero {d : WithBot ℕ} (hd : ⊥ < d) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w : ℂ, (0 : ℂ) = Q.eval w :=
  ⟨0, by simpa using hd, by simp⟩

private lemma exists_degree_lt_add {f g : ℂ → ℂ} {d : WithBot ℕ}
    (hf : ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f w = Q.eval w)
    (hg : ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, g w = Q.eval w) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f w + g w = Q.eval w := by
  obtain ⟨Qf, hQf, hQfz⟩ := hf
  obtain ⟨Qg, hQg, hQgz⟩ := hg
  exact ⟨Qf + Qg, (degree_add_le Qf Qg).trans_lt (max_lt hQf hQg), fun w ↦ by simp [hQfz, hQgz]⟩

private lemma exists_degree_lt_sub {f g : ℂ → ℂ} {d : WithBot ℕ}
    (hf : ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f w = Q.eval w)
    (hg : ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, g w = Q.eval w) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f w - g w = Q.eval w := by
  obtain ⟨Qf, hQf, hQfz⟩ := hf
  obtain ⟨Qg, hQg, hQgz⟩ := hg
  exact ⟨Qf - Qg, (degree_sub_le Qf Qg).trans_lt (max_lt hQf hQg), fun w ↦ by simp [hQfz, hQgz]⟩

private lemma exists_degree_lt_const_mul {f : ℂ → ℂ} {d : WithBot ℕ} (c : ℂ)
    (hf : ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f w = Q.eval w) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, c * f w = Q.eval w := by
  obtain ⟨Q, hQ, hQz⟩ := hf
  exact ⟨c • Q, (degree_smul_le c Q).trans_lt hQ, fun w ↦ by simp [hQz w]⟩

private lemma exists_degree_lt_mul_const {f : ℂ → ℂ} {d : WithBot ℕ} (c : ℂ)
    (hf : ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f w = Q.eval w) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f w * c = Q.eval w := by
  obtain ⟨Q, hQ, hQz⟩ := exists_degree_lt_const_mul c hf
  exact ⟨Q, hQ, fun w ↦ by rw [mul_comm, hQz w]⟩

private lemma exists_degree_lt_sum {α : Type*} (s : Finset α) {f : α → ℂ → ℂ} {d : WithBot ℕ}
    (hd : ⊥ < d) (hf : ∀ a ∈ s, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f a w = Q.eval w) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, ∑ a ∈ s, f a w = Q.eval w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using exists_degree_lt_zero hd
  | insert a s ha ih =>
    have hsum := exists_degree_lt_add (hf a (mem_insert_self a s))
      (ih fun b hb ↦ hf b (mem_insert_of_mem hb))
    simpa only [sum_insert ha] using hsum

private lemma degree_C_add_X_sub_C_mul_lt {a ζ : ℂ} {Q : ℂ[X]} {d : ℕ} (hQ : Q.degree < d) :
    (C a + (X - C ζ) * Q).degree < ((d + 1 : ℕ) : WithBot ℕ) := by
  refine (degree_add_le _ _).trans_lt (max_lt
    (degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr (Nat.succ_pos d))) ?_)
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp
  · rw [degree_eq_natDegree hQ0] at hQ
    have hlt : Q.natDegree < d := Nat.cast_lt.mp hQ
    calc ((X - C ζ) * Q).degree
        ≤ (X - C ζ).degree + Q.degree := degree_mul_le _ _
      _ = ((1 + Q.natDegree : ℕ) : WithBot ℕ) := by
          rw [degree_X_sub_C, degree_eq_natDegree hQ0]
          norm_cast
      _ < ((d + 1 : ℕ) : WithBot ℕ) := Nat.cast_lt.mpr (by omega)

end DegreeHelpers

/-! ### Univariate coordinate division -/

section Univariate

variable {ι : Type*} [DecidableEq ι]

/-- If `g : (ι → ℂ) → ℂ` is entire and `m < P.rootMultiplicity (z k)`, then the `m`-th partial
derivative along coordinate `k` annihilates `y ↦ g y * P.eval (y k)` at `z`. -/
theorem iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity [Finite ι]
    {g : (ι → ℂ) → ℂ} (hg : Differentiable ℂ g) {k : ι} {P : ℂ[X]} {z : ι → ℂ} {m : ℕ}
    (hm : m < P.rootMultiplicity (z k)) :
    (partialDeriv k)^[m] (fun y ↦ g y * P.eval (y k)) z = 0 := by
  have := Fintype.ofFinite ι
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hm
  have hgP : Differentiable ℂ (fun y ↦ g y * P.eval (y k)) :=
    hg.mul (P.differentiable.comp (differentiable_apply k))
  rw [iterate_partialDeriv_eq_iteratedDeriv_update hgP k m z]
  have hline : (fun w ↦ g (update z k w) * P.eval (update z k w k)) =
      (fun w ↦ g (update z k w)) * fun w ↦ P.eval w := by
    ext w
    simp
  have hg_line : Differentiable ℂ (fun w ↦ g (update z k w)) := fun w ↦
    (hg (update z k w)).comp w (hasFDerivAt_update z w).differentiableAt
  rw [hline, iteratedDeriv_mul hg_line.contDiff.contDiffAt P.differentiable.contDiff.contDiffAt]
  refine sum_eq_zero fun i _ ↦ ?_
  have hPi : (hasseDeriv (m - i) P).eval (z k) = 0 :=
    (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hP0).mp le_rfl (m - i) (by omega)
  rw [Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv, hPi, mul_zero, mul_zero]

/-- If `f₀ : (ι → ℂ) → ℂ` is entire, agrees with a polynomial of degree `< deg P` along the line
through `z` in coordinate `k`, and satisfies `∂_k^m f₀ (update z k ζ) = 0` for every root `ζ` of
`P` and every `m < P.rootMultiplicity ζ`, then `f₀ z = 0`. -/
theorem eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero [Finite ι]
    {f₀ : (ι → ℂ) → ℂ} (hf₀ : Differentiable ℂ f₀) {k : ι} {P : ℂ[X]} {z : ι → ℂ}
    (hdeg : ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w)
    (hzero : ∀ ζ, P.IsRoot ζ → ∀ m < P.rootMultiplicity ζ,
      (partialDeriv k)^[m] f₀ (update z k ζ) = 0) :
    f₀ z = 0 := by
  have := Fintype.ofFinite ι
  obtain ⟨Q, hQdeg, hQ⟩ := hdeg
  have hP0 : P ≠ 0 := ne_zero_of_degree_gt hQdeg
  suffices hQ0 : Q = 0 by simpa [hQ0] using hQ (z k)
  by_contra hQ0
  have hmult (ζ : ℂ) : P.rootMultiplicity ζ ≤ Q.rootMultiplicity ζ := by
    rcases Nat.eq_zero_or_pos (P.rootMultiplicity ζ) with hm0 | hmpos
    · simp [hm0]
    · have hζroot : P.IsRoot ζ := (rootMultiplicity_pos hP0).mp hmpos
      rw [le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hQ0]
      intro m hm
      have hfz : (partialDeriv k)^[m] f₀ (update z k ζ) = 0 := hzero ζ hζroot m hm
      rw [iterate_partialDeriv_eq_iteratedDeriv_update hf₀ k m (update z k ζ), update_self] at hfz
      have hline : (fun w ↦ f₀ (update (update z k ζ) k w)) = fun w ↦ Q.eval w :=
        funext fun w ↦ by simp [hQ]
      rw [hline, Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hfz
      exact (mul_eq_zero.mp hfz).resolve_left (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
  have hdvd : P ∣ Q := (IsAlgClosed.dvd_iff_roots_le_roots hP0 hQ0).mpr
    (Multiset.le_iff_count.mpr fun ζ ↦ by simpa [count_roots] using hmult ζ)
  exact hQ0 (eq_zero_of_dvd_of_degree_lt hdvd hQdeg)

/-- If `f(y) = f₀(y) + fk(y) P(y k)` with `f₀, fk` entire and `deg_{z_k} f₀ < deg P` along the
line through `z` in coordinate `k`, and if `∂_k^m f` vanishes at `update z k ζ` for every root `ζ`
of `P` and every `m < P.rootMultiplicity ζ`, then `f₀ z = 0`. -/
theorem eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero [Finite ι]
    {f f₀ fk : (ι → ℂ) → ℂ} (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k : ι}
    {P : ℂ[X]} (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k)) {z : ι → ℂ}
    (hdeg : ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w)
    (hzero : ∀ ζ, P.IsRoot ζ → ∀ m < P.rootMultiplicity ζ,
      (partialDeriv k)^[m] f (update z k ζ) = 0) :
    f₀ z = 0 := by
  have := Fintype.ofFinite ι
  have hf_eq : f = f₀ + fun y ↦ fk y * P.eval (y k) := funext hdiv
  have hterm : Differentiable ℂ (fun y ↦ fk y * P.eval (y k)) :=
    hfk.mul (P.differentiable.comp (differentiable_apply k))
  refine eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero hf₀ hdeg fun ζ hζ m hm ↦ ?_
  have hfz : (partialDeriv k)^[m] f (update z k ζ) = 0 := hzero ζ hζ m hm
  rw [hf_eq, iterate_partialDeriv_add hf₀ hterm k m, Pi.add_apply,
    iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity hfk (by simpa using hm),
    add_zero] at hfz
  exact hfz

/-- **Uniqueness of univariate coordinate division.** A function `f` admits at most one
decomposition `f(z) = f₀(z) + fk(z) P(z k)` with `fk` continuous and `deg_{z_k} f₀ < deg P` along
every line in coordinate `k`. -/
theorem eq_of_eq_add_mul_eval {f f₀ fk f₀' fk' : (ι → ℂ) → ℂ}
    (hfk : Continuous fk) (hfk' : Continuous fk') {k : ι} {P : ℂ[X]}
    (hdiv : ∀ z, f z = f₀ z + fk z * P.eval (z k))
    (hdiv' : ∀ z, f z = f₀' z + fk' z * P.eval (z k))
    (hdeg : ∀ z, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w)
    (hdeg' : ∀ z, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀' (update z k w) = Q.eval w) :
    f₀ = f₀' ∧ fk = fk' := by
  obtain ⟨_, hQ0deg, _⟩ := hdeg 0
  have hP0 : P ≠ 0 := ne_zero_of_degree_gt hQ0deg
  have hsub_div (z : ι → ℂ) : (f₀ z - f₀' z) + (fk z - fk' z) * P.eval (z k) = 0 := by
    linear_combination hdiv' z - hdiv z
  have hline_cont (z : ι → ℂ) : Continuous (fun w ↦ fk (update z k w) - fk' (update z k w)) :=
    (hfk.sub hfk').comp (continuous_const.update k continuous_id)
  have hf₀_eq : f₀ = f₀' := by
    ext z
    obtain ⟨Q, hQdeg, hQ⟩ := exists_degree_lt_sub (hdeg z) (hdeg' z)
    have hQ0 : Q = 0 := Polynomial.eq_zero_of_eval_add_mul_eval_eq_zero (IsAlgClosed.splits P)
      hQdeg (fun _ _ ↦ (hline_cont z).continuousAt) fun w ↦ by
        simpa [hQ w, update_self] using hsub_div (update z k w)
    exact sub_eq_zero.mp (by simpa [hQ0, update_eq_self] using hQ (z k))
  refine ⟨hf₀_eq, ?_⟩
  ext z
  rw [← sub_eq_zero]
  have hgP (w : ℂ) : (fk (update z k w) - fk' (update z k w)) * P.eval w = 0 := by
    simpa [hf₀_eq, update_self] using hsub_div (update z k w)
  simpa [update_eq_self] using
    Polynomial.eq_zero_of_mul_eval_eq_zero (w₀ := z k) (hline_cont z).continuousAt hP0 hgP

/-- When `5 * r ≤ R`, `0 < R`, and `ζ ∈ closedBall (c k) r`, `partialDslope k ζ f` is bounded on
`closedBall c R` by `5 / (2 * R) * M`. -/
private lemma norm_partialDslope_le_five_div_two_mul [Fintype ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {k : ι} {ζ : ℂ} {c : ι → ℂ} {r R M : ℝ}
    (hR : 0 < R) (hrR : 5 * r ≤ R) (hζ : ζ ∈ closedBall (c k) r)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {w : ι → ℂ} (hw : w ∈ closedBall c R) :
    ‖partialDslope k ζ f w‖ ≤ 5 / (2 * R) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg (f w)).trans (hM w hw)
  have hr_lt_R : r < R := by linarith [dist_nonneg.trans (mem_closedBall.mp hζ)]
  have hRr : 0 < R - r := sub_pos.mpr hr_lt_R
  refine (norm_partialDslope_le hf.differentiableOn hζ hr_lt_R hM hw).trans ?_
  rw [div_le_iff₀ hRr]
  have h1 : 4 * R ≤ 5 * (R - r) := by linarith
  have h2 : 4 * R * M ≤ 5 * (R - r) * M := mul_le_mul_of_nonneg_right h1 hM0
  have hRne : R ≠ 0 := hR.ne'
  calc 2 * M = (4 * R * M) / (2 * R) := by field_simp; ring
    _ ≤ (5 * (R - r) * M) / (2 * R) := div_le_div_of_nonneg_right h2 (by positivity)
    _ = 5 / (2 * R) * M * (R - r) := by ring

/-- One-step remainder norm bound for Newton coordinate division under `5 * r ≤ R`. -/
private lemma norm_update_add_sub_mul_le [Fintype ι] {f r' : (ι → ℂ) → ℂ} {k : ι} {ζ : ℂ}
    {c : ι → ℂ} {r R M : ℝ} {d : ℕ} (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hζ : ζ ∈ closedBall (c k) r) (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M)
    {z : ι → ℂ} (hz : z ∈ closedBall c R)
    (hr'z : ‖r' z‖ ≤ ((3 : ℝ) ^ d - 1) / 2 * (5 / (2 * R) * M)) :
    ‖f (update z k ζ) + (z k - ζ) * r' z‖ ≤ ((3 : ℝ) ^ (d + 1) - 1) / 2 * M := by
  have hr_lt_R : r < R := by linarith [dist_nonneg.trans (mem_closedBall.mp hζ)]
  have hfζ : ‖f (update z k ζ)‖ ≤ M :=
    hM _ (update_mem_closedBall (closedBall_subset_closedBall hr_lt_R.le hζ) hz)
  have hzk : ‖z k - c k‖ ≤ R := by
    simpa [dist_eq_norm] using (dist_le_pi_dist z c k).trans (mem_closedBall.mp hz)
  have hζc : ‖ζ - c k‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hζ
  have hzkζ : ‖z k - ζ‖ ≤ 6 / 5 * R := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (z k) (c k) ζ
    rw [norm_sub_rev (c k) ζ] at htri
    linarith
  have hRne : R ≠ 0 := hR.ne'
  calc ‖f (update z k ζ) + (z k - ζ) * r' z‖
      ≤ ‖f (update z k ζ)‖ + ‖(z k - ζ) * r' z‖ := norm_add_le _ _
    _ = ‖f (update z k ζ)‖ + ‖z k - ζ‖ * ‖r' z‖ := by rw [norm_mul]
    _ ≤ M + (6 / 5 * R) * (((3 : ℝ) ^ d - 1) / 2 * (5 / (2 * R) * M)) := by gcongr
    _ = ((3 : ℝ) ^ (d + 1) - 1) / 2 * M := by rw [pow_succ]; field_simp; ring

/-- Newton coordinate division along an explicit list of roots `l`: produces entire `f₀, fk` with
`f(z) = f₀(z) + fk(z) ∏_{ζ ∈ l} (z_k - ζ)`, `deg_{z_k} f₀ < l.length`, preservation of degree
bounds in all other coordinates `j ≠ k`, and intermediate polydisc bounds. -/
private theorem exists_eq_add_mul_prod_of_list [Fintype ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (k : ι) (l : List ℂ) :
    ∃ f₀ fk : (ι → ℂ) → ℂ,
      Differentiable ℂ f₀ ∧
      Differentiable ℂ fk ∧
      (∀ z, f z = f₀ z + fk z * (l.map fun ζ ↦ X - C ζ).prod.eval (z k)) ∧
      (∀ z, ∃ Q : ℂ[X], Q.degree < (l.length : ℕ) ∧ ∀ w, f₀ (update z k w) = Q.eval w) ∧
      (∀ j ≠ k, ∀ d : WithBot ℕ,
        (∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update z j w) = Q.eval w) →
        (∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f₀ (update z j w) = Q.eval w) ∧
        (∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, fk (update z j w) = Q.eval w)) ∧
      (∀ (c : ι → ℂ) (r R M : ℝ), 0 < R → 5 * r ≤ R →
        (∀ ζ ∈ l, ζ ∈ closedBall (c k) r) → (∀ w ∈ closedBall c R, ‖f w‖ ≤ M) →
        ∀ z ∈ closedBall c R,
          ‖f₀ z‖ ≤ ((3 : ℝ) ^ l.length - 1) / 2 * M ∧
          ‖fk z‖ ≤ (5 / (2 * R)) ^ l.length * M) := by
  induction l generalizing f with
  | nil =>
    refine ⟨0, f, differentiable_const 0, hf, fun z ↦ by simp, fun z ↦ ⟨0, by simp, by simp⟩,
      fun j _ d hdeg ↦ ⟨fun z ↦ ?_, hdeg⟩,
      fun c r R M _ _ _ hM z hz ↦ ⟨by simp, by simpa using hM z hz⟩⟩
    obtain ⟨Q, hQ, _⟩ := hdeg z
    exact exists_degree_lt_zero (bot_le.trans_lt hQ)
  | cons ζ l ih =>
    have hq₁ : Differentiable ℂ (partialDslope k ζ f) := differentiable_partialDslope hf k ζ
    obtain ⟨r', q', hr', hq', hdiv', hdeg', hdeg_ne', hnorm'⟩ := ih hq₁
    let f₀ : (ι → ℂ) → ℂ := fun z ↦ f (update z k ζ) + (z k - ζ) * r' z
    have hf₀ : Differentiable ℂ f₀ := by
      have hupd : Differentiable ℂ (fun z : ι → ℂ ↦ update z k ζ) :=
        differentiable_pi.mpr fun j ↦ by
          by_cases hj : j = k
          · subst hj; simp
          · simpa [hj] using differentiable_apply j
      exact (hf.comp hupd).add (((differentiable_apply k).sub (differentiable_const ζ)).mul hr')
    refine ⟨f₀, q', hf₀, hq', ?_, ?_, ?_, ?_⟩
    · intro z
      have hstep := eq_update_add_sub_mul_partialDslope k ζ f z
      rw [hdiv' z] at hstep
      simp only [f₀, List.map_cons, List.prod_cons, eval_mul, eval_sub, eval_X, eval_C]
      linear_combination hstep
    · intro z
      obtain ⟨Q', hQ'deg, hQ'⟩ := hdeg' z
      exact ⟨C (f (update z k ζ)) + (X - C ζ) * Q', degree_C_add_X_sub_C_mul_lt hQ'deg,
        fun w ↦ by simp [f₀, update_idem, update_self, hQ' w]⟩
    · intro j hjk d hfj
      obtain ⟨hr'j, hq'j⟩ :=
        hdeg_ne' j hjk d (exists_degree_lt_and_partialDslope_eq_eval hf k j ζ hfj)
      refine ⟨fun z ↦ ?_, hq'j⟩
      simpa only [f₀, update_of_ne hjk.symm] using exists_degree_lt_add
        (exists_degree_lt_and_update_eq_eval k j ζ hfj z)
        (exists_degree_lt_const_mul (z k - ζ) (hr'j z))
    · intro c r R M hR hrR hroots hM z hz
      have hζ : ζ ∈ closedBall (c k) r := hroots ζ List.mem_cons_self
      obtain ⟨hr'z, hq'z⟩ := hnorm' c r R (5 / (2 * R) * M) hR hrR
        (fun η hη ↦ hroots η (List.mem_cons_of_mem ζ hη))
        (fun w hw ↦ norm_partialDslope_le_five_div_two_mul hf hR hrR hζ hM hw) z hz
      exact ⟨norm_update_add_sub_mul_le hR hrR hζ hM hz hr'z,
        by simpa only [List.length_cons, pow_succ, mul_assoc] using hq'z⟩

/-- Specialises `exists_eq_add_mul_prod_of_list` to the root list `P.roots.toList` of a monic
polynomial `P : ℂ[X]`. -/
private theorem exists_eq_add_mul_eval_of_monic_full [Fintype ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (k : ι) {P : ℂ[X]} (hP : P.Monic) :
    ∃ f₀ fk : (ι → ℂ) → ℂ,
      Differentiable ℂ f₀ ∧
      Differentiable ℂ fk ∧
      (∀ z, f z = f₀ z + fk z * P.eval (z k)) ∧
      (∀ z, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w) ∧
      (∀ j ≠ k, ∀ d : WithBot ℕ,
        (∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update z j w) = Q.eval w) →
        (∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f₀ (update z j w) = Q.eval w) ∧
        (∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, fk (update z j w) = Q.eval w)) ∧
      (∀ (c : ι → ℂ) (r R M : ℝ), 0 < R → 5 * r ≤ R →
        (∀ ζ, P.IsRoot ζ → ζ ∈ closedBall (c k) r) → (∀ w ∈ closedBall c R, ‖f w‖ ≤ M) →
        ∀ z ∈ closedBall c R,
          ‖f₀ z‖ ≤ ((3 : ℝ) ^ P.natDegree - 1) / 2 * M ∧
          ‖fk z‖ ≤ (5 / (2 * R)) ^ P.natDegree * M) := by
  let l : List ℂ := P.roots.toList
  have hPprod : (l.map fun ζ ↦ X - C ζ).prod = P :=
    (Multiset.prod_map_toList P.roots _).trans
      ((IsAlgClosed.splits P).eq_prod_roots_of_monic hP).symm
  have hlen_nat : l.length = P.natDegree := by
    rw [Multiset.length_toList, ← (IsAlgClosed.splits P).natDegree_eq_card_roots]
  have hlen : (l.length : WithBot ℕ) = P.degree := by
    rw [hlen_nat, degree_eq_natDegree hP.ne_zero]
  obtain ⟨f₀, fk, hf₀, hfk, hdiv, hdeg, hdeg_ne, hnorm⟩ := exists_eq_add_mul_prod_of_list hf k l
  rw [hPprod] at hdiv
  rw [hlen] at hdeg
  rw [hlen_nat] at hnorm
  refine ⟨f₀, fk, hf₀, hfk, hdiv, hdeg, hdeg_ne, fun c r R M hR hrR hroots ↦ hnorm c r R M hR hrR
    fun ζ hζ ↦ hroots ζ ((mem_roots hP.ne_zero).mp (Multiset.mem_toList.mp hζ))⟩

/-- **Univariate coordinate division by a nonzero polynomial (Waldschmidt, Lemma 4.8).**
For any entire function `f : (ι → ℂ) → ℂ`, coordinate `k : ι`, and nonzero polynomial `P : ℂ[X]`,
there exist entire functions `f₀, fk : (ι → ℂ) → ℂ` such that `f(z) = f₀(z) + fk(z) P(z k)` and
`f₀` is a polynomial of degree strictly less than `deg P` in `z k` along every coordinate line. -/
theorem exists_eq_add_mul_eval_of_ne_zero [Finite ι] {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (k : ι) {P : ℂ[X]} (hP : P ≠ 0) :
    ∃ f₀ fk : (ι → ℂ) → ℂ,
      Differentiable ℂ f₀ ∧
      Differentiable ℂ fk ∧
      (∀ z, f z = f₀ z + fk z * P.eval (z k)) ∧
      (∀ z, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w) := by
  have := Fintype.ofFinite ι
  let P₁ : ℂ[X] := P * C P.leadingCoeff⁻¹
  have hP₁ : P₁.Monic := monic_mul_leadingCoeff_inv hP
  have hP₁_deg : P₁.degree = P.degree :=
    degree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hP))
  obtain ⟨f₀, fk₁, hf₀, hfk₁, hdiv₁, hdeg₁, -, -⟩ := exists_eq_add_mul_eval_of_monic_full hf k hP₁
  refine ⟨f₀, fun z ↦ P.leadingCoeff⁻¹ * fk₁ z, hf₀, hfk₁.const_mul _, fun z ↦ ?_,
    fun z ↦ by simpa only [hP₁_deg] using hdeg₁ z⟩
  have h := hdiv₁ z
  simp only [P₁, eval_mul, eval_C] at h
  linear_combination h

/-- **Polydisc supremum bounds for univariate coordinate division (Waldschmidt, Lemma 4.8).**
If `f(y) = f₀(y) + fk(y) P(y k)` with `f₀, fk` entire, `P` monic, and `deg_{z_k} f₀ < deg P`, and
if `0 < R`, `5 * r ≤ R`, every root of `P` lies in `closedBall (c k) r`, and `‖f‖ ≤ M` on
`closedBall c R`, then `‖f₀ z‖ ≤ 3 ^ P.natDegree * M` and `‖fk z‖ ≤ (3 / R) ^ P.natDegree * M` for
every `z ∈ closedBall c R`. -/
theorem norm_le_of_eq_add_mul_eval_of_monic [Fintype ι] {f f₀ fk : (ι → ℂ) → ℂ}
    (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k : ι} {P : ℂ[X]} (hP : P.Monic)
    (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k))
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update y k w) = Q.eval w)
    {c : ι → ℂ} {r R M : ℝ} (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hroots : ∀ ζ, P.IsRoot ζ → ζ ∈ closedBall (c k) r)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : ι → ℂ} (hz : z ∈ closedBall c R) :
    ‖f₀ z‖ ≤ 3 ^ P.natDegree * M ∧ ‖fk z‖ ≤ (3 / R) ^ P.natDegree * M := by
  have hf : Differentiable ℂ f := by
    have hfeq : f = fun y ↦ f₀ y + fk y * P.eval (y k) := funext hdiv
    rw [hfeq]
    exact hf₀.add (hfk.mul (P.differentiable.comp (differentiable_apply k)))
  obtain ⟨f₀', fk', _, hfk', hdiv', hdeg', -, hnorm'⟩ :=
    exists_eq_add_mul_eval_of_monic_full hf k hP
  obtain ⟨rfl, rfl⟩ := eq_of_eq_add_mul_eval hfk.continuous hfk'.continuous hdiv hdiv' hdeg hdeg'
  obtain ⟨h0, hk⟩ := hnorm' c r R M hR hrR hroots hM z hz
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hz)
  refine ⟨h0.trans (mul_le_mul_of_nonneg_right ?_ hM0),
    hk.trans (mul_le_mul_of_nonneg_right ?_ hM0)⟩
  · have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ P.natDegree := by positivity
    linarith
  · refine pow_le_pow_left₀ (by positivity) ?_ P.natDegree
    calc 5 / (2 * R) = (5 / 2) / R := by ring
      _ ≤ 3 / R := by gcongr; norm_num

/-- Monic case of coordinate degree preservation for univariate coordinate division. -/
private theorem exists_degree_lt_of_eq_add_mul_eval_of_monic [Finite ι] {f f₀ fk : (ι → ℂ) → ℂ}
    (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k j : ι} {P : ℂ[X]} (hP : P.Monic)
    (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k))
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update y k w) = Q.eval w)
    {d : WithBot ℕ} (hfj : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) :
    (∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f₀ (update y j w) = Q.eval w) ∧
    (∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, fk (update y j w) = Q.eval w) := by
  have := Fintype.ofFinite ι
  by_cases hjk : j = k
  · subst hjk
    have hline (y : ι → ℂ) :
        (∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f₀ (update y j w) = Q.eval w) ∧
        (∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, fk (update y j w) = Q.eval w) := by
      obtain ⟨Q, hQdeg, hQy⟩ := hfj y
      obtain ⟨R, hRdeg, hRy⟩ := hdeg y
      have hcont : Continuous (fun w ↦ fk (update y j w) - (Q /ₘ P).eval w) :=
        (hfk.continuous.comp (continuous_const.update j continuous_id)).sub (Q /ₘ P).continuous
      have hdiff (w : ℂ) : (R - Q %ₘ P).eval w +
          (fk (update y j w) - (Q /ₘ P).eval w) * P.eval w = 0 := by
        have h1 := hdiv (update y j w)
        have h2 : Q.eval w = (Q %ₘ P).eval w + (Q /ₘ P).eval w * P.eval w := by
          conv_lhs => rw [← modByMonic_add_div Q P]
          simp [mul_comm]
        simp only [hQy w, hRy w, update_self] at h1
        simp only [eval_sub]
        linear_combination h2 - h1
      have hR_eq : R = Q %ₘ P := sub_eq_zero.mp <|
        Polynomial.eq_zero_of_eval_add_mul_eval_eq_zero (IsAlgClosed.splits P)
          ((degree_sub_le R (Q %ₘ P)).trans_lt (max_lt hRdeg (degree_modByMonic_lt Q hP)))
          (fun _ _ ↦ hcont.continuousAt) hdiff
      refine ⟨⟨Q %ₘ P, degree_modByMonic_le_left.trans_lt hQdeg, fun w ↦ by rw [hRy w, hR_eq]⟩,
        ⟨Q /ₘ P, (degree_divByMonic_le Q P).trans_lt hQdeg, fun w ↦ sub_eq_zero.mp ?_⟩⟩
      exact Polynomial.eq_zero_of_mul_eval_eq_zero
        (g := fun u ↦ fk (update y j u) - (Q /ₘ P).eval u) (w₀ := w)
        hcont.continuousAt hP.ne_zero fun u ↦ by simpa [hR_eq] using hdiff u
    exact ⟨fun y ↦ (hline y).1, fun y ↦ (hline y).2⟩
  · have hf : Differentiable ℂ f := by
      have hfeq : f = fun y ↦ f₀ y + fk y * P.eval (y k) := funext hdiv
      rw [hfeq]
      exact hf₀.add (hfk.mul (P.differentiable.comp (differentiable_apply k)))
    obtain ⟨f₀', fk', _, hfk', hdiv', hdeg', hdeg_ne', -⟩ :=
      exists_eq_add_mul_eval_of_monic_full hf k hP
    obtain ⟨rfl, rfl⟩ := eq_of_eq_add_mul_eval hfk.continuous hfk'.continuous hdiv hdiv' hdeg hdeg'
    exact hdeg_ne' j hjk d hfj

/-- **Coordinate degree preservation for univariate division.** If `f(y) = f₀(y) + fk(y) P(y k)`
with `f₀, fk` entire and `deg_{z_k} f₀ < deg P`, then any strict polynomial degree bound `< d` on
`f` in any coordinate `j` transfers to both `f₀` and `fk`. -/
theorem exists_degree_lt_of_eq_add_mul_eval [Finite ι] {f f₀ fk : (ι → ℂ) → ℂ}
    (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k j : ι} {P : ℂ[X]}
    (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k))
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update y k w) = Q.eval w)
    {d : WithBot ℕ} (hfj : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) :
    (∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f₀ (update y j w) = Q.eval w) ∧
    (∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, fk (update y j w) = Q.eval w) := by
  have := Fintype.ofFinite ι
  obtain ⟨_, hQ0deg, _⟩ := hdeg 0
  have hP0 : P ≠ 0 := ne_zero_of_degree_gt hQ0deg
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  let P₁ : ℂ[X] := P * C P.leadingCoeff⁻¹
  have hP₁ : P₁.Monic := monic_mul_leadingCoeff_inv hP0
  have hP₁_deg : P₁.degree = P.degree := degree_mul_C (inv_ne_zero hlc)
  let fk₁ : (ι → ℂ) → ℂ := fun y ↦ P.leadingCoeff * fk y
  have hdiv₁ (y : ι → ℂ) : f y = f₀ y + fk₁ y * P₁.eval (y k) := by
    simp only [fk₁, P₁, eval_mul, eval_C]
    rw [hdiv y]
    field_simp [hlc]
  obtain ⟨h0, hk₁⟩ := exists_degree_lt_of_eq_add_mul_eval_of_monic hf₀ (hfk.const_mul _) hP₁
    hdiv₁ (fun y ↦ by simpa only [hP₁_deg] using hdeg y) hfj
  refine ⟨h0, fun y ↦ ?_⟩
  obtain ⟨Q, hQdeg, hQy⟩ := exists_degree_lt_const_mul P.leadingCoeff⁻¹ (hk₁ y)
  refine ⟨Q, hQdeg, fun w ↦ ?_⟩
  rw [← hQy w, inv_mul_cancel_left₀ hlc]

/-- If `f(y) = f₀(y) + fk(y) P(y k)` with `f₀, fk` entire and `deg_{z_k} f₀ < deg P`, then any
`natDegree ≤ e` bound on `f` in any coordinate `j` transfers to both `f₀` and `fk`. -/
theorem exists_natDegree_le_of_eq_add_mul_eval [Finite ι] {f f₀ fk : (ι → ℂ) → ℂ}
    (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k j : ι} {P : ℂ[X]}
    (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k))
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update y k w) = Q.eval w)
    {e : ℕ} (hfj : ∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update y j w) = Q.eval w) :
    (∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f₀ (update y j w) = Q.eval w) ∧
    (∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, fk (update y j w) = Q.eval w) := by
  simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using
    exists_degree_lt_of_eq_add_mul_eval hf₀ hfk hdiv hdeg (d := Order.succ (e : WithBot ℕ))
      (fun y ↦ by simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using hfj y)

end Univariate

/-! ### Multivariate coordinate division -/

section Multivariate

variable {ι : Type*} [LinearOrder ι]

/-- Homogeneous uniqueness of multivariate coordinate division over any finite subset `s` of
coordinates under triangular degree bounds and continuous quotients. -/
private theorem eq_zero_of_add_sum_mul_eval_eq_zero
    {f₀ : (ι → ℂ) → ℂ} {g : ι → (ι → ℂ) → ℂ} {P : ι → ℂ[X]}
    (hg : ∀ i, Continuous (g i)) (s : Finset ι)
    (hdiv : ∀ z, f₀ z + ∑ i ∈ s, g i z * (P i).eval (z i) = 0)
    (hdeg₀ : ∀ j ∈ s, ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hdeg_g : ∀ i ∈ s, ∀ j ∈ s, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w) :
    f₀ = 0 ∧ ∀ i ∈ s, g i = 0 := by
  induction s using Finset.induction_on_max with
  | empty =>
    exact ⟨funext fun z ↦ by simpa using hdiv z, fun _ hi ↦ (notMem_empty _ hi).elim⟩
  | insert j s hj ih =>
    have hjs : j ∉ s := fun h ↦ lt_irrefl j (hj j h)
    set F : (ι → ℂ) → ℂ := fun z ↦ f₀ z + ∑ a ∈ s, g a z * (P a).eval (z a) with hF_def
    have hsplit (z : ι → ℂ) : (0 : (ι → ℂ) → ℂ) z = F z + g j z * (P j).eval (z j) := by
      have h := hdiv z
      rw [sum_insert hjs] at h
      rw [hF_def, Pi.zero_apply]
      linear_combination -h
    obtain ⟨_, hPj_pos, _⟩ := hdeg₀ j (mem_insert_self j s) 0
    have hPj_bot : ⊥ < (P j).degree := bot_le.trans_lt hPj_pos
    have hF_deg (z : ι → ℂ) :
        ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, F (update z j w) = Q.eval w := by
      refine exists_degree_lt_add (hdeg₀ j (mem_insert_self j s) z)
        (exists_degree_lt_sum s hPj_bot fun a has ↦ ?_)
      have haj : a < j := hj a has
      simpa only [update_of_ne haj.ne] using exists_degree_lt_mul_const ((P a).eval (z a))
        (hdeg_g a (mem_insert_of_mem has) j (mem_insert_self j s) haj z)
    obtain ⟨hF0, hgj0⟩ := eq_of_eq_add_mul_eval (f := (0 : (ι → ℂ) → ℂ)) (f₀ := F) (fk := g j)
      (f₀' := 0) (fk' := 0) (hg j) continuous_const hsplit (fun _ ↦ by simp) hF_deg
      fun _ ↦ exists_degree_lt_zero hPj_bot
    obtain ⟨hf₀0, hgs0⟩ := ih (fun z ↦ by simpa [hF_def] using congrFun hF0 z)
      (fun a has ↦ hdeg₀ a (mem_insert_of_mem has))
      (fun a has b hbs ↦ hdeg_g a (mem_insert_of_mem has) b (mem_insert_of_mem hbs))
    exact ⟨hf₀0, fun i hi ↦ (mem_insert.mp hi).elim (fun h ↦ h ▸ hgj0) (hgs0 i)⟩

/-- **Uniqueness of multivariate coordinate division under triangular degree bounds.**
A function `f` has at most one decomposition `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` with
every `g_i` continuous, `deg_{z_j} f₀ < deg (P j)` for all `j`, and `deg_{z_j} g_i < deg (P j)`
for all `i < j`. -/
theorem eq_of_eq_add_sum_mul_eval [Fintype ι]
    {f f₀ f₀' : (ι → ℂ) → ℂ} {g g' : ι → (ι → ℂ) → ℂ} {P : ι → ℂ[X]}
    (hg : ∀ i, Continuous (g i)) (hg' : ∀ i, Continuous (g' i))
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdiv' : ∀ z, f z = f₀' z + ∑ i, g' i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hdeg₀' : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀' (update z j w) = Q.eval w)
    (hdeg_g : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w)
    (hdeg_g' : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g' i (update z j w) = Q.eval w) :
    f₀ = f₀' ∧ g = g' := by
  have hsub (z : ι → ℂ) : (f₀ - f₀') z + ∑ i ∈ univ, (g i - g' i) z * (P i).eval (z i) = 0 := by
    have hsum : ∑ i : ι, (g i - g' i) z * (P i).eval (z i) =
        (∑ i : ι, g i z * (P i).eval (z i)) - ∑ i : ι, g' i z * (P i).eval (z i) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ sub_mul (g i z) (g' i z) _
    rw [hsum, Pi.sub_apply]
    linear_combination hdiv' z - hdiv z
  obtain ⟨hf₀0, hg0⟩ := eq_zero_of_add_sum_mul_eval_eq_zero (fun i ↦ (hg i).sub (hg' i)) univ hsub
    (fun j _ z ↦ exists_degree_lt_sub (hdeg₀ j z) (hdeg₀' j z))
    (fun i _ j _ hij z ↦ exists_degree_lt_sub (hdeg_g i j hij z) (hdeg_g' i j hij z))
  exact ⟨sub_eq_zero.mp hf₀0, funext fun i ↦ sub_eq_zero.mp (hg0 i (mem_univ i))⟩

/-- Multivariate coordinate division along a strictly increasing list `l : List ι`: produces entire
`f₀` and `g` with triangular degree bounds. -/
private theorem exists_eq_add_sum_mul_eval_of_list [Finite ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {P : ι → ℂ[X]} (hP : ∀ i, P i ≠ 0) :
    ∀ (l : List ι), l.Pairwise (· < ·) →
      ∃ (f₀ : (ι → ℂ) → ℂ) (g : ι → (ι → ℂ) → ℂ),
        Differentiable ℂ f₀ ∧
        (∀ i, Differentiable ℂ (g i)) ∧
        (∀ z, f z = f₀ z + ∑ i ∈ l.toFinset, g i z * (P i).eval (z i)) ∧
        (∀ j ∈ l, ∀ z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w) ∧
        (∀ i ∈ l, ∀ j ∈ l, i < j → ∀ z,
          ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w) := by
  intro l hsort
  induction l with
  | nil =>
    exact ⟨f, fun _ ↦ 0, hf, fun _ ↦ differentiable_const 0, fun z ↦ by simp,
      fun _ hj ↦ by simp at hj, fun _ hi ↦ by simp at hi⟩
  | cons i l' ih =>
    obtain ⟨hilt, hsort'⟩ := List.pairwise_cons.mp hsort
    have hil' : i ∉ l' := fun h ↦ lt_irrefl i (hilt i h)
    obtain ⟨r', g', hr', hg', hdiv', hdeg_r', hdeg_g'⟩ := ih hsort'
    obtain ⟨f₀, gi, hf₀, hgi, hdiv_i, hdeg_i⟩ := exists_eq_add_mul_eval_of_ne_zero hr' i (hP i)
    let g : ι → (ι → ℂ) → ℂ := update g' i gi
    have hg (m : ι) : Differentiable ℂ (g m) := by
      by_cases hm : m = i
      · subst hm; simpa [g] using hgi
      · simpa [g, hm] using hg' m
    refine ⟨f₀, g, hf₀, hg, ?_, ?_, ?_⟩
    · intro z
      have hi_not : i ∉ l'.toFinset := by simpa using hil'
      rw [List.toFinset_cons, sum_insert hi_not]
      have hsum_eq : ∑ m ∈ l'.toFinset, g m z * (P m).eval (z m) =
          ∑ m ∈ l'.toFinset, g' m z * (P m).eval (z m) := sum_congr rfl fun m hm ↦ by
        simp [g, show m ≠ i from fun h ↦ hi_not (h ▸ hm)]
      rw [hsum_eq, hdiv' z, hdiv_i z]
      simp [g]
      ring
    · intro j hj z
      rcases List.mem_cons.mp hj with rfl | hjl'
      · exact hdeg_i z
      · exact (exists_degree_lt_of_eq_add_mul_eval hf₀ hgi hdiv_i hdeg_i (hdeg_r' j hjl')).1 z
    · intro a ha b hb hab z
      rcases List.mem_cons.mp ha with rfl | hal'
      · have hbl' : b ∈ l' := (List.mem_cons.mp hb).resolve_left hab.ne'
        simpa [g] using (exists_degree_lt_of_eq_add_mul_eval hf₀ hgi hdiv_i hdeg_i
          (hdeg_r' b hbl')).2 z
      · have hai : a ≠ i := (hilt a hal').ne'
        have hbl' : b ∈ l' := (List.mem_cons.mp hb).resolve_left fun hbi ↦
          (hab.trans (hbi ▸ hilt a hal')).false
        simpa [g, hai] using hdeg_g' a hal' b hbl' hab z

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
    let r' : (ι → ℂ) → ℂ := fun w ↦ f₀ w + g i w * (P i).eval (w i)
    have hr' : Differentiable ℂ r' :=
      hf₀.add ((hg i List.mem_cons_self).mul ((P i).differentiable.comp (differentiable_apply i)))
    have hdiv' (w : ι → ℂ) : f w = r' w + ∑ m ∈ l'.toFinset, g m w * (P m).eval (w m) := by
      have h := hdiv w
      rw [List.toFinset_cons, sum_insert hi_not] at h
      linear_combination h
    have hdeg_r' (j : ι) (hjl' : j ∈ l') (w : ι → ℂ) :
        ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ u, r' (update w j u) = Q.eval u := by
      have hij : i < j := hilt j hjl'
      simpa only [r', update_of_ne hij.ne] using exists_degree_lt_add
        (hdeg₀ j (List.mem_cons_of_mem i hjl') w)
        (exists_degree_lt_mul_const ((P i).eval (w i))
          (hdeg_g i List.mem_cons_self j (List.mem_cons_of_mem i hjl') hij w))
    have hnorm' := fun w hw ↦ ih hsort' hr' (fun m hm ↦ hg m (List.mem_cons_of_mem i hm))
      hdiv' hdeg_r' (fun a ha b hb ↦ hdeg_g a (List.mem_cons_of_mem i ha) b
        (List.mem_cons_of_mem i hb)) w hw
    let S' : ℕ := (l'.map fun j ↦ (P j).natDegree).sum
    obtain ⟨hf₀_z, hgi_z⟩ := norm_le_of_eq_add_mul_eval_of_monic hf₀ (hg i List.mem_cons_self)
      (hP i) (fun _ ↦ rfl) (hdeg₀ i List.mem_cons_self) hR hrR (hroots i)
      (fun w hw ↦ (hnorm' w hw).1) hz
    have hpow_sum : (3 : ℝ) ^ (P i).natDegree * (3 : ℝ) ^ S' =
        (3 : ℝ) ^ ((i :: l').map fun j ↦ (P j).natDegree).sum := by simp [S', pow_add]
    have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hz)
    refine ⟨?_, fun m hm ↦ ?_⟩
    · calc ‖f₀ z‖ ≤ (3 : ℝ) ^ (P i).natDegree * ((3 : ℝ) ^ S' * M) := hf₀_z
        _ = (3 : ℝ) ^ ((i :: l').map fun j ↦ (P j).natDegree).sum * M := by
          rw [← mul_assoc, hpow_sum]
    · rcases List.mem_cons.mp hm with rfl | hml'
      · simpa only [div_pow, ← hpow_sum] using hgi_z.trans_eq (by ring)
      · refine ((hnorm' z hz).2 m hml').trans (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right ?_ (by positivity)) hM0)
        simpa only [List.map_cons, List.sum_cons] using
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_add_left S' (P i).natDegree)

/-- **Multivariate coordinate division by nonzero polynomials (Waldschmidt, Lemma 4.8).**
For any entire function `f : (ι → ℂ) → ℂ` and nonzero polynomials `P : ι → ℂ[X]`, there exist
entire functions `f₀` and `g : ι → (ι → ℂ) → ℂ` such that
`f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)`, `f₀` has polynomial degree `< deg (P j)` in every
coordinate `z_j`, and each `g_i` has polynomial degree `< deg (P j)` in every coordinate `z_j` with
`i < j`. -/
theorem exists_eq_add_sum_mul_eval_of_ne_zero [Fintype ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {P : ι → ℂ[X]} (hP : ∀ i, P i ≠ 0) :
    ∃ (f₀ : (ι → ℂ) → ℂ) (g : ι → (ι → ℂ) → ℂ),
      Differentiable ℂ f₀ ∧
      (∀ i, Differentiable ℂ (g i)) ∧
      (∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i)) ∧
      (∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w) ∧
      (∀ i j, i < j → ∀ z,
        ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w) := by
  obtain ⟨f₀, g, hf₀, hg, hdiv, hdeg₀, hdeg_g⟩ :=
    exists_eq_add_sum_mul_eval_of_list hf hP (univ.sort) (Finset.sortedLT_sort univ).pairwise
  rw [Finset.sort_toFinset] at hdiv
  exact ⟨f₀, g, hf₀, hg, hdiv,
    fun j z ↦ hdeg₀ j ((Finset.mem_sort _).mpr (mem_univ j)) z,
    fun i j hij z ↦ hdeg_g i ((Finset.mem_sort _).mpr (mem_univ i))
      j ((Finset.mem_sort _).mpr (mem_univ j)) hij z⟩

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
  have hsum_eq : (univ.sort.map fun j ↦ (P j).natDegree).sum = ∑ j, (P j).natDegree := by
    rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq univ (· ≤ ·), Multiset.map_coe,
      Multiset.sum_coe]
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

end Multivariate

end TauCeti
