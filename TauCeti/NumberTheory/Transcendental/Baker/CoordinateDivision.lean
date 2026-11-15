/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.NumberTheory.Transcendental.Baker.MDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.DividedDifference

/-!
# Division of entire functions by monic coordinate polynomials

Let `f : ℂⁿ → ℂ` be an entire function and let `P₀, …, P_{n-1} ∈ ℂ[X]` be monic polynomials in one
variable. Iterating the coordinate divided difference `TauCeti.partialDslope` along the roots of a
single polynomial `P` in coordinate `k` produces Newton's division with remainder

  `f(z) = f₀(z) + f_k(z) P(z_k)`,

where `f₀` and `f_k` are entire and `z_k ↦ f₀(update z k z_k)` is a polynomial of degree strictly
less than `deg P` for every `z`. When `P ≠ 0`, the pair `(f₀, f_k)` is uniquely determined among
entire decompositions with `deg_{z_k} f₀ < deg P`. If all roots of `P` lie in `closedBall (c k) r`
with `5 r ≤ R` and `0 < R`, any bound `‖f‖ ≤ M` on the closed polydisc `closedBall c R` propagates
to `‖f₀‖ ≤ 3 ^ deg P * M` and `‖f_k‖ ≤ (3 / R) ^ deg P * M` on `closedBall c R`. Moreover, if at
every root `ζ` of `P` the partial derivatives `∂_k^m f` of order `m < P.rootMultiplicity ζ` vanish
along the hyperplane `z_k = ζ`, then `f₀ = 0`.

Applying univariate coordinate division backwards across the coordinates `n - 1, …, 0` yields
Waldschmidt's multivariate polynomial division (`W00`, §4.3, Lemma 4.8):

  `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)`,

where `f₀` has polynomial degree `< deg (P j)` in every coordinate `z_j`, each `g_i` has polynomial
degree `< deg (P j)` in every coordinate `z_j` with `i < j`, and on `closedBall c R` both `f₀` and
`R ^ deg (P i) * g_i` are bounded by `3 ^ (∑ j, deg (P j)) * M` (hence in particular by
`9 ^ (n * p) * M` for any `p` bounding every `deg (P j)`). When the mixed partial derivatives
`D^κ f(ζ)` vanish at every root tuple `ζ ∈ ∏ᵢ Pᵢ⁻¹(0)` for all multi-orders `κ` with
`κᵢ < (P i).rootMultiplicity (ζ i)`, the remainder `f₀` vanishes identically.

## Main results

* `TauCeti.Baker.exists_eq_add_mul_eval_of_monic`: univariate coordinate division by a monic
  polynomial `P`.
* `TauCeti.Baker.eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero`: vanishing of the
  univariate remainder under root-multiplicity derivative conditions.
* `TauCeti.Baker.eq_of_eq_add_mul_eval_of_ne_zero`: uniqueness of univariate coordinate division.
* `TauCeti.Baker.norm_le_of_eq_add_mul_eval_of_monic`,
  `TauCeti.Baker.exists_degree_lt_of_eq_add_mul_eval_of_monic`,
  `TauCeti.Baker.exists_natDegree_le_of_eq_add_mul_eval_of_monic`: polydisc supremum bounds and
  coordinate degree preservation for univariate coordinate division.
* `TauCeti.Baker.exists_eq_add_sum_mul_eval_of_monic`: multivariate coordinate division with
  triangular degree bounds.
* `TauCeti.Baker.eq_of_eq_add_sum_mul_eval_of_ne_zero`: uniqueness of multivariate coordinate
  division under triangular degree bounds.
* `TauCeti.Baker.norm_le_of_eq_add_sum_mul_eval_of_monic`,
  `TauCeti.Baker.norm_le_nine_pow_of_eq_add_sum_mul_eval_of_monic`: polydisc supremum bounds with
  factors `3 ^ (∑ j, deg (P j))` and `9 ^ (n * p)`.
* `TauCeti.Baker.eq_zero_of_eq_add_sum_mul_eval_of_mDeriv_eq_zero`: vanishing of the multivariate
  remainder when `D^κ f` vanishes on `∏ᵢ Pᵢ⁻¹(0)` up to the root multiplicities.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Lemma 4.8, pp. 123–128.
-/

public section

open Finset Function Metric Nat Polynomial

namespace TauCeti.Baker

/-! ### Univariate coordinate division -/

section Univariate

variable {ι : Type*} [DecidableEq ι]

/-- If `f(y) = f₀(y) + fk(y) P(y k)` with `f₀, fk` entire, `P ≠ 0`, and `deg_{z_k} f₀ < deg P`
along the line through `z` in coordinate `k`, and if `∂_k^m f` vanishes at `update z k ζ` for every
root `ζ` of `P` and every `m < P.rootMultiplicity ζ`, then `f₀ z = 0`. -/
theorem eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero [Finite ι]
    {f f₀ fk : (ι → ℂ) → ℂ} (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k : ι}
    {P : ℂ[X]} (hP0 : P ≠ 0) (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k)) {z : ι → ℂ}
    (hdeg : ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w)
    (hzero : ∀ ζ, P.IsRoot ζ → ∀ m < P.rootMultiplicity ζ,
      (partialDeriv k)^[m] f (update z k ζ) = 0) :
    f₀ z = 0 := by
  have := Fintype.ofFinite ι
  have hf : Differentiable ℂ f := by
    have hfeq : f = fun y ↦ f₀ y + fk y * P.eval (y k) := funext hdiv
    rw [hfeq]
    exact hf₀.add (hfk.mul (P.differentiable.comp (differentiable_apply k)))
  obtain ⟨Q, hQdeg, hQ⟩ := hdeg
  suffices hQ0 : Q = 0 by
    simpa [hQ0] using (hQ (z k)).trans rfl
  by_contra hQ0
  have hQlt : Q.natDegree < P.natDegree := by
    rw [degree_eq_natDegree hQ0, degree_eq_natDegree hP0] at hQdeg
    exact WithBot.coe_lt_coe.mp hQdeg
  -- At every root `ζ` of `P`, the vanishing of `∂_k^m f` forces `Q` to vanish to at least the
  -- same multiplicity `P.rootMultiplicity ζ`.
  have hmult (ζ : ℂ) : P.rootMultiplicity ζ ≤ Q.rootMultiplicity ζ := by
    rcases Nat.eq_zero_or_pos (P.rootMultiplicity ζ) with hm0 | hmpos
    · simp [hm0]
    · have hζroot : P.IsRoot ζ := (rootMultiplicity_pos hP0).mp hmpos
      rw [le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hQ0]
      intro m hm
      have hline : (fun w ↦ f (update z k w)) =
          (fun w ↦ Q.eval w) + ((fun w ↦ fk (update z k w)) * fun w ↦ P.eval w) := by
        ext w
        simp [hdiv, hQ]
      have hg : Differentiable ℂ (fun w ↦ fk (update z k w)) := fun w ↦
        (hfk (update z k w)).comp w (hasFDerivAt_update z w).differentiableAt
      have hfz : iteratedDeriv m (fun w ↦ f (update z k w)) ζ = 0 := by
        have h := iterate_partialDeriv_eq_iteratedDeriv_update hf k m (update z k ζ)
        simp only [update_idem, update_self] at h
        rw [← h]
        exact hzero ζ hζroot m hm
      rw [hline, iteratedDeriv_add Q.differentiable.contDiff.contDiffAt
        (hg.mul P.differentiable).contDiff.contDiffAt,
        iteratedDeriv_mul hg.contDiff.contDiffAt P.differentiable.contDiff.contDiffAt] at hfz
      have hsum0 : ∑ i ∈ range (m + 1),
          (m.choose i : ℂ) * iteratedDeriv i (fun w ↦ fk (update z k w)) ζ *
            iteratedDeriv (m - i) (fun w ↦ P.eval w) ζ = 0 := by
        refine sum_eq_zero fun i _ ↦ ?_
        have hPi : (hasseDeriv (m - i) P).eval ζ = 0 :=
          (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hP0).mp le_rfl (m - i) (by omega)
        rw [Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv, hPi, mul_zero, mul_zero]
      rw [hsum0, add_zero, Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hfz
      exact (mul_eq_zero.mp hfz).resolve_left (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
  have hPsum : ∑ ζ ∈ P.roots.toFinset, P.rootMultiplicity ζ = P.natDegree := by
    calc ∑ ζ ∈ P.roots.toFinset, P.rootMultiplicity ζ
        = ∑ ζ ∈ P.roots.toFinset, P.roots.count ζ :=
          sum_congr rfl fun _ _ ↦ (count_roots P).symm
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
      _ = P.natDegree := (IsAlgClosed.splits P).natDegree_eq_card_roots.symm
  have hle : P.natDegree ≤ Q.natDegree := by
    calc P.natDegree
        = ∑ ζ ∈ P.roots.toFinset, P.rootMultiplicity ζ := hPsum.symm
      _ ≤ ∑ ζ ∈ P.roots.toFinset, Q.rootMultiplicity ζ := sum_le_sum fun ζ _ ↦ hmult ζ
      _ ≤ Q.natDegree := Q.sum_rootMultiplicity_le_natDegree P.roots.toFinset
  exact hQlt.not_ge hle

/-- **Uniqueness of univariate coordinate division.** For `P ≠ 0`, an entire function `f` admits at
most one decomposition `f(z) = f₀(z) + fk(z) P(z k)` with `f₀, fk` entire and `deg_{z_k} f₀ < deg P`
along every line in coordinate `k`. -/
theorem eq_of_eq_add_mul_eval_of_ne_zero [Finite ι] {f f₀ fk f₀' fk' : (ι → ℂ) → ℂ}
    (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk)
    (hf₀' : Differentiable ℂ f₀') (hfk' : Differentiable ℂ fk') {k : ι} {P : ℂ[X]} (hP0 : P ≠ 0)
    (hdiv : ∀ z, f z = f₀ z + fk z * P.eval (z k))
    (hdiv' : ∀ z, f z = f₀' z + fk' z * P.eval (z k))
    (hdeg : ∀ z, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w)
    (hdeg' : ∀ z, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀' (update z k w) = Q.eval w) :
    f₀ = f₀' ∧ fk = fk' := by
  have := Fintype.ofFinite ι
  have hsub_div (z : ι → ℂ) :
      (0 : (ι → ℂ) → ℂ) z = (f₀ - f₀') z + (fk - fk') z * P.eval (z k) := by
    have h1 := hdiv z
    have h2 := hdiv' z
    simp only [Pi.zero_apply, Pi.sub_apply]
    linear_combination h1 - h2
  have hzero_iter (m : ℕ) : (partialDeriv k)^[m] (0 : (ι → ℂ) → ℂ) = 0 := by
    induction m with
    | zero => rfl
    | succ r ihr => rw [iterate_succ_apply', ihr, partialDeriv_zero_fun]
  have hf₀_eq : f₀ = f₀' := by
    ext z
    rw [← sub_eq_zero]
    refine eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero (hf₀.sub hf₀')
      (hfk.sub hfk') hP0 hsub_div ?_ fun _ _ m _ ↦ by simp [hzero_iter m]
    obtain ⟨Q, hQ, hQz⟩ := hdeg z
    obtain ⟨Q', hQ', hQ'z⟩ := hdeg' z
    exact ⟨Q - Q', (degree_sub_le Q Q').trans_lt (max_lt hQ hQ'),
      fun w ↦ by simp [hQz, hQ'z]⟩
  refine ⟨hf₀_eq, ?_⟩
  -- With `f₀ = f₀'`, `(fk - fk') z * P(z k) = 0` everywhere; differentiating `m = rootMultiplicity`
  -- times along coordinate `k` cancels `P` since its `m`-th Hasse derivative at `z k` is nonzero.
  ext z
  rw [← sub_eq_zero]
  set g : ℂ → ℂ := fun w ↦ fk (update z k w) - fk' (update z k w)
  have hg : Differentiable ℂ g := fun w ↦
    ((hfk.sub hfk') (update z k w)).comp w (hasFDerivAt_update z w).differentiableAt
  have hgP : (fun w ↦ g w * P.eval w) = fun _ ↦ 0 := by
    ext w
    have h := hsub_div (update z k w)
    simp only [hf₀_eq, sub_self, Pi.zero_apply, zero_add, update_self, Pi.sub_apply] at h
    exact h.symm
  set m := P.rootMultiplicity (z k)
  have hderiv : iteratedDeriv m (fun w ↦ g w * P.eval w) (z k) = 0 := by
    rw [hgP, iteratedDeriv_const]
    simp only [ite_self]
  rw [iteratedDeriv_fun_mul hg.contDiff.contDiffAt P.differentiable.contDiff.contDiffAt] at hderiv
  have htail : ∑ i ∈ (range (m + 1)).erase 0,
      (m.choose i : ℂ) * iteratedDeriv i g (z k) *
        iteratedDeriv (m - i) (fun w ↦ P.eval w) (z k) = 0 := by
    refine sum_eq_zero fun i hi ↦ ?_
    have hi0 : i ≠ 0 := (mem_erase.mp hi).1
    have him : i < m + 1 := mem_range.mp (mem_erase.mp hi).2
    have hPi : (hasseDeriv (m - i) P).eval (z k) = 0 :=
      (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hP0).mp le_rfl (m - i) (by omega)
    rw [Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv, hPi, mul_zero, mul_zero]
  rw [← add_sum_erase _ _ (mem_range.mpr (Nat.succ_pos m)), htail, add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero,
    Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hderiv
  have hne : ((m ! : ℂ) * (hasseDeriv m P).eval (z k)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
      (eval_hasseDeriv_rootMultiplicity_ne_zero hP0 (z k))
  have hg0 : g (z k) = 0 := (mul_eq_zero.mp hderiv).resolve_right hne
  simpa [g, update_eq_self] using hg0

/-- Newton coordinate division along an explicit list of roots `l`: produces entire `f₀, fk` with
`f(z) = f₀(z) + fk(z) ∏_{ζ ∈ l} (z_k - ζ)`, `deg_{z_k} f₀ < l.length`, preservation of degree
bounds in all other coordinates `j ≠ k`, and sharp intermediate polydisc bounds. -/
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
    exact ⟨0, bot_le.trans_lt hQ, by simp⟩
  | cons ζ l ih =>
    have hq₁ : Differentiable ℂ (partialDslope k ζ f) := differentiable_partialDslope hf k ζ
    obtain ⟨r', q', hr', hq', hdiv', hdeg', hdeg_ne', hnorm'⟩ := ih hq₁
    let f₀ : (ι → ℂ) → ℂ := fun z ↦ f (update z k ζ) + (z k - ζ) * r' z
    have hf₀ : Differentiable ℂ f₀ := by
      have hupd : Differentiable ℂ (fun z : ι → ℂ ↦ update z k ζ) := by
        refine differentiable_pi.mpr fun j ↦ ?_
        by_cases hj : j = k
        · subst hj; simp only [update_self]; fun_prop
        · simp only [update_of_ne hj]; fun_prop
      exact (hf.comp hupd).add (((differentiable_apply k).sub (differentiable_const ζ)).mul hr')
    refine ⟨f₀, q', hf₀, hq', ?_, ?_, ?_, ?_⟩
    · -- (1) Division identity `f(z) = f₀(z) + q'(z) ((z_k - ζ) ∏_{η ∈ l} (z_k - η))`.
      intro z
      have hstep := eq_update_add_sub_mul_partialDslope k ζ f z
      rw [hdiv' z] at hstep
      simp only [f₀, List.map_cons, List.prod_cons, eval_mul, eval_sub, eval_X, eval_C]
      linear_combination hstep
    · -- (2) Degree strictly below `l.length + 1` in coordinate `k`.
      intro z
      obtain ⟨Q', hQ'deg, hQ'⟩ := hdeg' z
      refine ⟨C (f (update z k ζ)) + (X - C ζ) * Q',
        (degree_add_le _ _).trans_lt (max_lt
          (degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr (Nat.succ_pos l.length))) ?_),
        fun w ↦ ?_⟩
      · rcases eq_or_ne Q' 0 with rfl | hQ'0
        · simp
        · rw [degree_eq_natDegree hQ'0] at hQ'deg
          have hlt : Q'.natDegree < l.length := Nat.cast_lt.mp hQ'deg
          calc ((X - C ζ) * Q').degree
              ≤ (X - C ζ).degree + Q'.degree := degree_mul_le _ _
            _ = ((1 + Q'.natDegree : ℕ) : WithBot ℕ) := by
                rw [degree_X_sub_C, degree_eq_natDegree hQ'0]; rfl
            _ < ((l.length + 1 : ℕ) : WithBot ℕ) := Nat.cast_lt.mpr (by omega)
      · simp [f₀, update_idem, update_self, hQ' w]
    · -- (3) Preservation of degree `< d` in every other coordinate `j ≠ k`.
      intro j hjk d hfj
      have hq₁j := exists_degree_lt_partialDslope_of_ne hf hjk ζ hfj
      obtain ⟨hr'j, hq'j⟩ := hdeg_ne' j hjk d hq₁j
      refine ⟨fun z ↦ ?_, hq'j⟩
      obtain ⟨Q₁, hQ₁deg, hQ₁⟩ := exists_degree_lt_update_of_ne hjk ζ hfj z
      obtain ⟨Q₂, hQ₂deg, hQ₂⟩ := hr'j z
      have hCQ₂ : (C (z k - ζ) * Q₂).degree ≤ Q₂.degree := by
        rcases eq_or_ne (z k - ζ) 0 with hc0 | hc0
        · simp [hc0]
        · rw [degree_C_mul hc0]
      exact ⟨Q₁ + C (z k - ζ) * Q₂,
        (degree_add_le _ _).trans_lt (max_lt hQ₁deg (hCQ₂.trans_lt hQ₂deg)),
        fun w ↦ by simp [f₀, update_of_ne hjk.symm, hQ₁ w, hQ₂ w]⟩
    · -- (4) Polydisc supremum bounds on `closedBall c R` when `5 * r ≤ R`.
      intro c r R M hR hrR hroots hM z hz
      have hζ : ζ ∈ closedBall (c k) r := hroots ζ List.mem_cons_self
      have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hz)
      have hr_lt_R : r < R := by linarith [dist_nonneg.trans (mem_closedBall.mp hζ)]
      have hRr : 0 < R - r := sub_pos.mpr hr_lt_R
      have hq₁M (w : ι → ℂ) (hw : w ∈ closedBall c R) :
          ‖partialDslope k ζ f w‖ ≤ 5 / (2 * R) * M := by
        refine (norm_partialDslope_le hf hζ hr_lt_R hM hw).trans ?_
        rw [div_le_iff₀ hRr]
        have h1 : 4 * R ≤ 5 * (R - r) := by linarith
        have h2 : 4 * R * M ≤ 5 * (R - r) * M := mul_le_mul_of_nonneg_right h1 hM0
        have hRne : R ≠ 0 := hR.ne'
        calc 2 * M = (4 * R * M) / (2 * R) := by field_simp; ring
          _ ≤ (5 * (R - r) * M) / (2 * R) := div_le_div_of_nonneg_right h2 (by positivity)
          _ = 5 / (2 * R) * M * (R - r) := by ring
      obtain ⟨hr'z, hq'z⟩ := hnorm' c r R (5 / (2 * R) * M) hR hrR
        (fun η hη ↦ hroots η (List.mem_cons_of_mem ζ hη)) hq₁M z hz
      refine ⟨?_, ?_⟩
      · have hfζ : ‖f (update z k ζ)‖ ≤ M :=
          norm_update_le_of_mem_closedBall hζ hr_lt_R.le hM hz
        have hz_pi : z ∈ Set.univ.pi fun i ↦ closedBall (c i) R := by rwa [← closedBall_pi c hR.le]
        have hzk : ‖z k - c k‖ ≤ R := by
          simpa [dist_eq_norm] using mem_closedBall.mp (hz_pi k trivial)
        have hζc : ‖ζ - c k‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hζ
        have hzkζ : ‖z k - ζ‖ ≤ 6 / 5 * R := by
          have htri := norm_sub_le_norm_sub_add_norm_sub (z k) (c k) ζ
          rw [norm_sub_rev (c k) ζ] at htri
          linarith
        have hRne : R ≠ 0 := hR.ne'
        calc ‖f₀ z‖
            ≤ ‖f (update z k ζ)‖ + ‖(z k - ζ) * r' z‖ := norm_add_le _ _
          _ = ‖f (update z k ζ)‖ + ‖z k - ζ‖ * ‖r' z‖ := by rw [norm_mul]
          _ ≤ M + (6 / 5 * R) * (((3 : ℝ) ^ l.length - 1) / 2 * (5 / (2 * R) * M)) := by
              gcongr
          _ = ((3 : ℝ) ^ (l.length + 1) - 1) / 2 * M := by
              rw [pow_succ]
              field_simp
              ring
      · simpa only [List.length_cons, pow_succ, mul_assoc] using hq'z

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
  have hPprod : (l.map fun ζ ↦ X - C ζ).prod = P := by
    have hcoe : (Multiset.ofList l) = P.roots := Multiset.coe_toList P.roots
    calc (l.map fun ζ ↦ X - C ζ).prod
        = ((Multiset.ofList l).map fun ζ ↦ X - C ζ).prod := rfl
      _ = (P.roots.map fun ζ ↦ X - C ζ).prod := by rw [hcoe]
      _ = P := ((IsAlgClosed.splits P).eq_prod_roots_of_monic hP).symm
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

/-- **Univariate coordinate division by a monic polynomial (Waldschmidt, Lemma 4.8).**
For any entire function `f : (ι → ℂ) → ℂ`, coordinate `k : ι`, and monic polynomial `P : ℂ[X]`,
there exist entire functions `f₀, fk : (ι → ℂ) → ℂ` such that `f(z) = f₀(z) + fk(z) P(z k)` and
`f₀` is a polynomial of degree strictly less than `deg P` in `z k` along every coordinate line. -/
theorem exists_eq_add_mul_eval_of_monic [Finite ι] {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (k : ι) {P : ℂ[X]} (hP : P.Monic) :
    ∃ f₀ fk : (ι → ℂ) → ℂ,
      Differentiable ℂ f₀ ∧
      Differentiable ℂ fk ∧
      (∀ z, f z = f₀ z + fk z * P.eval (z k)) ∧
      (∀ z, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w) := by
  have := Fintype.ofFinite ι
  obtain ⟨f₀, fk, hf₀, hfk, hdiv, hdeg, -, -⟩ := exists_eq_add_mul_eval_of_monic_full hf k hP
  exact ⟨f₀, fk, hf₀, hfk, hdiv, hdeg⟩

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
  obtain ⟨f₀', fk', hf₀', hfk', hdiv', hdeg', -, hnorm'⟩ :=
    exists_eq_add_mul_eval_of_monic_full hf k hP
  obtain ⟨rfl, rfl⟩ := eq_of_eq_add_mul_eval_of_ne_zero hf₀ hfk hf₀' hfk' hP.ne_zero
    hdiv hdiv' hdeg hdeg'
  obtain ⟨h0, hk⟩ := hnorm' c r R M hR hrR hroots hM z hz
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hz)
  refine ⟨h0.trans (mul_le_mul_of_nonneg_right ?_ hM0),
    hk.trans (mul_le_mul_of_nonneg_right ?_ hM0)⟩
  · have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ P.natDegree := by positivity
    linarith
  · refine pow_le_pow_left₀ (by positivity) ?_ P.natDegree
    calc 5 / (2 * R) = (5 / 2) / R := by ring
      _ ≤ 3 / R := by
          gcongr
          norm_num

/-- **Coordinate degree preservation for univariate division.** If `f(y) = f₀(y) + fk(y) P(y k)`
with `f₀, fk` entire, `P` monic, and `deg_{z_k} f₀ < deg P`, then any strict polynomial degree
bound `< d` on `f` in another coordinate `j ≠ k` transfers to both `f₀` and `fk`. -/
theorem exists_degree_lt_of_eq_add_mul_eval_of_monic [Finite ι] {f f₀ fk : (ι → ℂ) → ℂ}
    (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k j : ι} (hjk : j ≠ k)
    {P : ℂ[X]} (hP : P.Monic) (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k))
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update y k w) = Q.eval w)
    {d : WithBot ℕ} (hfj : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) :
    (∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f₀ (update y j w) = Q.eval w) ∧
    (∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, fk (update y j w) = Q.eval w) := by
  have := Fintype.ofFinite ι
  have hf : Differentiable ℂ f := by
    have hfeq : f = fun y ↦ f₀ y + fk y * P.eval (y k) := funext hdiv
    rw [hfeq]
    exact hf₀.add (hfk.mul (P.differentiable.comp (differentiable_apply k)))
  obtain ⟨f₀', fk', hf₀', hfk', hdiv', hdeg', hdeg_ne', -⟩ :=
    exists_eq_add_mul_eval_of_monic_full hf k hP
  obtain ⟨rfl, rfl⟩ := eq_of_eq_add_mul_eval_of_ne_zero hf₀ hfk hf₀' hfk' hP.ne_zero
    hdiv hdiv' hdeg hdeg'
  exact hdeg_ne' j hjk d hfj

/-- If `f(y) = f₀(y) + fk(y) P(y k)` with `f₀, fk` entire, `P` monic, and `deg_{z_k} f₀ < deg P`,
then any `natDegree ≤ e` bound on `f` in another coordinate `j ≠ k` transfers to both `f₀` and
`fk`. -/
theorem exists_natDegree_le_of_eq_add_mul_eval_of_monic [Finite ι] {f f₀ fk : (ι → ℂ) → ℂ}
    (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k j : ι} (hjk : j ≠ k)
    {P : ℂ[X]} (hP : P.Monic) (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k))
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update y k w) = Q.eval w)
    {e : ℕ} (hfj : ∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update y j w) = Q.eval w) :
    (∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f₀ (update y j w) = Q.eval w) ∧
    (∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, fk (update y j w) = Q.eval w) := by
  have hfj' (y : ι → ℂ) :
      ∃ Q : ℂ[X], Q.degree < (e + 1 : ℕ) ∧ ∀ w, f (update y j w) = Q.eval w := by
    obtain ⟨Q, hQ, hQy⟩ := hfj y
    exact ⟨Q, (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hQ)).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self e)), hQy⟩
  obtain ⟨h0, hk⟩ := exists_degree_lt_of_eq_add_mul_eval_of_monic hf₀ hfk hjk hP hdiv hdeg hfj'
  have toNat {h : (ι → ℂ) → ℂ}
      (hh : ∀ y, ∃ Q : ℂ[X], Q.degree < (e + 1 : ℕ) ∧ ∀ w, h (update y j w) = Q.eval w)
      (y : ι → ℂ) : ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, h (update y j w) = Q.eval w := by
    obtain ⟨Q, hQ, hQy⟩ := hh y
    refine ⟨Q, ?_, hQy⟩
    rcases eq_or_ne Q 0 with rfl | hQ0
    · simp
    · rw [degree_eq_natDegree hQ0] at hQ
      exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp hQ)
  exact ⟨toNat h0, toNat hk⟩

end Univariate

/-! ### Multivariate coordinate division -/

section Multivariate

variable {n : ℕ}

/-- A mixed partial derivative `mDeriv σ f` of an entire function `f` with `σ j = 0` preserves a
strict polynomial degree bound `< d` in coordinate `j`. -/
theorem exists_degree_lt_mDeriv_of_eq_zero {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    {j : Fin n} {σ : Fin n → ℕ} (hσj : σ j = 0) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) :
    ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, mDeriv σ f (update z j w) = Q.eval w := by
  suffices ∀ (s : Finset (Fin n)), j ∉ s →
      ∀ (τ : Fin n → ℕ), (∀ i ∉ s, τ i = 0) →
        ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, mDeriv τ f (update z j w) = Q.eval w by
    exact this (univ.filter fun i ↦ σ i ≠ 0) (by simp [hσj]) σ
      (fun i hi ↦ not_not.mp (by simpa using hi))
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ τ hτ
    have hτ0 : τ = 0 := by ext i; exact hτ i (notMem_empty i)
    rw [hτ0, mDeriv_zero]
    exact hdeg
  | insert i s his ih =>
    intro hjs τ hτ
    have hji : j ≠ i := fun h ↦ hjs (h ▸ mem_insert_self i s)
    have hjs' : j ∉ s := fun h ↦ hjs (mem_insert_of_mem h)
    have hupd : ∀ m ∉ s, update τ i 0 m = 0 := by
      intro m hms
      by_cases hmi : m = i
      · subst hmi; simp
      · simp [hmi, hτ m (fun hm ↦ hms ((mem_insert.mp hm).resolve_left hmi))]
    rw [mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero hf τ i]
    exact exists_degree_lt_iterate_partialDeriv_of_ne
      (differentiable_mDeriv hf (update τ i 0)) hji (ih hjs' (update τ i 0) hupd) (τ i)

/-- **Vanishing of the multivariate remainder (Waldschmidt, Lemma 4.8).**
Let `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` where `f₀` and each `g_i` are entire, each `P i`
is nonzero, and `f₀` is a polynomial of degree `< deg (P j)` in every coordinate `z_j`. If
`D^κ f(ζ) = 0` at every root tuple `ζ ∈ ∏ᵢ Pᵢ⁻¹(0)` and for every multi-order `κ` satisfying
`∀ i, κ i < (P i).rootMultiplicity (ζ i)`, then `f₀ = 0`. -/
theorem eq_zero_of_eq_add_sum_mul_eval_of_mDeriv_eq_zero
    {f f₀ : (Fin n → ℂ) → ℂ} {g : Fin n → (Fin n → ℂ) → ℂ} {P : Fin n → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀) (hg : ∀ i, Differentiable ℂ (g i)) (hP0 : ∀ i, P i ≠ 0)
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hzero : ∀ ζ : Fin n → ℂ, (∀ i, (P i).IsRoot (ζ i)) →
      ∀ κ : Fin n → ℕ, (∀ i, κ i < (P i).rootMultiplicity (ζ i)) → mDeriv κ f ζ = 0) :
    f₀ = 0 := by
  have hterm (i : Fin n) : Differentiable ℂ (fun y : Fin n → ℂ ↦ g i y * (P i).eval (y i)) :=
    (hg i).mul ((P i).differentiable.comp (differentiable_apply i))
  -- Induct on `m ≤ n`: when coordinates `≥ m` lie at roots of `P i` and `κ` vanishes on `< m`
  -- while staying below the root multiplicities on `≥ m`, `mDeriv κ f₀ z = 0`.
  have claim (m : ℕ) (hm : m ≤ n) :
      ∀ (z : Fin n → ℂ), (∀ i : Fin n, m ≤ i.val → (P i).IsRoot (z i)) →
      ∀ (κ : Fin n → ℕ), (∀ i : Fin n, i.val < m → κ i = 0) →
        (∀ i : Fin n, m ≤ i.val → κ i < (P i).rootMultiplicity (z i)) →
        mDeriv κ f₀ z = 0 := by
    induction m with
    | zero =>
      -- Base case `m = 0`: at a root tuple `z ∈ ∏ᵢ Pᵢ⁻¹(0)`, `D^κ` annihilates every term
      -- `g i * P i (z i)` because all derivatives of `P i` of order `≤ κ i` vanish at `z i`.
      intro z hz κ _ hκ
      have hz' : ∀ i, (P i).IsRoot (z i) := fun i ↦ hz i (Nat.zero_le _)
      have hκ' : ∀ i, κ i < (P i).rootMultiplicity (z i) := fun i ↦ hκ i (Nat.zero_le _)
      have hf_eq : f = f₀ + ∑ i : Fin n, fun y ↦ g i y * (P i).eval (y i) := by
        ext y
        simp [hdiv y, Finset.sum_apply]
      have h0 : mDeriv κ f z = 0 := hzero z hz' κ hκ'
      rw [hf_eq, mDeriv_add hf₀ (Differentiable.sum fun i _ ↦ hterm i),
        mDeriv_sum univ (fun i _ ↦ hterm i), Pi.add_apply, Finset.sum_apply] at h0
      have hsum0 : ∑ i : Fin n, mDeriv κ (fun y ↦ g i y * (P i).eval (y i)) z = 0 := by
        refine sum_eq_zero fun i _ ↦ ?_
        have hcomm : (fun y : Fin n → ℂ ↦ g i y * (P i).eval (y i)) =
            fun y ↦ (P i).eval (y i) * g i y := by
          ext y; ring
        have hPi_ent : Differentiable ℂ (fun y : Fin n → ℂ ↦ (P i).eval (y i)) :=
          (P i).differentiable.comp (differentiable_apply i)
        rw [hcomm, mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero (hPi_ent.fun_mul (hg i)) κ i,
          mDeriv_mul_of_update_eq hPi_ent (hg i) (fun j hj y s ↦ by
            have hji : i ≠ j := fun h ↦ hj (by subst h; simp)
            simp [update_of_ne hji])]
        set G : (Fin n → ℂ) → ℂ := mDeriv (update κ i 0) (g i)
        have hG : Differentiable ℂ G := differentiable_mDeriv (hg i) _
        rw [iterate_partialDeriv_eq_iteratedDeriv_update (hPi_ent.fun_mul hG) i (κ i) z]
        have hline : (fun w ↦ (P i).eval (update z i w i) * G (update z i w)) =
            (fun w ↦ (P i).eval w) * fun w ↦ G (update z i w) := by
          ext w; simp
        have hG_line : Differentiable ℂ (fun w ↦ G (update z i w)) := fun w ↦
          (hG (update z i w)).comp w (hasFDerivAt_update z w).differentiableAt
        rw [hline,
          iteratedDeriv_mul (P i).differentiable.contDiff.contDiffAt hG_line.contDiff.contDiffAt]
        refine sum_eq_zero fun r hr ↦ ?_
        have hr_lt : r < (P i).rootMultiplicity (z i) :=
          (Nat.lt_succ_iff.mp (mem_range.mp hr)).trans_lt (hκ' i)
        have hPir : (hasseDeriv r (P i)).eval (z i) = 0 :=
          (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero (hP0 i)).mp le_rfl r hr_lt
        rw [Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv, hPir, mul_zero,
          mul_zero, zero_mul]
      rw [hsum0, add_zero] at h0
      exact h0
    | succ m ih =>
      -- Inductive step: `D^κ f₀` has polynomial degree `< deg (P m)` in coordinate `j = m` and
      -- its partial derivatives `∂_j^r (D^κ f₀) = D^{κ + r e_j} f₀` vanish at every root of `P j`
      -- by the induction hypothesis, so univariate vanishing gives `D^κ f₀ z = 0`.
      intro z hz κ hκ0 hκ
      let j : Fin n := ⟨m, hm⟩
      have hj_val : j.val = m := rfl
      have hκj : κ j = 0 := hκ0 j (by simp [hj_val])
      have hF : Differentiable ℂ (mDeriv κ f₀) := differentiable_mDeriv hf₀ κ
      have hFdeg : ∃ Q : ℂ[X], Q.degree < (P j).degree ∧
          ∀ w, mDeriv κ f₀ (update z j w) = Q.eval w :=
        exists_degree_lt_mDeriv_of_eq_zero hf₀ hκj (hdeg₀ j) z
      refine eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero
        (f := mDeriv κ f₀) hF (differentiable_const 0) (hP0 j) (fun y ↦ by simp) hFdeg
        fun ζ hζ r hr ↦ ?_
      have hupd : update (κ + Pi.single j r) j 0 = κ := by
        ext i
        by_cases hij : i = j
        · subst hij; simp [hκj]
        · simp [hij]
      have hstep : (partialDeriv j)^[r] (mDeriv κ f₀) (update z j ζ) =
          mDeriv (κ + Pi.single j r) f₀ (update z j ζ) := by
        have h := congrFun
          (mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero hf₀ (κ + Pi.single j r) j)
          (update z j ζ)
        rw [hupd] at h
        simpa [hκj] using h.symm
      rw [hstep]
      refine ih (Nat.le_of_succ_le hm) (update z j ζ) ?_ (κ + Pi.single j r) ?_ ?_
      · intro i hi
        by_cases hij : i = j
        · subst hij; simpa using hζ
        · have him : i.val ≠ m := fun h ↦ hij (Fin.ext (h.trans hj_val.symm))
          rw [update_of_ne hij]
          exact hz i (by omega)
      · intro i hi
        have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
        simp [hij, hκ0 i (Nat.lt_succ_of_lt hi)]
      · intro i hi
        by_cases hij : i = j
        · subst hij
          simpa [hκj] using hr
        · have him : i.val ≠ m := fun h ↦ hij (Fin.ext (h.trans hj_val.symm))
          rw [update_of_ne hij, Pi.add_apply, Pi.single_eq_of_ne hij, add_zero]
          exact hκ i (by omega)
  ext z
  simpa using claim n le_rfl z (fun i hi ↦ (i.isLt.not_ge hi).elim) 0 (fun _ _ ↦ rfl)
    (fun i hi ↦ (i.isLt.not_ge hi).elim)

/-- **Uniqueness of multivariate coordinate division under triangular degree bounds.**
For `P : Fin n → ℂ[X]` with `∀ i, P i ≠ 0`, an entire function `f` has at most one decomposition
`f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` with `f₀` and all `g_i` entire,
`deg_{z_j} f₀ < deg (P j)` for all `j`, and `deg_{z_j} g_i < deg (P j)` for all `i < j`. -/
theorem eq_of_eq_add_sum_mul_eval_of_ne_zero
    {f f₀ f₀' : (Fin n → ℂ) → ℂ} {g g' : Fin n → (Fin n → ℂ) → ℂ} {P : Fin n → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀) (hg : ∀ i, Differentiable ℂ (g i))
    (hf₀' : Differentiable ℂ f₀') (hg' : ∀ i, Differentiable ℂ (g' i))
    (hP0 : ∀ i, P i ≠ 0)
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdiv' : ∀ z, f z = f₀' z + ∑ i, g' i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hdeg₀' : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀' (update z j w) = Q.eval w)
    (hdeg_g : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w)
    (hdeg_g' : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g' i (update z j w) = Q.eval w) :
    f₀ = f₀' ∧ g = g' := by
  have hmul_C_deg (Q : ℂ[X]) (c : ℂ) : (Q * C c).degree ≤ Q.degree := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · rw [degree_mul_C hc0]
  have hδ₀_ent : Differentiable ℂ (f₀ - f₀') := hf₀.sub hf₀'
  have hδ_ent (i : Fin n) : Differentiable ℂ (g i - g' i) := (hg i).sub (hg' i)
  have hδ₀_deg (j : Fin n) (z : Fin n → ℂ) :
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, (f₀ - f₀') (update z j w) = Q.eval w := by
    obtain ⟨Q, hQ, hQz⟩ := hdeg₀ j z
    obtain ⟨Q', hQ', hQ'z⟩ := hdeg₀' j z
    exact ⟨Q - Q', (degree_sub_le Q Q').trans_lt (max_lt hQ hQ'),
      fun w ↦ by simp [hQz, hQ'z]⟩
  have hδ_deg {i j : Fin n} (hij : i < j) (z : Fin n → ℂ) :
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, (g i - g' i) (update z j w) = Q.eval w := by
    obtain ⟨Q, hQ, hQz⟩ := hdeg_g i j hij z
    obtain ⟨Q', hQ', hQ'z⟩ := hdeg_g' i j hij z
    exact ⟨Q - Q', (degree_sub_le Q Q').trans_lt (max_lt hQ hQ'),
      fun w ↦ by simp [hQz, hQ'z]⟩
  -- Peel off coordinates `j = n - 1, …, 0`: at step `d + 1`, every remaining term with `i < j`
  -- has degree `< deg (P j)` in `z_j` by triangularity, so univariate uniqueness in `z_j` forces
  -- both `g j - g' j = 0` and the lower-index sum `F` to vanish.
  have peel (d : ℕ) (hd : d ≤ n) :
      (∀ z, (f₀ - f₀') z + ∑ i ∈ univ.filter (fun i : Fin n ↦ i.val < n - d),
        (g i - g' i) z * (P i).eval (z i) = 0) ∧
      (∀ i : Fin n, n - d ≤ i.val → g i - g' i = 0) := by
    induction d with
    | zero =>
      refine ⟨fun z ↦ ?_, fun i hi ↦ (i.isLt.not_ge (by simpa using hi)).elim⟩
      have hfilt : univ.filter (fun i : Fin n ↦ i.val < n - 0) = univ :=
        filter_true_of_mem fun (i : Fin n) _ ↦ by simp
      rw [hfilt]
      have h1 := hdiv z
      have h2 := hdiv' z
      have hsum : ∑ i : Fin n, (g i - g' i) z * (P i).eval (z i) =
          (∑ i : Fin n, g i z * (P i).eval (z i)) - ∑ i : Fin n, g' i z * (P i).eval (z i) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun i _ ↦ sub_mul (g i z) (g' i z) _
      rw [hsum, Pi.sub_apply]
      linear_combination h2 - h1
    | succ d ih =>
      obtain ⟨hsum_d, hzero_d⟩ := ih (Nat.le_of_succ_le hd)
      set j : Fin n := ⟨n - (d + 1), by omega⟩
      have hj_val : j.val = n - (d + 1) := rfl
      set S : Finset (Fin n) := univ.filter (fun i : Fin n ↦ i.val < n - (d + 1)) with hS_def
      set F : (Fin n → ℂ) → ℂ :=
        fun z ↦ (f₀ - f₀') z + ∑ i ∈ S, (g i - g' i) z * (P i).eval (z i) with hF_def
      have hF : Differentiable ℂ F := by
        rw [hF_def]
        exact hδ₀_ent.add (Differentiable.fun_sum fun i _ ↦
          (hδ_ent i).mul ((P i).differentiable.comp (differentiable_apply i)))
      have hsplit (z : Fin n → ℂ) :
          (0 : (Fin n → ℂ) → ℂ) z = F z + (g j - g' j) z * (P j).eval (z j) := by
        have hfilt : univ.filter (fun i : Fin n ↦ i.val < n - d) = insert j S := by
          ext i
          simp only [hS_def, mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff, hj_val]
          omega
        have hjS : j ∉ S := by simp [hS_def, hj_val]
        have h := hsum_d z
        rw [hfilt, sum_insert hjS] at h
        rw [hF_def, Pi.zero_apply]
        linear_combination -h
      have hF_deg (z : Fin n → ℂ) :
          ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, F (update z j w) = Q.eval w := by
        obtain ⟨Q₀, hQ₀, hQ₀z⟩ := hδ₀_deg j z
        have hS_deg : ∀ T : Finset (Fin n), T ⊆ S →
            ∃ QT : ℂ[X], QT.degree < (P j).degree ∧
              ∀ w, (∑ i ∈ T, (g i - g' i) (update z j w) * (P i).eval (update z j w i)) =
                QT.eval w := by
          intro T hTS
          induction T using Finset.induction_on with
          | empty => exact ⟨0, bot_le.trans_lt hQ₀, by simp⟩
          | insert a T haT ihT =>
            obtain ⟨QT, hQT, hQTz⟩ := ihT (Subset.trans (subset_insert a T) hTS)
            have haS : a ∈ S := hTS (mem_insert_self a T)
            have haj : a < j := by
              have ha_lt : a.val < n - (d + 1) := by
                rw [hS_def] at haS
                exact (mem_filter.mp haS).2
              exact Fin.lt_def.mpr (by rwa [hj_val])
            obtain ⟨Qa, hQa, hQaz⟩ := hδ_deg haj z
            refine ⟨Qa * C ((P a).eval (z a)) + QT,
              (degree_add_le _ _).trans_lt (max_lt ((hmul_C_deg Qa _).trans_lt hQa) hQT),
              fun w ↦ ?_⟩
            rw [sum_insert haT, eval_add, eval_mul, eval_C, ← hQTz w, ← hQaz w,
              update_of_ne haj.ne]
        obtain ⟨QS, hQS, hQSz⟩ := hS_deg S Subset.rfl
        exact ⟨Q₀ + QS, (degree_add_le _ _).trans_lt (max_lt hQ₀ hQS),
          fun w ↦ by simp only [hF_def, eval_add, hQ₀z w, hQSz w]⟩
      have h0_deg (z : Fin n → ℂ) :
          ∃ Q : ℂ[X], Q.degree < (P j).degree ∧
            ∀ w, (0 : (Fin n → ℂ) → ℂ) (update z j w) = Q.eval w := by
        obtain ⟨Q₀, hQ₀, _⟩ := hδ₀_deg j z
        exact ⟨0, bot_le.trans_lt hQ₀, by simp⟩
      obtain ⟨hF0, hδj0⟩ := eq_of_eq_add_mul_eval_of_ne_zero
        (f := (0 : (Fin n → ℂ) → ℂ)) (f₀ := F) (fk := g j - g' j)
        (f₀' := (0 : (Fin n → ℂ) → ℂ)) (fk' := (0 : (Fin n → ℂ) → ℂ))
        hF (hδ_ent j) (differentiable_const 0) (differentiable_const 0) (hP0 j)
        hsplit (fun _ ↦ by simp) hF_deg h0_deg
      refine ⟨fun z ↦ by simpa [hF_def] using congrFun hF0 z, fun i hi ↦ ?_⟩
      by_cases hij : i = j
      · subst hij; exact hδj0
      · have hij' : i.val ≠ n - (d + 1) := fun h ↦ hij (Fin.ext (h.trans hj_val.symm))
        exact hzero_d i (by omega)
  obtain ⟨h0_sum, h0_all⟩ := peel n le_rfl
  have hδ_eq (i : Fin n) : g i = g' i := sub_eq_zero.mp (h0_all i (by simp))
  refine ⟨sub_eq_zero.mp (funext fun z ↦ ?_), funext hδ_eq⟩
  simpa using h0_sum z

/-- Multivariate coordinate division along a sorted duplicate-free list `l : List (Fin n)`:
produces entire `f₀` and `g` with triangular degree bounds and sharp `3 ^ (∑_{j ∈ l} deg (P j))`
polydisc norm bounds. -/
private theorem exists_eq_add_sum_mul_eval_of_list {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    {P : Fin n → ℂ[X]} (hP : ∀ i, (P i).Monic) :
    ∀ (l : List (Fin n)), l.Nodup → l.Pairwise (· < ·) →
      ∃ (f₀ : (Fin n → ℂ) → ℂ) (g : Fin n → (Fin n → ℂ) → ℂ),
        Differentiable ℂ f₀ ∧
        (∀ i, Differentiable ℂ (g i)) ∧
        (∀ i ∉ l, g i = 0) ∧
        (∀ z, f z = f₀ z + ∑ i ∈ l.toFinset, g i z * (P i).eval (z i)) ∧
        (∀ j ∈ l, ∀ z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w) ∧
        (∀ i ∈ l, ∀ j ∈ l, i < j → ∀ z,
          ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w) ∧
        (∀ (c : Fin n → ℂ) (r R M : ℝ), 0 < R → 5 * r ≤ R →
          (∀ i ∈ l, ∀ ζ, (P i).IsRoot ζ → ζ ∈ closedBall (c i) r) →
          (∀ w ∈ closedBall c R, ‖f w‖ ≤ M) →
          ∀ z ∈ closedBall c R,
            ‖f₀ z‖ ≤ 3 ^ (l.map fun j ↦ (P j).natDegree).sum * M ∧
            ∀ i ∈ l, ‖g i z‖ ≤
              3 ^ (l.map fun j ↦ (P j).natDegree).sum / R ^ (P i).natDegree * M) := by
  intro l hl hsort
  induction l with
  | nil =>
    refine ⟨f, fun _ ↦ 0, hf, fun _ ↦ differentiable_const 0, fun _ _ ↦ rfl,
      fun z ↦ by simp, fun _ hj ↦ by simp at hj, fun _ hi ↦ by simp at hi,
      fun c r R M _ _ _ hM z hz ↦ ⟨by simpa using hM z hz, fun _ hi ↦ by simp at hi⟩⟩
  | cons i l' ih =>
    -- Divide `f` along the tail `l'` first (`i < j` for every `j ∈ l'`), then divide the
    -- intermediate remainder `r'` by `P i` in coordinate `i`, preserving `< deg (P j)` on `l'`.
    obtain ⟨hil', hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨hilt, hsort'⟩ := List.pairwise_cons.mp hsort
    obtain ⟨r', g', hr', hg', hg'_out, hdiv', hdeg_r', hdeg_g', hnorm'⟩ := ih hl' hsort'
    obtain ⟨f₀, gi, hf₀, hgi, hdiv_i, hdeg_i⟩ := exists_eq_add_mul_eval_of_monic hr' i (hP i)
    let g : Fin n → (Fin n → ℂ) → ℂ := update g' i gi
    have hg (m : Fin n) : Differentiable ℂ (g m) := by
      by_cases hm : m = i
      · subst hm; simpa [g] using hgi
      · simpa [g, hm] using hg' m
    refine ⟨f₀, g, hf₀, hg, ?_, ?_, ?_, ?_, ?_⟩
    · -- Support of `g` stays within `i :: l'`.
      intro m hm
      have hmi : m ≠ i := fun h ↦ hm (by simp [h])
      simp [g, hmi, hg'_out m (fun h ↦ hm (List.mem_cons_of_mem i h))]
    · -- Multivariate division identity across `i :: l'`.
      intro z
      have hi_not : i ∉ l'.toFinset := by simpa using hil'
      rw [List.toFinset_cons, sum_insert hi_not]
      have hsum_eq : ∑ m ∈ l'.toFinset, g m z * (P m).eval (z m) =
          ∑ m ∈ l'.toFinset, g' m z * (P m).eval (z m) := by
        refine sum_congr rfl fun m hm ↦ ?_
        have hmi : m ≠ i := fun h ↦ hi_not (h ▸ hm)
        simp [g, hmi]
      rw [hsum_eq, hdiv' z, hdiv_i z]
      simp [g]
      ring
    · -- Degree `< deg (P j)` of `f₀` for every `j ∈ i :: l'`.
      intro j hj z
      rcases List.mem_cons.mp hj with rfl | hjl'
      · exact hdeg_i z
      · have hji : j ≠ i := (hilt j hjl').ne'
        exact (exists_degree_lt_of_eq_add_mul_eval_of_monic hf₀ hgi hji (hP i) hdiv_i hdeg_i
          (hdeg_r' j hjl')).1 z
    · -- Triangular degree `< deg (P b)` of `g a` for `a < b` in `i :: l'`.
      intro a ha b hb hab z
      rcases List.mem_cons.mp ha with rfl | hal'
      · have hbl' : b ∈ l' := (List.mem_cons.mp hb).resolve_left hab.ne'
        have hbi : b ≠ a := hab.ne'
        have hgi_b := (exists_degree_lt_of_eq_add_mul_eval_of_monic hf₀ hgi hbi (hP a) hdiv_i
          hdeg_i (hdeg_r' b hbl')).2 z
        simpa [g] using hgi_b
      · have hai : a ≠ i := (hilt a hal').ne'
        have hbl' : b ∈ l' := (List.mem_cons.mp hb).resolve_left fun hbi ↦
          (hab.trans (hbi ▸ hilt a hal')).false
        simpa [g, hai] using hdeg_g' a hal' b hbl' hab z
    · -- Polydisc supremum bounds with factor `3 ^ ∑_{j ∈ i :: l'} deg (P j)`.
      intro c r R M hR hrR hroots hM z hz
      have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hz)
      let S' : ℕ := (l'.map fun j ↦ (P j).natDegree).sum
      have hr'_M (w : Fin n → ℂ) (hw : w ∈ closedBall c R) : ‖r' w‖ ≤ (3 : ℝ) ^ S' * M :=
        (hnorm' c r R M hR hrR (fun m hm ↦ hroots m (List.mem_cons_of_mem i hm)) hM w hw).1
      obtain ⟨hf₀_z, hgi_z⟩ := norm_le_of_eq_add_mul_eval_of_monic hf₀ hgi (hP i) hdiv_i hdeg_i
        hR hrR (hroots i List.mem_cons_self) hr'_M hz
      have hpow_sum : (3 : ℝ) ^ (P i).natDegree * (3 : ℝ) ^ S' =
          (3 : ℝ) ^ ((i :: l').map fun j ↦ (P j).natDegree).sum := by
        simp [S', pow_add]
      refine ⟨?_, fun m hm ↦ ?_⟩
      · calc ‖f₀ z‖
            ≤ (3 : ℝ) ^ (P i).natDegree * ((3 : ℝ) ^ S' * M) := hf₀_z
          _ = (3 : ℝ) ^ ((i :: l').map fun j ↦ (P j).natDegree).sum * M := by
              rw [← mul_assoc, hpow_sum]
      · rcases List.mem_cons.mp hm with rfl | hml'
        · simpa only [g, update_self, div_pow, ← hpow_sum] using
            (hgi_z.trans_eq (by ring))
        · have hmi : m ≠ i := (hilt m hml').ne'
          have hgm := (hnorm' c r R M hR hrR
            (fun b hb ↦ hroots b (List.mem_cons_of_mem i hb)) hM z hz).2 m hml'
          simp only [g, update_of_ne hmi]
          refine hgm.trans ?_
          have hle : (3 : ℝ) ^ S' ≤ (3 : ℝ) ^ ((i :: l').map fun j ↦ (P j).natDegree).sum := by
            simp only [List.map_cons, List.sum_cons]
            exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_left S' _)
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hle (by positivity)) hM0

/-- **Multivariate coordinate division by monic polynomials (Waldschmidt, Lemma 4.8).**
For any entire function `f : (Fin n → ℂ) → ℂ` and monic polynomials `P : Fin n → ℂ[X]`, there exist
entire functions `f₀` and `g : Fin n → (Fin n → ℂ) → ℂ` such that
`f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)`, `f₀` has polynomial degree `< deg (P j)` in every
coordinate `z_j`, and each `g_i` has polynomial degree `< deg (P j)` in every coordinate `z_j` with
`i < j`. -/
theorem exists_eq_add_sum_mul_eval_of_monic {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    {P : Fin n → ℂ[X]} (hP : ∀ i, (P i).Monic) :
    ∃ (f₀ : (Fin n → ℂ) → ℂ) (g : Fin n → (Fin n → ℂ) → ℂ),
      Differentiable ℂ f₀ ∧
      (∀ i, Differentiable ℂ (g i)) ∧
      (∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i)) ∧
      (∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w) ∧
      (∀ i j, i < j → ∀ z,
        ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w) := by
  obtain ⟨f₀, g, hf₀, hg, -, hdiv, hdeg₀, hdeg_g, -⟩ :=
    exists_eq_add_sum_mul_eval_of_list hf hP (List.finRange n)
      (List.nodup_finRange n) (List.pairwise_lt_finRange n)
  have hfin : (List.finRange n).toFinset = univ := by
    ext i
    simp
  rw [hfin] at hdiv
  exact ⟨f₀, g, hf₀, hg, hdiv, fun j ↦ hdeg₀ j (List.mem_finRange j),
    fun i j hij ↦ hdeg_g i (List.mem_finRange i) j (List.mem_finRange j) hij⟩

/-- **Polydisc supremum bounds for multivariate coordinate division.**
For any entire decomposition `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` with `P i` monic and
triangular degree bounds, if `0 < R`, `5 * r ≤ R`, every root of `P i` lies in `closedBall (c i) r`,
and `‖f‖ ≤ M` on `closedBall c R`, then for every `z ∈ closedBall c R`,
`‖f₀ z‖ ≤ 3 ^ (∑ j, (P j).natDegree) * M` and
`‖g i z‖ ≤ 3 ^ (∑ j, (P j).natDegree) / R ^ (P i).natDegree * M`. -/
theorem norm_le_of_eq_add_sum_mul_eval_of_monic
    {f f₀ : (Fin n → ℂ) → ℂ} {g : Fin n → (Fin n → ℂ) → ℂ} {P : Fin n → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀) (hg : ∀ i, Differentiable ℂ (g i)) (hP : ∀ i, (P i).Monic)
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hdeg_g : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w)
    {c : Fin n → ℂ} {r R M : ℝ} (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hroots : ∀ i ζ, (P i).IsRoot ζ → ζ ∈ closedBall (c i) r)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : Fin n → ℂ} (hz : z ∈ closedBall c R) :
    ‖f₀ z‖ ≤ 3 ^ (∑ j, (P j).natDegree) * M ∧
    ∀ i, ‖g i z‖ ≤ 3 ^ (∑ j, (P j).natDegree) / R ^ (P i).natDegree * M := by
  have hf : Differentiable ℂ f := by
    have hfeq : f = fun y ↦ f₀ y + ∑ i, g i y * (P i).eval (y i) := funext hdiv
    rw [hfeq]
    exact hf₀.add (Differentiable.fun_sum fun i _ ↦
      (hg i).mul ((P i).differentiable.comp (differentiable_apply i)))
  obtain ⟨f₀', g', hf₀', hg', -, hdiv', hdeg₀', hdeg_g', hnorm'⟩ :=
    exists_eq_add_sum_mul_eval_of_list hf hP (List.finRange n)
      (List.nodup_finRange n) (List.pairwise_lt_finRange n)
  have hfin : (List.finRange n).toFinset = univ := by ext i; simp
  rw [hfin] at hdiv'
  obtain ⟨rfl, rfl⟩ := eq_of_eq_add_sum_mul_eval_of_ne_zero hf₀ hg hf₀' hg'
    (fun i ↦ (hP i).ne_zero) hdiv hdiv' hdeg₀ (fun j ↦ hdeg₀' j (List.mem_finRange j))
    hdeg_g (fun i j hij ↦ hdeg_g' i (List.mem_finRange i) j (List.mem_finRange j) hij)
  have hsum_eq : ((List.finRange n).map fun j ↦ (P j).natDegree).sum = ∑ j, (P j).natDegree := by
    rw [Fin.sum_univ_def]
  obtain ⟨h0, hgi⟩ := hnorm' c r R M hR hrR (fun i _ ↦ hroots i) hM z hz
  rw [hsum_eq] at h0 hgi
  exact ⟨h0, fun i ↦ hgi i (List.mem_finRange i)⟩

/-- **Polydisc supremum bounds with Waldschmidt's `9 ^ (n * p)` factor (Lemma 4.8).**
Under the hypotheses of `norm_le_of_eq_add_sum_mul_eval_of_monic`, if `(P i).natDegree ≤ p` for
every `i`, then `‖f₀ z‖ ≤ 9 ^ (n * p) * M` and `‖g i z‖ ≤ 9 ^ (n * p) / R ^ (P i).natDegree * M`
for every `z ∈ closedBall c R`. -/
theorem norm_le_nine_pow_of_eq_add_sum_mul_eval_of_monic
    {f f₀ : (Fin n → ℂ) → ℂ} {g : Fin n → (Fin n → ℂ) → ℂ} {P : Fin n → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀) (hg : ∀ i, Differentiable ℂ (g i)) (hP : ∀ i, (P i).Monic)
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hdeg_g : ∀ i j, i < j → ∀ z,
      ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, g i (update z j w) = Q.eval w)
    {p : ℕ} (hp : ∀ i, (P i).natDegree ≤ p)
    {c : Fin n → ℂ} {r R M : ℝ} (hR : 0 < R) (hrR : 5 * r ≤ R)
    (hroots : ∀ i ζ, (P i).IsRoot ζ → ζ ∈ closedBall (c i) r)
    (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : Fin n → ℂ} (hz : z ∈ closedBall c R) :
    ‖f₀ z‖ ≤ 9 ^ (n * p) * M ∧
    ∀ i, ‖g i z‖ ≤ 9 ^ (n * p) / R ^ (P i).natDegree * M := by
  obtain ⟨h0, hgi⟩ := norm_le_of_eq_add_sum_mul_eval_of_monic hf₀ hg hP hdiv hdeg₀ hdeg_g
    hR hrR hroots hM hz
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z hz)
  have hsum_le : ∑ j : Fin n, (P j).natDegree ≤ n * p := by
    calc ∑ j : Fin n, (P j).natDegree
        ≤ ∑ _ : Fin n, p := sum_le_sum fun j _ ↦ hp j
      _ = n * p := by simp
  have hpow : (3 : ℝ) ^ (∑ j, (P j).natDegree) ≤ 9 ^ (n * p) := by
    calc (3 : ℝ) ^ (∑ j, (P j).natDegree)
        ≤ (3 : ℝ) ^ (n * p) := pow_le_pow_right₀ (by norm_num) hsum_le
      _ ≤ (9 : ℝ) ^ (n * p) := pow_le_pow_left₀ (by norm_num) (by norm_num) (n * p)
  exact ⟨h0.trans (mul_le_mul_of_nonneg_right hpow hM0), fun i ↦
    (hgi i).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hpow (by positivity)) hM0)⟩

end Multivariate

end TauCeti.Baker
