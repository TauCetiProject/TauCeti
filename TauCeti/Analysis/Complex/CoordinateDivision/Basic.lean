/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.DivByMonic
import TauCeti.Analysis.Complex.PartialDeriv.Degree
import TauCeti.RingTheory.Polynomial.DegreeLT
import TauCeti.Topology.Algebra.Polynomial.Basic
import TauCeti.Topology.Algebra.Polynomial.Root.Multiplicity

/-!
# Multivariate coordinate polynomial division for entire functions

For any finite linearly ordered index type `ι`, applying the univariate coordinate division
(`TauCeti.partialDivByMonic`, `TauCeti.partialModByMonic`) backwards across the coordinates
yields Waldschmidt's multivariate polynomial division (Waldschmidt 2000, §4.3, Lemma 4.8):

  `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)`,

where `f₀` has polynomial degree `< deg (P j)` in every coordinate `z_j`, each `g_i` has polynomial
degree `< deg (P j)` in every coordinate `z_j` with `i < j`, and when each `P i` is monic with
all roots in `closedBall (c i) r` (`5 * r ≤ R`, `0 < R`) and `‖f‖ ≤ M` on `closedBall c R`, both
`f₀` and `R ^ deg (P i) * g_i` are bounded on `closedBall c R` by `3 ^ (∑ j, deg (P j)) * M`
(hence in particular by `9 ^ (Fintype.card ι * p) * M` for any `p` bounding every `deg (P j)`).

The triangular representation `(f₀, g)` is uniquely determined among all decompositions with each
`g_i` continuous (`TauCeti.eq_of_eq_add_sum_mul_eval`).

## Main results

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
    have hPj0 : P j ≠ 0 := ne_zero_of_degree_gt (hdeg₀ j (mem_insert_self j s) 0).choose_spec.1
    set F : (ι → ℂ) → ℂ := fun z ↦ f₀ z + ∑ a ∈ s, g a z * (P a).eval (z a) with hF_def
    have hsplit (z : ι → ℂ) : F z + g j z * (P j).eval (z j) = 0 := by
      have h := hdiv z
      rw [sum_insert hjs] at h
      rw [hF_def]
      linear_combination h
    have hF_deg (z : ι → ℂ) :
        ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, F (update z j w) = Q.eval w :=
      exists_degree_lt_and_add_sum_mul_eval_eq_eval hjs (hdeg₀ j (mem_insert_self j s))
        (fun a ha ↦ hdeg_g a (mem_insert_of_mem ha) j (mem_insert_self j s) (hj a ha)) z
    have hcont (z : ι → ℂ) : Continuous fun w ↦ g j (update z j w) :=
      (hg j).comp (continuous_const.update j continuous_id)
    have hF0 : F = 0 := by
      ext z
      obtain ⟨Q, hQdeg, hQ⟩ := hF_deg z
      have hQ0 : Q = 0 := Polynomial.eq_zero_of_eval_add_mul_eval_eq_zero
        (IsAlgClosed.splits (P j)) hQdeg (fun _ _ ↦ (hcont z).continuousAt) fun w ↦ by
          simpa [hQ w, update_self] using hsplit (update z j w)
      simpa [hQ0, update_eq_self] using hQ (z j)
    have hgj0 : g j = 0 := by
      ext z
      simpa [update_eq_self] using Polynomial.eq_zero_of_mul_eval_eq_zero (w₀ := z j)
        (hcont z).continuousAt hPj0 fun w ↦ by
          simpa [hF0, update_self] using hsplit (update z j w)
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
    (fun j _ ↦ exists_degree_lt_and_sub_eq_eval (hdeg₀ j) (hdeg₀' j))
    (fun i _ j _ hij ↦ exists_degree_lt_and_sub_eq_eval (hdeg_g i j hij) (hdeg_g' i j hij))
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
  have := Fintype.ofFinite ι
  intro l hsort
  induction l with
  | nil =>
    exact ⟨f, fun _ ↦ 0, hf, fun _ ↦ differentiable_const 0, fun z ↦ by simp,
      fun _ hj ↦ by simp at hj, fun _ hi ↦ by simp at hi⟩
  | cons i l' ih =>
    obtain ⟨hilt, hsort'⟩ := List.pairwise_cons.mp hsort
    have hil' : i ∉ l' := fun h ↦ lt_irrefl i (hilt i h)
    obtain ⟨r', g', hr', hg', hdiv', hdeg_r', hdeg_g'⟩ := ih hsort'
    let P₁ : ℂ[X] := (P i) * C (P i).leadingCoeff⁻¹
    have hP₁ : P₁.Monic := monic_mul_leadingCoeff_inv (hP i)
    have hP₁_deg : P₁.degree = (P i).degree :=
      degree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr (hP i)))
    let f₀ : (ι → ℂ) → ℂ := partialModByMonic i r' P₁
    let gi : (ι → ℂ) → ℂ := fun z ↦ (P i).leadingCoeff⁻¹ * partialDivByMonic i r' P₁ z
    have hf₀ : Differentiable ℂ f₀ := differentiable_partialModByMonic hr' i P₁
    have hq₁ : Differentiable ℂ (partialDivByMonic i r' P₁) :=
      differentiable_partialDivByMonic hr' i P₁
    have hgi : Differentiable ℂ gi := hq₁.const_mul _
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
      have hdiv_i := (partialModByMonic_add_smul_partialDivByMonic i r' P₁ z).symm
      simp only [smul_eq_mul, P₁, eval_mul, eval_C] at hdiv_i
      rw [hsum_eq, hdiv' z, hdiv_i]
      simp only [g, update_self, f₀, gi]
      ring
    · intro j hj z
      rcases List.mem_cons.mp hj with rfl | hjl'
      · simpa only [hP₁_deg] using exists_degree_lt_partialModByMonic hP₁ hr' j z
      · exact exists_degree_lt_partialModByMonic_of_ne hr' (hilt j hjl').ne' P₁ (hdeg_r' j hjl') z
    · intro a ha b hb hab z
      rcases List.mem_cons.mp ha with rfl | hal'
      · have hbl' : b ∈ l' := (List.mem_cons.mp hb).resolve_left hab.ne'
        obtain ⟨Q, hQdeg, hQ⟩ :=
          exists_degree_lt_partialDivByMonic_of_ne hr' hab.ne' P₁ (hdeg_r' b hbl') z
        exact ⟨(P a).leadingCoeff⁻¹ • Q, (degree_smul_le _ _).trans_lt hQdeg,
          fun w ↦ by simp [g, gi, hQ w]⟩
      · have hai : a ≠ i := (hilt a hal').ne'
        have hbl' : b ∈ l' := (List.mem_cons.mp hb).resolve_left fun hbi ↦
          (hab.trans (hbi ▸ hilt a hal')).false
        simpa [g, hai] using hdeg_g' a hal' b hbl' hab z

omit [LinearOrder ι] in
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
