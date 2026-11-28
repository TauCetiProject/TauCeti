/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Polynomial.Degree.CoordinateLine
import TauCeti.Analysis.Complex.CoordinateDivision.Basic
import TauCeti.Topology.Algebra.Polynomial.Root.Multiplicity

/-!
# Multivariate coordinate polynomial division for entire functions

For any finite linearly ordered index type `ι` and any family of nonzero polynomials `P : ι → ℂ[X]`,
applying the univariate coordinate division (`TauCeti.partialDivByMonic`,
`TauCeti.partialModByMonic`) backwards across the coordinates yields Waldschmidt's multivariate
polynomial division (Waldschmidt 2000, §4.3, Lemma 4.8):

  `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)`,

where `f₀` has polynomial degree `< deg (P j)` in every coordinate `z_j` and each `g_i` has
polynomial degree `< deg (P j)` in every coordinate `z_j` with `i < j`.

The triangular representation `(f₀, g)` is uniquely determined among all decompositions with each
`g_i` continuous (`TauCeti.eq_of_eq_add_sum_mul_eval`). For polydisc supremum bounds on `(f₀, g)`
when each `P i` is monic, see `TauCeti.Analysis.Complex.CoordinateDivision.Multivariate.Estimate`.

## Main results

* `TauCeti.eq_of_eq_add_sum_mul_eval`: uniqueness of multivariate coordinate division under
  triangular degree bounds and continuous quotients.
* `TauCeti.exists_eq_add_sum_mul_eval_of_ne_zero`: multivariate coordinate division by nonzero
  polynomials with triangular degree bounds.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Lemma 4.8, pp. 123–128.
-/

public section

open Finset Function Nat Polynomial

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
    -- Phase 1: apply the induction hypothesis on `l'` and normalise `P i` to monic `P₁`.
    obtain ⟨hilt, hsort'⟩ := List.pairwise_cons.mp hsort
    have hil' : i ∉ l' := fun h ↦ lt_irrefl i (hilt i h)
    obtain ⟨r', g', hr', hg', hdiv', hdeg_r', hdeg_g'⟩ := ih hsort'
    let P₁ : ℂ[X] := (P i) * C (P i).leadingCoeff⁻¹
    have hP₁ : P₁.Monic := monic_mul_leadingCoeff_inv (hP i)
    have hP₁_deg : P₁.degree = (P i).degree :=
      degree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr (hP i)))
    -- Phase 2: divide `r'` by `P₁(z i)` and update `g'` at `i` to form `(f₀, g)`.
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
    -- Phase 3: verify the division identity along `i :: l'`.
    · intro z
      have hi_not : i ∉ l'.toFinset := by simpa using hil'
      rw [List.toFinset_cons, sum_insert hi_not]
      have hsum_eq : ∑ m ∈ l'.toFinset, g m z * (P m).eval (z m) =
          ∑ m ∈ l'.toFinset, g' m z * (P m).eval (z m) := sum_congr rfl fun m hm ↦ by
        have hmi : m ≠ i := fun h ↦ hi_not (h ▸ hm)
        simp [g, hmi]
      have hdiv_i := (partialModByMonic_add_smul_partialDivByMonic i r' P₁ z).symm
      simp only [smul_eq_mul, P₁, eval_mul, eval_C] at hdiv_i
      rw [hsum_eq, hdiv' z, hdiv_i]
      simp only [g, update_self, f₀, gi]
      ring
    -- Phase 4: verify the remainder degree bounds in coordinate `i` and along `l'`.
    · intro j hj z
      rcases List.mem_cons.mp hj with rfl | hjl'
      · simpa only [hP₁_deg] using exists_degree_lt_partialModByMonic hP₁ hr' j z
      · exact exists_degree_lt_partialModByMonic_of_ne hr' (hilt j hjl').ne' P₁ (hdeg_r' j hjl') z
    -- Phase 5: verify the triangular quotient degree bounds for `i < b` and within `l'`.
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

end Multivariate

end TauCeti
