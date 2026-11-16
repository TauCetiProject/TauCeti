/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Elliptic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Hyperbolic
public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero
import TauCeti.Algebra.Polynomial.RingDivision

/-!
# Elliptic–hyperbolic Williamson normal forms are nondegenerate

Let `(V, ω)` be a finite-dimensional real symplectic vector space with a Darboux basis
`b = (q₁, p₁, …, qₙ, pₙ)` and dual coordinates `(x₁, y₁, …, xₙ, yₙ)`. Williamson's normal forms
without focus-focus blocks put an elliptic block `Iₖ = (xₖ² + yₖ²) / 2`
(`TauCeti.SymplecticForm.elliptic`) or a hyperbolic block `Hₖ = xₖ yₖ`
(`TauCeti.SymplecticForm.hyperbolic`) on each plane `span(qₖ, pₖ)`. For a finite set `s` of
planes, `TauCeti.SymplecticForm.ellipticHyperbolic b s` is the family with `Iₖ` for `k ∈ s` and
`Hₖ` for `k ∉ s`. These forms pairwise Poisson-commute
(`IsDarbouxBasis.quadraticPoissonBracket_ellipticHyperbolic`), and this file proves that they form
a nondegenerate family
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_ellipticHyperbolic`): their
Hamiltonian endomorphisms span a Cartan subalgebra of `sp(V, ω)`. For `s = univ` these are the
elliptic blocks (`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic`),
for `s = ∅` the hyperbolic blocks
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_hyperbolic`), in every
dimension. With the focus-focus block
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_focusFocus`) these make up
the normal forms of Williamson's classification of nondegenerate rank-zero singularities of
integrable systems.

The certificate is a regular element. For any coefficients `c₁, …, cₙ`, the Hamiltonian
endomorphism `A_P` of `P = ∑ₖ cₖ Bₖ`, `Bₖ` the `k`-th block, acts on the plane `span(qₖ, pₖ)`
with square `μₖ = -cₖ²` for `k ∈ s` and `μₖ = cₖ²` for `k ∉ s`. It is semisimple, killed by the
squarefree polynomial `(∏ₜ (X² - t)) X` over the nonzero values `t` of the `μₖ`
(`IsDarbouxBasis.isSemisimple_hamiltonianEnd_sum_smul_ellipticHyperbolic`). If the `cₖ` are
nonzero and the squares of the coefficients of blocks of the same type are distinct, then the `μₖ`
are pairwise distinct, and every quadratic form Poisson-commuting with `P` is a combination of the
blocks (`IsDarbouxBasis.mem_span_ellipticHyperbolic_of_quadraticPoissonBracket_eq_zero`). Indeed,
if `R` Poisson-commutes with `P` then `polar R (A_P u) v = -polar R u (A_P v)`. Applied twice this
shows that the polar form of `R` pairs distinct planes trivially. On an elliptic plane it then is a
multiple of `xₖ² + yₖ²`, and on a hyperbolic plane a multiple of `xₖ yₖ`.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

noncomputable section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V}

variable (b) in
/-- The **elliptic–hyperbolic blocks** of a basis `(q₁, p₁, …, qₙ, pₙ)` of `V`, indexed as a
Darboux basis, for a set `s` of planes: the elliptic block `Iₖ = (xₖ² + yₖ²) / 2` for `k ∈ s` and
the hyperbolic block `Hₖ = xₖ yₖ` for `k ∉ s`. -/
def ellipticHyperbolic (s : Finset (Fin n)) (k : Fin n) : QuadraticForm ℝ V :=
  if k ∈ s then elliptic b k else hyperbolic b k

@[simp]
theorem ellipticHyperbolic_of_mem {s : Finset (Fin n)} {k : Fin n} (hk : k ∈ s) :
    ellipticHyperbolic b s k = elliptic b k := by
  simp [ellipticHyperbolic, hk]

@[simp]
theorem ellipticHyperbolic_of_notMem {s : Finset (Fin n)} {k : Fin n} (hk : k ∉ s) :
    ellipticHyperbolic b s k = hyperbolic b k := by
  simp [ellipticHyperbolic, hk]

variable (b) in
@[simp]
theorem ellipticHyperbolic_empty : ellipticHyperbolic b ∅ = hyperbolic b :=
  funext fun _ ↦ ellipticHyperbolic_of_notMem (Finset.notMem_empty _)

variable (b) in
@[simp]
theorem ellipticHyperbolic_univ : ellipticHyperbolic b Finset.univ = elliptic b :=
  funext fun _ ↦ ellipticHyperbolic_of_mem (Finset.mem_univ _)

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} (s : Finset (Fin n))

/-- In a Darboux basis, the Hamiltonian endomorphism of the `k`-th elliptic–hyperbolic block sends
`qₖ` to `-pₖ` if the block is elliptic and to `qₖ` if it is hyperbolic, and the other `qⱼ` to
`0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_ellipticHyperbolic_apply_fst (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (ellipticHyperbolic b s k) (b (j, 0)) =
      if j = k then (if k ∈ s then -b (k, 1) else b (k, 0)) else 0 := by
  by_cases hk : k ∈ s
  · simp [hk, hb.hamiltonianEnd_elliptic_apply_fst]
  · simp [hk, hb.hamiltonianEnd_hyperbolic_apply_fst]

/-- In a Darboux basis, the Hamiltonian endomorphism of the `k`-th elliptic–hyperbolic block sends
`pₖ` to `qₖ` if the block is elliptic and to `-pₖ` if it is hyperbolic, and the other `pⱼ` to
`0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_ellipticHyperbolic_apply_snd (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (ellipticHyperbolic b s k) (b (j, 1)) =
      if j = k then (if k ∈ s then b (k, 0) else -b (k, 1)) else 0 := by
  by_cases hk : k ∈ s
  · simp [hk, hb.hamiltonianEnd_elliptic_apply_snd]
  · simp [hk, hb.hamiltonianEnd_hyperbolic_apply_snd]

/-- The elliptic–hyperbolic blocks of a Darboux basis pairwise Poisson-commute. -/
theorem IsDarbouxBasis.quadraticPoissonBracket_ellipticHyperbolic (hb : ω.IsDarbouxBasis b)
    (k l : Fin n) :
    ω.quadraticPoissonBracket (ellipticHyperbolic b s k) (ellipticHyperbolic b s l) = 0 := by
  rw [quadraticPoissonBracket_eq_zero_iff, Commute, SemiconjBy]
  refine b.ext fun ⟨j, a⟩ ↦ ?_
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  all_goals
    simp only [mul_apply_eq_comp, hb.hamiltonianEnd_ellipticHyperbolic_apply_fst,
      hb.hamiltonianEnd_ellipticHyperbolic_apply_snd]
    split_ifs <;> simp_all [hb.hamiltonianEnd_ellipticHyperbolic_apply_fst,
      hb.hamiltonianEnd_ellipticHyperbolic_apply_snd]

section Regular

variable {c : Fin n → ℝ}

/-- In a Darboux basis, the Hamiltonian endomorphism of `∑ₖ cₖ Bₖ`, `Bₖ` the elliptic–hyperbolic
blocks, sends `qⱼ` to `-cⱼ pⱼ` on an elliptic plane and to `cⱼ qⱼ` on a hyperbolic plane. -/
theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst
    (hb : ω.IsDarbouxBasis b) (c : Fin n → ℝ) (j : Fin n) :
    ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k) (b (j, 0)) =
      if j ∈ s then -c j • b (j, 1) else c j • b (j, 0) := by
  split_ifs with hj <;>
    simp [map_sum, LinearMap.sum_apply, hb.hamiltonianEnd_ellipticHyperbolic_apply_fst, hj]

/-- In a Darboux basis, the Hamiltonian endomorphism of `∑ₖ cₖ Bₖ`, `Bₖ` the elliptic–hyperbolic
blocks, sends `pⱼ` to `cⱼ qⱼ` on an elliptic plane and to `-cⱼ pⱼ` on a hyperbolic plane. -/
theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd
    (hb : ω.IsDarbouxBasis b) (c : Fin n → ℝ) (j : Fin n) :
    ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k) (b (j, 1)) =
      if j ∈ s then c j • b (j, 0) else -c j • b (j, 1) := by
  split_ifs with hj <;>
    simp [map_sum, LinearMap.sum_apply, hb.hamiltonianEnd_ellipticHyperbolic_apply_snd, hj]

/-- The square of the Hamiltonian endomorphism of `∑ₖ cₖ Bₖ` is `-cₖ²` on an elliptic plane
`span(qₖ, pₖ)` and `cₖ²` on a hyperbolic one. -/
private theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_apply
    (hb : ω.IsDarbouxBasis b) (c : Fin n → ℝ) (i : Fin n × Fin 2) :
    ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k)
        (ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k) (b i)) =
      (if i.1 ∈ s then -c i.1 ^ 2 else c i.1 ^ 2) • b i := by
  obtain ⟨j, a⟩ := i
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  all_goals
    by_cases hj : j ∈ s <;>
    simp only [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst,
      hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd, map_smul, map_neg, smul_neg,
      neg_smul, smul_smul, hj, ↓reduceIte, neg_neg] <;>
    module

/-- The Hamiltonian endomorphism of `∑ₖ cₖ Bₖ`, `Bₖ` the elliptic–hyperbolic blocks, is
semisimple: it is killed by the squarefree polynomial `(∏ₜ (X² - t)) X`, the product running over
the nonzero values `t` of `-cₖ²` on elliptic planes and of `cₖ²` on hyperbolic planes. -/
theorem IsDarbouxBasis.isSemisimple_hamiltonianEnd_sum_smul_ellipticHyperbolic
    (hb : ω.IsDarbouxBasis b) :
    (ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k)).IsSemisimple := by
  set μ : Fin n → ℝ := fun k ↦ if k ∈ s then -c k ^ 2 else c k ^ 2
  set S := (Finset.univ.image μ).filter (· ≠ 0)
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (∏ t ∈ S, (X ^ 2 - C t)) * X) ?_ ?_
  · refine (Polynomial.Separable.mul (Polynomial.separable_prod' (fun t _ t' _ htt' ↦ ?_)
      fun t ht ↦ ?_) separable_X (IsCoprime.prod_left fun t ht ↦ ?_)).squarefree
    · exact Polynomial.isCoprime_sub_C_of_isUnit_sub _ (sub_ne_zero.2 htt').isUnit
    · exact Polynomial.separable_X_pow_sub_C _ (by norm_num) (Finset.mem_filter.1 ht).2
    · refine ⟨-C t⁻¹, C t⁻¹ * X, ?_⟩
      have h : C t⁻¹ * C t = (1 : ℝ[X]) := by
        rw [← C_mul, inv_mul_cancel₀ (Finset.mem_filter.1 ht).2, C_1]
      linear_combination h
  · -- A vector of the plane `span(qⱼ, pⱼ)` is killed by `X` if `μⱼ = 0` and by the factor
    -- `X² - μⱼ` otherwise, and the factors commute.
    refine b.ext fun i ↦ ?_
    rw [LinearMap.zero_apply]
    have hsq := hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_apply s c i
    by_cases hi : c i.1 = 0
    · have h0 : ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k) (b i) = 0 := by
        obtain ⟨j, a⟩ := i
        obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
        · rw [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst, hi]
          simp
        · rw [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd, hi]
          simp
      rw [map_mul, mul_apply_eq_comp, aeval_X, h0, map_zero]
    have hS : μ i.1 ∈ S := Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      by simp only [μ]; split_ifs <;> simp [hi]⟩
    rw [← Finset.prod_erase_mul _ _ hS, mul_right_comm, map_mul, mul_apply_eq_comp]
    have hi : aeval (ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k)) (X ^ 2 - C (μ i.1))
        (b i) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, sq, LinearMap.sub_apply, mul_apply_eq_comp,
        hsq, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        one_apply_eq_self, sub_self]
    rw [hi, map_zero]

/-- The coefficients of `∑ₖ cₖ Bₖ`, `Bₖ` the elliptic–hyperbolic blocks, are **regular** when they
are nonzero and coefficients of blocks of the same type have distinct squares. Then the squares
`-cₖ²` and `cₖ²` of the Hamiltonian endomorphism on the elliptic and hyperbolic planes are pairwise
distinct. -/
private theorem ellipticHyperbolic_sq_ne
    (hc : Pairwise fun k l ↦ (k ∈ s ↔ l ∈ s) → c k ^ 2 ≠ c l ^ 2) (hc0 : ∀ k, c k ≠ 0)
    {k l : Fin n} (hkl : k ≠ l) :
    (if k ∈ s then -c k ^ 2 else c k ^ 2) ≠ (if l ∈ s then -c l ^ 2 else c l ^ 2) := by
  have hk := sq_pos_of_ne_zero (hc0 k)
  have hl := sq_pos_of_ne_zero (hc0 l)
  have h := hc hkl
  by_cases hks : k ∈ s <;> by_cases hls : l ∈ s <;> simp only [hks, hls, ↓reduceIte] at h ⊢
  · exact fun e ↦ h (by simp) (neg_inj.1 e)
  · linarith
  · linarith
  · exact h (by simp)

/-- A quadratic form `R` Poisson-commuting with a regular combination `∑ₖ cₖ Bₖ` of the
elliptic–hyperbolic blocks pairs distinct planes trivially, and on each plane its polar form is
that of a multiple of the block. -/
private theorem IsDarbouxBasis.polar_apply_of_quadraticPoissonBracket_eq_zero
    (hb : ω.IsDarbouxBasis b) (hc : Pairwise fun k l ↦ (k ∈ s ↔ l ∈ s) → c k ^ 2 ≠ c l ^ 2)
    (hc0 : ∀ k, c k ≠ 0) {R : QuadraticForm ℝ V}
    (hR : ω.quadraticPoissonBracket R (∑ k, c k • ellipticHyperbolic b s k) = 0)
    (k : Fin n) (a : Fin 2) (i : Fin n × Fin 2) :
    QuadraticMap.polar R (b (k, a)) (b i) =
      if i.1 = k then
        (if k ∈ s then (if i.2 = a then QuadraticMap.polar R (b (k, 0)) (b (k, 0)) else 0)
          else (if i.2 = a then 0 else QuadraticMap.polar R (b (k, 0)) (b (k, 1))))
      else 0 := by
  set A := ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b s k)
  have hA₀ (j : Fin n) : A (b (j, 0)) = if j ∈ s then -c j • b (j, 1) else c j • b (j, 0) :=
    hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst s c j
  have hA₁ (j : Fin n) : A (b (j, 1)) = if j ∈ s then c j • b (j, 0) else -c j • b (j, 1) :=
    hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd s c j
  -- Since `A_R` commutes with `A_P` and `A_P ∈ sp(V, ω)`,
  -- `polar R (A_P u) v = -polar R u (A_P v)`.
  have hcomm (u : V) : ω.hamiltonianEnd R (A u) = A (ω.hamiltonianEnd R u) := by
    simpa only [mul_apply_eq_comp] using
      LinearMap.congr_fun (ω.quadraticPoissonBracket_eq_zero_iff.1 hR).eq u
  have hskew (u v : V) :
      QuadraticMap.polar R (A u) v = -QuadraticMap.polar R u (A v) := by
    rw [← apply_hamiltonianEnd, ← apply_hamiltonianEnd, hcomm, apply_hamiltonianEnd,
      apply_hamiltonianEnd_right, neg_neg]
  obtain ⟨l, a'⟩ := i
  rcases eq_or_ne l k with rfl | hlk
  · -- On the `l`-th plane, `polar R` is a multiple of `xₗ² + yₗ²` or of `xₗ yₗ`.
    have e₀₀ := hskew (b (l, 0)) (b (l, 0))
    have e₀₁ := hskew (b (l, 0)) (b (l, 1))
    have e₁₁ := hskew (b (l, 1)) (b (l, 1))
    have hpq := QuadraticMap.polar_comm R (b (l, 1)) (b (l, 0))
    by_cases hls : l ∈ s <;>
      simp only [hA₀, hA₁, hls, ↓reduceIte, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right, smul_eq_mul] at e₀₀ e₀₁ e₁₁
    · -- Elliptic plane: `polar R qₗ pₗ = 0` and `polar R pₗ pₗ = polar R qₗ qₗ`.
      have hqp : QuadraticMap.polar R (b (l, 0)) (b (l, 1)) = 0 := by
        have : c l * QuadraticMap.polar R (b (l, 0)) (b (l, 1)) = 0 := by
          rw [hpq] at e₀₀; linarith
        exact (mul_eq_zero.1 this).resolve_left (hc0 l)
      have hpp : QuadraticMap.polar R (b (l, 1)) (b (l, 1)) =
          QuadraticMap.polar R (b (l, 0)) (b (l, 0)) := by
        have : c l * (QuadraticMap.polar R (b (l, 1)) (b (l, 1)) -
            QuadraticMap.polar R (b (l, 0)) (b (l, 0))) = 0 := by linarith
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hc0 l))
      fin_cases a <;> fin_cases a' <;> simp [hls, hqp, hpp, hpq]
    · -- Hyperbolic plane: `polar R qₗ qₗ = 0` and `polar R pₗ pₗ = 0`.
      have hqq : QuadraticMap.polar R (b (l, 0)) (b (l, 0)) = 0 := by
        have : c l * QuadraticMap.polar R (b (l, 0)) (b (l, 0)) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left (hc0 l)
      have hpp : QuadraticMap.polar R (b (l, 1)) (b (l, 1)) = 0 := by
        have : c l * QuadraticMap.polar R (b (l, 1)) (b (l, 1)) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left (hc0 l)
      fin_cases a <;> fin_cases a' <;> simp [hls, hqq, hpp, hpq]
  · -- Distinct planes are orthogonal for `polar R`, since `A_P²` is a different homothety on the
    -- `k`-th and on the `l`-th plane.
    have e := hskew (A (b (k, a))) (b (l, a'))
    rw [hskew (b (k, a)) (A (b (l, a'))), neg_neg,
      hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_apply,
      hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_apply, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul] at e
    have := ellipticHyperbolic_sq_ne s hc hc0 hlk.symm
    have h : ((if k ∈ s then -c k ^ 2 else c k ^ 2) - (if l ∈ s then -c l ^ 2 else c l ^ 2)) *
        QuadraticMap.polar R (b (k, a)) (b (l, a')) = 0 := by
      linear_combination e
    rw [(mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 this)]
    simp [hlk]

/-- **The commutant of a regular elliptic–hyperbolic element.** If the coefficients `cₖ` are
nonzero and coefficients of blocks of the same type have distinct squares, every quadratic form
Poisson-commuting with `∑ₖ cₖ Bₖ`, `Bₖ` the elliptic–hyperbolic blocks, is a linear combination of
the blocks. -/
theorem IsDarbouxBasis.mem_span_ellipticHyperbolic_of_quadraticPoissonBracket_eq_zero
    (hb : ω.IsDarbouxBasis b) (hc : Pairwise fun k l ↦ (k ∈ s ↔ l ∈ s) → c k ^ 2 ≠ c l ^ 2)
    (hc0 : ∀ k, c k ≠ 0) {R : QuadraticForm ℝ V}
    (hR : ω.quadraticPoissonBracket R (∑ k, c k • ellipticHyperbolic b s k) = 0) :
    R ∈ Submodule.span ℝ (Set.range (ellipticHyperbolic b s)) := by
  -- `A_R` agrees on the basis with the Hamiltonian endomorphism of `∑ₖ dₖ Bₖ`, where
  -- `dₖ = polar R qₖ qₖ` on elliptic planes and `dₖ = polar R qₖ pₖ` on hyperbolic ones.
  have hpolar := hb.polar_apply_of_quadraticPoissonBracket_eq_zero s hc hc0 hR
  set d : Fin n → ℝ := fun k ↦ if k ∈ s then QuadraticMap.polar R (b (k, 0)) (b (k, 0))
    else QuadraticMap.polar R (b (k, 0)) (b (k, 1))
  have hB : ω.hamiltonianEnd R = ω.hamiltonianEnd (∑ k, d k • ellipticHyperbolic b s k) :=
    b.ext fun ⟨j, a⟩ ↦ by
      obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
      · rw [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst]
        refine ω.hamiltonianEnd_apply_eq_of_basis b fun i ↦ ?_
        obtain ⟨l, a'⟩ := i
        rw [hpolar j 0 (l, a')]
        obtain rfl | rfl : a' = 0 ∨ a' = 1 := by omega
        all_goals
          by_cases hj : j ∈ s <;>
          simp [d, hj, hb.apply_fst, hb.apply_snd, Finsupp.single_apply, eq_comm]
      · rw [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd]
        refine ω.hamiltonianEnd_apply_eq_of_basis b fun i ↦ ?_
        obtain ⟨l, a'⟩ := i
        rw [hpolar j 1 (l, a')]
        obtain rfl | rfl : a' = 0 ∨ a' = 1 := by omega
        all_goals
          by_cases hj : j ∈ s <;>
          simp [d, hj, hb.apply_fst, hb.apply_snd, Finsupp.single_apply, eq_comm]
  rw [ω.hamiltonianEnd_injective hB]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

end Regular

/-- **The elliptic–hyperbolic blocks are nondegenerate.** In a Darboux basis, for any set `s` of
planes, the elliptic blocks `Iₖ = (xₖ² + yₖ²) / 2` for `k ∈ s` together with the hyperbolic blocks
`Hₖ = xₖ yₖ` for `k ∉ s` form a nondegenerate family: their Hamiltonian endomorphisms span a
Cartan subalgebra of `sp(V, ω)`. -/
theorem IsDarbouxBasis.isNondegenerateQuadraticFamily_ellipticHyperbolic
    (hb : ω.IsDarbouxBasis b) : ω.IsNondegenerateQuadraticFamily (ellipticHyperbolic b s) := by
  have hc : Pairwise fun k l : Fin n ↦ ((k : ℝ) + 1) ^ 2 ≠ ((l : ℝ) + 1) ^ 2 := fun k l hkl h ↦
    hkl (Fin.ext (by
      have := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h
      exact_mod_cast add_right_cancel this))
  have hc0 (k : Fin n) : (k : ℝ) + 1 ≠ 0 := by positivity
  exact isNondegenerateQuadraticFamily_of_isSemisimple
    (hb.quadraticPoissonBracket_ellipticHyperbolic s)
    (hb.isSemisimple_hamiltonianEnd_sum_smul_ellipticHyperbolic s)
    fun R hR ↦ hb.mem_span_ellipticHyperbolic_of_quadraticPoissonBracket_eq_zero s
      (fun _ _ hkl _ ↦ hc hkl) hc0 hR

/-- **The hyperbolic blocks are nondegenerate.** In a Darboux basis, the hyperbolic blocks
`Hₖ = xₖ yₖ` form a nondegenerate family: their Hamiltonian endomorphisms span a Cartan
subalgebra of `sp(V, ω)`. -/
theorem IsDarbouxBasis.isNondegenerateQuadraticFamily_hyperbolic (hb : ω.IsDarbouxBasis b) :
    ω.IsNondegenerateQuadraticFamily (hyperbolic b) := by
  simpa using hb.isNondegenerateQuadraticFamily_ellipticHyperbolic ∅

/-- **The elliptic blocks are nondegenerate.** In a Darboux basis, the elliptic blocks
`Iₖ = (xₖ² + yₖ²) / 2` form a nondegenerate family: their Hamiltonian endomorphisms span a
Cartan subalgebra of `sp(V, ω)`. -/
theorem IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic (hb : ω.IsDarbouxBasis b) :
    ω.IsNondegenerateQuadraticFamily (elliptic b) := by
  simpa using hb.isNondegenerateQuadraticFamily_ellipticHyperbolic Finset.univ

end TauCeti.SymplecticForm
