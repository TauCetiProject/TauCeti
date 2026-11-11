/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Elliptic
import TauCeti.Algebra.CharZero.NatCast
import TauCeti.Algebra.Polynomial.RingDivision
import TauCeti.LinearAlgebra.End.SquareDiagonal

/-!
# The hyperbolic blocks are nondegenerate

Let `(V, ω)` be a finite-dimensional real symplectic vector space with a Darboux basis
`b = (q₁, p₁, …, qₙ, pₙ)` and dual coordinates `(x₁, y₁, …, xₙ, yₙ)`. The **hyperbolic blocks** of
`b` are the `n` quadratic forms

`Hₖ = xₖ yₖ`

(`TauCeti.SymplecticForm.hyperbolic b`). The Hamiltonian endomorphism of `Hₖ` fixes `qₖ`, negates
`pₖ` and kills the other basis vectors (`IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_fst`,
`IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_snd`): its flow is the hyperbolic scaling
`(xₖ, yₖ) ↦ (eᵗ xₖ, e⁻ᵗ yₖ)` of the `k`-th plane. Hence the `Hₖ` pairwise Poisson-commute
(`IsDarbouxBasis.quadraticPoissonBracket_hyperbolic`).

This file proves that they form a nondegenerate family
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_hyperbolic`): the
Hamiltonian endomorphisms `A_{Hₖ}` span a Cartan subalgebra of `sp(V, ω)`. This is the hyperbolic
type of Williamson's classification of nondegenerate rank-zero singularities of integrable
systems, in every dimension; in dimension two it is the indefinite case of
`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_const_iff`.

As for the elliptic blocks, the certificate is a regular element. For any rates `c₁, …, cₙ`, the
combination `P = ∑ₖ cₖ Hₖ` has semisimple Hamiltonian endomorphism, diagonal in the Darboux basis
with eigenvalues `±cₖ` on the `k`-th plane and killed by the squarefree polynomial
`(∏ₜ (X² - t)) X` over the nonzero squares `t = cₖ²`
(`IsDarbouxBasis.isSemisimple_hamiltonianEnd_sum_smul_hyperbolic`). If the rates are nonzero with
distinct squares, every quadratic form Poisson-commuting with `P` is a combination of the `Hₖ`
(`IsDarbouxBasis.mem_span_hyperbolic_of_quadraticPoissonBracket_eq_zero`). Indeed, if `R`
Poisson-commutes with `P` then `polar R (A_P u) v = -polar R u (A_P v)`; as `A_P²` is `cₖ²` on
the plane `span(qₖ, pₖ)`, the polar form of `R` pairs distinct planes trivially, and as `qₖ` and
`pₖ` are eigenvectors for `cₖ` and `-cₖ`, on each plane it is a multiple of `xₖ yₖ`.

Elliptic and hyperbolic blocks combine. On a direct sum `(V₁ × V₂, ω₁ ⊕ ω₂)` with Darboux bases of
`V₁` and `V₂`, the elliptic blocks of the first and the hyperbolic blocks of the second, extended by
zero, form a nondegenerate family
(`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_sumElim_elliptic_hyperbolic`). These are
the Williamson normal forms without focus-focus blocks, in every dimension. The two regular
elements have Hamiltonian endomorphisms killed by `∏ₖ (X² + cₖ²)` and `∏ₖ (X² - cₖ²)`
respectively (`IsDarbouxBasis.aeval_hamiltonianEnd_sum_smul_elliptic_prod`,
`IsDarbouxBasis.aeval_hamiltonianEnd_sum_smul_hyperbolic_prod`), which are coprime for nonzero
rates, so `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_sumElim_prod` applies.

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

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- The **hyperbolic blocks** of a basis `(q₁, p₁, …, qₙ, pₙ)` of `V`, indexed as a Darboux basis
with `qₖ = b (k, 0)` and `pₖ = b (k, 1)`: the quadratic forms `Hₖ = xₖ yₖ` in the dual
coordinates. -/
def hyperbolic (b : Basis (Fin n × Fin 2) ℝ V) (k : Fin n) : QuadraticForm ℝ V :=
  QuadraticMap.linMulLin (b.coord (k, 0)) (b.coord (k, 1))

@[simp]
theorem hyperbolic_apply (b : Basis (Fin n × Fin 2) ℝ V) (k : Fin n) (x : V) :
    hyperbolic b k x = b.repr x (k, 0) * b.repr x (k, 1) := by
  simp [hyperbolic]

/-- The polar form of the hyperbolic block `Hₖ` is `xₖ(u) yₖ(v) + yₖ(u) xₖ(v)`. -/
theorem polar_hyperbolic (b : Basis (Fin n × Fin 2) ℝ V) (k : Fin n) (u v : V) :
    QuadraticMap.polar (hyperbolic b k) u v =
      b.repr u (k, 0) * b.repr v (k, 1) + b.repr u (k, 1) * b.repr v (k, 0) := by
  simp only [QuadraticMap.polar, hyperbolic_apply, map_add, Finsupp.add_apply]
  ring

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {b : Basis (Fin n × Fin 2) ℝ V}

/-- In a Darboux basis, the Hamiltonian endomorphism of the hyperbolic block `Hₖ` fixes `qₖ` and
sends the other `qⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_fst (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (hyperbolic b k) (b (j, 0)) = if j = k then b (k, 0) else 0 := by
  refine ω.hamiltonianEnd_apply_eq_of_basis b fun c ↦ ?_
  rw [polar_hyperbolic]
  split_ifs with h
  · subst h
    simp [hb.apply_fst]
  · simp [Finsupp.single_apply, h]

/-- In a Darboux basis, the Hamiltonian endomorphism of the hyperbolic block `Hₖ` negates `pₖ` and
sends the other `pⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_snd (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (hyperbolic b k) (b (j, 1)) = if j = k then -b (k, 1) else 0 := by
  refine ω.hamiltonianEnd_apply_eq_of_basis b fun c ↦ ?_
  rw [polar_hyperbolic]
  split_ifs with h
  · subst h
    simp [hb.apply_snd]
  · simp [Finsupp.single_apply, h]

/-- The hyperbolic blocks of a Darboux basis pairwise Poisson-commute. -/
theorem IsDarbouxBasis.quadraticPoissonBracket_hyperbolic (hb : ω.IsDarbouxBasis b)
    (k l : Fin n) : ω.quadraticPoissonBracket (hyperbolic b k) (hyperbolic b l) = 0 := by
  rw [quadraticPoissonBracket_eq_zero_iff, Commute, SemiconjBy]
  refine b.ext fun ⟨j, a⟩ ↦ ?_
  fin_cases a <;>
    rcases eq_or_ne j k with rfl | hjk <;> rcases eq_or_ne j l with rfl | hjl <;>
    simp [hb.hamiltonianEnd_hyperbolic_apply_fst, hb.hamiltonianEnd_hyperbolic_apply_snd, *]

section Regular

variable {c : Fin n → ℝ}

/-- In a Darboux basis, the Hamiltonian endomorphism of `∑ₖ cₖ Hₖ` sends `qⱼ` to `cⱼ qⱼ`. -/
theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_hyperbolic_apply_fst (hb : ω.IsDarbouxBasis b)
    (c : Fin n → ℝ) (j : Fin n) :
    ω.hamiltonianEnd (∑ k, c k • hyperbolic b k) (b (j, 0)) = c j • b (j, 0) := by
  simp [map_sum, LinearMap.sum_apply, hb.hamiltonianEnd_hyperbolic_apply_fst]

/-- In a Darboux basis, the Hamiltonian endomorphism of `∑ₖ cₖ Hₖ` sends `pⱼ` to `-cⱼ pⱼ`. -/
theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_hyperbolic_apply_snd (hb : ω.IsDarbouxBasis b)
    (c : Fin n → ℝ) (j : Fin n) :
    ω.hamiltonianEnd (∑ k, c k • hyperbolic b k) (b (j, 1)) = -c j • b (j, 1) := by
  simp [map_sum, LinearMap.sum_apply, hb.hamiltonianEnd_hyperbolic_apply_snd]

/-- The square of the Hamiltonian endomorphism of `∑ₖ cₖ Hₖ` is `cₖ²` on the plane
`span(qₖ, pₖ)`. -/
private theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_hyperbolic_apply_apply
    (hb : ω.IsDarbouxBasis b) (c : Fin n → ℝ) (i : Fin n × Fin 2) :
    ω.hamiltonianEnd (∑ k, c k • hyperbolic b k)
        (ω.hamiltonianEnd (∑ k, c k • hyperbolic b k) (b i)) = c i.1 ^ 2 • b i := by
  obtain ⟨j, a⟩ := i
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_fst, map_smul,
      hb.hamiltonianEnd_sum_smul_hyperbolic_apply_fst, smul_smul, sq]
  · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_snd, map_smul,
      hb.hamiltonianEnd_sum_smul_hyperbolic_apply_snd, smul_smul, neg_mul_neg, sq]

/-- The Hamiltonian endomorphism of `∑ₖ cₖ Hₖ` is killed by `∏ₖ (X² - cₖ²)`. -/
theorem IsDarbouxBasis.aeval_hamiltonianEnd_sum_smul_hyperbolic_prod (hb : ω.IsDarbouxBasis b)
    (c : Fin n → ℝ) :
    aeval (ω.hamiltonianEnd (∑ k, c k • hyperbolic b k)) (∏ k, (X ^ 2 - C (c k ^ 2))) = 0 := by
  -- The factor of index `j` kills the plane `span(qⱼ, pⱼ)`, and the factors commute.
  refine b.ext fun i ↦ ?_
  have hi : aeval (ω.hamiltonianEnd (∑ k, c k • hyperbolic b k)) (X ^ 2 - C (c i.1 ^ 2))
      (b i) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, sq, LinearMap.sub_apply, mul_apply_eq_comp,
      hb.hamiltonianEnd_sum_smul_hyperbolic_apply_apply, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, one_apply_eq_self, sub_self]
  rw [LinearMap.zero_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i.1), map_mul,
    mul_apply_eq_comp, hi, map_zero]

/-- The Hamiltonian endomorphism of `∑ₖ cₖ Hₖ` is semisimple: it is killed by the squarefree
polynomial `(∏ₜ (X² - t)) X`, the product running over the nonzero squares `t = cₖ²`. -/
theorem IsDarbouxBasis.isSemisimple_hamiltonianEnd_sum_smul_hyperbolic
    (hb : ω.IsDarbouxBasis b) : (ω.hamiltonianEnd (∑ k, c k • hyperbolic b k)).IsSemisimple := by
  refine Module.End.isSemisimple_of_apply_apply_basis_eq_smul two_ne_zero b (fun i ↦ c i.1 ^ 2)
    (hb.hamiltonianEnd_sum_smul_hyperbolic_apply_apply c) fun ⟨j, a⟩ hj ↦ ?_
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_fst, pow_eq_zero_iff two_ne_zero |>.1 hj,
      zero_smul]
  · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_snd, pow_eq_zero_iff two_ne_zero |>.1 hj,
      neg_zero, zero_smul]

/-- A quadratic form `R` Poisson-commuting with `∑ₖ cₖ Hₖ`, for nonzero rates with distinct
squares, has a polar form pairing each `qₖ` only with `pₖ`, and each `pₖ` only with `qₖ`. -/
private theorem IsDarbouxBasis.polar_apply_of_quadraticPoissonBracket_sum_smul_hyperbolic_eq_zero
    (hb : ω.IsDarbouxBasis b) (hc : Pairwise fun k l ↦ c k ^ 2 ≠ c l ^ 2) (hc0 : ∀ k, c k ≠ 0)
    {R : QuadraticForm ℝ V} (hR : ω.quadraticPoissonBracket R (∑ k, c k • hyperbolic b k) = 0)
    (k : Fin n) (a : Fin 2) (i : Fin n × Fin 2) :
    QuadraticMap.polar R (b (k, a)) (b i) =
      if i.1 = k ∧ i.2 ≠ a then QuadraticMap.polar R (b (k, 0)) (b (k, 1)) else 0 := by
  set A := ω.hamiltonianEnd (∑ k, c k • hyperbolic b k)
  have hA₀ := hb.hamiltonianEnd_sum_smul_hyperbolic_apply_fst c
  have hA₁ := hb.hamiltonianEnd_sum_smul_hyperbolic_apply_snd c
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
  rcases eq_or_ne k l with rfl | hkl
  · -- On the `k`-th plane, `qₖ` and `pₖ` are isotropic for `polar R`.
    have hqq : QuadraticMap.polar R (b (k, 0)) (b (k, 0)) = 0 := by
      have e := hskew (b (k, 0)) (b (k, 0))
      rw [hA₀, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul] at e
      have : c k * QuadraticMap.polar R (b (k, 0)) (b (k, 0)) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hc0 k)
    have hpp : QuadraticMap.polar R (b (k, 1)) (b (k, 1)) = 0 := by
      have e := hskew (b (k, 1)) (b (k, 1))
      rw [hA₁, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul] at e
      have : c k * QuadraticMap.polar R (b (k, 1)) (b (k, 1)) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hc0 k)
    fin_cases a <;> fin_cases a' <;>
      simp [hqq, hpp, QuadraticMap.polar_comm R (b (k, 1)) (b (k, 0))]
  · -- Distinct planes are orthogonal for `polar R`, since `A_P²` is `cₖ²` on the `k`-th plane.
    have e := hskew (A (b (k, a))) (b (l, a'))
    rw [hskew (b (k, a)) (A (b (l, a'))), neg_neg,
      hb.hamiltonianEnd_sum_smul_hyperbolic_apply_apply,
      hb.hamiltonianEnd_sum_smul_hyperbolic_apply_apply, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul] at e
    have : (c k ^ 2 - c l ^ 2) * QuadraticMap.polar R (b (k, a)) (b (l, a')) = 0 := by
      linear_combination e
    rw [(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (hc hkl))]
    simp [Ne.symm hkl]

/-- **The commutant of a regular hyperbolic element.** If the rates `cₖ` are nonzero with distinct
squares, every quadratic form Poisson-commuting with `∑ₖ cₖ Hₖ` is a linear combination of the
hyperbolic blocks `Hₖ`. -/
theorem IsDarbouxBasis.mem_span_hyperbolic_of_quadraticPoissonBracket_eq_zero
    (hb : ω.IsDarbouxBasis b) (hc : Pairwise fun k l ↦ c k ^ 2 ≠ c l ^ 2) (hc0 : ∀ k, c k ≠ 0)
    {R : QuadraticForm ℝ V} (hR : ω.quadraticPoissonBracket R (∑ k, c k • hyperbolic b k) = 0) :
    R ∈ Submodule.span ℝ (Set.range (hyperbolic b)) := by
  -- `A_R` agrees on the basis with the Hamiltonian endomorphism of `∑ₖ dₖ Hₖ`,
  -- `dₖ = polar R qₖ pₖ`.
  have hpolar := hb.polar_apply_of_quadraticPoissonBracket_sum_smul_hyperbolic_eq_zero hc hc0 hR
  have hB : ω.hamiltonianEnd R =
      ω.hamiltonianEnd (∑ k, QuadraticMap.polar R (b (k, 0)) (b (k, 1)) • hyperbolic b k) :=
    b.ext fun ⟨j, a⟩ ↦ by
      obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
      · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_fst]
        refine ω.hamiltonianEnd_apply_eq_of_basis b fun ⟨l, a'⟩ ↦ ?_
        rw [hpolar j 0 (l, a')]
        fin_cases a' <;> simp [hb.apply_fst, Finsupp.single_apply, eq_comm]
      · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_snd]
        refine ω.hamiltonianEnd_apply_eq_of_basis b fun ⟨l, a'⟩ ↦ ?_
        rw [hpolar j 1 (l, a')]
        fin_cases a' <;> simp [hb.apply_snd, Finsupp.single_apply, eq_comm]
  rw [ω.hamiltonianEnd_injective hB]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

end Regular

/-- **The hyperbolic blocks are nondegenerate.** In a Darboux basis, the hyperbolic blocks
`Hₖ = xₖ yₖ` form a nondegenerate family: their Hamiltonian endomorphisms span a Cartan
subalgebra of `sp(V, ω)`. -/
theorem IsDarbouxBasis.isNondegenerateQuadraticFamily_hyperbolic (hb : ω.IsDarbouxBasis b) :
    ω.IsNondegenerateQuadraticFamily (hyperbolic b) :=
  isNondegenerateQuadraticFamily_of_isSemisimple hb.quadraticPoissonBracket_hyperbolic
    hb.isSemisimple_hamiltonianEnd_sum_smul_hyperbolic
    fun _ hR ↦ hb.mem_span_hyperbolic_of_quadraticPoissonBracket_eq_zero
      pairwise_sq_natCast_add_one_ne (fun k ↦ Nat.cast_add_one_ne_zero (k : ℕ)) hR

/-! ### Elliptic and hyperbolic blocks together -/

section Prod

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
  {ω₁ : SymplecticForm V₁} {ω₂ : SymplecticForm V₂} {n₁ n₂ : ℕ}
  {b₁ : Basis (Fin n₁ × Fin 2) ℝ V₁} {b₂ : Basis (Fin n₂ × Fin 2) ℝ V₂}

/-- **Mixed elliptic and hyperbolic blocks are nondegenerate.** On a direct sum `V₁ × V₂` of
symplectic vector spaces with Darboux bases `b₁` and `b₂`, the elliptic blocks of `b₁` and the
hyperbolic blocks of `b₂`, extended by zero, form a nondegenerate family for the direct-sum
symplectic form. These are the Williamson normal forms with no focus-focus blocks. -/
theorem isNondegenerateQuadraticFamily_sumElim_elliptic_hyperbolic (hb₁ : ω₁.IsDarbouxBasis b₁)
    (hb₂ : ω₂.IsDarbouxBasis b₂) :
    (ω₁.prod ω₂).IsNondegenerateQuadraticFamily
      (Sum.elim (fun k ↦ (elliptic b₁ k).prod 0) fun k ↦
        (0 : QuadraticForm ℝ V₁).prod (hyperbolic b₂ k)) := by
  -- The regular elements `∑ₖ (k + 1) Iₖ` and `∑ₖ (k + 1) Hₖ` have Hamiltonian endomorphisms
  -- killed by `∏ₖ (X² + (k + 1)²)` and `∏ₖ (X² - (k + 1)²)`, which are coprime.
  have hcop : IsCoprime
      (minpoly ℝ (ω₁.hamiltonianEnd (∑ k : Fin n₁, ((k : ℝ) + 1) • elliptic b₁ k)))
      (minpoly ℝ (ω₂.hamiltonianEnd (∑ k : Fin n₂, ((k : ℝ) + 1) • hyperbolic b₂ k))) := by
    refine (IsCoprime.prod_left fun i _ ↦ IsCoprime.prod_right fun j _ ↦ ?_)
      |>.of_isCoprime_of_dvd_left (minpoly.dvd _ _
        (hb₁.aeval_hamiltonianEnd_sum_smul_elliptic_prod _))
      |>.of_isCoprime_of_dvd_right (minpoly.dvd _ _
        (hb₂.aeval_hamiltonianEnd_sum_smul_hyperbolic_prod _))
    rw [← sub_neg_eq_add, ← C_neg]
    refine Polynomial.isCoprime_sub_C_of_isUnit_sub _ (IsUnit.mk0 _ ?_)
    rw [← neg_add']
    exact neg_ne_zero.2 (by positivity)
  exact isNondegenerateQuadraticFamily_sumElim_prod hb₁.quadraticPoissonBracket_elliptic
    hb₂.quadraticPoissonBracket_hyperbolic hb₁.isSemisimple_hamiltonianEnd_sum_smul_elliptic
    hb₂.isSemisimple_hamiltonianEnd_sum_smul_hyperbolic
    (fun _ hR ↦ hb₁.mem_span_elliptic_of_quadraticPoissonBracket_eq_zero
      pairwise_sq_natCast_add_one_ne (fun k ↦ Nat.cast_add_one_ne_zero (k : ℕ)) hR)
    (fun _ hR ↦ hb₂.mem_span_hyperbolic_of_quadraticPoissonBracket_eq_zero
      pairwise_sq_natCast_add_one_ne (fun k ↦ Nat.cast_add_one_ne_zero (k : ℕ)) hR) hcop

end Prod

end TauCeti.SymplecticForm
