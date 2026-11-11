/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero
import TauCeti.Algebra.CharZero.NatCast
import TauCeti.LinearAlgebra.End.SquareDiagonal

/-!
# The elliptic blocks are nondegenerate

Let `(V, ω)` be a finite-dimensional real symplectic vector space with a Darboux basis
`b = (q₁, p₁, …, qₙ, pₙ)` and dual coordinates `(x₁, y₁, …, xₙ, yₙ)`. The **elliptic blocks** of
`b` are the `n` harmonic oscillators

`Iₖ = (xₖ² + yₖ²) / 2`

(`TauCeti.SymplecticForm.elliptic b`). The Hamiltonian endomorphism of `Iₖ` rotates the plane
`span(qₖ, pₖ)`, `qₖ ↦ -pₖ` and `pₖ ↦ qₖ`, and kills the other basis vectors
(`IsDarbouxBasis.hamiltonianEnd_elliptic_apply_fst`,
`IsDarbouxBasis.hamiltonianEnd_elliptic_apply_snd`), so the `Iₖ` pairwise Poisson-commute
(`IsDarbouxBasis.quadraticPoissonBracket_elliptic`).

This file proves that they form a nondegenerate family
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic`): the
Hamiltonian endomorphisms `A_{Iₖ}` span a Cartan subalgebra of `sp(V, ω)`. This is the elliptic
type of Williamson's classification of nondegenerate rank-zero singularities of integrable
systems, in every dimension; with the hyperbolic blocks
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_hyperbolic`) and the
focus-focus block
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_focusFocus`) it makes up
the normal forms of that classification.

The certificate is a regular element. For any frequencies `c₁, …, cₙ`, the combination
`P = ∑ₖ cₖ Iₖ` has semisimple Hamiltonian endomorphism, killed by the squarefree polynomial
`(∏ₜ (X² + t)) X` over the nonzero squares `t = cₖ²`
(`IsDarbouxBasis.isSemisimple_hamiltonianEnd_sum_smul_elliptic`); without the squarefree
reduction, it is killed by `∏ₖ (X² + cₖ²)`
(`IsDarbouxBasis.aeval_hamiltonianEnd_sum_smul_elliptic_prod`). If the frequencies are nonzero
with distinct squares, every quadratic form Poisson-commuting with `P` is a combination of the
`Iₖ`
(`IsDarbouxBasis.mem_span_elliptic_of_quadraticPoissonBracket_eq_zero`). Indeed, if `R`
Poisson-commutes with `P` then `polar R (A_P u) v = -polar R u (A_P v)`; as `A_P²` is `-cₖ²` on
the plane `span(qₖ, pₖ)`, the polar form of `R` pairs distinct planes trivially, and on each plane
it is a multiple of `xₖ² + yₖ²`.

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

/-- The **elliptic blocks** of a basis `(q₁, p₁, …, qₙ, pₙ)` of `V`, indexed as a Darboux basis
with `qₖ = b (k, 0)` and `pₖ = b (k, 1)`: the harmonic oscillators `Iₖ = (xₖ² + yₖ²) / 2` in
the dual coordinates. -/
def elliptic (b : Basis (Fin n × Fin 2) ℝ V) (k : Fin n) : QuadraticForm ℝ V :=
  (2⁻¹ : ℝ) • (QuadraticMap.linMulLin (b.coord (k, 0)) (b.coord (k, 0)) +
    QuadraticMap.linMulLin (b.coord (k, 1)) (b.coord (k, 1)))

@[simp]
theorem elliptic_apply (b : Basis (Fin n × Fin 2) ℝ V) (k : Fin n) (x : V) :
    elliptic b k x = (b.repr x (k, 0) ^ 2 + b.repr x (k, 1) ^ 2) / 2 := by
  simp only [elliptic, smul_apply, add_apply,
    QuadraticMap.linMulLin_apply, Basis.coord_apply, smul_eq_mul]
  ring

/-- The polar form of the elliptic block `Iₖ` is `xₖ(u) xₖ(v) + yₖ(u) yₖ(v)`. -/
theorem polar_elliptic (b : Basis (Fin n × Fin 2) ℝ V) (k : Fin n) (u v : V) :
    QuadraticMap.polar (elliptic b k) u v =
      b.repr u (k, 0) * b.repr v (k, 0) + b.repr u (k, 1) * b.repr v (k, 1) := by
  simp only [QuadraticMap.polar, elliptic_apply, map_add, Finsupp.add_apply]
  ring

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {b : Basis (Fin n × Fin 2) ℝ V}

/-- In a Darboux basis, the Hamiltonian endomorphism of the elliptic block `Iₖ` sends `qₖ` to
`-pₖ` and the other `qⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_elliptic_apply_fst (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (elliptic b k) (b (j, 0)) = if j = k then -b (k, 1) else 0 := by
  refine ω.hamiltonianEnd_apply_eq_of_basis b fun c ↦ ?_
  rw [polar_elliptic]
  split_ifs with h
  · subst h
    simp [hb.apply_snd]
  · simp [Finsupp.single_apply, h]

/-- In a Darboux basis, the Hamiltonian endomorphism of the elliptic block `Iₖ` sends `pₖ` to
`qₖ` and the other `pⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_elliptic_apply_snd (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (elliptic b k) (b (j, 1)) = if j = k then b (k, 0) else 0 := by
  refine ω.hamiltonianEnd_apply_eq_of_basis b fun c ↦ ?_
  rw [polar_elliptic]
  split_ifs with h
  · subst h
    simp [hb.apply_fst]
  · simp [Finsupp.single_apply, h]

/-- The elliptic blocks of a Darboux basis pairwise Poisson-commute. -/
theorem IsDarbouxBasis.quadraticPoissonBracket_elliptic (hb : ω.IsDarbouxBasis b) (k l : Fin n) :
    ω.quadraticPoissonBracket (elliptic b k) (elliptic b l) = 0 := by
  rw [quadraticPoissonBracket_eq_zero_iff, Commute, SemiconjBy]
  refine b.ext fun ⟨j, a⟩ ↦ ?_
  fin_cases a <;>
    rcases eq_or_ne j k with rfl | hjk <;> rcases eq_or_ne j l with rfl | hjl <;>
    simp [hb.hamiltonianEnd_elliptic_apply_fst, hb.hamiltonianEnd_elliptic_apply_snd, *]

section Regular

variable {c : Fin n → ℝ}

/-- In a Darboux basis, the Hamiltonian endomorphism of `∑ₖ cₖ Iₖ` sends `qⱼ` to `-cⱼ pⱼ`. -/
theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_fst (hb : ω.IsDarbouxBasis b)
    (c : Fin n → ℝ) (j : Fin n) :
    ω.hamiltonianEnd (∑ k, c k • elliptic b k) (b (j, 0)) = -c j • b (j, 1) := by
  simp [map_sum, LinearMap.sum_apply, hb.hamiltonianEnd_elliptic_apply_fst]

/-- In a Darboux basis, the Hamiltonian endomorphism of `∑ₖ cₖ Iₖ` sends `pⱼ` to `cⱼ qⱼ`. -/
theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_snd (hb : ω.IsDarbouxBasis b)
    (c : Fin n → ℝ) (j : Fin n) :
    ω.hamiltonianEnd (∑ k, c k • elliptic b k) (b (j, 1)) = c j • b (j, 0) := by
  simp [map_sum, LinearMap.sum_apply, hb.hamiltonianEnd_elliptic_apply_snd]

/-- The square of the Hamiltonian endomorphism of `∑ₖ cₖ Iₖ` is `-cₖ²` on the plane
`span(qₖ, pₖ)`. -/
private theorem IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_apply
    (hb : ω.IsDarbouxBasis b) (c : Fin n → ℝ) (i : Fin n × Fin 2) :
    ω.hamiltonianEnd (∑ k, c k • elliptic b k) (ω.hamiltonianEnd (∑ k, c k • elliptic b k) (b i)) =
      -(c i.1 ^ 2) • b i := by
  obtain ⟨j, a⟩ := i
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_fst, map_smul,
      hb.hamiltonianEnd_sum_smul_elliptic_apply_snd, smul_smul]
    congr 1
    ring
  · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_snd, map_smul,
      hb.hamiltonianEnd_sum_smul_elliptic_apply_fst, smul_smul]
    congr 1
    ring

/-- The Hamiltonian endomorphism of `∑ₖ cₖ Iₖ` is killed by `∏ₖ (X² + cₖ²)`. -/
theorem IsDarbouxBasis.aeval_hamiltonianEnd_sum_smul_elliptic_prod (hb : ω.IsDarbouxBasis b)
    (c : Fin n → ℝ) :
    aeval (ω.hamiltonianEnd (∑ k, c k • elliptic b k)) (∏ k, (X ^ 2 + C (c k ^ 2))) = 0 := by
  -- The factor of index `j` kills the plane `span(qⱼ, pⱼ)`, and the factors commute.
  refine b.ext fun i ↦ ?_
  have hi : aeval (ω.hamiltonianEnd (∑ k, c k • elliptic b k)) (X ^ 2 + C (c i.1 ^ 2))
      (b i) = 0 := by
    rw [map_add, map_pow, aeval_X, aeval_C, sq, LinearMap.add_apply, mul_apply_eq_comp,
      hb.hamiltonianEnd_sum_smul_elliptic_apply_apply, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, one_apply_eq_self, neg_smul, neg_add_cancel]
  rw [LinearMap.zero_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i.1), map_mul,
    mul_apply_eq_comp, hi, map_zero]

/-- The Hamiltonian endomorphism of `∑ₖ cₖ Iₖ` is semisimple: it is killed by the squarefree
polynomial `(∏ₜ (X² + t)) X`, the product running over the nonzero squares `t = cₖ²`. -/
theorem IsDarbouxBasis.isSemisimple_hamiltonianEnd_sum_smul_elliptic (hb : ω.IsDarbouxBasis b) :
    (ω.hamiltonianEnd (∑ k, c k • elliptic b k)).IsSemisimple := by
  refine Module.End.isSemisimple_of_apply_apply_basis_eq_smul two_ne_zero b
    (fun i ↦ -(c i.1 ^ 2)) (hb.hamiltonianEnd_sum_smul_elliptic_apply_apply c) fun ⟨j, a⟩ hj ↦ ?_
  have hcj : c j = 0 := pow_eq_zero_iff two_ne_zero |>.1 (neg_eq_zero.1 hj)
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_fst, hcj, neg_zero, zero_smul]
  · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_snd, hcj, zero_smul]

/-- A quadratic form `R` Poisson-commuting with `∑ₖ cₖ Iₖ`, for nonzero frequencies with distinct
squares, has a polar form diagonal in the Darboux basis, with equal values on `qₖ` and `pₖ`. -/
private theorem IsDarbouxBasis.polar_apply_of_quadraticPoissonBracket_eq_zero
    (hb : ω.IsDarbouxBasis b) (hc : Pairwise fun k l ↦ c k ^ 2 ≠ c l ^ 2) (hc0 : ∀ k, c k ≠ 0)
    {R : QuadraticForm ℝ V} (hR : ω.quadraticPoissonBracket R (∑ k, c k • elliptic b k) = 0)
    (k : Fin n) (a : Fin 2) (i : Fin n × Fin 2) :
    QuadraticMap.polar R (b (k, a)) (b i) =
      if i = (k, a) then QuadraticMap.polar R (b (k, 0)) (b (k, 0)) else 0 := by
  set A := ω.hamiltonianEnd (∑ k, c k • elliptic b k)
  have hA₀ := hb.hamiltonianEnd_sum_smul_elliptic_apply_fst c
  have hA₁ := hb.hamiltonianEnd_sum_smul_elliptic_apply_snd c
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
  · -- On the `k`-th plane, `polar R` is a multiple of `xₖ² + yₖ²`.
    have hqp : QuadraticMap.polar R (b (k, 0)) (b (k, 1)) = 0 := by
      have e := hskew (b (k, 0)) (b (k, 0))
      rw [hA₀, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul,
        smul_eq_mul, QuadraticMap.polar_comm R (b (k, 1))] at e
      have : c k * QuadraticMap.polar R (b (k, 0)) (b (k, 1)) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hc0 k)
    have hpp : QuadraticMap.polar R (b (k, 1)) (b (k, 1)) =
        QuadraticMap.polar R (b (k, 0)) (b (k, 0)) := by
      have e := hskew (b (k, 0)) (b (k, 1))
      rw [hA₀, hA₁, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul,
        smul_eq_mul] at e
      have : c k * (QuadraticMap.polar R (b (k, 1)) (b (k, 1)) -
          QuadraticMap.polar R (b (k, 0)) (b (k, 0))) = 0 := by linarith
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hc0 k))
    fin_cases a <;> fin_cases a' <;>
      simp [hqp, hpp, QuadraticMap.polar_comm R (b (k, 1)) (b (k, 0))]
  · -- Distinct planes are orthogonal for `polar R`, since `A_P²` is `-cₖ²` on the `k`-th plane.
    have e := hskew (A (b (k, a))) (b (l, a'))
    rw [hskew (b (k, a)) (A (b (l, a'))), neg_neg, hb.hamiltonianEnd_sum_smul_elliptic_apply_apply,
      hb.hamiltonianEnd_sum_smul_elliptic_apply_apply, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul] at e
    have : (c k ^ 2 - c l ^ 2) * QuadraticMap.polar R (b (k, a)) (b (l, a')) = 0 := by
      linear_combination -e
    rw [(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (hc hkl))]
    simp [Ne.symm hkl]

/-- **The commutant of a regular elliptic element.** If the frequencies `cₖ` are nonzero with
distinct squares, every quadratic form Poisson-commuting with `∑ₖ cₖ Iₖ` is a linear combination
of the elliptic blocks `Iₖ`. -/
theorem IsDarbouxBasis.mem_span_elliptic_of_quadraticPoissonBracket_eq_zero
    (hb : ω.IsDarbouxBasis b) (hc : Pairwise fun k l ↦ c k ^ 2 ≠ c l ^ 2) (hc0 : ∀ k, c k ≠ 0)
    {R : QuadraticForm ℝ V} (hR : ω.quadraticPoissonBracket R (∑ k, c k • elliptic b k) = 0) :
    R ∈ Submodule.span ℝ (Set.range (elliptic b)) := by
  -- `A_R` agrees on the basis with the Hamiltonian endomorphism of `∑ₖ dₖ Iₖ`,
  -- `dₖ = polar R qₖ qₖ`.
  have hpolar := hb.polar_apply_of_quadraticPoissonBracket_eq_zero hc hc0 hR
  have hB : ω.hamiltonianEnd R =
      ω.hamiltonianEnd (∑ k, QuadraticMap.polar R (b (k, 0)) (b (k, 0)) • elliptic b k) :=
    b.ext fun ⟨j, a⟩ ↦ by
      obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
      · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_fst]
        refine ω.hamiltonianEnd_apply_eq_of_basis b fun i ↦ ?_
        rw [hpolar j 0 i]
        simp [hb.apply_snd, Finsupp.single_apply]
      · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_snd]
        refine ω.hamiltonianEnd_apply_eq_of_basis b fun i ↦ ?_
        rw [hpolar j 1 i]
        simp [hb.apply_fst, Finsupp.single_apply]
  rw [ω.hamiltonianEnd_injective hB]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

end Regular

/-- **The elliptic blocks are nondegenerate.** In a Darboux basis, the elliptic blocks
`Iₖ = (xₖ² + yₖ²) / 2` form a nondegenerate family: their Hamiltonian endomorphisms span a
Cartan subalgebra of `sp(V, ω)`. -/
theorem IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic (hb : ω.IsDarbouxBasis b) :
    ω.IsNondegenerateQuadraticFamily (elliptic b) := by
  have hc0 (k : Fin n) : (k : ℝ) + 1 ≠ 0 := by positivity
  exact isNondegenerateQuadraticFamily_of_isSemisimple hb.quadraticPoissonBracket_elliptic
    hb.isSemisimple_hamiltonianEnd_sum_smul_elliptic
    fun R hR ↦ hb.mem_span_elliptic_of_quadraticPoissonBracket_eq_zero
      pairwise_sq_natCast_add_one_ne hc0 hR

end TauCeti.SymplecticForm
