/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Hamiltonian.Quadratic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The elliptic blocks

Let `(V, ω)` be a finite-dimensional real symplectic vector space with a Darboux basis
`b = (q₁, p₁, …, qₙ, pₙ)` and dual coordinates `(x₁, y₁, …, xₙ, yₙ)`. The **elliptic blocks** of
`b` are the `n` harmonic oscillators

`Iₖ = (xₖ² + yₖ²) / 2`

(`TauCeti.SymplecticForm.elliptic b`). The Hamiltonian endomorphism of `Iₖ` rotates the plane
`span(qₖ, pₖ)`, `qₖ ↦ -pₖ` and `pₖ ↦ qₖ`, and kills the other basis vectors
(`IsDarbouxBasis.hamiltonianEnd_elliptic_apply_fst`,
`IsDarbouxBasis.hamiltonianEnd_elliptic_apply_snd`), so the `Iₖ` pairwise Poisson-commute
(`IsDarbouxBasis.quadraticPoissonBracket_elliptic`). The Hamiltonian endomorphism of a combination
`∑ₖ cₖ Iₖ` rotates each plane `span(qₖ, pₖ)` with angular frequency `cₖ`
(`IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_fst`,
`IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_snd`).

In the coordinates of `b` such a combination is a weighted sum of squares in which `cₖ / 2` is the
weight of both `xₖ` and `yₖ` (`TauCeti.SymplecticForm.equivalent_sum_smul_elliptic`). By
Sylvester's law of inertia its negative and positive indices of inertia are twice the numbers of
negative and positive `cₖ` (`TauCeti.SymplecticForm.sigNeg_sum_smul_elliptic`,
`TauCeti.SymplecticForm.sigPos_sum_smul_elliptic`); in particular both are even.

These are the elliptic blocks of Williamson's normal forms of nondegenerate rank-zero singularities
of integrable systems. That they form a nondegenerate family, in every dimension, is
`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic`, the case of
elliptic blocks on every plane of
`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_ellipticHyperbolic`.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

noncomputable section

open Module

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

/-- **Combinations of elliptic blocks are doubled weighted sums of squares.** In the coordinates
`(x₁, y₁, …, xₙ, yₙ)` of `b`, the combination `∑ₖ cₖ Iₖ` is the weighted sum of squares in which
`cₖ / 2` is the weight of both `xₖ` and `yₖ`. -/
theorem equivalent_sum_smul_elliptic (b : Basis (Fin n × Fin 2) ℝ V) (c : Fin n → ℝ) :
    (∑ k, c k • elliptic b k).Equivalent
      (QuadraticMap.weightedSumSquares ℝ fun p : Fin n × Fin 2 ↦ c p.1 / 2) := by
  have h : (∑ k, c k • elliptic b k).basisRepr b =
      QuadraticMap.weightedSumSquares ℝ fun p : Fin n × Fin 2 ↦ c p.1 / 2 := by
    ext w
    have hw (p : Fin n × Fin 2) : b.repr (∑ i, w i • b i) p = w p := by
      rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]
    rw [QuadraticMap.basisRepr_apply]
    simp only [sum_apply, smul_apply, elliptic_apply, hw]
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  exact ⟨h ▸ QuadraticMap.isometryEquivBasisRepr _ b⟩

/-- The pairs `(k, i)` of indices of a basis `(q₁, p₁, …, qₙ, pₙ)` whose first index satisfies a
property are twice as many as the `k` satisfying it. -/
private theorem ncard_setOf_fst (P : Fin n → Prop) :
    {p : Fin n × Fin 2 | P p.1}.ncard = 2 * {k | P k}.ncard := by
  rw [show {p : Fin n × Fin 2 | P p.1} = {k | P k} ×ˢ (Set.univ : Set (Fin 2)) by ext; simp,
    Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, mul_comm]

/-- **The negative index of a combination of elliptic blocks.** The negative index of inertia of
`∑ₖ cₖ Iₖ` is twice the number of `k` with `cₖ < 0`. -/
theorem sigNeg_sum_smul_elliptic (b : Basis (Fin n × Fin 2) ℝ V) (c : Fin n → ℝ) :
    sigNeg (∑ k, c k • elliptic b k) = 2 * {k | c k < 0}.ncard := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares (equivalent_sum_smul_elliptic b c),
    ← ncard_setOf_fst]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- **The positive index of a combination of elliptic blocks.** The positive index of inertia of
`∑ₖ cₖ Iₖ` is twice the number of `k` with `0 < cₖ`. -/
theorem sigPos_sum_smul_elliptic (b : Basis (Fin n × Fin 2) ℝ V) (c : Fin n → ℝ) :
    sigPos (∑ k, c k • elliptic b k) = 2 * {k | 0 < c k}.ncard := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares (equivalent_sum_smul_elliptic b c),
    ← ncard_setOf_fst]
  simp

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

end Regular

end TauCeti.SymplecticForm
