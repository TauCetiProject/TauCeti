/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Hamiltonian.Quadratic

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
