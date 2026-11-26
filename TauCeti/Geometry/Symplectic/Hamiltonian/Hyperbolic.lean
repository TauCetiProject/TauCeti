/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Hamiltonian.Quadratic

/-!
# The hyperbolic blocks

Let `(V, ω)` be a finite-dimensional real symplectic vector space with a Darboux basis
`b = (q₁, p₁, …, qₙ, pₙ)` and dual coordinates `(x₁, y₁, …, xₙ, yₙ)`. The **hyperbolic blocks**
of `b` are the `n` quadratic Hamiltonians

`Hₖ = xₖ yₖ`

(`TauCeti.SymplecticForm.hyperbolic b`). More generally, the Hamiltonian endomorphism of a
product `xᵢ yⱼ` of two coordinates sends `u` to `xᵢ(u) qⱼ - yⱼ(u) pᵢ`
(`IsDarbouxBasis.hamiltonianEnd_linMulLin_coord_apply`), and for any quadratic form `P` the
coordinates of the Hamiltonian endomorphism `A_P` are `xᵢ(A_P w) = ω(A_P pᵢ, w)` and
`yᵢ(A_P w) = -ω(A_P qᵢ, w)` (`IsDarbouxBasis.repr_hamiltonianEnd_apply_fst`,
`IsDarbouxBasis.repr_hamiltonianEnd_apply_snd`). The Hamiltonian endomorphism of `Hₖ`
is the hyperbolic scaling of the plane `span(qₖ, pₖ)`, `qₖ ↦ qₖ` and `pₖ ↦ -pₖ`, and it kills the
other basis vectors (`IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_fst`,
`IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_snd`), so `(qₖ, pₖ)` is a hyperbolic normal pair
in the sense of `TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Plane`, and the `Hₖ` pairwise
Poisson-commute (`IsDarbouxBasis.quadraticPoissonBracket_hyperbolic`).

Together with the elliptic blocks `Iₖ = (xₖ² + yₖ²) / 2` (`TauCeti.SymplecticForm.elliptic`) and
the focus-focus block (`TauCeti.SymplecticForm.focusFocus`), these are the blocks of Williamson's
normal forms of nondegenerate rank-zero singularities of integrable systems. That the hyperbolic
blocks form a nondegenerate family is
`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_hyperbolic`.

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

/-- In a Darboux basis, the `q`-coordinate of `A_P w` is `ω(A_P pᵢ, w)`, where `A_P` is the
Hamiltonian endomorphism of `P`. -/
theorem IsDarbouxBasis.repr_hamiltonianEnd_apply_fst (hb : ω.IsDarbouxBasis b)
    (P : QuadraticForm ℝ V) (i : Fin n) (w : V) :
    b.repr (ω.hamiltonianEnd P w) (i, 0) = ω (ω.hamiltonianEnd P (b (i, 1))) w := by
  rw [apply_hamiltonianEnd, ← neg_neg (b.repr _ _), ← hb.apply_snd, apply_hamiltonianEnd_right,
    neg_neg]

/-- In a Darboux basis, the `p`-coordinate of `A_P w` is `-ω(A_P qᵢ, w)`, where `A_P` is the
Hamiltonian endomorphism of `P`. -/
theorem IsDarbouxBasis.repr_hamiltonianEnd_apply_snd (hb : ω.IsDarbouxBasis b)
    (P : QuadraticForm ℝ V) (i : Fin n) (w : V) :
    b.repr (ω.hamiltonianEnd P w) (i, 1) = -ω (ω.hamiltonianEnd P (b (i, 0))) w := by
  rw [← hb.apply_fst, apply_hamiltonianEnd_right, apply_hamiltonianEnd]

/-- In a Darboux basis, the Hamiltonian endomorphism of the product `qᵢ pⱼ` of two coordinates
sends `u` to `qᵢ(u) qⱼ - pⱼ(u) pᵢ`. -/
theorem IsDarbouxBasis.hamiltonianEnd_linMulLin_coord_apply (hb : ω.IsDarbouxBasis b)
    (i j : Fin n) (u : V) :
    ω.hamiltonianEnd (QuadraticMap.linMulLin (b.coord (i, 0)) (b.coord (j, 1))) u =
      b.coord (i, 0) u • b (j, 0) - b.coord (j, 1) u • b (i, 1) := by
  refine ω.hamiltonianEnd_apply_eq_of_basis b fun c ↦ ?_
  simp only [Basis.coord_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    hb.apply_fst, hb.apply_snd, Basis.repr_self, smul_eq_mul, QuadraticMap.polar,
    QuadraticMap.linMulLin_apply, map_add]
  ring

/-- In a Darboux basis, the Hamiltonian endomorphism of the hyperbolic block `Hₖ` fixes `qₖ` and
sends the other `qⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_fst (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (hyperbolic b k) (b (j, 0)) = if j = k then b (k, 0) else 0 := by
  simp [hyperbolic, hb.hamiltonianEnd_linMulLin_coord_apply, Finsupp.single_apply]

/-- In a Darboux basis, the Hamiltonian endomorphism of the hyperbolic block `Hₖ` sends `pₖ` to
`-pₖ` and the other `pⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_snd (hb : ω.IsDarbouxBasis b)
    (k j : Fin n) :
    ω.hamiltonianEnd (hyperbolic b k) (b (j, 1)) = if j = k then -b (k, 1) else 0 := by
  simp [hyperbolic, hb.hamiltonianEnd_linMulLin_coord_apply, Finsupp.single_apply, neg_ite]

/-- The hyperbolic blocks of a Darboux basis pairwise Poisson-commute. -/
theorem IsDarbouxBasis.quadraticPoissonBracket_hyperbolic (hb : ω.IsDarbouxBasis b)
    (k l : Fin n) :
    ω.quadraticPoissonBracket (hyperbolic b k) (hyperbolic b l) = 0 := by
  rw [quadraticPoissonBracket_eq_zero_iff, Commute, SemiconjBy]
  refine b.ext fun ⟨j, a⟩ ↦ ?_
  fin_cases a <;>
    rcases eq_or_ne j k with rfl | hjk <;> rcases eq_or_ne j l with rfl | hjl <;>
    simp [hb.hamiltonianEnd_hyperbolic_apply_fst, hb.hamiltonianEnd_hyperbolic_apply_snd, *]

end TauCeti.SymplecticForm
