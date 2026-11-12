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

(`TauCeti.SymplecticForm.hyperbolic b`). The Hamiltonian endomorphism of `Hₖ` is the hyperbolic
scaling of the plane `span(qₖ, pₖ)`, `qₖ ↦ qₖ` and `pₖ ↦ -pₖ`, and it kills the other basis
vectors (`IsDarbouxBasis.hamiltonianEnd_hyperbolic_apply_fst`,
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

/-- In a Darboux basis, the Hamiltonian endomorphism of the hyperbolic block `Hₖ` sends `pₖ` to
`-pₖ` and the other `pⱼ` to `0`. -/
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
    (k l : Fin n) :
    ω.quadraticPoissonBracket (hyperbolic b k) (hyperbolic b l) = 0 := by
  rw [quadraticPoissonBracket_eq_zero_iff, Commute, SemiconjBy]
  refine b.ext fun ⟨j, a⟩ ↦ ?_
  fin_cases a <;>
    rcases eq_or_ne j k with rfl | hjk <;> rcases eq_or_ne j l with rfl | hjl <;>
    simp [hb.hamiltonianEnd_hyperbolic_apply_fst, hb.hamiltonianEnd_hyperbolic_apply_snd, *]

end TauCeti.SymplecticForm
