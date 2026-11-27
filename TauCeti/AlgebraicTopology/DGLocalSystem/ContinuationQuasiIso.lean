/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.QuasiIso
public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra

/-!
# Continuation maps over the loop chains with unit diagonal in the group ring

Let `ν` be a continuation cocycle over the chain algebra `C_*(Ω_x X; R)` of the Moore loops,
between two twisting cocycles on the same generators, which vanishes between distinct generators
of equal index. If the diagonal entry `ν a a` of each generator goes to a unit of the group ring
`R[π₁(X, x)] = H₀(Ω_x X; R)` under `TauCeti.loopChainToGroupAlgebra`, then the continuation map of
`ν` is a quasi-isomorphism of twisted complexes, for every DG right module over `C_*(Ω_x X; R)`
(`TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_isUnit_loopChainToGroupAlgebra`). So
twisting by the two cocycles gives the same cohomology.

This covers the continuation cocycles whose diagonal entries are point chains of loops, which are
units of the group ring but, for loops of positive length, not of the chain algebra: such a
cocycle need not be invertible as a matrix, so `TauCeti.ContinuationCocycle.continuationIsoOfIsUnit`
does not apply. A diagonal entry whose image in the group ring is a unit is invertible up to
homotopy (`TauCeti.exists_cubicalChainDifferential_eq_mul_sub_one_of_isUnit`), and the algebra
of the chains on a based loop space is concentrated in nonpositive cohomological degrees, so
`TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_nonpos` applies.

## Main results

* `TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_isUnit_loopChainToGroupAlgebra`: a
  continuation cocycle over the loop chains whose diagonal entries are units in the group ring
  induces quasi-isomorphisms of twisted complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4 and 2.2.
-/

public section

namespace TauCeti

universe u uM uP

namespace ContinuationCocycle

variable {X : Type u} [TopologicalSpace X] {x : X} {R : Type u} [CommRing R]
  {M : Type uM} [AddCommGroup M] [Module R M] [Module (loopChainAlgebra X x R)ᵐᵒᵖ M]
  [IsScalarTower R (loopChainAlgebra X x R)ᵐᵒᵖ M] [SMulCommClass R (loopChainAlgebra X x R)ᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace X x) R)).opposite.piece
    ℳ]
  {dM : M →ₗ[R] M} {P : Type uP} [Fintype P] {ind : P → ℤ}
  {m₁ m₂ : TwistingCocycle (R := R) (A := loopChainAlgebra X x R)
    (cubicalChainGrading (MooreLoopSpace X x) R) (cubicalChainDifferential (MooreLoopSpace X x) R)
    P ind}

/-- **A continuation cocycle over the loop chains whose diagonal is a unit in the group ring
induces quasi-isomorphisms.** Let `ν` be a continuation cocycle over `C_*(Ω_x X; R)` between
twisting cocycles on the same generators, vanishing between distinct generators of equal index,
whose diagonal entries go to units of `R[π₁(X, x)]`. Then for every differential graded right
module over `C_*(Ω_x X; R)` its continuation map is a quasi-isomorphism of twisted complexes. -/
theorem quasiIso_continuationHom_of_isUnit_loopChainToGroupAlgebra (ν : ContinuationCocycle m₁ m₂)
    (hν : ∀ a b, ind a = ind b → a ≠ b → ν.ν a b = 0)
    (hunit : ∀ a, IsUnit (loopChainToGroupAlgebra X x R (ν.ν a a)))
    (hM : IsDGRightModule (loopChain_isDGAlgebra X x R) ℳ dM) :
    QuasiIso (ν.continuationHom hM) :=
  ν.quasiIso_continuationHom_of_nonpos (fun _ hn ↦ cubicalChainGrading_eq_bot _ R hn) hν
    (fun a ↦ exists_cubicalChainDifferential_eq_mul_sub_one_of_isUnit
      (by simpa using ν.mem_graded a a) (hunit a)) hM

end ContinuationCocycle

end TauCeti
