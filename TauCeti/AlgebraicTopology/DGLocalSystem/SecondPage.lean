/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Homology
public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Classical

/-!
# The second page of the index spectral sequence with local coefficients

Let `m` be a twisting cocycle with values in the chain algebra `C_*(Ω_b B; R)` of the Moore loops
and `𝓕` a DG local system on `(B, b)`, a right DG module over that algebra. The second page of the
index spectral sequence of the twisted complex `𝓕 ⊗⟨P⟩` is the cohomology of the classical complex
(`TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIso`). Its terms in coefficient degree
`k` are products, over the generators of a given index, of `H^k(𝓕)`
(`TauCeti.shiftedModuleComplexHomologyEquiv`). This file shows that its differential is the
matrix of the degree-zero truncations of the entries of `m` in the group ring `R[π₁(B, b)]`, acting
on `H^k(𝓕)` through the representation of the fundamental group on the homology of `𝓕`
(`TauCeti.IsDGRightModule.cohomologyRepresentation`). So the classical complex is the complex of the
generators with coefficients in the local system `H^k(𝓕)`, the `E²` term `H(H_q(𝓕) ⊗⟨P⟩)` of BDHO,
with the truncated cocycle as its matrix.

A cycle `a` of degree zero of `C_*(Ω_b B; R)` is a zero chain, and its class in the cohomology of
the chain algebra is the class of its truncation `loopChainToGroupAlgebra a` in the group ring
(`TauCeti.loopChainCohomologyClass_eq_groupAlgebraToLoopChainCohomology`). The group ring acts on
`H(𝓕)` through the inclusion `groupAlgebraToLoopChainCohomology` of `R[π₁(B, b)]` as `H₀(Ω_b B; R)`,
and a basis element `g` acts as `ρ(g⁻¹)`, where `ρ` is the representation of the fundamental
group, which lets `g` act as the basis element `g⁻¹`
(`TauCeti.IsDGRightModule.cohomologyRepresentation_apply`). Under the identifications
`TauCeti.shiftedModuleComplexHomologyEquiv` of the terms of the classical complex with `H^k(𝓕)`,
the entry between a generator `x` of index `q + 1` and a generator `y` of index `q` therefore acts
as `(-1)^k` times the truncation `∑ u_g g` of `m x y`, that is as `(-1)^k ∑ u_g ρ(g⁻¹)`
(`TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry_loop`).

## Main results

* `TauCeti.TwistingCocycle.indexClassicalClass_eq_groupAlgebraToLoopChainCohomology`: the class of
  an entry of index difference one is the class of its truncation in the group ring.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry_loop`: the entries
  of the classical complex are the actions of the truncated entries of the cocycle on `H^k(𝓕)`.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalD_π_loop`: the
  classical differential, with coefficients in the local system `H^k(𝓕)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38 and Theorem 3.39.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

noncomputable section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe u uM uP

variable {B : Type u} [TopologicalSpace B] {b : B} {R : Type u} [CommRing R]

namespace TwistingCocycle

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module (loopChainAlgebra B b R)ᵐᵒᵖ M]
  [IsScalarTower R (loopChainAlgebra B b R)ᵐᵒᵖ M] {ℳ : ℤ → Submodule R M}
  [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece ℳ]
  {dM : M →ₗ[R] M} {P : Type uP} [Fintype P] {ind : P → ℤ}
  (m : LoopTwistingCocycle B b R P ind) (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM)
  (k : ℤ)

/-- The class of an entry `m x y` of index difference one is the class of its truncation in the
group ring. -/
theorem indexClassicalClass_eq_groupAlgebraToLoopChainCohomology {x y : P}
    (hxy : ind x = ind y + 1) :
    m.indexClassicalClass hxy =
      groupAlgebraToLoopChainCohomology B b R (loopChainToGroupAlgebra B b R (m.m x y)) := by
  rw [indexClassicalClass_def]
  exact loopChainCohomologyClass_eq_groupAlgebraToLoopChainCohomology
    (m.m_mem_zero_of_eq_add_one hxy) (m.d_m_eq_zero_of_eq_add_one hxy)

/-- **The entries of the classical complex of a loop cocycle act through the fundamental group**:
under the identifications `shiftedModuleComplexHomologyEquiv` of the terms of the classical complex
in coefficient degree `k` with `H^k(𝓕)`, the entry between a generator `x` of index `q + 1` and a
generator `y` of index `q` is `(-1)^k` times the action on `H^k(𝓕)` of the truncation `u` of
`m x y` in the group ring `R[π₁(B, b)]`. A basis element `g` acts as `ρ(g⁻¹)`, with `ρ` the
representation of the fundamental group on the homology of `𝓕`
(`IsDGRightModule.cohomologyRepresentation_apply`), so the entry is
`(-1)^k ∑ u_g ρ(g⁻¹)`. -/
theorem shiftedModuleComplexHomologyEquiv_indexClassicalEntry_loop (q : ℤ)
    (x : {x : P // ind x = q + 1}) (y : {y : P // ind y = q})
    (c : (shiftedModuleComplex.{u, u, uM, uP} hM (q + 1)).homology (k - (q + 1))) :
    (shiftedModuleComplexHomologyEquiv.{u, u, uM, uP} hM q (k - q)
        ((m.indexClassicalEntry hM k q x y).hom c) : hM.Cohomology) =
      k.negOnePow • (hM.cohomologyAction (groupAlgebraToLoopChainCohomology B b R
        (loopChainToGroupAlgebra B b R (m.m x y)))).unop
          (shiftedModuleComplexHomologyEquiv.{u, u, uM, uP} hM (q + 1) (k - (q + 1)) c) := by
  rw [shiftedModuleComplexHomologyEquiv_indexClassicalEntry,
    indexClassicalClass_eq_groupAlgebraToLoopChainCohomology]

/-- **The classical differential with local coefficients**: under the identifications
`shiftedModuleComplexHomologyEquiv` of the terms of the classical complex in coefficient degree `k`
with products of copies of `H^k(𝓕)`, the component at a generator `y` of index `q` of the
differential of a family `c` indexed by the generators of index `q + 1` is `(-1)^k` times the sum
over the generators `x` of the actions of the truncations of `m x y` in the group ring on the
components `c x`, that is `(-1)^k ∑ₓ ∑_g u^{xy}_g ρ(g⁻¹) c x`. -/
theorem shiftedModuleComplexHomologyEquiv_indexClassicalD_π_loop (q : ℤ)
    (y : {y : P // ind y = q})
    (c : ↑(∏ᶜ fun _ : {x : P // ind x = q + 1} ↦
      (shiftedModuleComplex.{u, u, uM, uP} hM (q + 1)).homology (k - (q + 1)))) :
    (shiftedModuleComplexHomologyEquiv.{u, u, uM, uP} hM q (k - q)
        ((m.indexClassicalD hM k q ≫ Pi.π _ y).hom c) : hM.Cohomology) =
      k.negOnePow • ∑ x : {x : P // ind x = q + 1},
        (hM.cohomologyAction (groupAlgebraToLoopChainCohomology B b R
          (loopChainToGroupAlgebra B b R (m.m x y)))).unop
            (shiftedModuleComplexHomologyEquiv.{u, u, uM, uP} hM (q + 1) (k - (q + 1))
              ((Pi.π (fun _ : {x : P // ind x = q + 1} ↦
                (shiftedModuleComplex.{u, u, uM, uP} hM (q + 1)).homology (k - (q + 1))) x).hom
                  c)) := by
  rw [shiftedModuleComplexHomologyEquiv_indexClassicalD_π]
  simp only [indexClassicalClass_eq_groupAlgebraToLoopChainCohomology]

end TwistingCocycle

end TauCeti
