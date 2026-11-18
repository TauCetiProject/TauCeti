/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.E2

/-!
# The entries of the classical complex on the cohomology of a DG module

The second page of the index spectral sequence of a twisted complex is the homology of the
classical complex `TauCeti.TwistingCocycle.indexClassicalComplex`, whose terms are products of the
cohomology of `shiftedModuleComplex hM q`, a reindexing of the complex of a DG right module `ℳ`,
and whose entries are the actions of the cycles `m x y` of degree zero. The cohomology of
`shiftedModuleComplex hM p` in degree `n` is the piece `H^{n + p}(ℳ)` of the intrinsic cohomology
`H(ℳ)` of the module (`TauCeti.shiftedModuleComplexHomologyEquiv`), and under these
identifications the action of a cycle `a` of degree zero twisted by the Koszul sign
(`TauCeti.shiftedModuleComplexActHomology`) is the action of the class of `a` in `H(A)`, with the
sign `(-1)^j` on `H^j(ℳ)`
(`TauCeti.shiftedModuleComplexHomologyEquiv_shiftedModuleComplexActHomology`).

This file defines the class in `H(A)` of an entry `m x y` of index difference one, which lies in
`H⁰(A)`, and computes, under these identifications, the entries and the components of the
differential of the classical complex in coefficient degree `k`: componentwise, the entry between
generators `x` and `y` is `(-1)^k` times the action on `H^k(ℳ)` of the class of `m x y`
(`TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry`). It does not
construct an `H⁰(A)`-module structure on `H^k(ℳ)`, nor an isomorphism of the classical complex
with a complex built from `H^k(ℳ)`.

## Main definitions

* `TauCeti.TwistingCocycle.indexClassicalClass`: the class in `H(A)` of an entry of index
  difference one.

## Main results

* `TauCeti.TwistingCocycle.indexClassicalClass_mem_cohomologyGrading_zero`: this class lies in
  `H⁰(A)`.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalEntry`: the entries of
  the classical complex are `(-1)^k` times the actions of the classes of the entries of the
  twisting cocycle.
* `TauCeti.TwistingCocycle.shiftedModuleComplexHomologyEquiv_indexClassicalD_π`: the components of
  the classical differential are `(-1)^k` times the sums of these actions.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM) (k : ℤ)

variable (h) in
/-- The class in the cohomology `H(A)` of the entry `m x y` between generators whose indices
differ by one, a cycle of degree zero. -/
noncomputable def indexClassicalClass {x y : P} (hxy : ind x = ind y + 1) : h.Cohomology :=
  Ideal.Quotient.mk h.boundaries.asIdeal
    ⟨m.m x y, h.mem_cycles.mpr (m.d_m_eq_zero_of_eq_add_one hxy)⟩

variable (h) in
theorem indexClassicalClass_def {x y : P} (hxy : ind x = ind y + 1) :
    m.indexClassicalClass h hxy = Ideal.Quotient.mk h.boundaries.asIdeal
      ⟨m.m x y, h.mem_cycles.mpr (m.d_m_eq_zero_of_eq_add_one hxy)⟩ :=
  (rfl)

variable (h) in
/-- The class of an entry of index difference one has degree zero: it lies in `H⁰(A)`. -/
theorem indexClassicalClass_mem_cohomologyGrading_zero {x y : P} (hxy : ind x = ind y + 1) :
    m.indexClassicalClass h hxy ∈ h.cohomologyGrading 0 :=
  h.mem_cohomologyGrading.mpr ⟨_, m.m_mem_zero_of_eq_add_one hxy, rfl⟩

/-- **The entries of the classical complex are the actions of the classes of the entries of the
twisting cocycle**: under the identifications `shiftedModuleComplexHomologyEquiv` of its terms
with `H^k(ℳ)`, the entry of the classical complex in coefficient degree `k` between a generator `x`
of index `q + 1` and a generator `y` of index `q` is `(-1)^k` times the action on `H^k(ℳ)` of
the class of `m x y` in `H⁰(A)`. -/
theorem shiftedModuleComplexHomologyEquiv_indexClassicalEntry (q : ℤ)
    (x : {x : P // ind x = q + 1}) (y : {y : P // ind y = q})
    (c : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1))) :
    (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q)
        ((m.indexClassicalEntry hM k q x y).hom c) : hM.Cohomology) =
      k.negOnePow • (hM.cohomologyAction
        (m.indexClassicalClass h (x := x.1) (y := y.1) (by rw [x.2, y.2]))).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) (k - (q + 1)) c) := by
  rw [indexClassicalEntry_def, shiftedModuleComplexHomologyEquiv_shiftedModuleComplexActHomology,
    congrArg Int.negOnePow (sub_add_cancel k (q + 1)), indexClassicalClass_def]

/-- **The classical differential on cohomology**: under the identifications
`shiftedModuleComplexHomologyEquiv` of the terms of the classical complex in coefficient degree `k`
with products of copies of `H^k(ℳ)`, the component at a generator `y` of index `q` of the
differential of a family `c` indexed by the generators of index `q + 1` is `(-1)^k` times the sum
of the actions of the classes of the entries `m x y` on the components `c x`. -/
theorem shiftedModuleComplexHomologyEquiv_indexClassicalD_π (q : ℤ) (y : {y : P // ind y = q})
    (c : ↑(∏ᶜ fun _ : {x : P // ind x = q + 1} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1)))) :
    (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM q (k - q)
        ((m.indexClassicalD hM k q ≫ Pi.π _ y).hom c) : hM.Cohomology) =
      k.negOnePow • ∑ x : {x : P // ind x = q + 1}, (hM.cohomologyAction
        (m.indexClassicalClass h (x := x.1) (y := y.1) (by rw [x.2, y.2]))).unop
          (shiftedModuleComplexHomologyEquiv.{uR, uA, uM, uP} hM (q + 1) (k - (q + 1))
            ((Pi.π (fun _ : {x : P // ind x = q + 1} ↦
              (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1))) x).hom
                c)) := by
  rw [indexClassicalD_π, ModuleCat.hom_sum, LinearMap.sum_apply, map_sum, Submodule.coe_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply,
    shiftedModuleComplexHomologyEquiv_indexClassicalEntry]

end TwistingCocycle

end TauCeti
