/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.Semicontinuity.Defs

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.TensorProduct.Quotient
import TauCeti.RingTheory.FittingIdeal.BaseChange

/-!
# Upper semicontinuity of fibre dimensions

For a module `M` over a commutative ring `R`, the fibre of `M` at a prime `p` is the
`κ(p)`-vector space `κ(p) ⊗[R] M`. This file proves that the dimensions of fibres, and of the
fibrewise homology of a complex, jump up only on closed subsets of `Spec R`.

* If `M` is finite, `p ↦ dim κ(p) ⊗[R] M` is upper semicontinuous: the primes where it exceeds
  `k` form the zero locus of the Fitting ideal `Fitt_k(M)`.
* If `M₁ → M₂ → M₃` is a complex with `M₂` finite and `M₃` finite projective, then the
  dimension of the homology of `κ(p) ⊗ M₁ → κ(p) ⊗ M₂ → κ(p) ⊗ M₃` is upper semicontinuous in `p`.

The second statement is the algebraic core of the semicontinuity theorem for the cohomology of
the fibres of a proper morphism: once that cohomology is computed by a bounded complex of finite
projective modules, upper semicontinuity of `s ↦ dim Hⁱ(X_s, F_s)` follows. At each prime, the
dimension of the fibre homology at `M₂` plus `dim κ(p) ⊗ M₃` equals the sum of the fibre
dimensions of `coker(M₁ → M₂)` and `coker(M₂ → M₃)` (`LinearMap.finrank_map_mkQ_ker_add_finrank`
together with `LinearMap.cokernelBaseChangeEquiv`). The cokernels are finite modules, and
`dim κ(p) ⊗ M₃` is locally constant because `M₃` is finite projective.

## Main declarations

* `Module.upperSemicontinuous_finrank_fiber`: fibre dimensions of a finite module are upper
  semicontinuous on `Spec R`.
* `LinearMap.upperSemicontinuous_finrank_fiber_homology`: dimensions of the fibrewise homology of
  a complex `M₁ → M₂ → M₃` with `M₂` finite and `M₃` finite projective are upper semicontinuous.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.8 and the proof of Theorem III.12.8.
* D. Mumford, *Abelian Varieties*, §5, Corollary (a).
-/

public section

open TensorProduct Module

namespace Module

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The dimension `dim κ(p) ⊗[R] M` of the fibres of a finite module `M` is an upper
semicontinuous function of `p ∈ Spec R`: the primes where it exceeds `k` form the zero locus of
the Fitting ideal `Fitt_k(M)`, a closed set. -/
theorem upperSemicontinuous_finrank_fiber [Module.Finite R M] :
    UpperSemicontinuous fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) := by
  refine upperSemicontinuous_iff_isOpen_preimage.2 fun y ↦ ?_
  cases y with
  | zero => simp
  | succ k =>
    convert (PrimeSpectrum.isClosed_zeroLocus (TauCeti.fittingIdeal R M k : Set R)).isOpen_compl
    ext p
    simp [PrimeSpectrum.mem_zeroLocus]

end Module

namespace LinearMap

variable {R M₁ M₂ M₃ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M₃] [Module R M₃]

/-- For a complex `M₁ → M₂ → M₃` of `R`-modules with `M₂` finite and `M₃` finite projective, the
dimension of the homology of the fibre `κ(p) ⊗ M₁ → κ(p) ⊗ M₂ → κ(p) ⊗ M₃` is an upper
semicontinuous function of `p ∈ Spec R`. The homology is written as the image of the cycles
`ker (κ(p) ⊗ g)` in the cokernel of `κ(p) ⊗ f`. -/
theorem upperSemicontinuous_finrank_fiber_homology [Module.Finite R M₂] [Module.Finite R M₃]
    [Module.Projective R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hfg : g ∘ₗ f = 0) :
    UpperSemicontinuous fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField
        ((ker (g.baseChange p.asIdeal.ResidueField)).map
          (range (f.baseChange p.asIdeal.ResidueField)).mkQ) := by
  have := Module.finitePresentation_of_projective R M₃
  -- Over each residue field, the fibre homology plus `dim κ(q) ⊗ M₃` is the sum of the fibre
  -- dimensions of the two cokernels.
  have key (q : PrimeSpectrum R) :
      finrank q.asIdeal.ResidueField
          ((ker (g.baseChange q.asIdeal.ResidueField)).map
            (range (f.baseChange q.asIdeal.ResidueField)).mkQ) + rankAtStalk M₃ q =
        finrank q.asIdeal.ResidueField (q.asIdeal.Fiber (M₂ ⧸ range f)) +
          finrank q.asIdeal.ResidueField (q.asIdeal.Fiber (M₃ ⧸ range g)) := by
    rw [rankAtStalk_eq, (f.cokernelBaseChangeEquiv (S := q.asIdeal.ResidueField)).finrank_eq,
      (g.cokernelBaseChangeEquiv (S := q.asIdeal.ResidueField)).finrank_eq]
    exact finrank_map_mkQ_ker_add_finrank _ _ (by rw [← baseChange_comp, hfg, baseChange_zero])
  -- Near `p` the fibre dimension of `M₃` is constant and those of the two cokernels do not
  -- increase.
  intro p y hy
  filter_upwards [(isLocallyConstant_rankAtStalk (R := R) (M := M₃)).eventually_eq p,
    upperSemicontinuous_finrank_fiber (M₂ ⧸ range f) p _ (Nat.lt_succ_self _),
    upperSemicontinuous_finrank_fiber (M₃ ⧸ range g) p _ (Nat.lt_succ_self _)] with q hq hf hg
  have := key p
  have := key q
  dsimp only at hy hf hg
  omega

end LinearMap
