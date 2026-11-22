/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The Clifford pairing of a linear map

Let `ρ : CliffordAlgebra Q →ₐ[R] Module.End S W` be a Clifford module, where the Clifford algebra
of `(M, Q)` acts by `S`-linear maps on an `S`-module `W` for an `R`-algebra `S` (for instance a
complex spinor module of a real Clifford algebra). For an `R`-linear map `L : M → W`,
`AlgHom.cliffordPairing ρ L` is the `R`-bilinear map `(v, w) ↦ c(v) (L w)`, where `c(v) = ρ (ι Q v)`
is Clifford multiplication by `v`. Contracting it along an inner product on `M` gives the Clifford
contraction `∑ₖ c(eₖ) (L eₖ)` over an orthonormal basis, the algebraic part of a Dirac operator,
which is applied to the covariant derivative `L = ∇ψ` of a spinor field.

## Main declarations

* `AlgHom.cliffordPairing`: the bilinear map `(v, w) ↦ c(v) (L w)`.
* `AlgHom.cliffordPairing_apply`: its values.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter II, §5.
-/

public section

open CliffordAlgebra

namespace AlgHom

variable {R S M W : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}
  [CommSemiring S] [Algebra R S] [AddCommMonoid W] [Module S W] [Module R W]
  [IsScalarTower R S W]

/-- The `R`-bilinear pairing `(v, w) ↦ c(v) (L w)` of an `R`-linear map `L : M → W` with the
Clifford multiplication `c(v) = ρ (ι Q v)`. Its contraction along an inner product on `M` is the
Clifford contraction `∑ₖ c(eₖ) (L eₖ)`. -/
def cliffordPairing (ρ : CliffordAlgebra Q →ₐ[R] Module.End S W) (L : M →ₗ[R] W) :
    M →ₗ[R] M →ₗ[R] W :=
  (LinearMap.restrictScalarsₗ R S W W R ∘ₗ ρ.toLinearMap ∘ₗ ι Q).compl₂ L

@[simp]
theorem cliffordPairing_apply (ρ : CliffordAlgebra Q →ₐ[R] Module.End S W) (L : M →ₗ[R] W)
    (v w : M) : ρ.cliffordPairing L v w = ρ (ι Q v) (L w) := by
  simp only [cliffordPairing, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearMap.restrictScalarsₗ_apply, LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]

end AlgHom
