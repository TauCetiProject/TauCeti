/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import TauCeti.LinearAlgebra.SymmetricAlgebra.Polarization

/-!
# The dominant integral weights are polynomially dense

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of its root
system. The symmetric algebra `S(H)` is the algebra of polynomial functions on the weights `H*`:
a weight `lam` evaluates `p : S(H)` through `SymmetricAlgebra.lift lam`.

A polynomial function on the weights is determined by its values at the dominant integral weights
alone. In the basis of `H` formed by the simple coroots, a weight has as coordinates its values on
the simple coroots, and the dominant integral weights are exactly the weights whose coordinates are
natural numbers. A polynomial vanishing on that box of natural numbers, which is infinite in every
direction because `K` has characteristic zero, is zero.

By polarization, the `n`-th powers of the dominant integral weights therefore span the whole
degree-`n` component of `S(H*)`. This is the form in which the density is used to show that the
restrictions to `H` of the trace polynomials `x ↦ tr (ρ(x) ^ n)` of the finite-dimensional
representations span the Weyl-invariant polynomials, the surjectivity half of Chevalley's
restriction theorem.

## Main results

* `TauCeti.polynomial_eq_zero_of_dominantIntegral`: an element of `S(H)` vanishing at every
  dominant integral weight is zero.
* `TauCeti.span_pow_eq_homogeneousSubmodule_of_isDominantIntegral`: the `n`-th powers of the
  dominant integral weights span the degree-`n` component of `S(H*)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base)

/-- **The dominant integral weights are polynomially dense.** An element of the symmetric algebra
`S(H)`, viewed as a polynomial function on the weights `H*`, that vanishes at every dominant
integral weight is zero. -/
theorem polynomial_eq_zero_of_dominantIntegral {p : SymmetricAlgebra K H}
    (hp : ∀ lam : Dual K H, IsDominantIntegral b lam → SymmetricAlgebra.lift lam p = 0) :
    p = 0 :=
  -- in the simple coroot basis, the dominant integral weights are the box of natural coordinates
  SymmetricAlgebra.eq_zero_of_forall_lift_eq_zero b.toCoweightBasis
    (fun _ ↦ Set.infinite_range_of_injective Nat.cast_injective) fun lam hlam ↦
      hp lam <| isDominantIntegral_iff.mpr fun i hi ↦ by
        obtain ⟨n, hn⟩ := hlam ⟨i, hi⟩
        exact ⟨n, by simpa using hn.symm⟩

/-- **The powers of the dominant integral weights span each symmetric power of `H*`.** The
`n`-th powers of the dominant integral weights span the degree-`n` component of the symmetric
algebra `S(H*)`. -/
theorem span_pow_eq_homogeneousSubmodule_of_isDominantIntegral (n : ℕ) :
    Submodule.span K ((fun lam ↦ SymmetricAlgebra.ι K (Dual K H) lam ^ n) ''
        {lam | IsDominantIntegral b lam}) =
      SymmetricAlgebra.homogeneousSubmodule K (Dual K H) n := by
  refine SymmetricAlgebra.span_pow_eq_homogeneous_of_polynomial_vanishing _ (fun p hp ↦ ?_) n
  -- transport `p` from `S(H**)` to `S(H)` along the evaluation equivalence `H ≃ H**`
  let e := SymmetricAlgebra.mapEquiv K (evalEquiv K H).symm
  have hlift (lam : Dual K H) :
      SymmetricAlgebra.lift lam (e p) = SymmetricAlgebra.lift (Dual.eval K (Dual K H) lam) p := by
    rw [SymmetricAlgebra.mapEquiv_apply, ← AlgHom.comp_apply]
    congr 1
    refine SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ ?_
    conv_rhs => rw [← (evalEquiv K H).apply_symm_apply φ]
    simp
  have hzero : e p = 0 :=
    polynomial_eq_zero_of_dominantIntegral b fun lam hlam ↦ by rw [hlift]; exact hp lam hlam
  simpa using hzero

end TauCeti
