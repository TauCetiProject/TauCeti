/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.Integral

/-!
# Example: `H⁰_Z(𝔸¹, 𝒪) = 0` for `Z = {0}`

On an integral scheme `X`, a global function supported in a closed subset `Z ≠ X` vanishes, so
`H⁰_Z(X, 𝒪_X) = 0` (`Scheme.Modules.subsingleton_cohomologyWithSupport_zero_unit`). For the affine
line `𝔸¹_k = Spec k[t]` and `Z = {0}` this is the vanishing `H⁰_Z(𝔸¹, 𝒪) = 0`: no nonzero
polynomial is killed by a power of `t`. It shows that `H⁰_Z(X, F)` is not `F(Z)` for the naive
candidates: the topological restriction `𝒪_{𝔸¹,0}` and the closed subscheme `k[t]/(t) = k` both
have nonzero sections over `Z`.
-/

public section

open AlgebraicGeometry TopologicalSpace Polynomial

namespace TauCeti.AlgebraicGeometry.SupportDegreeZeroExample

universe u

variable (k : Type u) [Field k]

/-- The origin `{0} = V(t)` of the affine line `𝔸¹_k = Spec k[t]`, as a closed subset. -/
noncomputable abbrev origin : Closeds (Spec (.of k[X])) :=
  ⟨PrimeSpectrum.zeroLocus {Polynomial.X}, PrimeSpectrum.isClosed_zeroLocus _⟩

/-- **`H⁰_{0}(𝔸¹_k, 𝒪) = 0`**: the affine line has no nonzero function supported at the origin. -/
theorem subsingleton_cohomologyWithSupport_zero_origin :
    Subsingleton ((Scheme.Modules.unit (Spec (.of k[X]))).cohomologyWithSupport
      (origin k) ⊤ 0) := by
  refine Scheme.Modules.subsingleton_cohomologyWithSupport_zero_unit _ fun h ↦ ?_
  -- The generic point `(0)` does not contain `t`.
  have : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k[X]) ∈ PrimeSpectrum.zeroLocus {Polynomial.X} :=
    (Set.eq_univ_iff_forall.1 h) _
  simp [PrimeSpectrum.mem_zeroLocus, Polynomial.X_ne_zero] at this

end TauCeti.AlgebraicGeometry.SupportDegreeZeroExample
