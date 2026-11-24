/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Generalized eigenspaces of a polynomial in an endomorphism

For an endomorphism `f` of a module over a commutative ring and a polynomial `p`, a vector killed
by `(f - μ) ^ k` is killed by `(p(f) - p(μ)) ^ k`: the generalized eigenspace of `f` at `μ` of
level `k` is contained in that of `p(f)` at `p(μ)`
(`Module.End.genEigenspace_le_genEigenspace_aeval`), and in particular so is the maximal one
(`Module.End.maxGenEigenspace_le_maxGenEigenspace_aeval`). Indeed `p - p(μ)` is divisible by
`X - μ`, and the quotient evaluated at `f` commutes with `f - μ`. This is the eigenspace form of
the spectral mapping theorem for the characteristic roots of `p(f)`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (1.5.1).
-/

public section

open Polynomial

namespace Module.End

/-- The generalized eigenspace of an endomorphism `f` at `μ` of level `k` is contained in the
generalized eigenspace of `p(f)` at `p(μ)` of the same level. -/
theorem genEigenspace_le_genEigenspace_aeval {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : End R M) (p : R[X]) (μ : R) (k : ℕ∞) :
    f.genEigenspace μ k ≤ (aeval f p).genEigenspace (p.eval μ) k := by
  intro x hx
  obtain ⟨l, hlk, hl⟩ := mem_genEigenspace.1 hx
  -- `p - p(μ)` vanishes at `μ`, so it is `q * (X - μ)` and `p(f) - p(μ) = q(f) * (f - μ)`.
  set q := (p - C (p.eval μ)) /ₘ (X - C μ)
  have hq : p - C (p.eval μ) = q * (X - C μ) := by
    rw [mul_comm, mul_divByMonic_eq_iff_isRoot.2 (by simp)]
  have hpf : aeval f p - p.eval μ • (1 : End R M) = aeval f q * (f - μ • 1) := by
    simpa [Algebra.algebraMap_eq_smul_one] using congrArg (aeval f) hq
  refine mem_genEigenspace.2 ⟨l, hlk, ?_⟩
  have hc : Commute (aeval f q) (f - μ • 1) := by
    have h := (Commute.all q (X - C μ)).map (aeval f)
    rwa [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
  rw [LinearMap.mem_ker] at hl ⊢
  rw [hpf, hc.mul_pow, mul_apply_eq_comp, hl, map_zero]

/-- The maximal generalized eigenspace of an endomorphism `f` at `μ` is contained in the maximal
generalized eigenspace of `p(f)` at `p(μ)`. -/
theorem maxGenEigenspace_le_maxGenEigenspace_aeval {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : End R M) (p : R[X]) (μ : R) :
    f.maxGenEigenspace μ ≤ (aeval f p).maxGenEigenspace (p.eval μ) :=
  genEigenspace_le_genEigenspace_aeval f p μ ⊤

end Module.End
