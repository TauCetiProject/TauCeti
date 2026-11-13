/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.BlockDehomogenize

/-!
# Projective coefficient heights of block dehomogenizations

On a multihomogeneous polynomial `P` in two-coordinate blocks `κ × Fin 2` of any multidegree
`e : κ → ℕ`, setting every homogenizing coordinate `X (h, 0)` to `1`
(`MvPolynomial.blockDehomogenize`) maps the support bijectively onto the support of the
dehomogenization without combining terms, so the set of nonzero coefficients is unchanged. Both the
multiplicative and logarithmic projective coefficient heights are therefore preserved
(`MvPolynomial.IsMultiHomogeneous.mulHeight_blockDehomogenize`,
`MvPolynomial.IsMultiHomogeneous.logHeight_blockDehomogenize`).

The equalities include `P = 0` and require no finiteness assumption on the block index type `κ`.
Combined with `MvPolynomial.IsMultiHomogeneous.formIndex_eq_weightedIndex_blockDehomogenize`, they
pass coefficient-height bounds from multihomogeneous auxiliary polynomials in projective blocks to
their affine dehomogenizations.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  proof of Lemma 7.5.19.
* Ralf Stephan, `DiophantineApproximation/GeneralizedRothLemma.lean` in `rwst/Subspace-Theorems`,
  commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

namespace MvPolynomial

variable {K κ : Type*} [Field K] [Height.AdmissibleAbsValues K] [DecidableEq κ]

/-- On a multihomogeneous polynomial `P` in two-coordinate blocks, `blockDehomogenize` preserves
the set of nonzero coefficients and therefore preserves `mulHeight`. -/
-- Cannot be `@[simp]` because `e` cannot be inferred by `simp` (`simpNF`).
theorem IsMultiHomogeneous.mulHeight_blockDehomogenize {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P) :
    (blockDehomogenize P).mulHeight = P.mulHeight :=
  le_antisymm
    (mulHeight_le_of_forall_exists_coeff_eq fun _ hm ↦
      let ⟨n, _, hn⟩ := IsMultiHomogeneous.exists_coeff_eq_of_mem_support_blockDehomogenize hP hm
      ⟨n, hn⟩)
    (mulHeight_le_of_forall_exists_coeff_eq fun _ hn ↦
      let ⟨m, _, _, hm⟩ :=
        IsMultiHomogeneous.exists_coeff_blockDehomogenize_eq_of_mem_support hP hn
      ⟨m, hm.symm⟩)

grind_pattern IsMultiHomogeneous.mulHeight_blockDehomogenize =>
  IsMultiHomogeneous e P, (blockDehomogenize P).mulHeight

/-- On a multihomogeneous polynomial `P` in two-coordinate blocks, `blockDehomogenize` preserves
`logHeight`. -/
-- Cannot be `@[simp]` because `e` cannot be inferred by `simp` (`simpNF`).
theorem IsMultiHomogeneous.logHeight_blockDehomogenize {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) K} (hP : IsMultiHomogeneous e P) :
    (blockDehomogenize P).logHeight = P.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    IsMultiHomogeneous.mulHeight_blockDehomogenize hP]

grind_pattern IsMultiHomogeneous.logHeight_blockDehomogenize =>
  IsMultiHomogeneous e P, (blockDehomogenize P).logHeight

end MvPolynomial
