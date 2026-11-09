/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.FixedBasis

/-!
# Bracket coordinates of signed root orbits

For a symmetric Gram matrix with finite norm-two shell, the integral fixed basis of a pinned
diagram action consists of Cartan orbit sums and signed root orbit sums. This file computes their
bracket coordinates from the ordered sign
of the ambient shell algebra. A root coordinate receives exactly the pairs whose sum is that
root; a Cartan coordinate receives exactly the opposite pairs, with their ordered sign and their
actual first root coordinate. In particular, negative-root sections are not replaced by inverse
lifts, which would change the opposite-root coefficients.

The formulas `basis_repr_orbitRoot_lie_orbitRoot_inl` and
`basis_repr_orbitRoot_lie_orbitRoot_inr` apply even to cycles
of negative monodromy. For cycles of positive monodromy, `fixedBasis_repr_inl` and
`fixedBasis_repr_inr` turn these into coordinates in the integral fixed basis simply by evaluating
at its chosen representatives. The mixed brackets are diagonal: an invariant Cartan vector acts
on a signed root orbit by its pairing with any representative (`cartan_lie_orbitRoot`). Together
with the vanishing Cartan--Cartan brackets, these give the fixed basis's complete bracket table,
without assuming that it is a normalized Chevalley basis of a folded root system. The double-sum
formulas are intended for explicit rewriting, not automatic expansion by the simplifier.

The construction uses the existing `Matrix.ShellLieAlgebra.fixedBasis`, `orbitRoot`, and
`rootBracket`, retaining their section and numbering conventions.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8--7.9.
-/

public section

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}

variable (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)

private theorem lie_orbitRoot_expansion
    (C D : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ⁅orbitRoot σ hσ C, orbitRoot σ hσ D⁆ =
      ∑ r ∈ Finset.range (Function.minimalPeriod (normTwoShellCongr hσ) C.out),
        ∑ s ∈ Finset.range (Function.minimalPeriod (normTwoShellCongr hσ) D.out),
          ((cycleCoeff σ hσ C.out r : ℤ) * (cycleCoeff σ hσ D.out s : ℤ)) •
            rootBracket B ((normTwoShellCongr hσ ^ r) C.out)
              ((normTwoShellCongr hσ ^ s) D.out) := by
  simp only [orbitRoot_def, ← bracketBilin_apply_apply, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply]
  simp only [bracketBilin_apply_apply, root_lie_root, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- The Cartan coefficient of a bracket of signed root orbits is the signed sum over opposite
pairs, weighted by the first root's coordinate. For positive cycles, evaluating at a vertex-orbit
representative gives the corresponding coefficient in `fixedBasis`. -/
theorem basis_repr_orbitRoot_lie_orbitRoot_inl
    (C D : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) (i : I) :
    (basis B).repr ⁅orbitRoot σ hσ C, orbitRoot σ hσ D⁆ (.inl i) =
      ∑ r ∈ Finset.range (Function.minimalPeriod (normTwoShellCongr hσ) C.out),
        ∑ s ∈ Finset.range (Function.minimalPeriod (normTwoShellCongr hσ) D.out),
          (cycleCoeff σ hσ C.out r : ℤ) * (cycleCoeff σ hσ D.out s : ℤ) *
            (if (((normTwoShellCongr hσ ^ r) C.out : B.normTwoShell) : I → ℤ) +
                (normTwoShellCongr hσ ^ s) D.out = 0 then
              ((B.orderedSignForm ((normTwoShellCongr hσ ^ r) C.out)
                ((normTwoShellCongr hσ ^ s) D.out)).negOnePow : ℤ) *
                  (((normTwoShellCongr hσ ^ r) C.out : B.normTwoShell) : I → ℤ) i
            else 0) := by
  simp only [lie_orbitRoot_expansion, map_sum, Finsupp.finsetSum_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul, basis_repr_rootBracket_inl]

/-- The root coefficient of a bracket of signed root orbits is the signed sum over pairs adding
to that root. For positive cycles, evaluating at a positive-cycle representative gives the
corresponding coefficient in `fixedBasis`. -/
theorem basis_repr_orbitRoot_lie_orbitRoot_inr
    (C D : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) (c : B.normTwoShell) :
    (basis B).repr ⁅orbitRoot σ hσ C, orbitRoot σ hσ D⁆ (.inr c) =
      ∑ r ∈ Finset.range (Function.minimalPeriod (normTwoShellCongr hσ) C.out),
        ∑ s ∈ Finset.range (Function.minimalPeriod (normTwoShellCongr hσ) D.out),
          (cycleCoeff σ hσ C.out r : ℤ) * (cycleCoeff σ hσ D.out s : ℤ) *
            (if (((normTwoShellCongr hσ ^ r) C.out : B.normTwoShell) : I → ℤ) +
                (normTwoShellCongr hσ ^ s) D.out = c then
              ((B.orderedSignForm ((normTwoShellCongr hσ ^ r) C.out)
                ((normTwoShellCongr hσ ^ s) D.out)).negOnePow : ℤ)
            else 0) := by
  simp only [lie_orbitRoot_expansion, map_sum, Finsupp.finsetSum_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul, basis_repr_rootBracket_inr]

/-- An invariant Cartan vector acts diagonally on each signed root orbit. This retains the
unscaled integral Cartan vector, rather than a normalized folded coroot. -/
@[simp]
theorem cartan_lie_orbitRoot (h : I → ℤ) (hh : h ∘ σ.symm = h)
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ⁅cartan B h, orbitRoot σ hσ C⁆ =
      (h ⬝ᵥ B *ᵥ (C.out : I → ℤ)) • orbitRoot σ hσ C := by
  simp only [orbitRoot_def]
  rw [← bracketBilin_apply_apply, map_sum]
  simp only [map_smul, bracketBilin_apply_apply, cartan_lie_root,
    dotProduct_mulVec_pow_normTwoShellCongr B σ hσ h hh, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun r _ ↦ by rw [mul_comm]

/-- A signed root orbit has the negative Cartan weight in the reversed bracket. -/
@[simp]
theorem orbitRoot_lie_cartan (h : I → ℤ) (hh : h ∘ σ.symm = h)
    (C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ))) :
    ⁅orbitRoot σ hσ C, cartan B h⁆ =
      -((h ⬝ᵥ B *ᵥ (C.out : I → ℤ)) • orbitRoot σ hσ C) := by
  simp only [orbitRoot_def]
  rw [← bracketBilin_apply_apply, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, bracketBilin_apply_apply, root_lie_cartan,
    dotProduct_mulVec_pow_normTwoShellCongr B σ hσ h hh, Finset.smul_sum, smul_neg,
    ← Finset.sum_neg_distrib, smul_smul]
  simp only [mul_comm]

end Matrix.ShellLieAlgebra
