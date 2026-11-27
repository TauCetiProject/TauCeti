/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.NonTorsionKernel
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.HomotopyGroup

/-!
# The alternatives of Proposition 5.11 for real projective space

Barraud, Damian, Humilière and Oancea detect closed characteristics on cotangent bundles of a base
`Q` through hypotheses on the homotopy groups of `Q`. This file verifies them for `Q = RPⁿ`,
`n ≥ 2`, whose `n`-th homotopy group is `ℤ` (`TauCeti.RealProjectiveSpace.homotopyGroupAddEquiv`):

* for every `d ≠ 0`, the homotopy groups of `RPⁿ` detect the degree `d`
  (`TauCeti.RealProjectiveSpace.homotopyGroupsDetectDegree_iff_ne_zero`), the hypothesis of their
  Theorem 5.10 and of Theorem A, which applies when `n` is odd and `RPⁿ` is orientable;
* squaring is not surjective on `πₙ(RPⁿ)`
  (`TauCeti.RealProjectiveSpace.not_surjective_pow_homotopyGroup` with exponent `2`), the hypothesis
  of their Theorems 5.15 and C, for the non-orientable `RPⁿ` with `n` even. With it,
  `exists_ne_zero_singularHomology_zmod_two_basedConstContractibleMoorePaths_of_not_surjective`
  in `TauCeti` finds a nonzero class in the mod-two kernel of the inclusion of the constant
  loops.

## Main results

* `TauCeti.RealProjectiveSpace.homotopyGroupsDetectDegree_iff_ne_zero`: the homotopy groups of
  `RPⁿ` detect exactly the nonzero degrees.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11, Theorems 5.10, 5.15,
  A and C.
-/

public section

namespace TauCeti

namespace RealProjectiveSpace

variable (n : ℕ)

/-- **The homotopy groups of `RPⁿ` detect every nonzero degree** for `n ≥ 2`: the alternatives of
Proposition 5.11 of Barraud–Damian–Humilière–Oancea hold for `RPⁿ` and `d` exactly when `d ≠ 0`,
because `πₙ(RPⁿ) ≅ ℤ` is annihilated by no power of `d`. -/
theorem homotopyGroupsDetectDegree_iff_ne_zero (x : RealProjectiveSpace (n + 2)) {d : ℤ} :
    HomotopyGroupsDetectDegree (RealProjectiveSpace (n + 2)) x d ↔ d ≠ 0 :=
  ⟨HomotopyGroupsDetectDegree.ne_zero, fun hd ↦
    .of_not_isMulTorsion hd (not_isMulTorsion_homotopyGroup n x)⟩

end RealProjectiveSpace

end TauCeti
