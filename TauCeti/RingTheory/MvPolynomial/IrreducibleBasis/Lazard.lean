/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.IrreducibleBasis.Basic
public import TauCeti.RingTheory.MvPolynomial.SquarefreeBasis.Lazard

/-!
# Roots of Lazard evaluations from an irreducible basis

Move the distinguished polynomial variable into the coefficient ring using
`MvPolynomial.optionEquivLeft` and `MvPolynomial.optionEquivRight`. Multiplicative Lazard
evaluation preserves the factorization into irreducible basis members, including where
ordinary specialization is nullified. Since every member of an irreducible basis divides a
nonzero input, the roots of the Lazard evaluations of the nonzero inputs are exactly the roots
of the Lazard evaluations of the basis members. So a complete stack for the basis is a complete
stack for the input family, and every one of its sections is used by an input.

The transfer of root multiplicities, which needs only a squarefree basis, is
`Finset.IsSquarefreeBasis.rootMultiplicity_lazardEval_eq`.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Sections 2 and 5.
The multiplicity reconstruction is
`Finset.IsSquarefreeBasis.exists_rootMultiplicity_lazardEval_eq_sum`;
the multiplicative evaluation is `MvPolynomial.lazardEvalHom`.
-/

public section

open MvPolynomial Polynomial

namespace Finset

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
  {F B : Finset (Polynomial (MvPolynomial (Fin n) R))}

local notation "swap" =>
  (AlgEquiv.trans (AlgEquiv.symm (optionEquivLeft R (Fin n)))
    (optionEquivRight R (Fin n)))

namespace IsIrreducibleBasis

/-- The union of the roots in `R` of the nonzero inputs' Lazard evaluations is
exactly the roots of the basis evaluations. Thus a complete basis stack also covers the
input family, and every basis section is used by an input. -/
theorem exists_isRoot_lazardEval_iff (hB : F.IsIrreducibleBasis B) (a : Fin n → R) (t : R) :
    (∃ f ∈ F, f ≠ 0 ∧ ((swap f).lazardEval (Polynomial.C ∘ a)).IsRoot t) ↔
      ∃ b ∈ B, ((swap b).lazardEval (Polynomial.C ∘ a)).IsRoot t := by
  classical
  constructor
  · rintro ⟨f, hf, hf0, ht⟩
    obtain ⟨e, he⟩ := hB.isSquarefreeBasis.exists_rootMultiplicity_lazardEval_eq_sum hf hf0
    have hp : swap f ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hf0
    have hpos := (Polynomial.rootMultiplicity_pos (lazardEval_ne_zero hp _)).mpr ht
    rw [he] at hpos
    obtain ⟨b, hb, hbpos⟩ := Finset.sum_pos_iff.mp hpos
    refine ⟨b, hb, Polynomial.rootMultiplicity_pos'.mp ?_ |>.2⟩
    exact pos_of_mul_pos_right hbpos (Nat.zero_le _)
  · rintro ⟨b, hb, ht⟩
    obtain ⟨f, hf, hf0, hbf⟩ := hB.exists_dvd b hb
    refine ⟨f, hf, hf0, ht.dvd ?_⟩
    simpa only [lazardEvalHom_apply] using
      _root_.map_dvd (lazardEvalHom (Polynomial.C ∘ a)) (_root_.map_dvd (swap) hbf)

end IsIrreducibleBasis

end Finset
