/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.IrreducibleBasis.Multiplicity
public import TauCeti.RingTheory.MvPolynomial.Lazard.Map

/-!
# Root multiplicities of Lazard evaluations from an irreducible basis

Move the distinguished polynomial variable into the coefficient ring using
`MvPolynomial.optionEquivLeft` and `MvPolynomial.optionEquivRight`. Multiplicative Lazard
evaluation preserves the factorization into irreducible basis members, including where
ordinary specialization is nullified. Root multiplicities are weighted sums of the basis
multiplicities, with weights independent of the base point.

These identities transfer invariant root multiplicities from the basis to the original
family. Zero inputs are included in the multiplicity transfer, with multiplicity zero.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Sections 2 and 5.
The factorization API is `Finset.IsIrreducibleBasis.exists_rootMultiplicity_eq_sum`;
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

/-- The multiplicities in a nonzero input's Lazard evaluation are fixed weighted sums
of the multiplicities in the basis evaluations, even on nullified ordinary fibers. -/
theorem exists_rootMultiplicity_lazardEval_eq_sum (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) (hf0 : f ≠ 0) :
    ∃ e : Polynomial (MvPolynomial (Fin n) R) → ℕ, ∀ (a : Fin n → R) (t : R),
      ((swap f).lazardEval (Polynomial.C ∘ a)).rootMultiplicity t =
        ∑ b ∈ B, e b * ((swap b).lazardEval (Polynomial.C ∘ a)).rootMultiplicity t := by
  obtain ⟨e, he⟩ := hB.exists_rootMultiplicity_eq_sum (A := R) hf
  refine ⟨e, fun a t ↦ ?_⟩
  let φ : Polynomial (MvPolynomial (Fin n) R) →*₀ Polynomial R :=
    (lazardEvalHom (Polynomial.C ∘ a)).comp (swap).toRingHom.toMonoidWithZeroHom
  have hφ (g : Polynomial (MvPolynomial (Fin n) R)) :
      φ g = (swap g).lazardEval (Polynomial.C ∘ a) := by
    simp only [φ, MonoidWithZeroHom.comp_apply, RingHom.coe_toMonoidWithZeroHom,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      lazardEvalHom_apply]
  have hC (c : MvPolynomial (Fin n) R) : ∃ r : R, φ (Polynomial.C c) = Polynomial.C r := by
    refine ⟨c.lazardEval a, ?_⟩
    rw [hφ, optionEquivRight_optionEquivLeft_symm_C,
      lazardEval_map Polynomial.C Polynomial.C_injective]
  have hp : swap f ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hf0
  simpa only [hφ] using he φ hC ((hφ f).symm ▸ lazardEval_ne_zero hp _) t

/-- The union of the roots in `R` of the nonzero inputs' Lazard evaluations is
exactly the roots of the basis evaluations. Thus a complete basis stack also covers the
input family, and every basis section is used by an input. -/
theorem exists_isRoot_lazardEval_iff (hB : F.IsIrreducibleBasis B) (a : Fin n → R) (t : R) :
    (∃ f ∈ F, f ≠ 0 ∧ ((swap f).lazardEval (Polynomial.C ∘ a)).IsRoot t) ↔
      ∃ b ∈ B, ((swap b).lazardEval (Polynomial.C ∘ a)).IsRoot t := by
  classical
  constructor
  · rintro ⟨f, hf, hf0, ht⟩
    obtain ⟨e, he⟩ := hB.exists_rootMultiplicity_lazardEval_eq_sum hf hf0
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

/-- Equal basis root multiplicities imply equal input root multiplicities after Lazard
evaluation. The base points and root coordinates may both differ. -/
theorem rootMultiplicity_lazardEval_eq (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F)
    {a a' : Fin n → R} {t t' : R}
    (hb : ∀ b ∈ B, ((swap b).lazardEval (Polynomial.C ∘ a)).rootMultiplicity t =
      ((swap b).lazardEval (Polynomial.C ∘ a')).rootMultiplicity t') :
    ((swap f).lazardEval (Polynomial.C ∘ a)).rootMultiplicity t =
      ((swap f).lazardEval (Polynomial.C ∘ a')).rootMultiplicity t' := by
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨e, he⟩ := hB.exists_rootMultiplicity_lazardEval_eq_sum hf hf0
  rw [he a t, he a' t']
  exact Finset.sum_congr rfl fun b hb' ↦ congrArg (e b * ·) (hb b hb')

end IsIrreducibleBasis

end Finset
