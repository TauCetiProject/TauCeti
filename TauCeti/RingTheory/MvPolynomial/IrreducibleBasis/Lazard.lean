/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.IrreducibleBasis.Multiplicity
public import TauCeti.RingTheory.MvPolynomial.Lazard.Map

/-!
# Reconstructing Lazard evaluations from an irreducible basis

Move the distinguished polynomial variable into the coefficient ring using
`MvPolynomial.optionEquivLeft` and `MvPolynomial.optionEquivRight`. Lazard evaluation
in the base coordinates is multiplicative, so an irreducible factorization survives it,
including where ordinary specialization is nullified. Its content becomes a nonzero
constant for every nonzero input. The removed base exponents add, and root multiplicities
are weighted sums of the basis multiplicities, with weights independent of the base point.

These identities transfer invariant base exponents and root multiplicities from the content
and basis to the original family. They do not require preservation of ordinary fiber degrees.
Zero inputs are included in the multiplicity transfer, with multiplicity zero.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Sections 2 and 5.
The factorization is `Finset.IsIrreducibleBasis.exists_eq_C_content_mul_unit_mul_prod`;
the multiplicative evaluation is `MvPolynomial.lazardEvalHom`.
-/

public section

open MvPolynomial Polynomial

namespace Finset.IsIrreducibleBasis

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
  {F B : Finset (Polynomial (MvPolynomial (Fin n) R))}

local notation "swap" =>
  (AlgEquiv.trans (AlgEquiv.symm (optionEquivLeft R (Fin n)))
    (optionEquivRight R (Fin n)))

section Content

variable [UniqueFactorizationMonoid (MvPolynomial (Fin n) R)]
  [NormalizedGCDMonoid (MvPolynomial (Fin n) R)]

/-- The Lazard evaluation of each input is a scalar times the product of powers
of the Lazard evaluations of its basis factors. The scalar contains the Lazard-evaluated
content and a unit, and the same factorization works at every base point. -/
theorem exists_lazardEval_eq_C_mul_prod (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) :
    ∃ (u : (MvPolynomial (Fin n) R)ˣ) (e : Polynomial (MvPolynomial (Fin n) R) → ℕ),
      ∀ a : Fin n → R, (swap f).lazardEval (Polynomial.C ∘ a) =
        Polynomial.C (f.content.lazardEval a * (u : MvPolynomial (Fin n) R).lazardEval a) *
          ∏ b ∈ B, (swap b).lazardEval (Polynomial.C ∘ a) ^ e b := by
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  refine ⟨u, e, fun a ↦ ?_⟩
  have hswap (g : MvPolynomial (Fin n) R) :
      swap (Polynomial.C g) = MvPolynomial.map Polynomial.C g :=
    optionEquivRight_optionEquivLeft_symm_C g
  conv_lhs => rw [hfe]
  rw [map_mul, hswap, lazardEval_mul, lazardEval_map Polynomial.C Polynomial.C_injective,
    lazardEval_mul]
  congr 1
  simp only [map_prod, map_pow]
  simpa only [map_pow, lazardEvalHom_apply] using
    map_prod (lazardEvalHom (Polynomial.C ∘ a)) (fun b ↦ swap b ^ e b) B

/-- For a nonzero input, the removed base exponents are the content exponents plus the
weighted sum of the basis exponents. The weights do not depend on the base point. -/
theorem exists_lazardExponent_eq_content_add_sum (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) (hf0 : f ≠ 0) :
    ∃ e : Polynomial (MvPolynomial (Fin n) R) → ℕ, ∀ a : Fin n → R,
      (swap f).lazardExponent (Polynomial.C ∘ a) = f.content.lazardExponent a +
        ∑ b ∈ B, e b • (swap b).lazardExponent (Polynomial.C ∘ a) := by
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  refine ⟨e, fun a ↦ ?_⟩
  have hc : f.content ≠ 0 := fun h ↦ hf0 (content_eq_zero_iff.mp h)
  have hu : (u : MvPolynomial (Fin n) R).lazardExponent a = 0 :=
    lazardExponent_eq_zero_of_eval_ne_zero (u.isUnit.map (MvPolynomial.eval a)).ne_zero
  have hb : ∀ b ∈ B, swap b ≠ 0 := fun b hb ↦
    (by simpa only [map_zero] using (swap).injective.ne (hB.irreducible b hb).ne_zero)
  have hswap (g : MvPolynomial (Fin n) R) :
      swap (Polynomial.C g) = MvPolynomial.map Polynomial.C g :=
    optionEquivRight_optionEquivLeft_symm_C g
  have hc' : MvPolynomial.map Polynomial.C (f.content * (u : MvPolynomial (Fin n) R)) ≠ 0 := by
    simpa only [map_zero] using
      (MvPolynomial.map_injective Polynomial.C Polynomial.C_injective).ne (mul_ne_zero hc u.ne_zero)
  conv_lhs => rw [hfe, map_mul, hswap]
  simp only [map_prod, map_pow]
  rw [lazardExponent_mul hc'
      (Finset.prod_ne_zero_iff.mpr fun b hb' ↦ pow_ne_zero _ (hb b hb')),
    lazardExponent_map Polynomial.C Polynomial.C_injective,
    lazardExponent_mul hc u.ne_zero, hu, add_zero,
    lazardExponent_prod B _ (fun b hb' ↦ pow_ne_zero _ (hb b hb'))]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun b hb' ↦
    lazardExponent_pow (hb b hb') _ _)

/-- Invariant content and basis exponents give invariant input exponents, including
zero inputs. No connectedness or nonnullification hypothesis is required. -/
theorem lazardExponent_eq (hB : F.IsIrreducibleBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) {a a' : Fin n → R}
    (hc : f.content.lazardExponent a = f.content.lazardExponent a')
    (hb : ∀ b ∈ B, (swap b).lazardExponent (Polynomial.C ∘ a) =
      (swap b).lazardExponent (Polynomial.C ∘ a')) :
    (swap f).lazardExponent (Polynomial.C ∘ a) =
      (swap f).lazardExponent (Polynomial.C ∘ a') := by
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨e, he⟩ := hB.exists_lazardExponent_eq_content_add_sum hf hf0
  rw [he a, he a', hc]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun b hb' ↦ congrArg (e b • ·) (hb b hb'))

end Content

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
    rw [hφ, AlgEquiv.trans_apply, optionEquivRight_optionEquivLeft_symm_C,
      lazardEval_map Polynomial.C Polynomial.C_injective]
  have hp : swap f ≠ 0 := by simpa only [map_zero] using (swap).injective.ne hf0
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
    have hp : swap f ≠ 0 := by simpa only [map_zero] using (swap).injective.ne hf0
    have hpos := (Polynomial.rootMultiplicity_pos (lazardEval_ne_zero hp _)).mpr ht
    rw [he] at hpos
    obtain ⟨b, hb, hbpos⟩ := Finset.sum_pos_iff.mp hpos
    refine ⟨b, hb, Polynomial.rootMultiplicity_pos'.mp ?_ |>.2⟩
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hbpos
    exact lt_irrefl _ hbpos
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

end Finset.IsIrreducibleBasis
