/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Operations
public import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Int.Associated
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The genus of an integral lattice

Two integral lattices have the same genus when their real signatures agree and their integral
localizations are isometric at every prime. This relation also makes sense for degenerate forms.
The local condition concerns the actual forms on `ℤ_p ⊗[ℤ] L`, rather than just their extensions
to `ℚ_p`.

The genus determines the signed determinant. Integral local isometry at `p` changes the
determinant by the square of a unit of `ℤ_p`, so the absolute determinants have the same
`p`-adic valuation at every prime and are therefore equal. The real signature fixes the sign,
since the signed determinant is `(-1) ^ n₋` times the absolute determinant.

For lattices with equal nonzero signed determinants, the local tests reduce to the finite set
of prime factors of twice the absolute determinant. Outside that set, the local determinants
are units at an odd prime, so the rank and determinant classification gives an isometry. The
signature equality already supplies the rank equality.

The genus also fixes the rational quadratic space at every place. An integral local isometry
extends to the completions, so lattices in one genus have isometric completed rational spaces
`ℚ_p ⊗[ℚ] V` at every prime, while at the real place their signatures agree by definition.
Combining these local isometries into an isometry of the rational forms over `ℚ` is the
Hasse–Minkowski theorem and is not done here. Conversely, for lattices whose rational forms are
isometric, the signature condition holds automatically, and the genus is decided by the integral
localizations alone.

## Main results

* `TauCeti.IntegralLattice.SameGenus.determinant_eq`: the genus determines the signed determinant.
* `TauCeti.IntegralLattice.SameGenus.completedRationalForm_equivalent`: lattices in one genus have
  isometric completed rational spaces at every prime.
* `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_equivalent_primeFactors`: for equal
  nonzero determinants, only the primes dividing twice the determinant need checking.
* `TauCeti.IntegralLattice.sameGenus_iff_localIntegralForm_equivalent`: on isometric rational
  spaces, the genus is decided by integral local isometry.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter IX, for genera of lattices and
  the odd-prime unimodular classification.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, for integral local equivalence.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W U : Type*}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  [AddCommGroup U] [Module ℚ U]

/-- Two integral lattices have the same genus if their signatures agree and their integral
local forms are isometric at every prime. No nondegeneracy assumption is imposed. -/
def SameGenus (L : IntegralLattice V) (M : IntegralLattice W) : Prop :=
  L.signature = M.signature ∧
    ∀ (p : ℕ) [Fact p.Prime], (L.localIntegralForm p).Equivalent (M.localIntegralForm p)

/-- The signature and integral local isometry conditions characterizing the genus relation. -/
theorem sameGenus_iff (L : IntegralLattice V) (M : IntegralLattice W) :
    L.SameGenus M ↔ L.signature = M.signature ∧
      ∀ (p : ℕ) [Fact p.Prime], (L.localIntegralForm p).Equivalent (M.localIntegralForm p) :=
  (Iff.rfl)

namespace SameGenus

variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- Lattices in the same genus have equal real signatures. -/
theorem signature_eq (h : L.SameGenus M) : L.signature = M.signature :=
  (sameGenus_iff L M).mp h |>.1

/-- Lattices in the same genus have isometric integral localizations at every prime. -/
theorem localIntegralForm_equivalent (h : L.SameGenus M) (p : ℕ) [Fact p.Prime] :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) :=
  (sameGenus_iff L M).mp h |>.2 p

/-- Lattices in the same genus have equal ranks. -/
theorem finrank_eq (h : L.SameGenus M) : Module.finrank ℤ L = Module.finrank ℤ M :=
  L.finrank_eq_of_signature_eq h.signature_eq

/-- Lattices in the same genus have the same positive index. -/
theorem sigPos_eq (h : L.SameGenus M) : L.sigPos = M.sigPos := by
  have hsig := h.signature_eq
  simp only [signature, Prod.mk.injEq] at hsig
  exact hsig.1

/-- Lattices in the same genus have the same null index. -/
theorem sigNull_eq (h : L.SameGenus M) : L.sigNull = M.sigNull := by
  have hsig := h.signature_eq
  simp only [signature, Prod.mk.injEq] at hsig
  exact hsig.2.1

/-- Lattices in the same genus have the same negative index. -/
theorem sigNeg_eq (h : L.SameGenus M) : L.sigNeg = M.sigNeg := by
  have hsig := h.signature_eq
  simp only [signature, Prod.mk.injEq] at hsig
  exact hsig.2.2

/-- Lattices in the same genus have isomorphic ambient spaces. -/
theorem nonempty_linearEquiv (h : L.SameGenus M) : Nonempty (V ≃ₗ[ℚ] W) := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  refine FiniteDimensional.nonempty_linearEquiv_of_finrank_eq ?_
  rw [← L.finrank_carrier, ← M.finrank_carrier, h.finrank_eq]

/-- Positive definiteness is a property of the genus. -/
theorem isPosDef_iff (h : L.SameGenus M) : L.IsPosDef ↔ M.IsPosDef := by
  rw [M.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero,
    L.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero, h.sigNull_eq, h.sigNeg_eq]

/-- Negative definiteness is a property of the genus. -/
theorem isNegDef_iff (h : L.SameGenus M) : L.IsNegDef ↔ M.IsNegDef := by
  rw [M.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero,
    L.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero, h.sigPos_eq, h.sigNull_eq]

/-- Every integral lattice belongs to its own genus. -/
@[refl, simp]
theorem refl (L : IntegralLattice V) : L.SameGenus L :=
  (sameGenus_iff L L).mpr ⟨rfl, fun _ ↦ LinearMap.BilinForm.Equivalent.refl _⟩

/-- The genus relation is symmetric. -/
@[symm]
theorem symm (h : L.SameGenus M) : M.SameGenus L :=
  (sameGenus_iff M L).mpr
    ⟨h.signature_eq.symm, fun p ↦ (h.localIntegralForm_equivalent p).symm⟩

/-- The genus relation is transitive. -/
@[trans]
theorem trans (h : L.SameGenus M) (h' : M.SameGenus N) : L.SameGenus N :=
  (sameGenus_iff L N).mpr
    ⟨h.signature_eq.trans h'.signature_eq,
      fun p ↦ (h.localIntegralForm_equivalent p).trans (h'.localIntegralForm_equivalent p)⟩

/-- **Lattices in the same genus have equal signed determinants.** No nondegeneracy assumption is
needed: degenerate lattices in one genus both have determinant zero. -/
theorem determinant_eq (h : L.SameGenus M) : L.determinant = M.determinant := by
  have habs : L.determinant.natAbs = M.determinant.natAbs := by
    refine Int.natAbs_eq_iff_associated.mpr
      (Int.associated_iff_forall_associated_padicInt.mpr fun p _ ↦ ?_)
    obtain ⟨u, hu⟩ := L.exists_determinant_eq_unit_sq_mul_of_localIntegralForm_equivalent M p
      (h.localIntegralForm_equivalent p)
    exact Associated.symm ⟨u ^ 2, by rw [hu, Units.val_pow_eq_pow_val, mul_comm]⟩
  have hneg : L.sigNeg = M.sigNeg := congrArg (fun s ↦ s.2.2) h.signature_eq
  rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
    M.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hneg, discriminant_def,
    discriminant_def, habs]

/-- Scaling by a common nonzero integer preserves the genus relation. -/
theorem smul {n : ℤ} (hn : n ≠ 0) (h : L.SameGenus M) : (n • L).SameGenus (n • M) := by
  refine (sameGenus_iff _ _).mpr ⟨?_, fun p _ ↦ ?_⟩
  · rcases hn.lt_or_gt with hneg | hpos
    · rw [signature_smul_of_neg hneg, signature_smul_of_neg hneg, h.sigPos_eq, h.sigNull_eq,
        h.sigNeg_eq]
    · rw [signature_smul_of_pos hpos, signature_smul_of_pos hpos]
      exact h.signature_eq
  · rw [localIntegralForm_smul, localIntegralForm_smul]
    exact (LinearMap.BilinForm.equivalent_smul_iff
      (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn))).mpr
      (h.localIntegralForm_equivalent p)

/-- **Lattices in the same genus have isometric completed rational spaces**: at every prime `p`
the quadratic spaces `ℚ_p ⊗[ℚ] V` and `ℚ_p ⊗[ℚ] W` are isometric, since the integral local
isometry extends to the completions. -/
theorem completedRationalForm_equivalent (h : L.SameGenus M) (p : ℕ) [Fact p.Prime] :
    (L.completedRationalForm p).Equivalent (M.completedRationalForm p) :=
  completedRationalForm_equivalent_of_localIntegralForm_equivalent p
    (h.localIntegralForm_equivalent p)

end SameGenus

/-- An integral-lattice isometry preserves the genus. -/
theorem Isometry.sameGenus {L : IntegralLattice V} {M : IntegralLattice W}
    (e : Isometry L M) : L.SameGenus M :=
  (sameGenus_iff L M).mpr ⟨e.signature_eq, fun p ↦ ⟨e.localCarrierIsometry p⟩⟩

/-- For lattices with equal nonzero signed determinants, equal signatures and integral local
isometry at the prime factors of twice the absolute determinant characterize the genus.
This is a finite family of local isometry conditions; no local classification at its primes
is assumed. -/
theorem sameGenus_iff_localIntegralForm_equivalent_primeFactors
    (L : IntegralLattice V) (M : IntegralLattice W)
    (hdet : L.determinant = M.determinant) (hdet0 : L.determinant ≠ 0) :
    L.SameGenus M ↔ L.signature = M.signature ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∈ (2 * L.determinant.natAbs).primeFactors →
        (L.localIntegralForm p).Equivalent (M.localIntegralForm p) := by
  constructor
  · intro h
    exact ⟨h.signature_eq, fun p _ _ ↦ h.localIntegralForm_equivalent p⟩
  · rintro ⟨hsig, hlocal⟩
    have hn : 2 * L.determinant.natAbs ≠ 0 :=
      mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hdet0)
    refine (sameGenus_iff L M).mpr ⟨hsig, fun p ↦ ?_⟩
    by_cases hp : p ∣ 2 * L.determinant.natAbs
    · exact hlocal p ((Fact.out : p.Prime).mem_primeFactors hp hn)
    · exact L.localIntegralForm_equivalent_of_not_dvd M (L.finrank_eq_of_signature_eq hsig)
        hdet hp

/-- **On isometric rational spaces the genus is decided by the integral localizations.** If the
rational forms of `L` and `M` are isometric, then `L` and `M` lie in one genus exactly when their
integral localizations are isometric at every prime: the rational isometry already supplies the
equality of signatures. -/
theorem sameGenus_iff_localIntegralForm_equivalent {L : IntegralLattice V} {M : IntegralLattice W}
    (hform : L.form.Equivalent M.form) :
    L.SameGenus M ↔
      ∀ (p : ℕ) [Fact p.Prime], (L.localIntegralForm p).Equivalent (M.localIntegralForm p) :=
  ⟨fun h p _ ↦ h.localIntegralForm_equivalent p,
    fun h ↦ (sameGenus_iff L M).mpr ⟨signature_eq_of_equivalent hform, h⟩⟩

end TauCeti.IntegralLattice
