/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import Mathlib.Data.Nat.PrimeFin

/-!
# The genus of an integral lattice

Two integral lattices have the same genus when their real signatures agree and their integral
localizations are isometric at every prime. This relation also makes sense for degenerate forms.
The local condition concerns the actual forms on `ℤ_p ⊗[ℤ] L`, rather than just their extensions
to `ℚ_p`.

For lattices with equal nonzero signed determinants, the local tests reduce to the finite set
of prime factors of twice the absolute determinant. Outside that set, the local determinants
are units at an odd prime, so the rank and determinant classification gives an isometry. The
signature equality already supplies the rank equality.

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
    have hrank : Module.finrank ℤ L = Module.finrank ℤ M := by
      rw [L.finrank_carrier, M.finrank_carrier,
        ← L.signature_sum_eq_finrank, ← M.signature_sum_eq_finrank]
      exact congrArg (fun s : ℕ × ℕ × ℕ ↦ s.1 + s.2.1 + s.2.2) hsig
    have hn : 2 * L.determinant.natAbs ≠ 0 :=
      mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hdet0)
    refine (sameGenus_iff L M).mpr ⟨hsig, fun p ↦ ?_⟩
    by_cases hp : p ∣ 2 * L.determinant.natAbs
    · exact hlocal p ((Fact.out : p.Prime).mem_primeFactors hp hn)
    · exact L.localIntegralForm_equivalent_of_not_dvd M hrank hdet hp

end TauCeti.IntegralLattice
