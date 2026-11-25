/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.Genericity.DecomposedGeneric
import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic

/-!
# Restriction at a completely split witness

A decomposed generic prime stays a witness after restricting the representation to an
intermediate base field in which the prime still splits completely. Its residue cardinality
at every new place stays the same, so the forbidden ratios and Frobenius tests are preserved.
-/

public section

open NumberField Ideal Module

/-- A decomposed generic prime survives restriction to any intermediate base in which it
splits completely, for the same representation field and the same rational prime. -/
theorem MonoidHom.IsDecomposedGenericPrime.restrictScalars
    {F E L k n : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Field L]
    [Algebra F L] [Algebra F E] [Algebra E L] [IsScalarTower F E L] [Field k] [Fintype n]
    [DecidableEq n] {r : Gal(L/F) →* GL n k} {q : ℕ} (hq : r.IsDecomposedGenericPrime q)
    (hsplit : ((span {(q : ℤ)}).primesOver (𝓞 E)).ncard = finrank ℚ E) :
    (r.comp (AlgEquiv.restrictScalarsHom F : Gal(L/E) →* Gal(L/F))).IsDecomposedGenericPrime q := by
  refine MonoidHom.isDecomposedGenericPrime_iff.mpr
    ⟨hq.prime, hq.natCast_ne_zero, hsplit, fun Q _ _ σ hσ ↦ ?_⟩
  have hnorm := absNorm_eq_of_ncard_primesOver_eq_finrank (Q.under (𝓞 E)) hsplit
  have hcard : Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) = Nat.card (𝓞 F ⧸ Q.under (𝓞 F)) := by
    simpa only [absNorm_apply, Submodule.cardQuot_apply] using
      hnorm.trans (hq.absNorm_eq (Q.under (𝓞 F))).symm
  have hσF : IsArithFrobAt (𝓞 F) (σ.restrictScalars F) Q := fun x ↦ hcard ▸ hσ x
  obtain ⟨hI, hg⟩ := MonoidHom.isGenericAt_iff.mp (hq.isGenericAt Q hσF)
  -- Restricting scalars leaves the action on the top ring of integers unchanged.
  exact MonoidHom.isGenericAt_iff.mpr ⟨fun τ hτ ↦ hI (x := τ.restrictScalars F) hτ, hg⟩
