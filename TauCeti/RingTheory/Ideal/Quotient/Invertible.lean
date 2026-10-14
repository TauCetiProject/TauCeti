/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RingTheory.PicardGroup.Quotient
public import TauCeti.RingTheory.Ideal.Quotient.ModuleFinite

/-!
# Quotients by products with invertible ideals

For an ideal `I` that is invertible as an `R`-module and an ideal `J` with semilocal
quotient, `I / IJ` is isomorphic to `R / J`. Consequently, when `R` is an algebra over
a field and both ideals have finite codimension, codimension is additive on `I * J`.
Neither a domain hypothesis nor a choice of fraction field is required.

These are the commutative-algebra steps in the point-to-class surjectivity argument,
adapted from Chris Birkbeck's AINTLIB (`github.com/CBirkbeck/AINTLIB`,
`HasseWeil/Pic0/ToClassSurjective.lean`, revision `dev/hasse-weil @ 513e83879e2f`, Apache-2.0).
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- For an invertible ideal `I` and a semilocal quotient `R / J`, the quotient `I / IJ`
is isomorphic to `R / J` as an `R`-module. -/
theorem nonempty_quotient_comap_mul_linearEquiv_quotient (I J : Ideal R)
    [Module.Invertible R I]
    [Finite (MaximalSpectrum (R ⧸ J))] :
    Nonempty ((I ⧸ Submodule.comap I.subtype (I * J)) ≃ₗ[R] R ⧸ J) := by
  obtain ⟨e⟩ := Module.Invertible.nonempty_quotientEquiv I J
  exact ⟨(Submodule.quotEquivOfEq _ _ (I.smul_top_eq_comap_mul J).symm).trans e⟩

/-- Codimension is additive on a product of finite-codimensional ideals when the first
ideal is invertible as a module. -/
theorem finrank_quotient_mul (K : Type*) [Field K] [Algebra K R] (I J : Ideal R)
    [Module.Invertible R I] [Module.Finite K (R ⧸ I)] [Module.Finite K (R ⧸ J)] :
    Module.finrank K (R ⧸ I * J) =
      Module.finrank K (R ⧸ I) + Module.finrank K (R ⧸ J) := by
  let : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite K (R ⧸ J)
  have : Module.Finite K (R ⧸ I * J) := I.finite_quotient_mul J
  obtain ⟨eI⟩ := nonempty_quotient_comap_mul_linearEquiv_quotient I J
  let g : I →ₗ[R] R ⧸ I * J := (I * J).mkQ.comp I.subtype
  let N := LinearMap.range g
  have hN : N = Submodule.map (I * J).mkQ I := by
    dsimp only [N, g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have e₁ : ((R ⧸ I * J) ⧸ N) ≃ₗ[R] R ⧸ I := by
    rw [hN]
    exact Submodule.quotientQuotientEquivQuotient (I * J) I Ideal.mul_le_left
  let e₂ : N ≃ₗ[R] I ⧸ Submodule.comap I.subtype (I * J) :=
    g.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ (by
      simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ]))
  let eN : N ≃ₗ[R] R ⧸ J := e₂.trans eI
  let eNK := ((N.restrictScalarsEquiv K).restrictScalars K).trans (eN.restrictScalars K)
  let e₁K := (Submodule.Quotient.restrictScalarsEquiv K N).trans (e₁.restrictScalars K)
  rw [← (N.restrictScalars K).finrank_quotient_add_finrank,
    e₁K.finrank_eq, eNK.finrank_eq]

end Ideal
