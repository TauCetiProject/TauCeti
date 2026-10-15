/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Artinian.Module
import TauCeti.LinearAlgebra.Dimension.Tower
public import TauCeti.RingTheory.PicardGroup.Quotient
public import TauCeti.RingTheory.Ideal.Quotient.Finite

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
  let p := (I * J).restrictScalars K
  let q := I.restrictScalars K
  let eTop (L : Submodule K R) :
      ((⊤ : Submodule K R) ⧸ L.submoduleOf ⊤) ≃ₗ[K] R ⧸ L :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.ofTop ⊤ rfl) (by
      rw [LinearEquiv.toLinearMap_ofTop, Submodule.submoduleOf,
        Submodule.map_comap_subtype, top_inf_eq])
  let eIJ := (eTop p).trans (Submodule.Quotient.restrictScalarsEquiv K (I * J))
  let eQ := (eTop q).trans (Submodule.Quotient.restrictScalarsEquiv K I)
  -- The canonical scalar-restriction equivalence preserves ideal carriers and subtype maps.
  let eRestrict : q ≃ₗ[K] I := (I.restrictScalarsEquiv K).restrictScalars K
  have hsub : (p.submoduleOf q).map eRestrict.toLinearMap =
      (Submodule.comap I.subtype (I * J)).restrictScalars K := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    rfl
  let eIK : (q ⧸ p.submoduleOf q) ≃ₗ[K] R ⧸ J :=
    (Submodule.Quotient.equiv _ _ eRestrict hsub).trans
      ((Submodule.Quotient.restrictScalarsEquiv K
        (Submodule.comap I.subtype (I * J))).trans (eI.restrictScalars K))
  have h := TauCeti.rank_quotient_submoduleOf_tower
    (p := p) (q := q) (r := ⊤) (by exact Ideal.mul_le_left) le_top
  rw [eIJ.rank_eq, eIK.rank_eq, eQ.rank_eq, add_comm] at h
  simpa only [← Module.finrank_eq_rank, ← Nat.cast_add, Nat.cast_inj] using h

end Ideal
