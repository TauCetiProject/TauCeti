/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# Point actions through Hopf quotients of the general linear group

A coordinate map that kills a Hopf ideal factors through its quotient. Consequently its
base-valued points preserve every subcomodule of the quotient's standard representation.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.GeneralLinear

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Points of a coordinate map killing `J` preserve subcomodules of the quotient representation. -/
theorem quotientStandardComodule_mulVec_mem
    (J : HopfIdeal R (coordinateHopfAlgebra R n))
    {B : CommHopfAlgCat.{u} R} (φ : coordinateHopfAlgebra R n ⟶ B)
    (hφ : J.toIdeal ≤ RingHom.ker φ.hom.toAlgHom.toRingHom) :
    let _ := corestrictStandardComodule R n
      (Bialgebra.Quotient.mkBialgHom (R := R) J.toIdeal)
    ∀ (N : Subcomodule R (coordinateHopfAlgebra R n ⧸ J.toIdeal) (Fin n → R))
      (p : WithConv (B →ₐ[R] R)) {v : Fin n → R}, v ∈ N →
      (pointToGeneralLinear n (toConv (p.ofConv.comp φ.hom.toAlgHom)) :
        Matrix (Fin n) (Fin n) R) *ᵥ v ∈ N := by
  let _ := corestrictStandardComodule R n
    (Bialgebra.Quotient.mkBialgHom (R := R) J.toIdeal)
  dsimp only
  intro N p v hv
  let φbar := CommHopfAlgCat.liftQuotient J φ hφ
  have hcomp : φbar.hom.comp (Bialgebra.Quotient.mkBialgHom (R := R) J.toIdeal) =
      φ.hom := by
    simpa only [CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_mkQuotient] using
      congrArg CommHopfAlgCat.Hom.hom (CommHopfAlgCat.mkQuotient_comp_liftQuotient J φ hφ)
  have h := corestrictStandardComodule_mulVec_mem R n
    (Bialgebra.Quotient.mkBialgHom (R := R) J.toIdeal) N
    (toConv (p.ofConv.comp φbar.hom.toAlgHom)) hv
  change (pointToGeneralLinear n (toConv ((p.ofConv.comp φbar.hom.toAlgHom).comp
    (Bialgebra.Quotient.mkBialgHom (R := R) J.toIdeal).toAlgHom)) :
      Matrix (Fin n) (Fin n) R) *ᵥ v ∈ N at h
  simpa only [AlgHom.comp_assoc, ← BialgHom.comp_toAlgHom, hcomp] using h

end TauCeti.GeneralLinear
