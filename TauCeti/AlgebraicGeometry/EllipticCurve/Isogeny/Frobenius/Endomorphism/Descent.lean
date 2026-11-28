/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Endomorphism.Field
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Descent

/-!
# Frobenius descent of ordinary elliptic endomorphisms

`WeierstrassCurve.baseChangeEndEquivOfIsOrdinary` identifies endomorphism rings by base change
along algebraic extensions of finite fields. It uses `WeierstrassCurve.mul_comm_of_isOrdinary`
and `TauCeti.Isogeny.existsUnique_map_eq_iff_baseChangeFrobenius_comp_eq`. Its specialization
`WeierstrassCurve.geometricEndEquivOfIsOrdinary` compares with the separable closure. Composing its
inverse with `TauCeti.OrdinaryEnd.orderEquiv` gives
`WeierstrassCurve.geometricEndOrderEquivOfIsOrdinary`, identifying the geometric ring with that
order. See [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.3.
-/

public section

open TauCeti.Isogeny
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [ExpChar F p]
  (W : WeierstrassCurve F) [W.IsElliptic]
  (K : Type*) [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]

/-- Base change identifies the endomorphism rings of an ordinary elliptic curve over a
finite field and over any algebraic extension (Silverman V.3). -/
noncomputable def baseChangeEndEquivOfIsOrdinary (hW : W.IsOrdinary p) :
    Hom W.toAffine W.toAffine ≃+* Hom (W⁄K).toAffine (W⁄K).toAffine :=
  let V := W.toAffine.map (algebraMap F K)
  RingEquiv.ofBijective (S := Hom V V) (Hom.mapRingHom (algebraMap F K)) <| by
    constructor
    · intro f g hfg
      apply Hom.map_injective (algebraMap F K)
      simpa only [Hom.mapRingHom_apply] using hfg
    · intro f
      rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
      · exact ⟨0, map_zero _⟩
      have : ExpChar K p :=
        expChar_of_injective_algebraMap (algebraMap F K).injective p
      have hgeom := (W.isOrdinary_baseChange_iff K).mpr hW
      let V' := (W⁄K).toAffine
      let π : TauCeti.Isogeny V' V' := baseChangeFrobenius K W.toAffine
      let χ : TauCeti.Isogeny V' V' := φ
      have hcomm := (W.baseChange K).mul_comm_of_isOrdinary hgeom
        (Hom.ofIsogeny π) (Hom.ofIsogeny χ)
      rw [Hom.mul_def, Hom.mul_def, Hom.ofIsogeny_comp_ofIsogeny,
        Hom.ofIsogeny_comp_ofIsogeny] at hcomm
      obtain ⟨ψ, hψ, -⟩ := existsUnique_map_eq_iff_baseChangeFrobenius_comp_eq.mpr
        (Hom.ofIsogeny_injective hcomm)
      have hmap : ψ.map (algebraMap F K) = φ := hψ
      exact ⟨Hom.ofIsogeny ψ, by rw [Hom.mapRingHom_apply, Hom.ofIsogeny_map, hmap]⟩

/-- The ordinary endomorphism comparison acts by base change. -/
@[simp]
theorem baseChangeEndEquivOfIsOrdinary_apply (hW : W.IsOrdinary p)
    (f : Hom W.toAffine W.toAffine) :
    W.baseChangeEndEquivOfIsOrdinary K hW f = f.map (algebraMap F K) :=
  (RingEquiv.ofBijective_apply _ _ _).trans (Hom.mapRingHom_apply _ _)

/-- Base-changing a descended endomorphism recovers the original endomorphism. -/
@[simp]
theorem map_baseChangeEndEquivOfIsOrdinary_symm (hW : W.IsOrdinary p)
    (g : Hom (W⁄K).toAffine (W⁄K).toAffine) :
    ((W.baseChangeEndEquivOfIsOrdinary K hW).symm g).map (algebraMap F K) = g :=
  (W.baseChangeEndEquivOfIsOrdinary_apply K hW _).symm.trans
    ((W.baseChangeEndEquivOfIsOrdinary K hW).apply_symm_apply g)

/-- Base change identifies the rational and geometric endomorphism rings of an ordinary
elliptic curve over a finite field (Silverman V.3). -/
noncomputable abbrev geometricEndEquivOfIsOrdinary (hW : W.IsOrdinary p) :
    Hom W.toAffine W.toAffine ≃+* W.GeometricEnd :=
  W.baseChangeEndEquivOfIsOrdinary (SeparableClosure F) hW

/-- The geometric endomorphism ring of an ordinary elliptic curve over a finite field is
the same order in `ℚ(π_q)` as the rational endomorphism ring. -/
noncomputable def geometricEndOrderEquivOfIsOrdinary (hW : W.IsOrdinary p) :
    W.GeometricEnd ≃+* (TauCeti.OrdinaryEnd.order hW).toSubalgebra :=
  (W.geometricEndEquivOfIsOrdinary hW).symm.trans
    ((TauCeti.OrdinaryEnd.ringEquiv hW).symm.trans (TauCeti.OrdinaryEnd.orderEquiv hW))

/-- The geometric order comparison takes a base-changed endomorphism to its rational order image. -/
@[simp]
theorem geometricEndOrderEquivOfIsOrdinary_map (hW : W.IsOrdinary p)
    (f : Hom W.toAffine W.toAffine) :
    W.geometricEndOrderEquivOfIsOrdinary hW (f.map (algebraMap F (SeparableClosure F))) =
      TauCeti.OrdinaryEnd.orderEquiv hW ((TauCeti.OrdinaryEnd.ringEquiv hW).symm f) := by
  have h := (W.geometricEndEquivOfIsOrdinary hW).symm_apply_apply f
  rw [baseChangeEndEquivOfIsOrdinary_apply] at h
  exact congrArg (fun g ↦ TauCeti.OrdinaryEnd.orderEquiv hW
    ((TauCeti.OrdinaryEnd.ringEquiv hW).symm g)) h

end WeierstrassCurve

end
