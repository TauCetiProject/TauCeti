/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Place
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal

/-!
# Galois actions on divisors of Weierstrass curves

Coefficient automorphisms act on divisors by transporting their places and retaining their integer
coefficients. This action preserves degree and takes `div f` to `div (σ f)`, so it preserves
linear equivalence. Together with the equivariance of the point–place dictionary, this transports
the divisors and rational functions entering the Weil pairing.

The action reuses Mathlib's `Finsupp.domCongr` on the existing `TauCeti.Divisor` carrier.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 and III.8.
-/

public section

open TauCeti AlgebraicGeometry
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

/-- **The Galois action on divisors of a base-changed curve.** It pushes forward each place by
`placeGaloisAction` and leaves its integer coefficient unchanged. -/
noncomputable def divisorGaloisAction :
    (K ≃ₐ[F] K) →* Multiplicative (AddAut (Divisor K (W⁄K).toAffine.FunctionField)) where
  toFun σ := Multiplicative.ofAdd (Finsupp.domCongr (W.placeGaloisAction σ))
  map_one' := by
    simp only [map_one, Equiv.Perm.one_def, Finsupp.domCongr_refl,
      ← AddAut.zero_def, ofAdd_zero]
  map_mul' σ τ := by
    simp only [map_mul]
    exact congrArg Multiplicative.ofAdd (Finsupp.domCongr_trans
      (W.placeGaloisAction τ) (W.placeGaloisAction σ)).symm

/-- The divisor action is the formal pushforward along the Galois action on places. -/
theorem divisorGaloisAction_apply (σ : K ≃ₐ[F] K)
    (D : Divisor K (W⁄K).toAffine.FunctionField) :
    Multiplicative.toAdd (W.divisorGaloisAction σ) D =
      WeilDivisor.pushforward (W.placeGaloisAction σ) D := by
  simp [divisorGaloisAction, Finsupp.equivMapDomain_eq_mapDomain, WeilDivisor.pushforward_apply]

/-- The coefficient at `v` after conjugation is the old coefficient at `σ⁻¹ v`. -/
@[simp]
theorem divisorGaloisAction_coeff (σ : K ≃ₐ[F] K)
    (D : Divisor K (W⁄K).toAffine.FunctionField)
    (v : Place K (W⁄K).toAffine.FunctionField) :
    (Multiplicative.toAdd (W.divisorGaloisAction σ) D).coeff v =
      D.coeff (W.placeGaloisAction σ.symm v) := by
  simp [divisorGaloisAction, WeilDivisor.coeff, Finsupp.equivMapDomain_apply]

/-- Conjugation takes a prime divisor to the prime divisor at the conjugate place. -/
@[simp]
theorem divisorGaloisAction_ofPoint (σ : K ≃ₐ[F] K)
    (v : Place K (W⁄K).toAffine.FunctionField) :
    Multiplicative.toAdd (W.divisorGaloisAction σ) (WeilDivisor.ofPoint v) =
      WeilDivisor.ofPoint (W.placeGaloisAction σ v) := by
  rw [divisorGaloisAction_apply, WeilDivisor.pushforward_ofPoint]

/-- Galois conjugation preserves divisor degree. -/
@[simp]
theorem divisorGaloisAction_degree (σ : K ≃ₐ[F] K)
    (D : Divisor K (W⁄K).toAffine.FunctionField) :
    Divisor.degree (Multiplicative.toAdd (W.divisorGaloisAction σ) D) = Divisor.degree D := by
  rw [divisorGaloisAction_apply, Divisor.degree_eq_weightedDegree,
    WeilDivisor.weightedDegree_pushforward, Divisor.degree_eq_weightedDegree]
  simp only [Function.comp_def, placeGaloisAction_degree]

/-- **Principal divisors are Galois-equivariant.** The zeros and poles of `σ f` are the
conjugates of those of `f`, with the same multiplicities. -/
@[simp]
theorem divisorGaloisAction_principal (σ : K ≃ₐ[F] K) (f : (W⁄K).toAffine.FunctionFieldˣ) :
    Divisor.principal (W⁄K).toAffine.isFunctionField
        (Units.map (W.functionFieldGaloisAction σ).toMonoidHom f) =
      Multiplicative.toAdd (W.divisorGaloisAction σ)
        (Divisor.principal (W⁄K).toAffine.isFunctionField f) := by
  ext v
  simp [Divisor.coeff_principal, divisorGaloisAction_coeff, placeGaloisAction_ord]

/-- Galois conjugation preserves and reflects linear equivalence of divisors. -/
@[simp]
theorem divisorGaloisAction_linearlyEquivalent_iff (σ : K ≃ₐ[F] K)
    (A B : Divisor K (W⁄K).toAffine.FunctionField) :
    (Place.orderSystem (W⁄K).toAffine.isFunctionField).LinearlyEquivalent
        (Multiplicative.toAdd (W.divisorGaloisAction σ) A)
        (Multiplicative.toAdd (W.divisorGaloisAction σ) B) ↔
      (Place.orderSystem (W⁄K).toAffine.isFunctionField).LinearlyEquivalent A B := by
  rw [Divisor.linearlyEquivalent_iff, Divisor.linearlyEquivalent_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Units.map (W.functionFieldGaloisAction σ.symm).toMonoidHom f, ?_⟩
    rw [divisorGaloisAction_principal, hf, map_sub]
    simp [← AlgEquiv.aut_inv]
  · rintro ⟨f, hf⟩
    refine ⟨Units.map (W.functionFieldGaloisAction σ).toMonoidHom f, ?_⟩
    rw [divisorGaloisAction_principal, hf, map_sub]

end WeierstrassCurve
