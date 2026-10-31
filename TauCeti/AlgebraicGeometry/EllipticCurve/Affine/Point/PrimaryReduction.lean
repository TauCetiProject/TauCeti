/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction

/-!
# Primary torsion and the local isogeny ratio at good reduction

At good reduction over a completed discretely valued field, reduction identifies the entire
`n`-primary component with that of the reduced curve whenever `n` is prime to the residue
characteristic. Here `n` need not be prime: the primary component consists of all points killed
by some power of `n`. Unlike the full torsion subgroup, it contains no residue-characteristic
torsion. The identification uses unique lifting of torsion of order dividing `n^k` for every `k`.

This identifies the finite torsion groups that compute local kernel/cokernel ratios of
isogenies away from their degree with residue-field data. It does not require a bound on
the exponent of the primary component or finiteness of the residue field.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VII.3.1 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open IsDedekindDomain IsLocalRing

namespace WeierstrassCurve

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  {u : HeightOneSpectrum A}

local notation "F_u" => HeightOneSpectrum.adicCompletion F u
local notation "O_u" => HeightOneSpectrum.adicCompletionIntegers F u
local notation "v_u" => (Valued.v : Valuation (HeightOneSpectrum.adicCompletion F u)
  (WithZero (Multiplicative ℤ)))
local notation "R_u" => Valuation.valuationSubring
  (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

variable (C : WeierstrassCurve (u.adicCompletionIntegers F)) [C.IsElliptic]
  [DecidableEq (u.adicCompletion F)]
  [DecidableEq (ResidueField
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ))).valuationSubring)]

local instance : IsIntegral O_u (C.baseChange F_u) := ⟨C, rfl⟩

local instance : ((C.baseChange F_u).integralModel O_u).IsElliptic := by
  rw [integralModel_baseChange_self]
  infer_instance

local instance : (integralModel R_u (C.baseChange F_u).toAffine).IsElliptic :=
  inferInstanceAs (((C.baseChange F_u).integralModel O_u).IsElliptic)

/-- Reduction identifies the `n`-primary components at good reduction when `n` is prime
to the residue characteristic. Neither primality of `n` nor finiteness of the residue field
is required. The target is the integral model used by the reduction homomorphism. -/
noncomputable def primaryReductionAddEquiv {n : ℕ} (hn : (n : A) ∉ u.asIdeal) :
    AddCommGroup.primaryComponent (C.baseChange F_u).toAffine.Point n ≃+
      AddCommGroup.primaryComponent
        ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point n := by
  -- The formal-kernel API uses classical equality decisions on the completed field.
  cases Subsingleton.elim (inferInstance : DecidableEq F_u)
    (fun a b ↦ Classical.propDecidable (a = b))
  classical
  have hpow (k : ℕ) : ((n ^ k : ℕ) : A) ∉ u.asIdeal := by
    simpa only [Nat.cast_pow] using fun h ↦ hn (u.isPrime.mem_of_pow_mem k h)
  let ρ := Affine.Point.reductionHom v_u (W := (C.baseChange F_u).toAffine)
  let f : AddCommGroup.primaryComponent (C.baseChange F_u).toAffine.Point n →+
      AddCommGroup.primaryComponent
        ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point n :=
    { toFun := fun P ↦ ⟨ρ P, by
        obtain ⟨k, hk⟩ := P.property
        exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
      map_zero' := Subtype.ext (map_zero ρ)
      map_add' := fun P Q ↦ Subtype.ext (map_add ρ (P : (C.baseChange F_u).toAffine.Point)
        (Q : (C.baseChange F_u).toAffine.Point)) }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro P Q h
    apply Subtype.ext
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp (sub_mem P.property Q.property)
    apply sub_eq_zero.mp
    apply C.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero u (hpow k) _ hk
    rw [Affine.Point.mem_kerReduction_iff_reductionHom_eq_zero, map_sub, sub_eq_zero]
    exact congrArg Subtype.val h
  · intro Q
    obtain ⟨k, hk⟩ := Q.property
    obtain ⟨P, hP, -⟩ := Affine.Point.existsUnique_torsion_lift u C (hpow k) Q hk
    exact ⟨⟨P, ⟨k, hP.1⟩⟩, Subtype.ext hP.2⟩

/-- The primary specialization equivalence sends a point to its reduction. -/
@[simp]
theorem coe_primaryReductionAddEquiv_apply {n : ℕ} (hn : (n : A) ∉ u.asIdeal)
    (P : AddCommGroup.primaryComponent (C.baseChange F_u).toAffine.Point n) :
    (C.primaryReductionAddEquiv hn P :
      ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point) =
        Affine.Point.reductionHom v_u (W := (C.baseChange F_u).toAffine) P := by
  -- Transport the point-group structure to the equality decisions used in the construction.
  cases Subsingleton.elim (inferInstance : DecidableEq F_u)
    (fun a b ↦ Classical.propDecidable (a = b))
  rfl

/-- The inverse primary specialization equivalence lifts a point with the prescribed reduction. -/
@[simp]
theorem reductionHom_primaryReductionAddEquiv_symm {n : ℕ} (hn : (n : A) ∉ u.asIdeal)
    (Q : AddCommGroup.primaryComponent
      ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point n) :
    Affine.Point.reductionHom v_u (W := (C.baseChange F_u).toAffine)
        ((C.primaryReductionAddEquiv hn).symm Q : (C.baseChange F_u).toAffine.Point) = Q := by
  have h := congrArg Subtype.val ((C.primaryReductionAddEquiv hn).apply_symm_apply Q)
  simpa only [coe_primaryReductionAddEquiv_apply] using h

end WeierstrassCurve
