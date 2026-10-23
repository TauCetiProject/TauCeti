/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Localization

/-!
# The overlap of the two affine charts of a function field

Let `F / k` be an algebraic function field and `x ∈ F` transcendental over `k`. The affine model
`R_x`, the integral closure of `k[x]` in `F`, is the holomorphy ring of the places at which `x` is
regular (`TauCeti.restrictScalars_integralClosure_adjoin_eq_holomorphyRing`), and the model
`R_{x⁻¹}` is the holomorphy ring of the places at which `x` has no zero. The two charts cover the
place set, since no place is both a zero and a pole of `x`, and they overlap on the places at which
`x` is a unit.

This file identifies the ring of the overlap. Inverting `x` in `R_x` gives the localization
`R_x[1/x]`, realized inside `F` by Mathlib's `Localization.subalgebra.ofField`, and by
`TauCeti.coe_ofField_powers_eq_holomorphyRing` this localization is the holomorphy ring of the
overlap. Applied to `x⁻¹`, the same statement identifies `R_{x⁻¹}[x]` with the same ring, so the
two localizations are one and the same subring of `F`: the two charts glue along their common
localization, and `TauCeti.ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv` is the
resulting ring isomorphism `R_x[1/x] ≃+* R_{x⁻¹}[x]`, compatible with the two inclusions into `F`.
The overlap ring is a Dedekind domain whose height one primes are the places of the overlap
(`TauCeti.ofFieldPowersHeightOneSpectrumEquiv`), and the prime of the overlap ring below such a
place contracts to the prime of `R_x` below it (`TauCeti.Place.comap_center_asIdeal`).

## Main results

* `TauCeti.coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing` and
  `TauCeti.coe_ofField_powers_integralClosure_adjoin_eq_coe_ofField_powers_inv`: the two charts
  `R_x` and `R_{x⁻¹}` localize to one and the same subring of `F`, the holomorphy ring of the
  places at which `x` is a unit.
* `TauCeti.ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv`: the ring isomorphism
  `R_x[1/x] ≃+* R_{x⁻¹}[x]` induced by that equality, with
  `TauCeti.coe_ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv_apply` and its `symm`
  version recording that it commutes with the inclusions into `F`.
* `TauCeti.valuation_integralClosureAdjoinHeightOneSpectrumEquiv_eq_valuation_inv`: at a place
  of the overlap, the primes of `R_x` and of `R_{x⁻¹}` below it induce the same valuation on `F`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2.
-/

public section

open IsDedekindDomain Localization.subalgebra

open scoped nonZeroDivisors

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

variable (x : F) [IsFractionRing (integralClosure (Algebra.adjoin k {x}) F) F]

/-! ### The two charts `R_x` and `R_{x⁻¹}` glue along their common localization -/

section Gluing

variable (hx : Submonoid.powers
    (⟨x, (integralClosure (Algebra.adjoin k {x}) F).algebraMap_mem
      ⟨x, Algebra.self_mem_adjoin_singleton k x⟩⟩ : integralClosure (Algebra.adjoin k {x}) F) ≤
      (integralClosure (Algebra.adjoin k {x}) F)⁰)
  (hx' : Submonoid.powers
    (⟨x⁻¹, (integralClosure (Algebra.adjoin k {x⁻¹}) F).algebraMap_mem
      ⟨x⁻¹, Algebra.self_mem_adjoin_singleton k x⁻¹⟩⟩ :
        integralClosure (Algebra.adjoin k {x⁻¹}) F) ≤
      (integralClosure (Algebra.adjoin k {x⁻¹}) F)⁰)

/-- **`R_x[1/x]` is the holomorphy ring of the overlap of the two charts**: the places at which
`x` is a unit, the intersection of the finite chart of `R_x` with that of `R_{x⁻¹}`. -/
theorem coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing (hF : IsFunctionField k F) :
    (ofField F (Submonoid.powers
      (⟨x, (integralClosure (Algebra.adjoin k {x}) F).algebraMap_mem
        ⟨x, Algebra.self_mem_adjoin_singleton k x⟩⟩ : integralClosure (Algebra.adjoin k {x}) F))
          hx : Set F) =
      holomorphyRing ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers}) :=
  coe_ofField_powers_eq_holomorphyRing hF (by
    rw [← Subalgebra.coe_restrictScalars k,
      restrictScalars_integralClosure_adjoin_eq_holomorphyRing hF]) _ hx

/-- **The two charts glue along their common localization**: inside `F`, the localization
`R_x[1/x]` of the model of `x` and the localization `R_{x⁻¹}[x]` of the model of `x⁻¹` are one
and the same subring, the holomorphy ring of the places at which `x` is a unit. -/
theorem coe_ofField_powers_integralClosure_adjoin_eq_coe_ofField_powers_inv
    (hF : IsFunctionField k F)
    [IsFractionRing (integralClosure (Algebra.adjoin k {x⁻¹}) F) F] :
    (ofField F (Submonoid.powers
      (⟨x, (integralClosure (Algebra.adjoin k {x}) F).algebraMap_mem
        ⟨x, Algebra.self_mem_adjoin_singleton k x⟩⟩ : integralClosure (Algebra.adjoin k {x}) F))
          hx : Set F) =
      (ofField F (Submonoid.powers
        (⟨x⁻¹, (integralClosure (Algebra.adjoin k {x⁻¹}) F).algebraMap_mem
          ⟨x⁻¹, Algebra.self_mem_adjoin_singleton k x⁻¹⟩⟩ :
            integralClosure (Algebra.adjoin k {x⁻¹}) F)) hx' : Set F) := by
  rw [coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing x hx hF,
    coe_ofField_powers_integralClosure_adjoin_eq_holomorphyRing x⁻¹ hx' hF, inv_inv,
    Set.inter_comm]

/-- **The two charts glue along their common localization, as rings**: the ring isomorphism
`R_x[1/x] ≃+* R_{x⁻¹}[x]` induced by
`TauCeti.coe_ofField_powers_integralClosure_adjoin_eq_coe_ofField_powers_inv`. It is the identity
of `F` restricted to the overlap ring, so it commutes with the two inclusions into `F`
(`TauCeti.coe_ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv_apply`). -/
noncomputable def ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv
    (hF : IsFunctionField k F)
    [IsFractionRing (integralClosure (Algebra.adjoin k {x⁻¹}) F) F] :
    ofField F (Submonoid.powers
      (⟨x, (integralClosure (Algebra.adjoin k {x}) F).algebraMap_mem
        ⟨x, Algebra.self_mem_adjoin_singleton k x⟩⟩ : integralClosure (Algebra.adjoin k {x}) F))
          hx ≃+*
      ofField F (Submonoid.powers
        (⟨x⁻¹, (integralClosure (Algebra.adjoin k {x⁻¹}) F).algebraMap_mem
          ⟨x⁻¹, Algebra.self_mem_adjoin_singleton k x⁻¹⟩⟩ :
            integralClosure (Algebra.adjoin k {x⁻¹}) F)) hx' :=
  Subalgebra.ringEquivOfSetEq _ _
    (coe_ofField_powers_integralClosure_adjoin_eq_coe_ofField_powers_inv x hx hx' hF)

@[simp]
theorem coe_ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv_apply
    (hF : IsFunctionField k F)
    [IsFractionRing (integralClosure (Algebra.adjoin k {x⁻¹}) F) F]
    (a : ofField F (Submonoid.powers
      (⟨x, (integralClosure (Algebra.adjoin k {x}) F).algebraMap_mem
        ⟨x, Algebra.self_mem_adjoin_singleton k x⟩⟩ : integralClosure (Algebra.adjoin k {x}) F))
          hx) :
    (ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv x hx hx' hF a : F) = a :=
  Subalgebra.coe_ringEquivOfSetEq_apply _ _ _ a

@[simp]
theorem coe_ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv_symm_apply
    (hF : IsFunctionField k F)
    [IsFractionRing (integralClosure (Algebra.adjoin k {x⁻¹}) F) F]
    (b : ofField F (Submonoid.powers
      (⟨x⁻¹, (integralClosure (Algebra.adjoin k {x⁻¹}) F).algebraMap_mem
        ⟨x⁻¹, Algebra.self_mem_adjoin_singleton k x⁻¹⟩⟩ :
          integralClosure (Algebra.adjoin k {x⁻¹}) F)) hx') :
    ((ofFieldPowersIntegralClosureAdjoinEquivOfFieldPowersInv x hx hx' hF).symm b : F) = b :=
  Subalgebra.coe_ringEquivOfSetEq_symm_apply _ _ _ b

end Gluing

/-! ### The two normalized valuations agree on the overlap -/

/-- **The two normalized valuations agree on the overlap**: at a place `P` at which `x` is a unit,
the height one prime of `R_x` below `P` and the height one prime of `R_{x⁻¹}` below `P` induce
one and the same valuation on `F`, namely the valuation of `P`
(`TauCeti.Place.valuation_center` on each chart). -/
theorem valuation_integralClosureAdjoinHeightOneSpectrumEquiv_eq_valuation_inv
    [IsDedekindDomain (integralClosure (Algebra.adjoin k {x}) F)]
    [IsDedekindDomain (integralClosure (Algebra.adjoin k {x⁻¹}) F)]
    [IsFractionRing (integralClosure (Algebra.adjoin k {x⁻¹}) F) F]
    {P : Place k F} (hx : x ∈ P.integers) (hx' : x⁻¹ ∈ P.integers) :
    (integralClosureAdjoinHeightOneSpectrumEquiv x ⟨P, hx⟩).valuation F =
      (integralClosureAdjoinHeightOneSpectrumEquiv x⁻¹ ⟨P, hx'⟩).valuation F := by
  rw [integralClosureAdjoinHeightOneSpectrumEquiv_apply,
    integralClosureAdjoinHeightOneSpectrumEquiv_apply, Place.valuation_center,
    Place.valuation_center]

end TauCeti
