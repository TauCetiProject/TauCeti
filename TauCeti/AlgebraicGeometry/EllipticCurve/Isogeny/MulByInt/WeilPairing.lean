/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.KummerCharacter
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.DivisorPullback
-- Proof-only: `n(T) - n(O)` and the line function are principal.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.TorsionDivisor
-- Proof-only: `F` is integrally closed in `F(W)`, so functions with equal divisors differ by a
-- constant.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
-- Proof-only: the functions fixed by the `N`-torsion translations are the pullbacks along `[N]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Galois

/-!
# The Weil pairing

Let `W` be an elliptic curve over a separably closed field `F` and `N` a positive integer
invertible in `F`. For `T ∈ E[N]` the divisor `[N]^* (T) - [N]^* (O)` is principal
(`TauCeti.Isogeny.exists_principal_eq_weilPairingDivisor`); let `g_T` be a function
with that divisor. Its `N`-th power has divisor `[N]^* (N (T) - N (O))`, the pullback of a principal
divisor, so `g_T ^ N` is itself a pullback along `[N]`. The translations by the `N`-torsion fix
every pullback, so they move `g_T` by `N`-th roots of unity, and these are constants: the Kummer
character of `g_T` (`TauCeti.Isogeny.kummerCharacter`). The **Weil pairing** is

    e_N(S, T) = τ_S g_T / g_T,

independent of the choice of `g_T`, since two choices differ by a constant. It is additive in `S`
because the Kummer character is a homomorphism, and additive in `T` because `g_{T₁} g_{T₂} h`,
with `h` the line function of `T₁` and `T₂`, is a choice of `g_{T₁ + T₂}` and `[N]^* h` is a
pullback. It is nondegenerate in `T`: if `e_N(·, T)` is trivial then `g_T` is fixed by the
`N`-torsion translations, hence a pullback `[N]^* h`, and `div h = (T) - (O)` forces `T = O`.

This is the construction of Silverman III.8.1. It is a divisor construction, and its inputs are
the divisor calculus of the function field and the fibre of `[N]`; it does not use Weil
reciprocity, which the alternative construction through evaluation of functions on divisors
requires.

## Main definitions

* `TauCeti.Isogeny.weilPairing`: the pairing `E[N] →+ E[N] →+ μ_N`, additive in both variables.

## Main results

* `TauCeti.Isogeny.algebraMap_weilPairing`: `e_N(S, T) = τ_S g / g` for every `g` with divisor
  `[N]^* (T) - [N]^* (O)`.
* `TauCeti.Isogeny.eq_zero_of_forall_weilPairing_eq_zero`: the pairing is nondegenerate in its
  second variable.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain

namespace TauCeti.Isogeny

open AlgebraicGeometry

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- The coordinate ring of an elliptic curve is a Dedekind domain. -/
local instance : IsDedekindDomain W.toAffine.CoordinateRing :=
  have := WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing W.toAffine
  W.toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

attribute [local instance] isIntegrallyClosedIn_functionField

/-- **A function with divisor `[n]^* (T) - [n]^* (O)` has its `n`-th power pulled back along
`[n]`**, at an `n`-torsion point `T`: that power has divisor `[n]^* (n (T) - n (O))`, the pullback
of a principal divisor. -/
theorem zpow_mem_fieldRange_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    {T : W.toAffine.Point} (hT : n • T = 0) {g : W.toAffine.FunctionFieldˣ}
    (hg : Divisor.principal W.toAffine.isFunctionField g = weilPairingDivisor W hn T) :
    (g : W.toAffine.FunctionField) ^ n ∈
      (mulByIntIsogeny W (hn)).fieldPullback.fieldRange := by
  let _ := (mulByIntIsogeny W (hn)).fieldPullback.toAlgebra
  obtain ⟨f, hf⟩ := W.toAffine.exists_principal_eq_zsmul_ofPoint_sub_infinity hT
  have hdiv : Divisor.principal W.toAffine.isFunctionField (g ^ n) =
      Divisor.principal W.toAffine.isFunctionField
        (Units.map (algebraMap W.toAffine.FunctionField W.toAffine.FunctionField : _ →* _) f) := by
    rw [← divisorPullback_principal _ (fun _ ↦ rfl), hf, map_zsmul, map_sub,
      ← weilPairingDivisor_def W hn T, ← hg, Divisor.principal_zpow]
  obtain ⟨c, hc⟩ := Divisor.exists_units_algebraMap_mul_of_principal_eq _
    (isIntegrallyClosedIn_functionField W.toAffine) hdiv
  rw [← Units.val_zpow_eq_zpow_val, hc]
  exact mul_mem (IntermediateField.algebraMap_mem _ _) ⟨f, rfl⟩

section Pairing

variable [IsSepClosed F] (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0)

-- The invertibility of `N` in the form the `[n]` API takes it, `n` being an integer there.
omit [DecidableEq F] [IsSepClosed F] [NeZero N] in
include hN in
private theorem intCast_natCast_ne_zero : ((N : ℤ) : F) ≠ 0 := by
  rwa [Int.cast_natCast]

omit [DecidableEq F] [W.IsElliptic] [IsSepClosed F] [NeZero N] in
include hN in
private theorem psiFunctionField_natCast_ne_zero : psiFunctionField W (N : ℤ) ≠ 0 :=
  psiFunctionField_ne_zero W (intCast_natCast_ne_zero N hN)

-- `E[N]` inside `ker [N]`, through the identification of the points of `W` and of `W⁄F`.
private noncomputable def torsionToKer :
    Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ) →+
      (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).ker :=
  AddMonoidHom.codRestrict (((Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom).comp
    (Submodule.subtype _).toAddMonoidHom) _ fun S ↦ by
      rw [mem_ker_mulByIntIsogeny_iff]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
        LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]
      rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp S.2, map_zero]

omit [NeZero N] in
-- A function `g_T` with divisor `[N]^* (T) - [N]^* (O)`, the stable term that `weilPairingAux`
-- chooses from.
private theorem exists_principal_eq_weilPairingDivisor_torsion
    (T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)) :
    ∃ g : W.toAffine.FunctionFieldˣ, Divisor.principal W.toAffine.isFunctionField g =
      weilPairingDivisor W (psiFunctionField_natCast_ne_zero W N hN) T :=
  exists_principal_eq_weilPairingDivisor W (intCast_natCast_ne_zero N hN)
    ((Submodule.mem_torsionBy_iff _ _).mp T.2)

omit [IsSepClosed F] [NeZero N] in
-- The `N`-th power of `g_T` is a pullback along `[N]`.
private theorem pow_mem_fieldRange_of_principal_eq
    {T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)} {g : W.toAffine.FunctionFieldˣ}
    (hg : Divisor.principal W.toAffine.isFunctionField g =
      weilPairingDivisor W (psiFunctionField_natCast_ne_zero W N hN) T) :
    (g : W.toAffine.FunctionField) ^ N ∈
      (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).fieldPullback.fieldRange := by
  have := zpow_mem_fieldRange_mulByIntIsogeny W _
    ((Submodule.mem_torsionBy_iff _ _).mp T.2) hg
  rwa [zpow_natCast] at this

-- `S ↦ e_N(S, T)`, through a chosen function `g_T`.
private noncomputable def weilPairingAux (T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)) :
    Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ) →+ Additive (rootsOfUnity N F) :=
  MonoidHom.toAdditiveRight
    (((mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).kummerCharacter N
    (exists_principal_eq_weilPairingDivisor_torsion W N hN T).choose
    (pow_mem_fieldRange_of_principal_eq W N hN
      (exists_principal_eq_weilPairingDivisor_torsion W N hN T).choose_spec)).comp
      (AddMonoidHom.toMultiplicative (torsionToKer W N hN)))

-- The choice of `g_T` does not matter.
private theorem weilPairingAux_eq {T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)}
    {g : W.toAffine.FunctionFieldˣ}
    (hg : Divisor.principal W.toAffine.isFunctionField g =
      weilPairingDivisor W (psiFunctionField_natCast_ne_zero W N hN) T) :
    weilPairingAux W N hN T = MonoidHom.toAdditiveRight
      (((mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).kummerCharacter N g
      (pow_mem_fieldRange_of_principal_eq W N hN hg)).comp
        (AddMonoidHom.toMultiplicative (torsionToKer W N hN))) := by
  rw [weilPairingAux, kummerCharacter_eq_of_principal_eq _ _
    ((exists_principal_eq_weilPairingDivisor_torsion W N hN T).choose_spec.trans hg.symm)]

-- Additivity in `T`: `g_{T₁} g_{T₂} [N]^* h` is a choice of `g_{T₁ + T₂}`, for `h` the line
-- function of `T₁` and `T₂`, and the Kummer character of `[N]^* h` is trivial.
private theorem weilPairingAux_add (T₁ T₂ : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)) :
    weilPairingAux W N hN (T₁ + T₂) = weilPairingAux W N hN T₁ + weilPairingAux W N hN T₂ := by
  let _ := (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).fieldPullback.toAlgebra
  obtain ⟨h, hh⟩ := W.toAffine.exists_principal_eq_ofPoint_add_sub (T₁ : W.toAffine.Point) T₂
  have hg₁ := (exists_principal_eq_weilPairingDivisor_torsion W N hN T₁).choose_spec
  have hg₂ := (exists_principal_eq_weilPairingDivisor_torsion W N hN T₂).choose_spec
  set g₁ := (exists_principal_eq_weilPairingDivisor_torsion W N hN T₁).choose
  set g₂ := (exists_principal_eq_weilPairingDivisor_torsion W N hN T₂).choose
  let h' := Units.map (algebraMap W.toAffine.FunctionField W.toAffine.FunctionField :
    W.toAffine.FunctionField →* W.toAffine.FunctionField) h
  have hh' : Divisor.principal W.toAffine.isFunctionField h' =
      (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).divisorPullback (fun _ ↦ rfl)
        (Divisor.principal W.toAffine.isFunctionField h) :=
    (divisorPullback_principal _ (fun _ ↦ rfl) h).symm
  have hprod : Divisor.principal W.toAffine.isFunctionField (g₁ * g₂ * h') =
      weilPairingDivisor W (psiFunctionField_natCast_ne_zero W N hN) (T₁ + T₂ :) := by
    rw [Divisor.principal_mul, Divisor.principal_mul, hg₁, hg₂, hh', hh, weilPairingDivisor_def,
      weilPairingDivisor_def, weilPairingDivisor_def]
    simp only [map_sub, Submodule.coe_add]
    abel
  have hp₁ := pow_mem_fieldRange_of_principal_eq W N hN hg₁
  have hp₂ := pow_mem_fieldRange_of_principal_eq W N hN hg₂
  have hmem : (h' : W.toAffine.FunctionField) ∈
      (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).fieldPullback.fieldRange :=
    ⟨h, rfl⟩
  have hp₁₂ : ((g₁ * g₂ : W.toAffine.FunctionFieldˣ) : W.toAffine.FunctionField) ^ N ∈
      (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).fieldPullback.fieldRange := by
    rw [Units.val_mul, mul_pow]
    exact mul_mem hp₁ hp₂
  rw [weilPairingAux_eq W N hN hprod, weilPairingAux, weilPairingAux,
    kummerCharacter_mul hp₁₂ (pow_mem hmem N) _, kummerCharacter_mul hp₁ hp₂ _,
    kummerCharacter_eq_one_of_mem_fieldRange _ hmem, mul_one, MonoidHom.mul_comp]
  exact AddMonoidHom.ext fun _ ↦ ofMul_mul _ _

/-- **The Weil pairing** `e_N(S, T) = τ_S g_T / g_T` (Silverman III.8.1), over a separably closed
field in which `N` is invertible, additive in both variables. -/
noncomputable def weilPairing :
    Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ) →+
      Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ) →+ Additive (rootsOfUnity N F) :=
  (AddMonoidHom.mk' (weilPairingAux W N hN) (weilPairingAux_add W N hN)).flip

/-- **The value of the Weil pairing**: `e_N(S, T) = τ_S g / g` for every function `g` with divisor
`[N]^* (T) - [N]^* (O)`. -/
theorem algebraMap_weilPairing {S T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)}
    {g : W.toAffine.FunctionFieldˣ} {hψ : psiFunctionField W N ≠ 0}
    (hg : Divisor.principal W.toAffine.isFunctionField g = weilPairingDivisor W hψ T) :
    algebraMap F W.toAffine.FunctionField ((weilPairing W N hN S T).toMul : Fˣ) =
      translation W.toAffine (Point.equivBaseChangeSelf W.toAffine S) g / g := by
  rw [weilPairing, AddMonoidHom.flip_apply, AddMonoidHom.mk'_apply, weilPairingAux_eq W N hN hg]
  exact algebraMap_kummerCharacter (pow_mem_fieldRange_of_principal_eq W N hN hg)
    (Multiplicative.ofAdd (torsionToKer W N hN S))

-- If `e_N(·, T)` is trivial, every `N`-torsion translation fixes each choice of `g_T`.
private theorem translation_eq_of_forall_weilPairing_eq_zero
    {T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)} (hT : ∀ S, weilPairing W N hN S T = 0)
    {g : W.toAffine.FunctionFieldˣ}
    (hg : Divisor.principal W.toAffine.isFunctionField g =
      weilPairingDivisor W (psiFunctionField_natCast_ne_zero W N hN) T)
    {P : (W.toAffine⁄F).toAffine.Point} (hP : (N : ℤ) • P = 0) :
    translation W.toAffine P g = g := by
  let S : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ) :=
    ⟨(Point.equivBaseChangeSelf W.toAffine).symm P, (Submodule.mem_torsionBy_iff _ _).mpr
      (by rw [← map_zsmul, hP, map_zero])⟩
  have h1 := algebraMap_weilPairing W N hN (S := S) hg
  rw [hT S, AddEquiv.apply_symm_apply] at h1
  simp only [toMul_zero, OneMemClass.coe_one, Units.val_one, map_one] at h1
  exact (div_eq_one_iff_eq g.ne_zero).mp h1.symm

/-- **The Weil pairing is nondegenerate in its second variable**: if `e_N(S, T) = 1` for every
`S`, then `T = O`. -/
theorem eq_zero_of_forall_weilPairing_eq_zero
    {T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)} (hT : ∀ S, weilPairing W N hN S T = 0) :
    T = 0 := by
  let _ := (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)).fieldPullback.toAlgebra
  obtain ⟨g, hg⟩ := exists_principal_eq_weilPairingDivisor_torsion W N hN T
  -- `g` is fixed by the `N`-torsion translations, hence a pullback `[N]^* h`
  obtain ⟨h, hh⟩ := AlgHom.mem_fieldRange.mp
    ((mem_fieldRange_mulByIntIsogeny_iff W.toAffine (intCast_natCast_ne_zero N hN)).mpr
      fun _ ↦ translation_eq_of_forall_weilPairing_eq_zero W N hN hT hg)
  have h0 : h ≠ 0 := by
    rintro rfl
    exact g.ne_zero (by rw [← hh, map_zero])
  -- `div g` is the pullback of `div h`, so `div h = (T) - (O)`
  have hdiv : Divisor.principal W.toAffine.isFunctionField (Units.mk0 h h0) =
      WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine T).1 -
        WeilDivisor.ofPoint (Place.infinity W.toAffine) := by
    refine divisorPullback_injective
      (mulByIntIsogeny W (psiFunctionField_natCast_ne_zero W N hN)) (fun _ ↦ rfl) ?_
    rw [divisorPullback_principal, map_sub, ← weilPairingDivisor_def W _ T, ← hg]
    congr 1
    exact Units.ext hh
  have hσ := W.toAffine.divisorSum_eq_zero_iff
    (D := ⟨_, W.toAffine.ofPoint_sub_ofPoint_mem_ker_degree T 0⟩)
  rw [divisorSum_ofPoint_sub_ofPoint, sub_zero] at hσ
  refine Subtype.ext (hσ.mpr ⟨Units.mk0 h h0, ?_⟩)
  rw [hdiv]
  exact congrArg (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine T).1 -
    WeilDivisor.ofPoint ·) (coe_pointEquivDegreeOnePlace_zero _).symm

end Pairing

end TauCeti.Isogeny

end
