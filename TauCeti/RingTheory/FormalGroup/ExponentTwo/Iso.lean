/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Basic
public import TauCeti.RingTheory.FormalGroup.Hom
public import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange
import TauCeti.RingTheory.PowerSeries.SubstInv

/-!
# The normalised strict isomorphism of a formal group law of exponent two

Let `F` be a commutative formal group law over a commutative ring `R` with `[2]_F = 0`. Its
normalised logarithm `g = FormalGroup.exponentTwoLog` is additive along `F` and has linear
coefficient one, so it has a compositional inverse, the normalised exponential
`f = FormalGroup.exponentTwoExp`, which satisfies `F(f(X), f(Y)) = f(X + Y)`. Together they form a
strict isomorphism `FormalGroup.exponentTwoLogIso` from `F` to the additive formal group law, with
`g` as forward and `f` as inverse homomorphism. This is the exponent-two counterpart of the
isomorphism `FormalGroup.logIso` over `ℚ`-algebras, which is not available here because `2 = 0`
in `R`. No field, reducedness or nontriviality hypothesis on `R` is used.

Unlike over a `ℚ`-algebra, `F` has many strict isomorphisms to the additive formal group law;
`FormalGroup.eq_exponentTwoLogIso_iff` singles out the normalised one as the strict isomorphism
whose forward series has no term of degree `2ᵏ`, `k ≥ 1`. Both series commute with every
coefficient-ring homomorphism, injective or not (`FormalGroup.map_exponentTwoLog`,
`FormalGroup.map_exponentTwoExp`), because the normalisation is preserved by base change.

The construction of `FormalGroup.exponentTwoExp` and `FormalGroup.exponentTwoLogIso` and the
characterisation `FormalGroup.eq_exponentTwoLogIso_iff` are adapted from Tau Ceti PR #21049
(https://github.com/TauCetiProject/TauCeti/pull/21049). The base-change proofs here are new.

## Main definitions

* `FormalGroup.exponentTwoExp`: the normalised exponential, the compositional inverse of
  `FormalGroup.exponentTwoLog`.
* `FormalGroup.exponentTwoLogIso`: the normalised strict isomorphism from `F` to the additive
  formal group law, with forward homomorphism `FormalGroup.exponentTwoLogHom` and inverse
  `FormalGroup.exponentTwoExpHom`.

## Main results

* `FormalGroup.subst_exponentTwoExp_toPowerSeries`: `F(f(X), f(Y)) = f(X + Y)`.
* `FormalGroup.eq_exponentTwoLogIso_iff`: an isomorphism from `F` to the additive formal group
  law is the normalised one exactly when it is strict and its forward series has no term of degree
  `2ᵏ`, `k ≥ 1`.
* `FormalGroup.map_exponentTwoLog` and `FormalGroup.map_exponentTwoExp`: the normalised logarithm
  and exponential commute with base change.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) [F.IsComm]
  (hF : F.nsmulSeries 2 = 0)

/-- **The normalised exponential** `f` of a commutative formal group law `F` with `[2]_F = 0`:
the compositional inverse of the normalised logarithm `FormalGroup.exponentTwoLog`, which exists
since that logarithm is `X + ⋯`. -/
noncomputable def exponentTwoExp : PowerSeries R :=
  (F.exponentTwoLog hF).substInvOfIsUnit (by simp)

/-- The normalised exponential has no constant term. -/
@[simp]
theorem constantCoeff_exponentTwoExp : PowerSeries.constantCoeff (F.exponentTwoExp hF) = 0 := by
  simp [exponentTwoExp]

/-- The normalised exponential has linear coefficient `1`. -/
@[simp]
theorem coeff_one_exponentTwoExp : PowerSeries.coeff 1 (F.exponentTwoExp hF) = 1 := by
  simp [exponentTwoExp]

/-- `g(f(X)) = X`. -/
@[simp]
theorem subst_exponentTwoExp_exponentTwoLog :
    PowerSeries.subst (F.exponentTwoExp hF) (F.exponentTwoLog hF) = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right _ (F.constantCoeff_exponentTwoLog hF) _

/-- `f(g(X)) = X`. -/
@[simp]
theorem subst_exponentTwoLog_exponentTwoExp :
    PowerSeries.subst (F.exponentTwoLog hF) (F.exponentTwoExp hF) = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left _ (F.constantCoeff_exponentTwoLog hF) _

/-- The normalised logarithm, bundled as a homomorphism to the additive formal group law. -/
noncomputable def exponentTwoLogHom : TauCeti.FormalGroupHom F (𝔾ₐ (R := R)) where
  toPowerSeries := F.exponentTwoLog hF
  zero_constantCoeff := F.constantCoeff_exponentTwoLog hF
  hom := (TauCeti.FormalGroupHom.hom_additive_iff (F.constantCoeff_exponentTwoLog hF)).mpr
    (F.subst_toPowerSeries_exponentTwoLog hF)

@[simp]
theorem exponentTwoLogHom_toPowerSeries :
    (F.exponentTwoLogHom hF).toPowerSeries = F.exponentTwoLog hF := (rfl)

/-- The normalised exponential, bundled as a homomorphism from the additive formal group law. -/
noncomputable def exponentTwoExpHom : TauCeti.FormalGroupHom (𝔾ₐ (R := R)) F :=
  (F.exponentTwoLogHom hF).ofInverse (F.exponentTwoExp hF) (F.constantCoeff_exponentTwoExp hF)
    (F.subst_exponentTwoExp_exponentTwoLog hF) (F.subst_exponentTwoLog_exponentTwoExp hF)

@[simp]
theorem exponentTwoExpHom_toPowerSeries :
    (F.exponentTwoExpHom hF).toPowerSeries = F.exponentTwoExp hF :=
  TauCeti.FormalGroupHom.ofInverse_toPowerSeries _ _ _ _ _

/-- **The normalised exponential carries addition to `F`**: `F(f(X), f(Y)) = f(X + Y)`. -/
theorem subst_exponentTwoExp_toPowerSeries :
    subst (fun i ↦ (F.exponentTwoExp hF).toMvPowerSeries i) F.toPowerSeries =
      PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) R) (F.exponentTwoExp hF) := by
  simpa only [exponentTwoExpHom_toPowerSeries, 𝔾ₐ_toPowerSeries] using
    (F.exponentTwoExpHom hF).hom.symm

/-- **The normalised strict isomorphism** from a commutative formal group law `F` with
`[2]_F = 0` to the additive formal group law: the normalised logarithm, with the normalised
exponential as its inverse. -/
noncomputable def exponentTwoLogIso : TauCeti.FormalGroupIso F (𝔾ₐ (R := R)) :=
  .ofSubstEqX (F.exponentTwoLogHom hF) (F.exponentTwoExpHom hF) (by simp) (by simp)

@[simp]
theorem exponentTwoLogIso_toHom : (F.exponentTwoLogIso hF).toHom = F.exponentTwoLogHom hF :=
  TauCeti.FormalGroupIso.ofSubstEqX_toHom _ _ _ _

@[simp]
theorem exponentTwoLogIso_invHom : (F.exponentTwoLogIso hF).invHom = F.exponentTwoExpHom hF :=
  TauCeti.FormalGroupIso.ofSubstEqX_invHom _ _ _ _

instance : (F.exponentTwoLogIso hF).IsStrict where
  coeff_one := by simp

/-- **Characterisation of the normalised strict isomorphism.** An isomorphism from `F` to the
additive formal group law is `FormalGroup.exponentTwoLogIso` exactly when it is strict and its
forward series has no term of degree `2ᵏ` for `k ≥ 1`. -/
theorem eq_exponentTwoLogIso_iff (f : TauCeti.FormalGroupIso F (𝔾ₐ (R := R))) :
    f = F.exponentTwoLogIso hF ↔
      f.IsStrict ∧ ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) f.toHom.toPowerSeries = 0 := by
  constructor
  · rintro rfl
    exact ⟨inferInstance, fun _ hk ↦ by simp [F.coeff_two_pow_exponentTwoLog hF hk]⟩
  · rintro ⟨hf, hp⟩
    refine TauCeti.FormalGroupIso.ext (TauCeti.FormalGroupHom.ext ?_)
    simpa only [exponentTwoLogIso_toHom, exponentTwoLogHom_toPowerSeries] using
      F.eq_exponentTwoLog hF f.toHom.zero_constantCoeff hf.coeff_one hp
        ((TauCeti.FormalGroupHom.hom_additive_iff f.toHom.zero_constantCoeff).mp f.toHom.hom)

/-- **The normalised logarithm commutes with base change**: applying a ring homomorphism
`f : R →+* S` to the coefficients of the normalised logarithm of `F` gives the normalised logarithm
of `F.map f`. -/
@[simp]
theorem map_exponentTwoLog (f : R →+* S) :
    (F.exponentTwoLog hF).map f =
      (F.map f).exponentTwoLog (by rw [← F.map_nsmulSeries, hF, map_zero]) := by
  refine (F.map f).eq_exponentTwoLog _ ?_ (by simp) (fun k hk ↦ ?_)
    (F.subst_map_toPowerSeries_map f (F.subst_toPowerSeries_exponentTwoLog hF))
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, F.constantCoeff_exponentTwoLog hF, map_zero]
  · rw [PowerSeries.coeff_map, F.coeff_two_pow_exponentTwoLog hF hk, map_zero]

/-- **The normalised exponential commutes with base change**: applying a ring homomorphism
`f : R →+* S` to the coefficients of the normalised exponential of `F` gives the normalised
exponential of `F.map f`. -/
@[simp]
theorem map_exponentTwoExp (f : R →+* S) :
    (F.exponentTwoExp hF).map f =
      (F.map f).exponentTwoExp (by rw [← F.map_nsmulSeries, hF, map_zero]) := by
  rw [exponentTwoExp, PowerSeries.map_substInvOfIsUnit f (F.constantCoeff_exponentTwoLog hF),
    exponentTwoExp]
  congr 1
  exact F.map_exponentTwoLog hF f

end FormalGroup
