/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.ExponentTwo
public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange

/-!
# The universal ring of formal group laws of exponent two

A commutative formal group law `F` over a commutative ring `R` with `[2]_F = 0` has a unique
normalised logarithm (`FormalGroup.exponentTwoLog`): the power series

  `g(X) = X + ∑ aₙ Xⁿ`, with `aₙ` running over the degrees `n ≥ 2` that are not powers of two,

such that `g(F(X, Y)) = g(X) + g(Y)`. Conversely, if `2 = 0` in `R`, every family `(aₙ)` of
coefficients in these degrees comes from a unique such formal group law, namely

  `F(X, Y) = g⁻¹(g(X) + g(Y))`,

the transport of the additive formal group law along the strict coordinate `g⁻¹`
(`FormalGroup.changeCoordinate`). So commutative formal group laws of exponent two over `R`
correspond bijectively to families of elements of `R` indexed by the degrees `n ≥ 2` that are not
powers of two, and the bijection is natural in `R`.

Consequently the polynomial ring

  `𝔽₂[aₙ | n ≥ 2, n not a power of two]`

carries a universal commutative formal group law of exponent two: ring homomorphisms from it to `R`
correspond to commutative formal group laws over `R` with `[2]_F = 0`, by base change of the
universal law. This is Quillen's description of the coefficient ring of the universal formal group
law of exponent two, which he identified with the unoriented bordism ring `MO_*`. Giving `aₙ` the
homological degree `n - 1`, the polynomial generators lie in the degrees other than `2ᵏ - 1`.

## Main definitions

* `TauCeti.exponentTwoLogDegrees`: the degrees `n ≥ 2` that are not powers of two.
* `TauCeti.FormalCoordinate.ofExponentTwoCoeffs a`: the strict coordinate `X + ∑ aₙ Xⁿ`.
* `TauCeti.exponentTwoFormalGroup a`: the formal group law `g⁻¹(g(X) + g(Y))` for
  `g = X + ∑ aₙ Xⁿ`.
* `TauCeti.exponentTwoFormalGroupEquiv`: if `2 = 0` in `R`, the bijection between coefficient
  families and commutative formal group laws over `R` of exponent two.
* `TauCeti.ExponentTwoLazardRing`: the polynomial ring `𝔽₂[aₙ]`, with its universal formal group
  law `TauCeti.ExponentTwoLazardRing.formalGroup` and the classifying bijection
  `TauCeti.ExponentTwoLazardRing.lift`.

## Main results

* `TauCeti.exponentTwoLog_exponentTwoFormalGroup`: the normalised logarithm of
  `g⁻¹(g(X) + g(Y))` is `g`.
* `TauCeti.exponentTwoFormalGroup_coeff_exponentTwoLog`: every commutative formal group law of
  exponent two is `g⁻¹(g(X) + g(Y))` for its normalised logarithm `g`.
* `TauCeti.map_exponentTwoFormalGroup`: the construction commutes with base change.
* `TauCeti.ExponentTwoLazardRing.lift_map`: the universal property is natural in the coefficient
  ring.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open MvPowerSeries

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The degrees `n ≥ 2` that are not powers of two: the degrees in which the coefficients of the
normalised logarithm of a formal group law of exponent two are free. -/
def exponentTwoLogDegrees : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ k, n ≠ 2 ^ k}

@[simp]
theorem mem_exponentTwoLogDegrees {n : ℕ} :
    n ∈ exponentTwoLogDegrees ↔ n ≠ 0 ∧ ∀ k, n ≠ 2 ^ k :=
  Iff.rfl

namespace FormalCoordinate

/-- The strict formal coordinate `X + ∑ aₙ Xⁿ`, the sum over the degrees `n ≥ 2` that are not
powers of two. These are the normalised logarithms of formal group laws of exponent two. -/
def ofExponentTwoCoeffs (a : exponentTwoLogDegrees → R) : FormalCoordinate R where
  toPowerSeries := PowerSeries.mk (Function.extend Subtype.val a (Pi.single 1 1))
  constantCoeff_toPowerSeries := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      Function.extend_apply' _ _ _ fun ⟨n, hn⟩ ↦ n.2.1 hn]
    simp
  isUnit_coeff_one := by
    rw [PowerSeries.coeff_mk, Function.extend_apply' _ _ _ fun ⟨n, hn⟩ ↦ n.2.2 0 hn]
    simp

/-- The coefficient of `Xⁿ` in `X + ∑ aₙ Xⁿ` is `aₙ`, for `n ≥ 2` not a power of two. -/
@[simp]
theorem coeff_ofExponentTwoCoeffs (a : exponentTwoLogDegrees → R) (n : exponentTwoLogDegrees) :
    PowerSeries.coeff (n : ℕ) (ofExponentTwoCoeffs a).toPowerSeries = a n := by
  rw [ofExponentTwoCoeffs, PowerSeries.coeff_mk, Subtype.val_injective.extend_apply]

/-- The coefficient of `X` in `X + ∑ aₙ Xⁿ` is `1`. -/
@[simp]
theorem coeff_one_ofExponentTwoCoeffs (a : exponentTwoLogDegrees → R) :
    PowerSeries.coeff 1 (ofExponentTwoCoeffs a).toPowerSeries = 1 := by
  rw [ofExponentTwoCoeffs, PowerSeries.coeff_mk,
    Function.extend_apply' _ _ _ fun ⟨n, hn⟩ ↦ n.2.2 0 hn]
  simp

/-- `X + ∑ aₙ Xⁿ` has no term of degree `2ᵏ` for `k ≥ 1`. -/
theorem coeff_two_pow_ofExponentTwoCoeffs (a : exponentTwoLogDegrees → R) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff (2 ^ k) (ofExponentTwoCoeffs a).toPowerSeries = 0 := by
  rw [ofExponentTwoCoeffs, PowerSeries.coeff_mk,
    Function.extend_apply' _ _ _ fun ⟨n, hn⟩ ↦ n.2.2 k hn,
    Pi.single_eq_of_ne (Nat.one_lt_two_pow hk.ne').ne']

/-- A power series `g = X + ⋯` without terms of degree `2ᵏ`, `k ≥ 1`, is the coordinate
`X + ∑ aₙ Xⁿ` of its own coefficients `aₙ`. -/
theorem toPowerSeries_ofExponentTwoCoeffs_coeff {g : PowerSeries R}
    (h₀ : PowerSeries.constantCoeff g = 0) (h₁ : PowerSeries.coeff 1 g = 1)
    (hp : ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) g = 0) :
    (ofExponentTwoCoeffs fun n : exponentTwoLogDegrees ↦ PowerSeries.coeff n g).toPowerSeries =
      g := by
  ext n
  by_cases hn : n ∈ exponentTwoLogDegrees
  · exact coeff_ofExponentTwoCoeffs _ ⟨n, hn⟩
  · simp only [mem_exponentTwoLogDegrees, not_and_or, not_not, not_forall] at hn
    rcases hn with rfl | ⟨k, rfl⟩
    · simp [h₀]
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [h₁]
      · rw [coeff_two_pow_ofExponentTwoCoeffs _ hk, hp k hk]

/-- Base change of `X + ∑ aₙ Xⁿ` along `f` is `X + ∑ f(aₙ) Xⁿ`. -/
@[simp]
theorem map_ofExponentTwoCoeffs (f : R →+* S) (a : exponentTwoLogDegrees → R) :
    map f (ofExponentTwoCoeffs a) = ofExponentTwoCoeffs (f ∘ a) := by
  refine FormalCoordinate.ext ?_
  rw [toPowerSeries_map,
    ← toPowerSeries_ofExponentTwoCoeffs_coeff
      (g := PowerSeries.map f (ofExponentTwoCoeffs a).toPowerSeries)
    (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]; simp)
    (by simp) fun k hk ↦ by simp [coeff_two_pow_ofExponentTwoCoeffs _ hk]]
  congr 2
  funext n
  simp

end FormalCoordinate

/-- The formal group law `g⁻¹(g(X) + g(Y))` with normalised logarithm `g = X + ∑ aₙ Xⁿ`, the sum
over the degrees `n ≥ 2` that are not powers of two: the transport of the additive formal group law
along the coordinate `g⁻¹`. -/
def exponentTwoFormalGroup (a : exponentTwoLogDegrees → R) : FormalGroup R :=
  (FormalCoordinate.ofExponentTwoCoeffs a)⁻¹ • FormalGroup.𝔾ₐ

instance (a : exponentTwoLogDegrees → R) : (exponentTwoFormalGroup a).IsComm :=
  FormalGroup.instIsCommSMul _ _

/-- The coordinate `g = X + ∑ aₙ Xⁿ` is additive along `g⁻¹(g(X) + g(Y))`:
`g(F(X, Y)) = g(X) + g(Y)`. -/
theorem subst_toPowerSeries_exponentTwoFormalGroup (a : exponentTwoLogDegrees → R) :
    PowerSeries.subst (exponentTwoFormalGroup a).toPowerSeries
        (FormalCoordinate.ofExponentTwoCoeffs a).toPowerSeries =
      PowerSeries.subst (X 0) (FormalCoordinate.ofExponentTwoCoeffs a).toPowerSeries +
        PowerSeries.subst (X 1) (FormalCoordinate.ofExponentTwoCoeffs a).toPowerSeries := by
  set φ := FormalCoordinate.ofExponentTwoCoeffs a
  have hφ (i : Fin 2) := φ.hasSubst_subst (PowerSeries.HasSubst.X (S := R) i)
  have hxy := hasSubst_finTwo (hφ 0) (hφ 1)
  rw [FormalGroup.subst_toPowerSeries_eq_subst_smul_toPowerSeries, exponentTwoFormalGroup,
    smul_smul, mul_inv_cancel, one_smul, FormalGroup.𝔾ₐ_toPowerSeries, subst_add hxy, subst_X hxy,
    subst_X hxy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- If `2 = 0` in `R`, the formal group law `g⁻¹(g(X) + g(Y))` has exponent two:
`[2]_F(X) = g⁻¹(2 g(X)) = 0`. -/
theorem nsmulSeries_two_exponentTwoFormalGroup (h2 : (2 : R) = 0)
    (a : exponentTwoLogDegrees → R) : (exponentTwoFormalGroup a).nsmulSeries 2 = 0 := by
  set φ := FormalCoordinate.ofExponentTwoCoeffs a
  have hX := PowerSeries.HasSubst.X' (R := R)
  have hφ := φ.hasSubst_subst hX
  have hxy := hasSubst_finTwo hφ hφ
  have h : PowerSeries.subst (PowerSeries.X : PowerSeries R) φ.toPowerSeries +
      PowerSeries.subst (PowerSeries.X : PowerSeries R) φ.toPowerSeries = 0 := by
    rw [← two_smul R, h2, zero_smul]
  rw [FormalGroup.nsmulSeries_succ, FormalGroup.nsmulSeries_one, exponentTwoFormalGroup,
    FormalGroup.subst_smul_toPowerSeries _ _ hX hX, inv_inv, FormalGroup.𝔾ₐ_toPowerSeries,
    subst_add hxy, subst_X hxy, subst_X hxy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h, PowerSeries.subst_zero_of_constantCoeff_zero φ⁻¹.constantCoeff_toPowerSeries]

/-- The normalised logarithm of `g⁻¹(g(X) + g(Y))` is `g`. -/
theorem exponentTwoLog_exponentTwoFormalGroup (a : exponentTwoLogDegrees → R)
    (hF : (exponentTwoFormalGroup a).nsmulSeries 2 = 0) :
    (exponentTwoFormalGroup a).exponentTwoLog hF =
      (FormalCoordinate.ofExponentTwoCoeffs a).toPowerSeries :=
  ((exponentTwoFormalGroup a).eq_exponentTwoLog hF (by simp) (by simp)
    (fun _ hk ↦ FormalCoordinate.coeff_two_pow_ofExponentTwoCoeffs a hk)
    (subst_toPowerSeries_exponentTwoFormalGroup a)).symm

/-- The coefficient of `Xⁿ` in the normalised logarithm of `g⁻¹(g(X) + g(Y))` is `aₙ`. -/
@[simp]
theorem coeff_exponentTwoLog_exponentTwoFormalGroup (a : exponentTwoLogDegrees → R)
    (hF : (exponentTwoFormalGroup a).nsmulSeries 2 = 0) (n : exponentTwoLogDegrees) :
    PowerSeries.coeff (n : ℕ) ((exponentTwoFormalGroup a).exponentTwoLog hF) = a n := by
  rw [exponentTwoLog_exponentTwoFormalGroup, FormalCoordinate.coeff_ofExponentTwoCoeffs]

/-- **A formal group law of exponent two is determined by its logarithm**: a commutative formal
group law `F` with `[2]_F = 0` is `g⁻¹(g(X) + g(Y))` for its normalised logarithm `g`. -/
theorem exponentTwoFormalGroup_coeff_exponentTwoLog (F : FormalGroup R) [F.IsComm]
    (hF : F.nsmulSeries 2 = 0) :
    exponentTwoFormalGroup (fun n : exponentTwoLogDegrees ↦
      PowerSeries.coeff n (F.exponentTwoLog hF)) = F := by
  set φ := FormalCoordinate.ofExponentTwoCoeffs fun n : exponentTwoLogDegrees ↦
    PowerSeries.coeff n (F.exponentTwoLog hF)
  have hg : φ.toPowerSeries = F.exponentTwoLog hF :=
    FormalCoordinate.toPowerSeries_ofExponentTwoCoeffs_coeff (by simp) (by simp)
      fun _ hk ↦ F.coeff_two_pow_exponentTwoLog hF hk
  -- `φ • F = φ(F(φ⁻¹(X), φ⁻¹(Y))) = φ(φ⁻¹(X)) + φ(φ⁻¹(Y))` is the additive formal group law
  have hadd : φ • F = FormalGroup.𝔾ₐ := by
    have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
    have hφ (i : Fin 2) := φ⁻¹.hasSubst_subst (hX i)
    refine FormalGroup.ext ?_
    rw [FormalGroup.smul_toPowerSeries, hg, F.subst_subst_toPowerSeries_exponentTwoLog hF (hφ 0)
      (hφ 1), ← hg, φ.subst_subst_inv (hX 0), φ.subst_subst_inv (hX 1),
      FormalGroup.𝔾ₐ_toPowerSeries]
  rw [exponentTwoFormalGroup, ← hadd, inv_smul_smul]

/-- **Formal group laws of exponent two are classified by their logarithms.** If `2 = 0` in `R`,
families `(aₙ)` of elements of `R` indexed by the degrees `n ≥ 2` that are not powers of two
correspond to commutative formal group laws `F` over `R` with `[2]_F = 0`: the family `a` gives
`g⁻¹(g(X) + g(Y))` for `g = X + ∑ aₙ Xⁿ`, and `F` gives the coefficients of its normalised
logarithm. -/
def exponentTwoFormalGroupEquiv (h2 : (2 : R) = 0) :
    (exponentTwoLogDegrees → R) ≃ {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} where
  toFun a := ⟨exponentTwoFormalGroup a, inferInstance, nsmulSeries_two_exponentTwoFormalGroup h2 a⟩
  invFun F n := have := F.2.1; PowerSeries.coeff n (F.1.exponentTwoLog F.2.2)
  left_inv a := funext fun n ↦ coeff_exponentTwoLog_exponentTwoFormalGroup a _ n
  right_inv F := have := F.2.1; Subtype.ext (exponentTwoFormalGroup_coeff_exponentTwoLog F.1 F.2.2)

/-- The formal group law attached to `a` by `TauCeti.exponentTwoFormalGroupEquiv` is
`g⁻¹(g(X) + g(Y))` for `g = X + ∑ aₙ Xⁿ`. -/
@[simp]
theorem coe_exponentTwoFormalGroupEquiv_apply (h2 : (2 : R) = 0)
    (a : exponentTwoLogDegrees → R) :
    (exponentTwoFormalGroupEquiv h2 a).1 = exponentTwoFormalGroup a :=
  (rfl)

/-- The family attached to `F` by `TauCeti.exponentTwoFormalGroupEquiv` consists of the
coefficients of the normalised logarithm of `F`. -/
@[simp]
theorem exponentTwoFormalGroupEquiv_symm_apply (h2 : (2 : R) = 0) (F : FormalGroup R) [F.IsComm]
    (hF : F.nsmulSeries 2 = 0) (n : exponentTwoLogDegrees) :
    (exponentTwoFormalGroupEquiv h2).symm ⟨F, inferInstance, hF⟩ n =
      PowerSeries.coeff n (F.exponentTwoLog hF) :=
  (rfl)

/-- **The construction commutes with base change**: the base change of `g⁻¹(g(X) + g(Y))` along
`f` is the formal group law attached to the coefficients `f(aₙ)`. -/
@[simp]
theorem map_exponentTwoFormalGroup (f : R →+* S) (a : exponentTwoLogDegrees → R) :
    (exponentTwoFormalGroup a).map f = exponentTwoFormalGroup (f ∘ a) := by
  rw [exponentTwoFormalGroup, FormalGroup.map_smul, map_inv,
    FormalCoordinate.map_ofExponentTwoCoeffs, FormalGroup.map_𝔾ₐ, exponentTwoFormalGroup]

/-- **Quillen's ring** `𝔽₂[aₙ | n ≥ 2, n not a power of two]`, the coefficient ring of the universal
commutative formal group law of exponent two (`TauCeti.ExponentTwoLazardRing.lift`). -/
abbrev ExponentTwoLazardRing : Type :=
  MvPolynomial exponentTwoLogDegrees (ZMod 2)

namespace ExponentTwoLazardRing

/-- The **universal formal group law of exponent two** `g⁻¹(g(X) + g(Y))` over
`𝔽₂[aₙ]`, for the universal normalised logarithm `g = X + ∑ aₙ Xⁿ`. -/
def formalGroup : FormalGroup ExponentTwoLazardRing :=
  exponentTwoFormalGroup MvPolynomial.X

instance : formalGroup.IsComm :=
  inferInstanceAs (exponentTwoFormalGroup _).IsComm

/-- The universal formal group law has exponent two. -/
@[simp]
theorem nsmulSeries_two_formalGroup : formalGroup.nsmulSeries 2 = 0 :=
  nsmulSeries_two_exponentTwoFormalGroup CharTwo.two_eq_zero _

/-- The normalised logarithm of the universal formal group law is `X + ∑ aₙ Xⁿ`. -/
@[simp]
theorem exponentTwoLog_formalGroup (hF : formalGroup.nsmulSeries 2 = 0) :
    formalGroup.exponentTwoLog hF =
      (FormalCoordinate.ofExponentTwoCoeffs MvPolynomial.X).toPowerSeries :=
  exponentTwoLog_exponentTwoFormalGroup _ hF

/-- The ring homomorphism `ZMod 2 →+* R` to a ring with `2 = 0`. -/
private def zmodTwoHom (h2 : (2 : R) = 0) : ZMod 2 →+* R :=
  ZMod.castHom (ringChar.dvd (by exact_mod_cast h2)) R

/-- The ring homomorphism `𝔽₂[aₙ] →+* R` sending `aₙ` to the coefficient of `Xⁿ` in the normalised
logarithm of `F`. -/
private def liftHom (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0) :
    ExponentTwoLazardRing →+* R :=
  MvPolynomial.eval₂Hom (zmodTwoHom (F.natCast_eq_zero_of_nsmulSeries_eq_zero hF))
    fun n ↦ PowerSeries.coeff n (F.exponentTwoLog hF)

/-- The universal formal group law base-changes along `φ` to the formal group law attached to the
images `φ(aₙ)` of the generators. -/
theorem map_formalGroup (φ : ExponentTwoLazardRing →+* R) :
    formalGroup.map φ = exponentTwoFormalGroup fun n ↦ φ (MvPolynomial.X n) := by
  rw [formalGroup, map_exponentTwoFormalGroup]
  rfl

/-- The base change of the universal formal group law along any ring homomorphism has exponent
two. -/
@[simp]
theorem nsmulSeries_two_map_formalGroup (φ : ExponentTwoLazardRing →+* R) :
    (formalGroup.map φ).nsmulSeries 2 = 0 := by
  rw [← FormalGroup.map_nsmulSeries, nsmulSeries_two_formalGroup, map_zero]

/-- The coefficient of `Xⁿ` in the normalised logarithm of a formal group law equal to
`g⁻¹(g(X) + g(Y))` is `aₙ`. -/
private theorem coeff_exponentTwoLog_of_eq {F : FormalGroup R} [F.IsComm]
    (hF : F.nsmulSeries 2 = 0) {a : exponentTwoLogDegrees → R} (h : exponentTwoFormalGroup a = F)
    (n : exponentTwoLogDegrees) : PowerSeries.coeff n (F.exponentTwoLog hF) = a n := by
  subst h
  exact coeff_exponentTwoLog_exponentTwoFormalGroup a hF n

/-- A ring homomorphism out of `𝔽₂[aₙ]` is determined by the base change of the universal formal
group law along it. -/
theorem hom_ext {φ ψ : ExponentTwoLazardRing →+* R} (h : formalGroup.map φ = formalGroup.map ψ) :
    φ = ψ := by
  refine MvPolynomial.ringHom_ext (fun r ↦ by rw [← RingHom.comp_apply, ← RingHom.comp_apply,
    RingHom.ext_zmod (φ.comp MvPolynomial.C) (ψ.comp MvPolynomial.C)]) fun n ↦ ?_
  have hφ := nsmulSeries_two_map_formalGroup φ
  exact (coeff_exponentTwoLog_of_eq hφ (map_formalGroup φ).symm n).symm.trans
    (coeff_exponentTwoLog_of_eq hφ ((map_formalGroup ψ).symm.trans h.symm) n)

private theorem map_liftHom (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0) :
    formalGroup.map (liftHom F hF) = F := by
  simp only [map_formalGroup, liftHom, MvPolynomial.eval₂Hom_X']
  exact exponentTwoFormalGroup_coeff_exponentTwoLog F hF

/-- **The universal property of Quillen's ring**: commutative formal group laws `F` over `R` with
`[2]_F = 0` correspond to ring homomorphisms `𝔽₂[aₙ] →+* R`. The homomorphism attached to `F`
sends `aₙ` to the coefficient of `Xⁿ` in the normalised logarithm of `F`; conversely a
homomorphism `φ` gives the base change of the universal formal group law along `φ`. -/
def lift : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ≃ (ExponentTwoLazardRing →+* R)
    where
  toFun F := have := F.2.1; liftHom F.1 F.2.2
  invFun φ := ⟨formalGroup.map φ, inferInstance, nsmulSeries_two_map_formalGroup φ⟩
  left_inv F := have := F.2.1; Subtype.ext (map_liftHom F.1 F.2.2)
  right_inv _ := hom_ext (map_liftHom _ _)

/-- The homomorphism `lift F` sends `aₙ` to the coefficient of `Xⁿ` in the normalised logarithm
of `F`. -/
@[simp]
theorem lift_X (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0)
    (n : exponentTwoLogDegrees) :
    lift ⟨F, inferInstance, hF⟩ (MvPolynomial.X n) = PowerSeries.coeff n (F.exponentTwoLog hF) :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- The universal formal group law base-changes along `lift F` to `F`. -/
@[simp]
theorem map_lift (F : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0}) :
    formalGroup.map (lift F) = F.1 :=
  congrArg Subtype.val (lift.left_inv F)

/-- The formal group law attached to `φ : 𝔽₂[aₙ] →+* R` is the base change of the universal
formal group law along `φ`. -/
@[simp]
theorem coe_lift_symm (φ : ExponentTwoLazardRing →+* R) : (lift.symm φ).1 = formalGroup.map φ :=
  (rfl)

/-- The universal property is natural in the coefficient ring: the homomorphism classifying the
base change of `F` along `g` is `g` composed with the homomorphism classifying `F`. -/
theorem lift_map (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0) (g : R →+* S) :
    lift ⟨F.map g, inferInstance, by rw [← FormalGroup.map_nsmulSeries, hF, map_zero]⟩ =
      g.comp (lift ⟨F, inferInstance, hF⟩) :=
  hom_ext <| by rw [map_lift, ← FormalGroup.map_comp, map_lift]

end ExponentTwoLazardRing

end TauCeti
