/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Iso
-- Proof-only: graded normalised logarithms, multiplication series under isomorphisms, and
-- evaluation of weighted homogeneous polynomials in graded rings.
import TauCeti.RingTheory.FormalGroup.ExponentTwo.Graded
import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The universal formal group law of exponent two

A commutative formal group law `F` over a commutative ring `R` with `[2]_F = 0` has a normalised
logarithm `g_F(X) = X + ∑_{i ≥ 1} aᵢ X^(i + 1)` with `a_(2ᵏ - 1) = 0` for every `k ≥ 1`
(`FormalGroup.exponentTwoLog`), and `F(X, Y) = g_F⁻¹(g_F(X) + g_F(Y))`. Conversely, if `2 = 0` in
`R`, every strict coordinate `g = X + ∑ aᵢ X^(i + 1)` with `a_(2ᵏ - 1) = 0` is the normalised
logarithm of the formal group law `g⁻¹(g(X) + g(Y))`, which has exponent two because `2 X = 0`.
So formal group laws of exponent two over `R` are classified by the free families
`(aᵢ)_{i ∉ {2ᵏ - 1}}`, and they are represented by the polynomial ring

  `𝔽₂[aᵢ : i ≥ 1, i ≠ 2ᵏ - 1]`

(`TauCeti.ExponentTwoLazardRing`). With `aᵢ` in degree `i`, this is the universal graded ring for
formal group laws of exponent two whose formal parameter has degree one, the grading of the formal
group law of a real orientation in homological degrees: graded ring homomorphisms out of it
correspond to the formal group laws whose coefficient of `Xⁱ Yʲ` has degree `i + j - 1`. Quillen
identified this ring with the unoriented bordism ring `MO_*`, the formal group law being that of
the canonical real orientation of `MO`.

## Main definitions

* `TauCeti.ExponentTwoLazardRing`: the polynomial ring `𝔽₂[aᵢ : i ≥ 1, i ≠ 2ᵏ - 1]`.
* `TauCeti.ExponentTwoLazardRing.log`: the universal normalised logarithm
  `X + ∑ aᵢ X^(i + 1)`, as a strict formal coordinate.
* `TauCeti.ExponentTwoLazardRing.formalGroup`: the universal formal group law of exponent two,
  `log⁻¹(log(X) + log(Y))`.
* `TauCeti.ExponentTwoLazardRing.lift`: the bijection between commutative formal group laws of
  exponent two over `R` and ring homomorphisms `ExponentTwoLazardRing →+* R`.
* `TauCeti.ExponentTwoLazardRing.grading`: the grading with `aᵢ` in degree `i`.
* `TauCeti.ExponentTwoLazardRing.gradedLift`: the graded version of `lift`.

## Main results

* `FormalGroup.inv_smul_𝔾ₐ_eq`: a commutative formal group law of exponent two is the transport of
  the additive formal group law along the inverse of its normalised logarithm.
* `FormalGroup.nsmulSeries_two_inv_smul_𝔾ₐ`, `FormalGroup.exponentTwoLog_inv_smul_𝔾ₐ`: if `2 = 0`,
  transporting the additive law along `g⁻¹` gives a law of exponent two, whose normalised logarithm
  is `g` when `g` is strict without terms of degree `2ᵏ`, `k ≥ 1`.
* `TauCeti.ExponentTwoLazardRing.map_lift`: the universal formal group law base-changes along
  `lift F` to `F`.
* `TauCeti.ExponentTwoLazardRing.lift_mem_iff`: `lift F` is graded exactly when the coefficient of
  `Xⁱ Yʲ` in `F` has degree `i + j - 1`.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open TauCeti

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- **A formal group law of exponent two is determined by its normalised logarithm**: if the
formal coordinate `φ` has series the normalised logarithm `g` of `F`, then
`F(X, Y) = g⁻¹(g(X) + g(Y))`, that is, `F` is the transport `φ⁻¹ • 𝔾ₐ` of the additive formal
group law. -/
theorem inv_smul_𝔾ₐ_eq (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0)
    {φ : FormalCoordinate R} (hφ : φ.toPowerSeries = F.exponentTwoLog hF) :
    φ⁻¹ • 𝔾ₐ = F := by
  rw [← (F.exponentTwoLogHom hF).smul_eq ((F.exponentTwoLogHom_toPowerSeries hF).trans hφ.symm),
    inv_smul_smul]

variable (φ : FormalCoordinate R)

/-- **Transporting the additive formal group law gives exponent two when `2 = 0`**: if `2 = 0` in
`R`, then `[2](X) = 0` for the formal group law `φ⁻¹ • 𝔾ₐ = φ⁻¹(φ(X) + φ(Y))`. -/
theorem nsmulSeries_two_inv_smul_𝔾ₐ (h2 : (2 : R) = 0) :
    (φ⁻¹ • (𝔾ₐ : FormalGroup R)).nsmulSeries 2 = 0 := by
  -- Transport `[2]_{𝔾ₐ}(X) = 2 X = 0` along the isomorphism `φ⁻¹ : 𝔾ₐ → φ⁻¹ • 𝔾ₐ`.
  have h := (smulIso φ⁻¹ (𝔾ₐ (R := R))).zsmulSeries_eq_subst 2
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zsmulSeries_natCast, zsmulSeries_natCast,
    nsmulSeries_𝔾ₐ, Nat.cast_ofNat, ← map_ofNat PowerSeries.C 2, h2, map_zero, zero_mul,
    PowerSeries.subst_zero_of_constantCoeff_zero (smulIso φ⁻¹ 𝔾ₐ).toHom.zero_constantCoeff,
    PowerSeries.subst_zero] at h
  exact h

/-- **The normalised logarithm of a transported additive formal group law**: if `2 = 0` in `R` and
`φ = X + ⋯` has no term of degree `2ᵏ` for `k ≥ 1`, then `φ` is the normalised logarithm of
`φ⁻¹ • 𝔾ₐ = φ⁻¹(φ(X) + φ(Y))`. -/
theorem exponentTwoLog_inv_smul_𝔾ₐ (h2 : (2 : R) = 0) (h₁ : PowerSeries.coeff 1 φ.toPowerSeries = 1)
    (hp : ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) φ.toPowerSeries = 0) :
    (φ⁻¹ • (𝔾ₐ : FormalGroup R)).exponentTwoLog (nsmulSeries_two_inv_smul_𝔾ₐ φ h2) =
      φ.toPowerSeries := by
  -- `φ` is the series of the inverse of the isomorphism `φ⁻¹ : 𝔾ₐ → φ⁻¹ • 𝔾ₐ`.
  have hφ := (smulIso φ⁻¹ (𝔾ₐ (R := R))).invHom.hom
  rw [smulIso_invHom_toPowerSeries, inv_inv] at hφ
  exact ((φ⁻¹ • 𝔾ₐ).eq_exponentTwoLog _ φ.constantCoeff_toPowerSeries h₁ hp
    ((TauCeti.FormalGroupHom.hom_additive_iff φ.constantCoeff_toPowerSeries).mp hφ)).symm

end FormalGroup

namespace TauCeti

/-- The indices `i ≥ 1` with `i + 1` not a power of two, those of the free coefficients `aᵢ` of
the normalised logarithm `X + ∑ aᵢ X^(i + 1)` of a formal group law of exponent two. -/
abbrev ExponentTwoLazardRing.Index : Type :=
  {i : ℕ+ // ∀ k : ℕ, (i : ℕ) + 1 ≠ 2 ^ k}

/-- The **universal ring for formal group laws of exponent two**: the polynomial ring
`𝔽₂[aᵢ : i ≥ 1, i ≠ 2ᵏ - 1]` over `𝔽₂ = ZMod 2`. Ring homomorphisms out of it are the commutative
formal group laws `F` with `[2]_F = 0` (`TauCeti.ExponentTwoLazardRing.lift`), `aᵢ` being sent to
the coefficient of `X^(i + 1)` in the normalised logarithm of `F`. -/
abbrev ExponentTwoLazardRing : Type :=
  MvPolynomial ExponentTwoLazardRing.Index (ZMod 2)

namespace ExponentTwoLazardRing

open MvPolynomial

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- The coefficients of the universal normalised logarithm: `aᵢ` for `i + 1` not a power of two,
and `0` otherwise. -/
private def logCoeffs (i : ℕ+) : ExponentTwoLazardRing :=
  if h : ∀ k : ℕ, (i : ℕ) + 1 ≠ 2 ^ k then X ⟨i, h⟩ else 0

/-- The **universal normalised logarithm** `X + ∑ aᵢ X^(i + 1)` over `ExponentTwoLazardRing`, with
`aᵢ = 0` when `i + 1` is a power of two. -/
def log : FormalCoordinate ExponentTwoLazardRing :=
  FormalCoordinate.ofStrictCoeffs logCoeffs

/-- The universal normalised logarithm has the generator `aᵢ` as its coefficient of `X^(i + 1)`. -/
@[simp]
theorem coeff_succ_log (i : Index) : PowerSeries.coeff (i.1 + 1) log.toPowerSeries = X i := by
  simp [log, logCoeffs, i.2]

/-- The universal normalised logarithm has linear coefficient `1`. -/
@[simp]
theorem coeff_one_log : PowerSeries.coeff 1 log.toPowerSeries = 1 :=
  FormalCoordinate.coeff_one_ofStrictCoeffs _

/-- The universal normalised logarithm has no term of degree `2ᵏ` for `k ≥ 1`. -/
theorem coeff_two_pow_log {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff (2 ^ k) log.toPowerSeries = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ+, (i : ℕ) + 1 = 2 ^ k :=
    ⟨⟨2 ^ k - 1, by have := Nat.one_lt_two_pow hk.ne'; omega⟩,
      Nat.sub_add_cancel Nat.one_le_two_pow⟩
  rw [← hi, log, FormalCoordinate.coeff_succ_ofStrictCoeffs]
  simp [logCoeffs, hi]

/-- The **universal formal group law of exponent two**, `log⁻¹(log(X) + log(Y))` for the universal
normalised logarithm `log`. -/
def formalGroup : FormalGroup ExponentTwoLazardRing :=
  log⁻¹ • FormalGroup.𝔾ₐ

/-- The universal formal group law of exponent two is the transport of the additive formal group
law along the inverse of the universal normalised logarithm. -/
theorem formalGroup_def : formalGroup = log⁻¹ • FormalGroup.𝔾ₐ :=
  (rfl)

instance : formalGroup.IsComm :=
  FormalGroup.instIsCommSMul _ _

/-- `2 = 0` in the universal ring. -/
private theorem two_eq_zero : (2 : ExponentTwoLazardRing) = 0 := by
  rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 from rfl, map_zero]

/-- The universal formal group law has exponent two: `[2](X) = 0`. -/
theorem nsmulSeries_two_formalGroup : formalGroup.nsmulSeries 2 = 0 :=
  FormalGroup.nsmulSeries_two_inv_smul_𝔾ₐ log two_eq_zero

/-- The normalised logarithm of the universal formal group law is the universal normalised
logarithm. -/
@[simp]
theorem exponentTwoLog_formalGroup :
    formalGroup.exponentTwoLog nsmulSeries_two_formalGroup = log.toPowerSeries :=
  FormalGroup.exponentTwoLog_inv_smul_𝔾ₐ log two_eq_zero coeff_one_log fun _ ↦ coeff_two_pow_log

/-- A ring homomorphism out of `ExponentTwoLazardRing` is determined by its base change of the
universal formal group law. -/
theorem hom_ext {f g : ExponentTwoLazardRing →+* R}
    (h : formalGroup.map f = formalGroup.map g) : f = g := by
  -- The base change of `log` along `f` is the normalised logarithm of `formalGroup.map f`.
  have hlog (f : ExponentTwoLazardRing →+* R) := FormalGroup.map_exponentTwoLog _
    nsmulSeries_two_formalGroup f
  have key : log.toPowerSeries.map f = log.toPowerSeries.map g := by
    rw [← exponentTwoLog_formalGroup, hlog, hlog]
    congr 1
  refine ringHom_ext (fun r ↦ RingHom.congr_fun (RingHom.ext_zmod (f.comp C) (g.comp C)) r)
    fun i ↦ ?_
  simpa using congrArg (PowerSeries.coeff ((i.1 : ℕ) + 1)) key

/-- The base change of the universal normalised logarithm along `f` is the series `g = X + ⋯`
without terms of degree `2ᵏ`, `k ≥ 1`, whose coefficient of `X^(i + 1)` is `f (aᵢ)`. -/
private theorem toPowerSeries_map_log_eq (f : ExponentTwoLazardRing →+* R) {g : PowerSeries R}
    (h₀ : PowerSeries.constantCoeff g = 0) (h₁ : PowerSeries.coeff 1 g = 1)
    (hp : ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) g = 0)
    (hX : ∀ i : Index, f (X i) = PowerSeries.coeff ((i.1 : ℕ) + 1) g) :
    (FormalCoordinate.map f log).toPowerSeries = g := by
  ext (_ | _ | n)
  · simp [h₀]
  · simp [h₁]
  · rw [FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map]
    by_cases hn : ∀ k : ℕ, n + 1 + 1 ≠ 2 ^ k
    · exact (congrArg f (coeff_succ_log ⟨n.succPNat, hn⟩)).trans (hX ⟨n.succPNat, hn⟩)
    · obtain ⟨k, hk⟩ := not_forall_not.mp hn
      have hk0 : 0 < k := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hk
      rw [hk, coeff_two_pow_log hk0, hp k hk0, map_zero]

/-- The homomorphism classifying `F`, sending `aᵢ` to the coefficient of `X^(i + 1)` in the
normalised logarithm of `F`. It is defined on `𝔽₂`-coefficients since `2 = 0` in `R`. -/
private def liftHom (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0) :
    ExponentTwoLazardRing →+* R :=
  eval₂Hom (ZMod.castHom (ringChar.dvd (F.natCast_eq_zero_of_nsmulSeries_eq_zero hF)) R)
    fun i ↦ PowerSeries.coeff ((i.1 : ℕ) + 1) (F.exponentTwoLog hF)

private theorem map_liftHom (F : FormalGroup R) [F.IsComm] (hF : F.nsmulSeries 2 = 0) :
    formalGroup.map (liftHom F hF) = F := by
  rw [formalGroup, FormalGroup.map_smul, map_inv, FormalGroup.map_𝔾ₐ]
  exact F.inv_smul_𝔾ₐ_eq hF (toPowerSeries_map_log_eq _ (by simp) (by simp)
    (fun k hk ↦ F.coeff_two_pow_exponentTwoLog hF hk) fun i ↦ eval₂Hom_X' _ _ _)

/-- **The universal property of `ExponentTwoLazardRing`**: commutative formal group laws `F` over
`R` with `[2]_F = 0` correspond to ring homomorphisms `ExponentTwoLazardRing →+* R`. The
homomorphism attached to `F` sends `aᵢ` to the coefficient of `X^(i + 1)` in the normalised
logarithm of `F` (`TauCeti.ExponentTwoLazardRing.lift_X`), and the formal group law attached to
`f` is the base change of the universal formal group law along `f`. Both sides are empty unless
`2 = 0` in `R`. -/
def lift : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0} ≃ (ExponentTwoLazardRing →+* R)
    where
  toFun F := have := F.2.1; liftHom F.1 F.2.2
  invFun f := ⟨formalGroup.map f, inferInstance, by
    rw [← FormalGroup.map_nsmulSeries, nsmulSeries_two_formalGroup, map_zero]⟩
  left_inv F := have := F.2.1; Subtype.ext (map_liftHom F.1 F.2.2)
  right_inv f := hom_ext (map_liftHom _ _)

/-- The homomorphism classifying `F` sends `aᵢ` to the coefficient of `X^(i + 1)` in the
normalised logarithm of `F`. -/
@[simp]
theorem lift_X (F : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0}) (i : Index) :
    lift F (X i) =
      PowerSeries.coeff ((i.1 : ℕ) + 1) (@FormalGroup.exponentTwoLog _ _ F.1 F.2.1 F.2.2) :=
  eval₂Hom_X' _ _ i

/-- The formal group law classified by `f` is the base change of the universal formal group law
along `f`. -/
@[simp]
theorem coe_lift_symm (f : ExponentTwoLazardRing →+* R) :
    (lift.symm f).1 = formalGroup.map f :=
  (rfl)

/-- The universal formal group law base-changes along `lift F` to `F`. -/
@[simp]
theorem map_lift (F : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0}) :
    formalGroup.map (lift F) = F.1 := by
  rw [← coe_lift_symm, Equiv.symm_apply_apply]

/-- **Naturality of `lift`**: the homomorphism classifying the base change of `F` along
`g : R →+* S` is `g` composed with the homomorphism classifying `F`. -/
theorem lift_map {S : Type*} [CommRing S]
    (F : {F : FormalGroup R // F.IsComm ∧ F.nsmulSeries 2 = 0}) (g : R →+* S) :
    lift ⟨F.1.map g, have := F.2.1; inferInstance,
      by rw [← FormalGroup.map_nsmulSeries, F.2.2, map_zero]⟩ = g.comp (lift F) :=
  hom_ext <| by rw [map_lift, ← FormalGroup.map_comp, map_lift]

section Graded

open MvPolynomial

/-- The **grading of `ExponentTwoLazardRing`** with the generator `aᵢ` in degree `i`: the degree of
the coefficient of `X^(i + 1)` in the normalised logarithm of the formal group law of a real
orientation, in homological degrees. -/
abbrev grading (n : ℕ) : Submodule (ZMod 2) ExponentTwoLazardRing :=
  weightedHomogeneousSubmodule (ZMod 2) (fun i : Index ↦ (i.1 : ℕ)) n

/-- An element of `ExponentTwoLazardRing` has degree `n` exactly when it is a polynomial in the
`aᵢ` that is homogeneous of degree `n` when `aᵢ` has degree `i`. -/
theorem mem_grading_iff {n : ℕ} {x : ExponentTwoLazardRing} :
    x ∈ grading n ↔ x.IsWeightedHomogeneous (fun i : Index ↦ (i.1 : ℕ)) n :=
  mem_weightedHomogeneousSubmodule _ _ _ _

/-- `ExponentTwoLazardRing` is graded by `TauCeti.ExponentTwoLazardRing.grading`. -/
instance : GradedAlgebra grading :=
  weightedGradedAlgebra (ZMod 2) _

/-- The generator `aᵢ` has degree `i`. -/
theorem X_mem_grading (i : Index) : X i ∈ grading i :=
  mem_grading_iff.2 (isWeightedHomogeneous_X _ _ i)

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- **The graded universal property of `ExponentTwoLazardRing`**, pointwise: for a commutative ring
`A` graded by `𝒜`, the homomorphism classifying a commutative formal group law `F` over `A` with
`[2]_F = 0` is graded exactly when the coefficient of every monomial `X^(d 0) Y^(d 1)` in `F` lies
in `𝒜 (d 0 + d 1 - 1)`, that is, when the formal parameter of `F` has degree one. -/
theorem lift_mem_iff (F : {F : FormalGroup A // F.IsComm ∧ F.nsmulSeries 2 = 0}) :
    (∀ ⦃n : ℕ⦄ ⦃x : ExponentTwoLazardRing⦄, x ∈ grading n → lift F x ∈ 𝒜 n) ↔
      ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.1.toPowerSeries ∈ 𝒜 (d.degree - 1) := by
  obtain ⟨F, hc, hF⟩ := F
  rw [← FormalGroup.forall_coeff_exponentTwoLog_mem_iff F hF]
  refine ⟨fun h ↦ ?_, fun h n x hx ↦ ?_⟩
  · -- The coefficients of `X⁰`, `X¹` and `X^(2ᵏ)` are `0`, `1` and `0`; the others are values of
    -- `lift F` at generators.
    rintro (_ | _ | n)
    · simp [zero_mem]
    · simpa using SetLike.GradedOne.one_mem (A := 𝒜)
    · by_cases hn : ∀ k : ℕ, n + 1 + 1 ≠ 2 ^ k
      · simpa using h (X_mem_grading ⟨n.succPNat, hn⟩)
      · obtain ⟨k, hk⟩ := not_forall_not.mp hn
        have hk0 : 0 < k := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hk
        rw [hk, F.coeff_two_pow_exponentTwoLog hF hk0]
        exact zero_mem _
  · -- `lift F` evaluates polynomials over `𝔽₂`, whose coefficients land in degree zero.
    have he : lift ⟨F, hc, hF⟩ =
        eval₂Hom ((lift ⟨F, hc, hF⟩).comp C) (lift ⟨F, hc, hF⟩ ∘ X) :=
      ringHom_ext (fun _ ↦ by simp) fun _ ↦ by simp
    rw [he, coe_eval₂Hom]
    refine (mem_grading_iff.1 hx).eval₂_mem (fun r ↦ ?_) fun i ↦ ?_
    · rw [← ZMod.natCast_zmod_val r, RingHom.comp_apply, map_natCast, map_natCast]
      exact SetLike.natCast_mem_graded _ _
    · simpa using h ((i.1 : ℕ) + 1)

/-- **The graded universal property of `ExponentTwoLazardRing`**: for a commutative ring `A` graded
by `𝒜`, graded ring homomorphisms out of `ExponentTwoLazardRing` correspond to commutative formal
group laws `F` over `A` with `[2]_F = 0` whose coefficient of every monomial `X^(d 0) Y^(d 1)` lies
in `𝒜 (d 0 + d 1 - 1)`. A formal group law corresponds to the homomorphism
`TauCeti.ExponentTwoLazardRing.lift` classifying it. -/
def gradedLift :
    {F : FormalGroup A // F.IsComm ∧ F.nsmulSeries 2 = 0 ∧
      ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈ 𝒜 (d.degree - 1)} ≃
      (grading →+*ᵍ 𝒜) where
  toFun F :=
    { toRingHom := lift ⟨F.1, F.2.1, F.2.2.1⟩
      map_mem := fun hx ↦ (lift_mem_iff ⟨F.1, F.2.1, F.2.2.1⟩).2 F.2.2.2 hx }
  invFun φ := ⟨formalGroup.map φ.toRingHom, inferInstance, (lift.symm φ.toRingHom).2.2,
    (lift_mem_iff (lift.symm φ.toRingHom)).1 (by simpa using fun _ _ ↦ φ.map_mem)⟩
  left_inv F := Subtype.ext <| map_lift ⟨F.1, F.2.1, F.2.2.1⟩
  right_inv φ := GradedRingHom.ext fun x ↦
    DFunLike.congr_fun (lift.apply_symm_apply φ.toRingHom) x

/-- The graded homomorphism attached to `F` is the homomorphism classifying `F`. -/
@[simp]
theorem toRingHom_gradedLift (F : {F : FormalGroup A // F.IsComm ∧ F.nsmulSeries 2 = 0 ∧
      ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈ 𝒜 (d.degree - 1)}) :
    (gradedLift F).toRingHom = lift ⟨F.1, F.2.1, F.2.2.1⟩ :=
  (rfl)

/-- The formal group law attached to a graded homomorphism `φ` is the base change of the universal
formal group law along `φ`. -/
@[simp]
theorem coe_gradedLift_symm (φ : grading →+*ᵍ 𝒜) :
    (gradedLift.symm φ).1 = formalGroup.map φ.toRingHom :=
  (rfl)

end Graded

end ExponentTwoLazardRing

end TauCeti
