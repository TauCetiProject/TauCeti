/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Reduction
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.Topology.Algebra.Valued.Integer
public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.Analysis.Normed.Ring.UnitBall
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.Valued.LocallyCompact

import TauCeti.Topology.Algebra.Ring.Subring

/-!
# The Gauss unit ball of a Tate algebra and its reduction

Let `K` be a nontrivially normed ultrametric field with ring of integers `𝒪[K]` and residue
field `𝓀[K]`, and let `T = K⟨X⟩` be the Tate algebra of unit-radius restricted series in the
variables `σ`. More generally, over any ultrametric normed ring `R` with `‖1‖ = 1`, the Gauss unit
ball `R⟨X⟩° = {f | ‖f‖ ≤ 1}` consists of the series with coefficients in `R°`, giving an isometric
ring isomorphism `R°⟨X⟩ ≃+* R⟨X⟩°` (`TauCeti.MvPowerSeries.restrictedUnitClosedBallEquiv`).
Specializing along `𝒪[K] ≃+* K°` identifies `T°` with `𝒪[K]⟨X⟩`. For commutative `R` and any
positive polyradius `r`, constant series embed `R°` into `R{X/r}°` as a retract via the constant
coefficient, and inverting any unit of `R` of norm `< 1` localizes `R{X/r}°` to `R{X/r}`; over a
nontrivially normed ultrametric field `K`, any `K°`-compatible ring homomorphism out of `K{X/r}°`
therefore extends uniquely to a `K`-algebra homomorphism out of `K{X/r}`.

Reducing coefficients modulo the maximal ideal of `𝒪[K]` sends a series in `T°` to a
polynomial, because only finitely many of its coefficients have norm one. This gives a surjective
ring homomorphism `T° → 𝓀[K][X]` whose kernel is `T°° = {f | ‖f‖ < 1}`, hence
`T° ⧸ T°° ≃ 𝓀[K][X]`. The unit ball is also the subring of power-bounded elements of `T`, and
`T°°` is the set of topologically nilpotent elements of `T`.

Reduction is the basic tool for transferring statements about polynomials over the residue field
to Tate algebras: a series has norm one exactly when its reduction is nonzero. Over a complete
field it also detects units: the kernel `T°°` lies in the Jacobson radical of `T°`, so a series of
`T°` is a unit exactly when its reduction is, that is, when its constant coefficient has norm one
and all other coefficients have norm less than one. Units of `T°` are the units of `T` of norm
one; a nonzero constant of norm less than one is a unit of `T` but not of `T°`.

Reduction is natural. A norm-nonincreasing homomorphism `φ : K →+* L` of nonarchimedean fields
maps `T°` into the Gauss unit ball of `L⟨X⟩`, and reducing the image of `f` is mapping the
reduction of `f` along the induced homomorphism `𝓀[K] →+* 𝓀[L]` of residue fields. In finitely
many variables and for complete `L`, evaluation at a point `x` with coordinates in `𝒪[L]` sends
`T°` to `𝒪[L]`, and the residue of `f(x)` is the value of the reduction of `f` at the residue of
`x`. In particular `‖f(x)‖ < 1` exactly when the reduction of `f` vanishes at the residue of `x`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedUnitClosedBallEquiv`: the isometric ring isomorphism
  `R°⟨X⟩ ≃+* R⟨X⟩°` for an ultrametric normed ring `R` with `‖1‖ = 1`.
* `TauCeti.MvPowerSeries.unitClosedBallCoeffHom` and
  `TauCeti.MvPowerSeries.unitClosedBallConstantCoeffHom`: the constant-series inclusion
  `R° →+* R{X/r}°` and its constant-coefficient retraction.
* `TauCeti.MvPowerSeries.restrictedIntegerUnitClosedBallEquiv`: the coefficientwise isometric ring
  isomorphism `𝒪[K]{X/r} ≃+* K°{X/r}` at any polyradius `r`.
* `TauCeti.MvPowerSeries.restrictedIntegerEquiv`: the isometric ring isomorphism
  `𝒪[K]⟨X⟩ ≃ T°`.
* `TauCeti.MvPowerSeries.restrictedReduction`: coefficientwise reduction `T° →+* 𝓀[K][X]`, defined
  from `(maximalIdeal 𝒪[K]).isRestrictedReduction`
  (`TauCeti.MvPowerSeries.restrictedReduction_restrictedIntegerEquiv_eq`).
* `TauCeti.MvPowerSeries.restrictedReductionQuotientEquiv`: `T° ⧸ T°° ≃+* 𝓀[K][X]`, where the
  kernel `T°°` is described by `TauCeti.MvPowerSeries.restrictedReduction_eq_zero_iff`.
* `TauCeti.MvPowerSeries.canonicalReductionAlgEquiv`: the `𝓀[K]`-algebra isomorphism
  `Huber.CanonicalReduction T ≃ₐ[𝓀[K]] 𝓀[K][X]`.

## Main results

* `TauCeti.MvPowerSeries.mem_unitClosedBall_iff`: a restricted series lies in the unit ball
  exactly when all its coefficients have norm at most one.
* `TauCeti.MvPowerSeries.isLocalizationAway_unitClosedBallCoeffHom`: inverting a unit of `R` of
  norm `< 1` localizes `R{X/r}°` to `R{X/r}`.
* `RingHom.existsUnique_algHom_of_unitClosedBall`: over a nontrivially normed ultrametric field
  `K`, a `K°`-compatible ring homomorphism out of `K{X/r}°` extends uniquely to `K{X/r}`.
* `TauCeti.MvPowerSeries.restrictedReduction_eq_zero_iff`: the reduction of `f` vanishes exactly
  when `‖f‖ < 1`.
* `TauCeti.MvPowerSeries.restrictedReduction_surjective`: every polynomial over `𝓀[K]` is a
  reduction.
* `TauCeti.MvPowerSeries.ker_restrictedReduction`: the kernel of reduction is the open-ball ideal
  `TauCeti.unitBallIdeal T`.
* `TauCeti.MvPowerSeries.restrictedReduction_restrictedIntegerEquiv_eq_isRestrictedSubringReduction`
  states compatibility with open-ideal reduction over `𝒪[K]`.
* `TauCeti.MvPowerSeries.restrictedReduction_restrictedMap`: reduction commutes with coefficient
  maps of nonarchimedean fields.
* `TauCeti.MvPowerSeries.residue_restrictedEval₂`: reduction commutes with evaluation at integral
  points; `TauCeti.MvPowerSeries.norm_restrictedEval₂_lt_one_iff` is the resulting criterion for
  a value of norm less than one.
* `TauCeti.MvPowerSeries.isLocalHom_restrictedReduction`: over a complete field, a series whose
  reduction is a unit is a unit of `T°`.
* `TauCeti.MvPowerSeries.isUnit_iff_norm_constantCoeff_eq_one_and_norm_coeff_lt_one`: the
  coefficient criterion for the units of `T°`.
* `TauCeti.MvPowerSeries.not_isUnit_algebraMap_of_norm_lt_one`: a constant of norm less than
  one is not a unit of `T°`, although a nonzero one is a unit of `T`.
* `TauCeti.MvPowerSeries.powerBoundedSubring_eq_unitClosedBall`: the power-bounded elements of
  `T` form its Gauss unit ball.
* `TauCeti.MvPowerSeries.isTopologicallyNilpotent_iff_norm_lt_one`: the topologically nilpotent
  elements of `T` are the series of Gauss norm less than one.
* `TauCeti.MvPowerSeries.isDomain_canonicalReduction`: the canonical reduction of `T` is a domain.
* `TauCeti.MvPowerSeries.finiteType_canonicalReduction` and
  `TauCeti.MvPowerSeries.isNoetherianRing_canonicalReduction`: in finitely many variables, the
  canonical reduction of `T` is of finite type over `𝓀[K]` and Noetherian.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.1.2–5.1.3.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138), for the general localization step extending a
  `K°`-compatible homomorphism on the Gauss unit ball to `K{X/r}`.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries IsLocalRing Filter
open scoped NormedField Valued

section UnitBall

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R]

/-- **Coefficient criterion for the Gauss unit ball.** A unit-radius restricted series has norm
at most one exactly when all its coefficients do. -/
theorem mem_unitClosedBall_iff [NormOneClass R]
    {f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)} :
    f ∈ Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) ↔
      ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ ≤ 1 := by
  simp [norm_le_iff]

/-- **Coefficient criterion for the open Gauss unit ball.** A unit-radius restricted series has
norm less than one exactly when all its coefficients do. -/
theorem norm_lt_one_iff {f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)} :
    ‖f‖ < 1 ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ < 1 := by
  simp [norm_lt_iff]

/-- The coefficients of a series in the Gauss unit ball have norm at most one. -/
theorem norm_coeff_le_one [NormOneClass R]
    (f : Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1))) (t : σ →₀ ℕ) :
    ‖coeff t ((f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R)‖ ≤ 1 :=
  mem_unitClosedBall_iff.mp f.property t

/-- A norm-nonincreasing coefficient map sends the Gauss unit ball into the Gauss unit ball. -/
theorem restrictedMap_mem_unitClosedBall [NormOneClass R] {S : Type*} [NormedRing S]
    [IsUltrametricDist S] [NormOneClass S] (φ : R →+* S) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (f : Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1))) :
    restrictedMap φ (C := 1) (fun a ↦ (hφ a).trans (one_mul ‖a‖).ge)
        (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) ∈
      Subring.unitClosedBall (IsRestricted.subring (R := S) (fun _ : σ ↦ 1)) :=
  mem_unitClosedBall_iff.mpr fun t ↦ by
    rw [coeff_restrictedMap]
    exact (hφ _).trans (norm_coeff_le_one f t)

/-- The inclusion of `Subring.unitClosedBall R` into `R` is bounded with constant one. -/
private theorem norm_unitClosedBall_subtype_le [NormOneClass R] (x : Subring.unitClosedBall R) :
    ‖(Subring.unitClosedBall R).subtype x‖ ≤ 1 * ‖x‖ := by
  rw [Subring.coe_subtype, one_mul, AddSubgroupClass.coe_norm]

/-- The map `R°⟨X⟩ →+* R⟨X⟩°` including the coefficients. -/
private noncomputable def restrictedUnitClosedBallHom [NormOneClass R] :
    IsRestricted.subring (R := Subring.unitClosedBall R) (fun _ : σ ↦ 1) →+*
      Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :=
  (restrictedMap (Subring.unitClosedBall R).subtype norm_unitClosedBall_subtype_le).codRestrict _
    fun f ↦ mem_unitClosedBall_iff.mpr fun t ↦ by
      rw [coeff_restrictedMap, Subring.coe_subtype]
      exact Subring.mem_unitClosedBall.mp
        (coeff t (f : MvPowerSeries σ (Subring.unitClosedBall R))).property

private theorem restrictedUnitClosedBallHom_bijective [NormOneClass R] :
    Function.Bijective (restrictedUnitClosedBallHom (σ := σ) (R := R)) := by
  refine ⟨fun f g h ↦ Subtype.ext <| MvPowerSeries.ext fun t ↦ Subtype.ext ?_, fun f ↦ ?_⟩
  · simpa [restrictedUnitClosedBallHom] using
      congrArg (fun g : Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) ↦
        coeff t ((g : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R)) h
  · let g : MvPowerSeries σ (Subring.unitClosedBall R) :=
      fun t ↦ ⟨coeff t ((f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R),
        Subring.mem_unitClosedBall.mpr (norm_coeff_le_one f t)⟩
    have hgc (t : σ →₀ ℕ) :
        coeff t g =
          ⟨coeff t ((f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R),
            Subring.mem_unitClosedBall.mpr (norm_coeff_le_one f t)⟩ :=
      MvPowerSeries.coeff_apply g t
    have hg : IsRestricted (fun _ : σ ↦ 1) g := by
      have hf : IsRestricted (fun _ : σ ↦ 1)
          ((f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R) :=
        f.val.property
      simp only [IsRestricted] at hf ⊢
      simpa [hgc, AddSubgroupClass.coe_norm] using hf
    exact ⟨⟨g, hg⟩, Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      simp [restrictedUnitClosedBallHom, hgc]⟩

/-- **The Gauss unit ball as restricted series over `R°`.** Including coefficients identifies
unit-radius restricted series over `Subring.unitClosedBall R` with the series in `R⟨X⟩` of Gauss
norm at most one. -/
noncomputable def restrictedUnitClosedBallEquiv [NormOneClass R] :
    IsRestricted.subring (R := Subring.unitClosedBall R) (fun _ : σ ↦ 1) ≃+*
      Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :=
  RingEquiv.ofBijective _ restrictedUnitClosedBallHom_bijective

/-- `restrictedUnitClosedBallEquiv` includes each coefficient into `R`. -/
@[simp]
theorem coeff_restrictedUnitClosedBallEquiv [NormOneClass R]
    (f : IsRestricted.subring (R := Subring.unitClosedBall R) (fun _ : σ ↦ 1)) (t : σ →₀ ℕ) :
    coeff t ((restrictedUnitClosedBallEquiv f :
        IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R) =
      coeff t (f : MvPowerSeries σ (Subring.unitClosedBall R)) := by
  simp [restrictedUnitClosedBallEquiv, restrictedUnitClosedBallHom]

/-- The coefficients of `restrictedUnitClosedBallEquiv.symm f` are those of `f`. -/
@[simp]
theorem coeff_restrictedUnitClosedBallEquiv_symm [NormOneClass R]
    (f : Subring.unitClosedBall (IsRestricted.subring (R := R) (fun _ : σ ↦ 1))) (t : σ →₀ ℕ) :
    ((coeff t (restrictedUnitClosedBallEquiv.symm f :
        MvPowerSeries σ (Subring.unitClosedBall R)) : Subring.unitClosedBall R) : R) =
      coeff t ((f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPowerSeries σ R) := by
  conv_rhs => rw [← restrictedUnitClosedBallEquiv.apply_symm_apply f]
  rw [coeff_restrictedUnitClosedBallEquiv]

/-- `restrictedUnitClosedBallEquiv` preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedUnitClosedBallEquiv [NormOneClass R]
    (f : IsRestricted.subring (R := Subring.unitClosedBall R) (fun _ : σ ↦ 1)) :
    ‖(restrictedUnitClosedBallEquiv f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1))‖ =
      ‖f‖ := by
  refine le_antisymm (norm_le_iff.mpr fun t ↦ ?_) (norm_le_iff.mpr fun t ↦ ?_)
  · simpa [AddSubgroupClass.coe_norm] using norm_coeff_mul_prod_le f t
  · simpa [AddSubgroupClass.coe_norm] using
      norm_coeff_mul_prod_le
        (restrictedUnitClosedBallEquiv f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) t

end UnitBall

section CoeffHom

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
  {r : σ → ℝ} [∀ i, Fact (0 < r i)]

/-- **Scalar inclusion into the Gauss unit ball.** Constants of norm at most one in `R` embed as
constant series of Gauss norm at most one in `R{X/r}°`. -/
noncomputable def unitClosedBallCoeffHom :
    Subring.unitClosedBall R →+* Subring.unitClosedBall (IsRestricted.subring (R := R) r) :=
  (algebraMap R (IsRestricted.subring (R := R) r)).restrict _ _ fun x hx ↦
    Subring.mem_unitClosedBall.mpr <| by
      rw [norm_algebraMap_isRestrictedSubring]
      exact Subring.mem_unitClosedBall.mp hx

@[simp]
theorem coe_unitClosedBallCoeffHom (x : Subring.unitClosedBall R) :
    (unitClosedBallCoeffHom (σ := σ) (r := r) x : IsRestricted.subring (R := R) r) =
      algebraMap R (IsRestricted.subring (R := R) r) (x : R) := (rfl)

/-- **Constant-coefficient retraction on Gauss unit balls.** The constant coefficient maps
`R{X/r}°` back onto `R°`. -/
noncomputable def unitClosedBallConstantCoeffHom :
    Subring.unitClosedBall (IsRestricted.subring (R := R) r) →+* Subring.unitClosedBall R :=
  ((constantCoeff : MvPowerSeries σ R →+* R).comp
      (IsRestricted.subring (R := R) r).subtype).restrict
    _ _ fun f hf ↦ Subring.mem_unitClosedBall.mpr <|
      (norm_constantCoeff_le f).trans (Subring.mem_unitClosedBall.mp hf)

@[simp]
theorem coe_unitClosedBallConstantCoeffHom
    (f : Subring.unitClosedBall (IsRestricted.subring (R := R) r)) :
    (unitClosedBallConstantCoeffHom f : R) =
      constantCoeff ((f : IsRestricted.subring (R := R) r) : MvPowerSeries σ R) := (rfl)

@[simp]
theorem unitClosedBallConstantCoeffHom_unitClosedBallCoeffHom (x : Subring.unitClosedBall R) :
    unitClosedBallConstantCoeffHom (unitClosedBallCoeffHom (σ := σ) (r := r) x) = x := by
  ext
  simp [coe_algebraMap_isRestrictedSubring]

@[simp]
theorem unitClosedBallConstantCoeffHom_comp_unitClosedBallCoeffHom :
    (unitClosedBallConstantCoeffHom (σ := σ) (R := R) (r := r)).comp unitClosedBallCoeffHom =
      RingHom.id _ :=
  RingHom.ext unitClosedBallConstantCoeffHom_unitClosedBallCoeffHom

/-- `restrictedUnitClosedBallEquiv` maps constants in `R°` to constant series in `R⟨X⟩°`. -/
@[simp]
theorem restrictedUnitClosedBallEquiv_algebraMap (c : Subring.unitClosedBall R) :
    restrictedUnitClosedBallEquiv
        (algebraMap (Subring.unitClosedBall R)
          (IsRestricted.subring (R := Subring.unitClosedBall R) (fun _ : σ ↦ 1)) c) =
      unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) c := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  ext t
  rw [coeff_restrictedUnitClosedBallEquiv, coe_unitClosedBallCoeffHom,
    coe_algebraMap_isRestrictedSubring, coe_algebraMap_isRestrictedSubring, coeff_C, coeff_C]
  split_ifs <;> simp

/-- **Inverting any unit of `R` of norm `< 1` localizes `R{X/r}°` to `R{X/r}`.**

This is the general localization step underlying the integral-presentation bridge (cf. Bosch,
*Lectures on Formal and Rigid Geometry*, §6.4, proof of Lemma 5, pp. 137–138). -/
theorem isLocalizationAway_unitClosedBallCoeffHom (π : Subring.unitClosedBall R)
    (hπ0 : IsUnit (π : R)) (hπ1 : ‖(π : R)‖ < 1) :
    IsLocalization.Away (unitClosedBallCoeffHom (σ := σ) (r := r) π)
      (IsRestricted.subring (R := R) r) :=
  (Subring.unitClosedBall (IsRestricted.subring (R := R) r)).isLocalizationAway_of_isOpen
    (Subring.isOpen_unitClosedBall _) (unitClosedBallCoeffHom π)
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one <| by
      simpa [coe_unitClosedBallCoeffHom, norm_algebraMap_isRestrictedSubring] using hπ1)
    (by
      rw [coe_unitClosedBallCoeffHom]
      exact hπ0.map (algebraMap R (IsRestricted.subring (R := R) r)))

/-- **Unique extension of a ring homomorphism on the Gauss unit ball to a `K`-algebra
homomorphism** (generalizing Bosch, *Lectures on Formal and Rigid Geometry*, §6.4, proof of
Lemma 5, pp. 137–138). Over a nontrivially normed ultrametric field `K`, any ring homomorphism
`ψ : Subring.unitClosedBall (IsRestricted.subring (R := K) r) →+* A` into a commutative
`K`-algebra `A` that agrees with `algebraMap K A` on `Subring.unitClosedBall K` extends uniquely
to a `K`-algebra homomorphism `π : IsRestricted.subring (R := K) r →ₐ[K] A` via localization at a
pseudouniformizer. -/
theorem _root_.RingHom.existsUnique_algHom_of_unitClosedBall {σ K A : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] {r : σ → ℝ} [∀ i, Fact (0 < r i)]
    [CommRing A] [Algebra K A]
    (ψ : Subring.unitClosedBall (IsRestricted.subring (R := K) r) →+* A)
    (hψ : ∀ c : Subring.unitClosedBall K, ψ (unitClosedBallCoeffHom c) = algebraMap K A c) :
    ∃! π : IsRestricted.subring (R := K) r →ₐ[K] A,
      ∀ f : Subring.unitClosedBall (IsRestricted.subring (R := K) r), π f = ψ f := by
  -- Choose a nonzero scalar of norm `< 1`; inverting it localizes `K°` to `K` and `K{X/r}°` to
  -- `K{X/r}`.
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  let p : Subring.unitClosedBall K := ⟨ϖ, Subring.mem_unitClosedBall.mpr hϖ1.le⟩
  have hp0 : IsUnit (p : K) := isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0)
  have : IsLocalization.Away p K :=
    (Subring.unitClosedBall K).isLocalizationAway_of_isOpen
      (Subring.isOpen_unitClosedBall K) p (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1) hp0
  let x := unitClosedBallCoeffHom (σ := σ) (r := r) p
  have : IsLocalization.Away x (IsRestricted.subring (R := K) r) :=
    isLocalizationAway_unitClosedBallCoeffHom p hp0 hϖ1
  -- Lift `ψ` along the localization and verify `K`-linearity on `K°[1/p] = K`.
  have hx : IsUnit (ψ x) := by
    rw [hψ p]
    exact hp0.map (algebraMap K A)
  let π₀ : IsRestricted.subring (R := K) r →+* A := IsLocalization.Away.lift x hx
  have hπ₀_ball (f : Subring.unitClosedBall (IsRestricted.subring (R := K) r)) : π₀ f = ψ f := by
    simpa [Algebra.algebraMap_ofSubring] using
      IsLocalization.Away.lift_eq (S := IsRestricted.subring (R := K) r) x hx f
  have hcomm : π₀.comp (algebraMap K (IsRestricted.subring (R := K) r)) = algebraMap K A :=
    IsLocalization.ringHom_ext (Submonoid.powers p) <| RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply, Algebra.algebraMap_ofSubring, Subring.coe_subtype]
      rw [← coe_unitClosedBallCoeffHom (σ := σ) (r := r), hπ₀_ball, hψ]
  let π : IsRestricted.subring (R := K) r →ₐ[K] A :=
    { π₀ with commutes' := RingHom.congr_fun hcomm }
  have hπ_ball (f : Subring.unitClosedBall (IsRestricted.subring (R := K) r)) : π f = ψ f := by
    simpa [π] using hπ₀_ball f
  -- Uniqueness follows from `IsLocalization.ringHom_ext` on `K{X/r}°[1/x] = K{X/r}`.
  refine ⟨π, hπ_ball, fun π' hπ' ↦ AlgHom.toRingHom_injective ?_⟩
  refine IsLocalization.ringHom_ext (Submonoid.powers x) (RingHom.ext fun f ↦ ?_)
  simpa [Algebra.algebraMap_ofSubring, AlgHom.coe_toRingHom] using (hπ' f).trans (hπ_ball f).symm

end CoeffHom

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)
local notation "T°" => Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
local notation "Tint" => IsRestricted.subring (R := 𝒪[K]) (fun _ : σ ↦ 1)

/-- The coefficients of a series in the Gauss unit ball lie in `𝒪[K]`. -/
theorem coeff_mem_integer (f : T°) (t : σ →₀ ℕ) :
    coeff t ((f : T) : MvPowerSeries σ K) ∈ 𝒪[K] :=
  Valued.integer.mem_iff.mpr (norm_coeff_le_one f t)

section IntegerEquiv

/-- **Coefficientwise identification `𝒪[K]{X/r} ≃+* K°{X/r}`.** Transporting coefficients along
`TauCeti.integerUnitClosedBallEquiv` identifies restricted series over `𝒪[K]` with restricted
series over `K°` at any polyradius `r`. -/
noncomputable def restrictedIntegerUnitClosedBallEquiv {r : σ → ℝ} :
    IsRestricted.subring (R := 𝒪[K]) r ≃+*
      IsRestricted.subring (R := Subring.unitClosedBall K) r :=
  RingEquiv.ofRingHom
    (restrictedMap (integerUnitClosedBallEquiv (K := K)).toRingHom (C := 1) fun x ↦ by
      simp [AddSubgroupClass.coe_norm])
    (restrictedMap (integerUnitClosedBallEquiv (K := K)).symm.toRingHom (C := 1) fun x ↦ by
      simp [AddSubgroupClass.coe_norm])
    (RingHom.ext fun f ↦ Subtype.ext <| MvPowerSeries.ext fun t ↦ by simp)
    (RingHom.ext fun f ↦ Subtype.ext <| MvPowerSeries.ext fun t ↦ by simp)

/-- `restrictedIntegerUnitClosedBallEquiv` maps each coefficient along
`integerUnitClosedBallEquiv`. -/
@[simp]
theorem coeff_restrictedIntegerUnitClosedBallEquiv {r : σ → ℝ}
    (f : IsRestricted.subring (R := 𝒪[K]) r) (t : σ →₀ ℕ) :
    coeff t (restrictedIntegerUnitClosedBallEquiv f :
        MvPowerSeries σ (Subring.unitClosedBall K)) =
      integerUnitClosedBallEquiv (coeff t (f : MvPowerSeries σ 𝒪[K])) := by
  simp [restrictedIntegerUnitClosedBallEquiv]

/-- The inverse of `restrictedIntegerUnitClosedBallEquiv` maps each coefficient along
`integerUnitClosedBallEquiv.symm`. -/
@[simp]
theorem coeff_restrictedIntegerUnitClosedBallEquiv_symm {r : σ → ℝ}
    (f : IsRestricted.subring (R := Subring.unitClosedBall K) r) (t : σ →₀ ℕ) :
    coeff t (restrictedIntegerUnitClosedBallEquiv.symm f : MvPowerSeries σ 𝒪[K]) =
      integerUnitClosedBallEquiv.symm
        (coeff t (f : MvPowerSeries σ (Subring.unitClosedBall K))) := by
  simp [restrictedIntegerUnitClosedBallEquiv]

/-- `restrictedIntegerUnitClosedBallEquiv` preserves the Gauss norm at any positive polyradius. -/
@[simp]
theorem norm_restrictedIntegerUnitClosedBallEquiv {r : σ → ℝ} [∀ i, Fact (0 < r i)]
    (f : IsRestricted.subring (R := 𝒪[K]) r) :
    ‖restrictedIntegerUnitClosedBallEquiv f‖ = ‖f‖ :=
  norm_restrictedMap _ _ (fun x ↦ by simp [AddSubgroupClass.coe_norm]) f

/-- **The Gauss unit ball as restricted series over the integers.** Including coefficients
identifies unit-radius restricted series over `𝒪[K]` with the series in `K⟨X⟩` of Gauss norm at
most one. -/
noncomputable def restrictedIntegerEquiv : Tint ≃+* T° :=
  restrictedIntegerUnitClosedBallEquiv.trans restrictedUnitClosedBallEquiv

/-- `restrictedIntegerEquiv` includes each coefficient into `K`. -/
@[simp]
theorem coeff_restrictedIntegerEquiv (f : Tint) (t : σ →₀ ℕ) :
    coeff t ((restrictedIntegerEquiv f : T) : MvPowerSeries σ K) =
      coeff t (f : MvPowerSeries σ 𝒪[K]) := by
  simp [restrictedIntegerEquiv]

/-- The coefficients of `restrictedIntegerEquiv.symm f` are those of `f`. -/
@[simp]
theorem coeff_restrictedIntegerEquiv_symm (f : T°) (t : σ →₀ ℕ) :
    ((coeff t (restrictedIntegerEquiv.symm f : MvPowerSeries σ 𝒪[K]) : 𝒪[K]) : K) =
      coeff t ((f : T) : MvPowerSeries σ K) := by
  conv_rhs => rw [← restrictedIntegerEquiv.apply_symm_apply f]
  rw [coeff_restrictedIntegerEquiv]

/-- `restrictedIntegerEquiv` preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedIntegerEquiv (f : Tint) : ‖(restrictedIntegerEquiv f : T)‖ = ‖f‖ := by
  simp [restrictedIntegerEquiv]

/-- `restrictedIntegerEquiv` maps constants in `𝒪[K]` to constant series in `K⟨X⟩°`. -/
@[simp]
theorem restrictedIntegerEquiv_algebraMap (c : 𝒪[K]) :
    restrictedIntegerEquiv (algebraMap 𝒪[K] Tint c) =
      unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) (integerUnitClosedBallEquiv c) := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  ext t
  rw [coeff_restrictedIntegerEquiv, coe_unitClosedBallCoeffHom, coe_algebraMap_isRestrictedSubring,
    coe_algebraMap_isRestrictedSubring, coeff_C, coeff_C]
  split_ifs <;> simp

end IntegerEquiv

section Reduction

/-- **Reduction of the Gauss unit ball.** A series of Gauss norm at most one in `K⟨X⟩` is sent to
the polynomial over the residue field `𝓀[K]` obtained by reducing each coefficient; only finitely
many coefficients have nonzero residue. -/
noncomputable def restrictedReduction : T° →+* MvPolynomial σ 𝓀[K] :=
  (𝓂[K].isRestrictedSubringReduction TauCeti.isOpen_maximalIdeal_integer).comp
    restrictedIntegerEquiv.symm.toRingHom

/-- Over the integer subring `𝒪[K]` of a nonarchimedean normed field, Gauss unit-ball reduction
under `restrictedIntegerEquiv` agrees with open-ideal reduction modulo `𝓂[K]`. -/
theorem restrictedReduction_restrictedIntegerEquiv_eq_isRestrictedSubringReduction (f : Tint) :
    restrictedReduction (restrictedIntegerEquiv f) =
      𝓂[K].isRestrictedSubringReduction TauCeti.isOpen_maximalIdeal_integer f :=
  congrArg (𝓂[K].isRestrictedSubringReduction TauCeti.isOpen_maximalIdeal_integer)
    (restrictedIntegerEquiv.symm_apply_apply f)

/-- The coefficients of the reduction are the residues of the coefficients. -/
@[simp]
theorem coeff_restrictedReduction (f : T°) (t : σ →₀ ℕ) :
    (restrictedReduction f).coeff t =
      residue 𝒪[K] ⟨coeff t ((f : T) : MvPowerSeries σ K), coeff_mem_integer f t⟩ :=
  (Ideal.coeff_isRestrictedSubringReduction 𝓂[K] TauCeti.isOpen_maximalIdeal_integer
    (restrictedIntegerEquiv.symm f) t).trans <|
    (residue_def _).symm.trans <| congrArg (residue 𝒪[K]) (Subtype.ext (by simp))

/-- **Compatibility of unit-ball reduction and open-ideal reduction.** Under the coefficient
identification `restrictedIntegerEquiv : 𝒪[K]⟨X⟩ ≃+* K⟨X⟩°`, the residue-field reduction
`TauCeti.MvPowerSeries.restrictedReduction` on the Gauss unit ball agrees with
`(maximalIdeal 𝒪[K]).isRestrictedReduction` on `𝒪[K]⟨X⟩`. -/
theorem restrictedReduction_restrictedIntegerEquiv_eq (f : Tint) :
    restrictedReduction (restrictedIntegerEquiv f) =
      (maximalIdeal 𝒪[K]).isRestrictedReduction TauCeti.isOpen_maximalIdeal_integer f := by
  refine MvPolynomial.ext _ _ fun t ↦ ?_
  rw [coeff_restrictedReduction]
  exact (congrArg (residue 𝒪[K]) (Subtype.ext (coeff_restrictedIntegerEquiv f t))).trans
    (Ideal.coeff_isRestrictedReduction (maximalIdeal 𝒪[K]) TauCeti.isOpen_maximalIdeal_integer
      f t).symm


/-- A coefficient of the reduction vanishes exactly when the corresponding coefficient of the
series has norm less than one. -/
theorem coeff_restrictedReduction_eq_zero_iff {f : T°} {t : σ →₀ ℕ} :
    (restrictedReduction f).coeff t = 0 ↔ ‖coeff t ((f : T) : MvPowerSeries σ K)‖ < 1 := by
  rw [coeff_restrictedReduction, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    Valued.integer.isUnit_iff_norm_eq_one]
  exact ⟨fun h ↦ (norm_coeff_le_one f t).lt_of_ne h, ne_of_lt⟩

/-- The reduction of a series vanishes exactly when its Gauss norm is less than one: the kernel
of `restrictedReduction` is the open unit ball `T°°`. -/
theorem restrictedReduction_eq_zero_iff {f : T°} :
    restrictedReduction f = 0 ↔ ‖(f : T)‖ < 1 := by
  rw [norm_lt_one_iff, MvPolynomial.ext_iff]
  exact forall_congr' fun t ↦ by
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      coeff_restrictedReduction_eq_zero_iff]

/-- A series in the Gauss unit ball has norm one exactly when its reduction is nonzero. -/
theorem restrictedReduction_ne_zero_iff {f : T°} :
    restrictedReduction f ≠ 0 ↔ ‖(f : T)‖ = 1 := by
  rw [Ne, restrictedReduction_eq_zero_iff, not_lt]
  exact ⟨fun h ↦ le_antisymm (Subring.mem_unitClosedBall.mp f.property) h, ge_of_eq⟩

/-- Membership in the kernel of `restrictedReduction` is the strict bound `‖f‖ < 1`. -/
theorem mem_ker_restrictedReduction {f : T°} :
    f ∈ RingHom.ker restrictedReduction ↔ ‖(f : T)‖ < 1 := by
  rw [RingHom.mem_ker, restrictedReduction_eq_zero_iff]

/-- **The kernel of reduction is the open-ball ideal** `T°° = TauCeti.unitBallIdeal T` of the
Gauss unit ball. -/
theorem ker_restrictedReduction :
    RingHom.ker (restrictedReduction (σ := σ) (K := K)) = unitBallIdeal T := by
  ext f
  rw [mem_ker_restrictedReduction, mem_unitBallIdeal]

/-- The reduction of a polynomial with integral coefficients is its coefficientwise reduction. -/
@[simp]
theorem restrictedReduction_restrictedIntegerEquiv (q : MvPolynomial σ 𝒪[K]) :
    restrictedReduction (restrictedIntegerEquiv
        ⟨(q : MvPowerSeries σ 𝒪[K]), MvPolynomial.isRestricted _ q⟩) =
      q.map (residue 𝒪[K]) := by
  refine MvPolynomial.ext _ _ fun t ↦ ?_
  simp only [coeff_restrictedReduction, coeff_restrictedIntegerEquiv, MvPolynomial.coeff_map,
    MvPolynomial.coeff_coe]

/-- **Every polynomial over the residue field is a reduction**: lift its coefficients to
`𝒪[K]`. -/
theorem restrictedReduction_surjective :
    Function.Surjective (restrictedReduction (σ := σ) (K := K)) := by
  intro p
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ (residue_surjective (R := 𝒪[K])) p
  exact ⟨_, restrictedReduction_restrictedIntegerEquiv q⟩

/-- **`T° ⧸ T°° ≃ 𝓀[K][X]`.** Reduction identifies the quotient of the Gauss unit ball by the
kernel of reduction, the series of norm less than one (`mem_ker_restrictedReduction`), with the
polynomial ring over the residue field. -/
noncomputable def restrictedReductionQuotientEquiv :
    T° ⧸ RingHom.ker (restrictedReduction (σ := σ) (K := K)) ≃+* MvPolynomial σ 𝓀[K] :=
  RingHom.quotientKerEquivOfSurjective restrictedReduction_surjective

/-- `restrictedReductionQuotientEquiv` sends the class of `f` to its reduction. -/
@[simp]
theorem restrictedReductionQuotientEquiv_mk (f : T°) :
    restrictedReductionQuotientEquiv (Ideal.Quotient.mk _ f) = restrictedReduction f := (rfl)

/-- A constant of norm at most one reduces to the constant polynomial on its residue. -/
@[simp]
theorem restrictedReduction_algebraMap (a : 𝒪[K]) (h : algebraMap K T a ∈ T°) :
    restrictedReduction ⟨algebraMap K T a, h⟩ = MvPolynomial.C (residue 𝒪[K] a) := by
  classical
  have : (⟨algebraMap K T a, h⟩ : T°) =
      restrictedIntegerEquiv
        ⟨((MvPolynomial.C a : MvPolynomial σ 𝒪[K]) : MvPowerSeries σ 𝒪[K]),
          MvPolynomial.isRestricted _ _⟩ :=
    Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      rw [coeff_restrictedIntegerEquiv]
      simp only [coe_algebraMap_isRestrictedSubring, MvPolynomial.coe_C, coeff_C]
      split_ifs <;> simp
  rw [this, restrictedReduction_restrictedIntegerEquiv, MvPolynomial.map_C]

/-- Each variable reduces to the corresponding variable. -/
@[simp]
theorem restrictedReduction_X (i : σ) (h : (⟨X i, isRestricted_X _ i⟩ : T) ∈ T°) :
    restrictedReduction ⟨⟨X i, isRestricted_X _ i⟩, h⟩ = MvPolynomial.X i := by
  classical
  have : (⟨⟨X i, isRestricted_X _ i⟩, h⟩ : T°) =
      restrictedIntegerEquiv
        ⟨((MvPolynomial.X i : MvPolynomial σ 𝒪[K]) : MvPowerSeries σ 𝒪[K]),
          MvPolynomial.isRestricted _ _⟩ :=
    Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      rw [coeff_restrictedIntegerEquiv]
      simp only [MvPolynomial.coe_X, coeff_X]
      split_ifs <;> simp
  rw [this, restrictedReduction_restrictedIntegerEquiv, MvPolynomial.map_X]

end Reduction

section Functoriality

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] (φ : K →+* L)
  (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)

/-- **Reduction commutes with coefficient maps.** For a norm-nonincreasing homomorphism
`φ : K →+* L` of nonarchimedean fields, reducing the coefficientwise image of a series of the
Gauss unit ball is mapping its reduction along the induced homomorphism `𝓀[K] →+* 𝓀[L]` of
residue fields. -/
@[simp]
theorem restrictedReduction_restrictedMap (f : T°)
    (h : restrictedMap φ (C := 1) (fun a ↦ (hφ a).trans (one_mul ‖a‖).ge) (f : T) ∈
      Subring.unitClosedBall (IsRestricted.subring (R := L) (fun _ : σ ↦ 1))) :
    restrictedReduction ⟨_, h⟩ =
      (restrictedReduction f).map (ResidueField.map (φ.integerRestrict hφ)) := by
  refine MvPolynomial.ext _ _ fun t ↦ ?_
  rw [MvPolynomial.coeff_map, coeff_restrictedReduction, coeff_restrictedReduction,
    ResidueField.map_residue]
  exact congrArg _ (Subtype.ext (by simp))

end Functoriality

section Eval

variable {k : ℕ} {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (φ : K →+* L) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (x : Fin k → 𝒪[L])

local notation "Tₖ" => IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1)
local notation "Tₖ°" => Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1))

/-- A series of the Gauss unit ball takes integral values at integral points. -/
theorem restrictedEval₂_mem_integer (f : Tₖ°) :
    restrictedEval₂ φ (fun i ↦ (x i : L)) hφ (fun i ↦ Valued.integer.mem_iff.1 (x i).property)
      (f : Tₖ) ∈ 𝒪[L] :=
  Valued.integer.mem_iff.2 ((norm_restrictedEval₂_le _ _ _ _ _).trans
    (Subring.mem_unitClosedBall.mp f.property))

/-- **Reduction commutes with evaluation at integral points.** Let `φ : K →+* L` be a
norm-nonincreasing homomorphism into a complete nonarchimedean field and let `x` be a point with
coordinates in `𝒪[L]`. For a series `f` of Gauss norm at most one, the residue of the value
`f(x)` is the value of the reduction of `f` at the residue of `x`, with coefficients mapped along
the induced homomorphism `𝓀[K] →+* 𝓀[L]` of residue fields. -/
@[simp]
theorem residue_restrictedEval₂ (f : Tₖ°)
    (h : restrictedEval₂ φ (fun i ↦ (x i : L)) hφ (fun i ↦ Valued.integer.mem_iff.1 (x i).property)
      (f : Tₖ) ∈ 𝒪[L]) :
    residue 𝒪[L] ⟨_, h⟩ = (restrictedReduction f).eval₂ (ResidueField.map (φ.integerRestrict hφ))
      (fun i ↦ residue 𝒪[L] (x i)) := by
  classical
  -- Truncate `f` to the finitely many exponents where its reduction is nonzero; this gives a
  -- polynomial `q` with integral coefficients whose image `P` in `T°` satisfies `‖f - P‖ < 1`.
  let s := (restrictedReduction f).support
  let q : MvPolynomial (Fin k) 𝒪[K] :=
    truncFinset 𝒪[K] s (restrictedIntegerEquiv.symm f : MvPowerSeries (Fin k) 𝒪[K])
  let P : Tₖ° := restrictedIntegerEquiv ⟨q, MvPolynomial.isRestricted _ q⟩
  have hfP : ‖((f - P : Tₖ°) : Tₖ)‖ < 1 := by
    refine norm_lt_one_iff.mpr fun t ↦ ?_
    by_cases ht : t ∈ s
    · simp [P, q, coeff_truncFinset_of_mem _ ht]
    · simpa [P, q, coeff_truncFinset_eq_zero _ ht] using
        coeff_restrictedReduction_eq_zero_iff.mp (MvPolynomial.notMem_support_iff.mp ht)
  have hred : restrictedReduction f = q.map (residue 𝒪[K]) := by
    rw [← restrictedReduction_restrictedIntegerEquiv q, ← sub_eq_zero, ← map_sub,
      restrictedReduction_eq_zero_iff]
    exact hfP
  -- The value of `P` at `x` is the integral polynomial value `q(x)`.
  have hP : restrictedEval₂ φ (fun i ↦ (x i : L)) hφ (fun i ↦ Valued.integer.mem_iff.1
      (x i).property)
      (P : Tₖ) = ((MvPolynomial.eval₂ (φ.integerRestrict hφ) x q : 𝒪[L]) : L) := by
    have : (P : Tₖ) = ⟨(q.map (𝒪[K]).subtype : MvPolynomial (Fin k) K),
        MvPolynomial.isRestricted _ _⟩ :=
      Subtype.ext <| MvPowerSeries.ext fun t ↦ by simp [P, MvPolynomial.coeff_map]
    rw [this, restrictedEval₂_polynomial, MvPolynomial.eval₂_map, ← Subring.coe_subtype,
      MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext fun a ↦ by simp
  -- So `f(x)` and `q(x)` have the same residue, since `‖(f - P)(x)‖ ≤ ‖f - P‖ < 1`.
  have hres : residue 𝒪[L] ⟨_, h⟩ =
      residue 𝒪[L] (MvPolynomial.eval₂ (φ.integerRestrict hφ) x q) := by
    refine Valued.integer.residue_eq_residue_iff_norm_sub_lt_one.mpr ?_
    rw [← hP, ← map_sub, ← AddSubgroupClass.coe_sub]
    exact (norm_restrictedEval₂_le _ _ _ _ _).trans_lt hfP
  rw [hres, hred, MvPolynomial.eval₂_map, ResidueField.map_comp_residue,
    MvPolynomial.eval₂_comp_left, Function.comp_def]

/-- A series of the Gauss unit ball has a value of norm less than one at an integral point `x`
exactly when its reduction vanishes at the residue of `x`. -/
theorem norm_restrictedEval₂_lt_one_iff (f : Tₖ°) :
    ‖restrictedEval₂ φ (fun i ↦ (x i : L)) hφ (fun i ↦ Valued.integer.mem_iff.1 (x i).property)
      (f : Tₖ)‖ < 1 ↔ (restrictedReduction f).eval₂ (ResidueField.map (φ.integerRestrict hφ))
        (fun i ↦ residue 𝒪[L] (x i)) = 0 := by
  rw [← residue_restrictedEval₂ φ hφ x f (restrictedEval₂_mem_integer φ hφ x f),
    Valued.integer.residue_eq_zero_iff_norm_lt_one]

end Eval

section Units

/-- **Small constants are not units of `T°`.** A constant of norm less than one is not a unit of
the Gauss unit ball `T°`. When it is nonzero it is nevertheless a unit of the Tate algebra `T`,
as the image of a unit of `K` under `algebraMap`. -/
theorem not_isUnit_algebraMap_of_norm_lt_one {a : K} (ha : ‖a‖ < 1) :
    ¬IsUnit (⟨algebraMap K T a, Subring.mem_unitClosedBall.mpr
      ((norm_algebraMap_isRestrictedSubring a).trans_le ha.le)⟩ : T°) := fun hu ↦ ha.ne <|
  (norm_algebraMap_isRestrictedSubring a).symm.trans (isUnit_unitClosedBall_iff.mp hu).2

variable [CompleteSpace K]

/-- **Units lift along reduction.** Over a complete field, reduction `T° → 𝓀[K][X]` is a local
homomorphism: a series of Gauss norm at most one whose reduction is a unit is a unit of `T°`.
Together with `isUnit_map_iff`, a series of `T°` is a unit exactly when its reduction is a
unit. -/
instance isLocalHom_restrictedReduction :
    IsLocalHom (restrictedReduction (σ := σ) (K := K)) := by
  have hker :
      IsLocalHom (Ideal.Quotient.mk (RingHom.ker (restrictedReduction (σ := σ) (K := K)))) :=
    isLocalHom_of_le_jacobson (by
      simpa only [Ideal.jacobson_bot] using
        ker_restrictedReduction.le.trans (unitBallIdeal_le_jacobson_bot T))
  have h : restrictedReduction (σ := σ) (K := K) =
      (restrictedReductionQuotientEquiv (σ := σ) (K := K) : _ →+* _).comp
        (Ideal.Quotient.mk (RingHom.ker (restrictedReduction (σ := σ) (K := K)))) :=
    RingHom.ext fun f ↦ (restrictedReductionQuotientEquiv_mk f).symm
  rw [h]
  infer_instance

/-- **The units of the Gauss unit ball.** Over a complete field, a series of Gauss norm at most
one is a unit of `T°` exactly when its constant coefficient has norm one and every other
coefficient has norm less than one, that is, when its reduction is a nonzero constant. Such a
series is in particular a unit of `T` of norm one; conversely, by
`TauCeti.isUnit_unitClosedBall_iff`, a unit of `T` lies in the units of `T°` only if it has
norm one, so a nonzero constant of norm less than one is a unit of `T` but not of `T°`
(`not_isUnit_algebraMap_of_norm_lt_one`). -/
theorem isUnit_iff_norm_constantCoeff_eq_one_and_norm_coeff_lt_one {f : T°} :
    IsUnit f ↔ ‖constantCoeff ((f : T) : MvPowerSeries σ K)‖ = 1 ∧
      ∀ t ≠ 0, ‖coeff t ((f : T) : MvPowerSeries σ K)‖ < 1 := by
  rw [← isUnit_map_iff restrictedReduction, MvPolynomial.isUnit_iff, isUnit_iff_ne_zero,
    ← coeff_zero_eq_constantCoeff_apply, ne_eq, coeff_restrictedReduction_eq_zero_iff, not_lt,
    (norm_coeff_le_one f 0).ge_iff_eq]
  simp_rw [isNilpotent_iff_eq_zero, coeff_restrictedReduction_eq_zero_iff]

end Units

section PowerBounded

/-- **The power-bounded subring of `K⟨X⟩` is its Gauss unit ball.** The Gauss norm is
multiplicative, and a constant of norm strictly between zero and one is a pseudouniformiser. -/
theorem powerBoundedSubring_eq_unitClosedBall :
    Huber.powerBoundedSubring T = Subring.unitClosedBall T := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖ : Huber.IsPseudoUniformizer (algebraMap K T ϖ) :=
    .of_norm_lt_one ((isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0)).map _)
      (by rwa [norm_algebraMap_isRestrictedSubring])
  exact SetLike.coe_injective <| (hϖ.coe_powerBoundedSubring_eq_closedBall
    fun f n _ ↦ norm_pow f n).trans (Subring.coe_unitClosedBall T).symm

/-- **The topologically nilpotent elements of `K⟨X⟩`** are the series of Gauss norm less than
one, since the Gauss norm is multiplicative. Within the unit ball `T°` they form the kernel `T°°`
of reduction (`mem_ker_restrictedReduction`). -/
theorem isTopologicallyNilpotent_iff_norm_lt_one {f : T} : IsTopologicallyNilpotent f ↔ ‖f‖ < 1 :=
  isTopologicallyNilpotent_iff_norm_lt_one_of_isPowMul fun f n _ ↦ norm_pow f n

/-- **The canonical reduction of `K⟨X⟩` is the polynomial algebra `𝓀[K][X]`.** -/
noncomputable def canonicalReductionAlgEquiv :
    Huber.CanonicalReduction T ≃ₐ[𝓀[K]] MvPolynomial σ 𝓀[K] :=
  let e₀ : Huber.powerBoundedSubring T ≃+* T° :=
    RingEquiv.subringCongr (powerBoundedSubring_eq_unitClosedBall (σ := σ) (K := K))
  have hmap : Ideal.map (e₀ : _ →+* _) (Huber.topologicallyNilpotentIdeal T) =
      RingHom.ker (restrictedReduction (σ := σ) (K := K)) := by
    rw [Ideal.map_comap_of_equiv e₀]
    ext g
    rw [Ideal.mem_comap, Huber.mem_topologicallyNilpotentIdeal,
      isTopologicallyNilpotent_iff_norm_lt_one, mem_ker_restrictedReduction]
    exact Iff.of_eq (by rw [RingEquiv.subringCongr_symm, RingEquiv.coe_subringCongr_apply])
  AlgEquiv.ofRingEquiv
    (f := (Ideal.quotientEquiv _ _ e₀ hmap.symm).trans restrictedReductionQuotientEquiv)
    fun x ↦ by
      obtain ⟨c, rfl⟩ := residue_surjective (R := 𝒪[K]) x
      have hc : algebraMap K T c ∈ T° := Subring.mem_unitClosedBall.mpr
        ((norm_algebraMap_isRestrictedSubring (c : K)).trans_le (Valued.integer.norm_le_one c))
      rw [Huber.algebraMap_canonicalReduction_residue, RingEquiv.trans_apply,
        Ideal.quotientEquiv_mk, restrictedReductionQuotientEquiv_mk]
      have he₀ : e₀ (Huber.integerToPowerBounded K T c) = ⟨algebraMap K T c, hc⟩ :=
        Subtype.ext ((RingEquiv.coe_subringCongr_apply _ _).trans
          (Huber.coe_integerToPowerBounded c))
      rw [he₀, restrictedReduction_algebraMap c hc, MvPolynomial.algebraMap_eq]

@[simp]
theorem canonicalReductionAlgEquiv_mk (f : Huber.powerBoundedSubring T) :
    canonicalReductionAlgEquiv (Ideal.Quotient.mk (Huber.topologicallyNilpotentIdeal T) f) =
      restrictedReduction
        ⟨f.val, (powerBoundedSubring_eq_unitClosedBall (σ := σ) (K := K)).le f.property⟩ := by
  rw [canonicalReductionAlgEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    Ideal.quotientEquiv_mk, restrictedReductionQuotientEquiv_mk]
  exact congrArg restrictedReduction (Subtype.ext (RingEquiv.coe_subringCongr_apply _ f))

/-- The canonical reduction of a Tate algebra `K⟨X⟩` is a domain. -/
instance isDomain_canonicalReduction : IsDomain (Huber.CanonicalReduction T) :=
  (canonicalReductionAlgEquiv (σ := σ) (K := K)).toMulEquiv.isDomain _

/-- For finitely many variables, the canonical reduction of a Tate algebra `K⟨X⟩` is a
finite-type `𝓀[K]`-algebra. -/
instance finiteType_canonicalReduction [Finite σ] :
    Algebra.FiniteType 𝓀[K] (Huber.CanonicalReduction T) :=
  .of_surjective (canonicalReductionAlgEquiv (σ := σ) (K := K)).symm.toAlgHom
    (canonicalReductionAlgEquiv (σ := σ) (K := K)).symm.surjective

/-- For finitely many variables, the canonical reduction of a Tate algebra `K⟨X⟩` is Noetherian. -/
instance isNoetherianRing_canonicalReduction [Finite σ] :
    IsNoetherianRing (Huber.CanonicalReduction T) :=
  Algebra.FiniteType.isNoetherianRing 𝓀[K] (Huber.CanonicalReduction T)

end PowerBounded

end TauCeti.MvPowerSeries
