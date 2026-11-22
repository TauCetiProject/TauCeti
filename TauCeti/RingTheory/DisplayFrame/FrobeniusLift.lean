/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import TauCeti.RingTheory.DeltaRing.PowerSeries
public import TauCeti.RingTheory.DisplayFrame.Basic
public import TauCeti.RingTheory.PowerSeries.Jacobson
public import TauCeti.RingTheory.WittVector.Frobenius
public import TauCeti.RingTheory.WittVector.Units

/-!
# The `p`-frame of a `p`-torsion-free ring with a Frobenius lift

Let `S` be a commutative ring in which `p` is a non-zero-divisor and lies in the Jacobson radical,
and let `φ` be a ring endomorphism of `S` lifting the `p`-th power map modulo `p`. Then
`(S, p S, φ, φ₁)` with `φ₁ (p a) = φ a` is a `p`-frame (`TauCeti.DisplayFrame.ofFrobeniusLift`):
`φ₁` is well defined because `p` is a non-zero-divisor, and `φ₁ p = 1` generates `S`.

A ring homomorphism intertwining two such Frobenius lifts is a strict homomorphism of the frames
(`TauCeti.DisplayFrame.Hom.ofFrobeniusLift`). Two instances are the coefficient frames of
Dieudonné theory over a perfect ring and of Breuil–Kisin theory:

* For a perfect ring `R` of characteristic `p`, the Witt frame `(W(R), V W(R), F, V⁻¹)`
  (`TauCeti.DisplayFrame.wittVector`). Its ideal `p W(R)` is the image of the Verschiebung
  (`WittVector.mem_span_p_iff_exists_verschiebung`) and its divided Frobenius is
  the inverse of the Verschiebung (`TauCeti.DisplayFrame.wittVector_divFrobenius_verschiebung`).
  Over a perfect field `k` this is the frame `D_k` whose displays are Dieudonné modules.
* For the same `R`, the Breuil–Kisin frame `(W(R)⟦u⟧, p W(R)⟦u⟧, φ, φ / p)` with `φ` the
  Witt-vector Frobenius on coefficients and `φ(u) = u ^ p`
  (`TauCeti.DisplayFrame.wittVectorPowerSeries`), obtained from the general power-series frame
  `TauCeti.DisplayFrame.powerSeries`. Its divided Frobenius sends `p u` to `u ^ p`, not to
  `p u ^ p`.

## Main definitions

* `TauCeti.DisplayFrame.ofFrobeniusLift`: the `p`-frame `(S, p S, φ, φ / p)`.
* `TauCeti.DisplayFrame.wittVector`: the Witt frame of a perfect ring.
* `TauCeti.DisplayFrame.powerSeries`: the `p`-frame of `A⟦u⟧` with `φ(u) = u ^ p`, for a
  `p`-torsion-free ring `A` with a Frobenius lift and `p` in its Jacobson radical.
* `TauCeti.DisplayFrame.wittVectorPowerSeries`: the Breuil–Kisin frame `W(R)⟦u⟧`.
* `TauCeti.DisplayFrame.Hom.ofFrobeniusLift`: the strict homomorphism given by a ring homomorphism
  intertwining Frobenius lifts; for instance the reduction `u ↦ 0`
  (`TauCeti.DisplayFrame.powerSeriesConstantCoeff`).

## Main results

* `TauCeti.DisplayFrame.ofFrobeniusLift_divFrobenius_natCast_mul`: `φ₁ (p a) = φ a`.
* `TauCeti.DisplayFrame.isPFrame_ofFrobeniusLift`: these frames are `p`-frames.

## References

* E. Lau, *Relations between Dieudonné displays and crystalline Dieudonné theory*, Algebra Number
  Theory 8 (2014), §2A, p. 2214, and Lemma 2.4, p. 2216.
* M. Kisin, G. Pappas and R. Zhou, *Integral models of Shimura varieties with parahoric level
  structure, II*, §5.1.2.
-/

public section

open scoped PowerSeries

namespace TauCeti.DisplayFrame

universe u

section FrobeniusLift

variable {p : ℕ} {S : Type u} [CommRing S]

/-- Multiplication by a non-zero-divisor `p` identifies `S` with the ideal `p S`. -/
private noncomputable def natCastSpanEquiv (hp : IsRegular (p : S)) :
    S ≃ₗ[S] Ideal.span {(p : S)} :=
  (LinearEquiv.ofInjective (LinearMap.toSpanSingleton S S (p : S)) fun a b h ↦
      hp.right (by simpa using h)).trans
    (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range S S (p : S)).symm)

private theorem coe_natCastSpanEquiv (hp : IsRegular (p : S)) (a : S) :
    (natCastSpanEquiv hp a : S) = a * p :=
  (rfl)

/-- The `p`-frame `(S, p S, φ, φ₁)` with `φ₁ (p a) = φ a`, for a ring `S` in which `p` is a
non-zero-divisor lying in the Jacobson radical and a Frobenius lift `φ` of `S`. -/
noncomputable def ofFrobeniusLift (hp : IsRegular (p : S)) (hjac : (p : S) ∈ Ring.jacobson S)
    (φ : S →+* S) (hφ : DeltaRing.IsFrobeniusLift p φ) : DisplayFrame p (Ideal.span {(p : S)}) where
  frobenius := φ
  divFrobenius := φ.toSemilinearMap ∘ₛₗ (natCastSpanEquiv hp).symm.toLinearMap
  isFrobeniusLift := hφ
  sup_span_le_jacobson := by
    rwa [sup_idem, Ideal.span_le, Set.singleton_subset_iff]
  span_range_divFrobenius := by
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨natCastSpanEquiv hp 1, ?_⟩) isUnit_one
    simp

variable (hp : IsRegular (p : S)) (hjac : (p : S) ∈ Ring.jacobson S) (φ : S →+* S)
  (hφ : DeltaRing.IsFrobeniusLift p φ)

@[simp]
theorem ofFrobeniusLift_frobenius : (ofFrobeniusLift hp hjac φ hφ).frobenius = φ :=
  (rfl)

private theorem ofFrobeniusLift_divFrobenius_apply (x : Ideal.span {(p : S)}) :
    (ofFrobeniusLift hp hjac φ hφ).divFrobenius x = φ ((natCastSpanEquiv hp).symm x) :=
  (rfl)

/-- The divided Frobenius of `ofFrobeniusLift` sends `p a` to `φ a`. -/
@[simp]
theorem ofFrobeniusLift_divFrobenius_natCast_mul (a : S) :
    (ofFrobeniusLift hp hjac φ hφ).divFrobenius
      ⟨p * a, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self _)⟩ = φ a := by
  have : (⟨p * a, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self _)⟩ :
      Ideal.span {(p : S)}) = natCastSpanEquiv hp a :=
    Subtype.ext (by rw [coe_natCastSpanEquiv]; exact mul_comm _ _)
  rw [this, ofFrobeniusLift_divFrobenius_apply, LinearEquiv.symm_apply_apply]

/-- The divided Frobenius of `ofFrobeniusLift` is determined by `p φ₁ x = φ x`. -/
theorem natCast_mul_ofFrobeniusLift_divFrobenius (x : Ideal.span {(p : S)}) :
    p * (ofFrobeniusLift hp hjac φ hφ).divFrobenius x = φ x := by
  have h := congrArg φ (coe_natCastSpanEquiv hp ((natCastSpanEquiv hp).symm x))
  rw [LinearEquiv.apply_symm_apply, map_mul, map_natCast] at h
  rw [ofFrobeniusLift_divFrobenius_apply, h, mul_comm]

/-- `ofFrobeniusLift` is a `p`-frame. -/
theorem isPFrame_ofFrobeniusLift : (ofFrobeniusLift hp hjac φ hφ).IsPFrame := by
  rw [isPFrame_iff]
  intro x
  rw [natCast_mul_ofFrobeniusLift_divFrobenius, ofFrobeniusLift_frobenius]

@[simp]
theorem constant_ofFrobeniusLift : (ofFrobeniusLift hp hjac φ hφ).constant = p :=
  (isPFrame_iff_constant_eq _).mp (isPFrame_ofFrobeniusLift hp hjac φ hφ)

variable {S' : Type*} [CommRing S'] {hp' : IsRegular (p : S')} {hjac' : (p : S') ∈ Ring.jacobson S'}
  {φ' : S' →+* S'} {hφ' : DeltaRing.IsFrobeniusLift p φ'}

variable {hp hjac φ hφ} in
/-- A ring homomorphism intertwining the Frobenius lifts is a strict homomorphism of the
`p`-frames `ofFrobeniusLift`. -/
noncomputable def Hom.ofFrobeniusLift (f : S →+* S') (hf : ∀ s, f (φ s) = φ' (f s)) :
    Hom (ofFrobeniusLift hp hjac φ hφ) (ofFrobeniusLift hp' hjac' φ' hφ') where
  toRingHom := f
  map_mem' a ha := by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  map_frobenius' := hf
  map_divFrobenius' a := hp'.left <| by
    beta_reduce
    have h := congrArg f (natCast_mul_ofFrobeniusLift_divFrobenius hp hjac φ hφ a)
    rw [map_mul, map_natCast, hf] at h
    rw [natCast_mul_ofFrobeniusLift_divFrobenius, h]

variable {hp hjac φ hφ} in
@[simp]
theorem Hom.coe_ofFrobeniusLift (f : S →+* S') (hf : ∀ s, f (φ s) = φ' (f s)) :
    ⇑(Hom.ofFrobeniusLift (hp := hp) (hjac := hjac) (hφ := hφ) (hp' := hp') (hjac' := hjac')
      (hφ' := hφ') f hf) = f :=
  (rfl)

end FrobeniusLift

section WittVector

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p] [PerfectRing R p]

/-- The Witt frame `(W(R), p W(R), F, F / p)` of a perfect ring `R` of characteristic `p`. Its
ideal is the image `V W(R)` of the Verschiebung, and its divided Frobenius is the inverse of the
Verschiebung (`TauCeti.DisplayFrame.wittVector_divFrobenius_verschiebung`). -/
noncomputable def wittVector : DisplayFrame p (Ideal.span {(p : WittVector p R)}) :=
  ofFrobeniusLift WittVector.isRegular_natCast WittVector.natCast_mem_jacobson
    WittVector.frobenius ⟨WittVector.natCast_dvd_frobenius_sub_pow⟩

@[simp]
theorem wittVector_frobenius : (wittVector p R).frobenius = WittVector.frobenius :=
  (rfl)

theorem isPFrame_wittVector : (wittVector p R).IsPFrame :=
  isPFrame_ofFrobeniusLift ..

variable {p R}

/-- The divided Frobenius of the Witt frame inverts the Verschiebung: `φ₁ (V x) = x`. -/
@[simp]
theorem wittVector_divFrobenius_verschiebung (x : WittVector p R) :
    (wittVector p R).divFrobenius
      ⟨WittVector.verschiebung x, WittVector.mem_span_p_iff_exists_verschiebung.mpr ⟨x, rfl⟩⟩ =
        x := by
  have : (⟨WittVector.verschiebung x,
        WittVector.mem_span_p_iff_exists_verschiebung.mpr ⟨x, rfl⟩⟩ :
        Ideal.span {(p : WittVector p R)}) =
      ⟨p * (WittVector.frobeniusEquiv p R).symm x,
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)⟩ :=
    Subtype.ext ((WittVector.verschiebung_eq_frobeniusEquiv_symm_mul x).trans (mul_comm _ _))
  rw [this, wittVector, ofFrobeniusLift_divFrobenius_natCast_mul,
    ← WittVector.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

end WittVector

section PowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {A : Type u} [CommRing A]

/-- The `p`-frame `(A⟦u⟧, p A⟦u⟧, φ, φ / p)`, where `φ` applies a Frobenius lift `σ` of `A` to the
coefficients and sends `u` to `u ^ p`, for a ring `A` in which `p` is a non-zero-divisor lying in
the Jacobson radical. -/
noncomputable def powerSeries (hpA : IsRegular (p : A)) (hjac : (p : A) ∈ Ring.jacobson A)
    (σ : A →+* A) (hσ : DeltaRing.IsFrobeniusLift p σ) :
    DisplayFrame p (Ideal.span {(p : A⟦X⟧)}) :=
  ofFrobeniusLift
    (isRegular_iff_mem_nonZeroDivisors.mpr <| MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff <|
      by rwa [map_natCast, ← isRegular_iff_mem_nonZeroDivisors])
    (by rwa [← map_natCast (PowerSeries.C (R := A)), PowerSeries.C_mem_jacobson_iff])
    ((PowerSeries.map σ).comp (PowerSeries.expand p hp.out.ne_zero : A⟦X⟧ →ₐ[A] A⟦X⟧))
    hσ.powerSeries

variable (hpA : IsRegular (p : A)) (hjac : (p : A) ∈ Ring.jacobson A) (σ : A →+* A)
  (hσ : DeltaRing.IsFrobeniusLift p σ)

/-- The Frobenius of `powerSeries` applies `σ` to the coefficients and substitutes `u ^ p` for
`u`. -/
theorem powerSeries_frobenius_apply (f : A⟦X⟧) :
    (powerSeries hpA hjac σ hσ).frobenius f =
      PowerSeries.map σ (PowerSeries.expand p hp.out.ne_zero f) :=
  (rfl)

@[simp]
theorem powerSeries_frobenius_C (a : A) :
    (powerSeries hpA hjac σ hσ).frobenius (PowerSeries.C a) = PowerSeries.C (σ a) := by
  simp [powerSeries, PowerSeries.expand_C]

@[simp]
theorem powerSeries_frobenius_X :
    (powerSeries hpA hjac σ hσ).frobenius PowerSeries.X = PowerSeries.X ^ p := by
  simp [powerSeries]

theorem isPFrame_powerSeries : (powerSeries hpA hjac σ hσ).IsPFrame :=
  isPFrame_ofFrobeniusLift ..

/-- The reduction `u ↦ 0`, a strict homomorphism from the frame `A⟦u⟧` to the frame `A`. -/
noncomputable def powerSeriesConstantCoeff :
    Hom (powerSeries hpA hjac σ hσ) (ofFrobeniusLift hpA hjac σ hσ) :=
  Hom.ofFrobeniusLift PowerSeries.constantCoeff fun f ↦ by
    rw [RingHom.comp_apply, RingHom.coe_coe, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_expand]

@[simp]
theorem coe_powerSeriesConstantCoeff :
    ⇑(powerSeriesConstantCoeff hpA hjac σ hσ) = PowerSeries.constantCoeff :=
  (rfl)

/-- The divided Frobenius of `powerSeries` sends `p f` to `φ f`; in particular `p u ↦ u ^ p`. -/
@[simp]
theorem powerSeries_divFrobenius_natCast_mul (f : A⟦X⟧) :
    (powerSeries hpA hjac σ hσ).divFrobenius
      ⟨p * f, Ideal.mul_mem_right f _ (Ideal.mem_span_singleton_self _)⟩ =
        (powerSeries hpA hjac σ hσ).frobenius f :=
  ofFrobeniusLift_divFrobenius_natCast_mul ..

end PowerSeries

section WittVectorPowerSeries

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p] [PerfectRing R p]

/-- The Breuil–Kisin frame `(W(R)⟦u⟧, p W(R)⟦u⟧, φ, φ / p)` of a perfect ring `R` of
characteristic `p`, with `φ` the Witt-vector Frobenius on coefficients and `φ(u) = u ^ p`. -/
noncomputable def wittVectorPowerSeries : DisplayFrame p (Ideal.span {(p : (WittVector p R)⟦X⟧)}) :=
  powerSeries WittVector.isRegular_natCast WittVector.natCast_mem_jacobson
    WittVector.frobenius ⟨WittVector.natCast_dvd_frobenius_sub_pow⟩

theorem isPFrame_wittVectorPowerSeries : (wittVectorPowerSeries p R).IsPFrame :=
  isPFrame_powerSeries ..

@[simp]
theorem wittVectorPowerSeries_frobenius_C (a : WittVector p R) :
    (wittVectorPowerSeries p R).frobenius (PowerSeries.C a) =
      PowerSeries.C (WittVector.frobenius a) :=
  powerSeries_frobenius_C ..

@[simp]
theorem wittVectorPowerSeries_frobenius_X :
    (wittVectorPowerSeries p R).frobenius PowerSeries.X = PowerSeries.X ^ p :=
  powerSeries_frobenius_X ..

/-- The reduction `u ↦ 0`, a strict homomorphism from the Breuil–Kisin frame `W(R)⟦u⟧` to the
Witt frame `W(R)`. -/
noncomputable def wittVectorPowerSeriesConstantCoeff :
    Hom (wittVectorPowerSeries p R) (wittVector p R) :=
  powerSeriesConstantCoeff ..

@[simp]
theorem coe_wittVectorPowerSeriesConstantCoeff :
    ⇑(wittVectorPowerSeriesConstantCoeff p R) = PowerSeries.constantCoeff :=
  (rfl)

/-- The divided Frobenius of the Breuil–Kisin frame sends `p u` to `u ^ p`. -/
theorem wittVectorPowerSeries_divFrobenius_natCast_mul_X :
    (wittVectorPowerSeries p R).divFrobenius
      ⟨(p : (WittVector p R)⟦X⟧) * PowerSeries.X,
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)⟩ =
        PowerSeries.X ^ p := by
  rw [wittVectorPowerSeries, powerSeries_divFrobenius_natCast_mul, powerSeries_frobenius_X]

end WittVectorPowerSeries

end TauCeti.DisplayFrame
