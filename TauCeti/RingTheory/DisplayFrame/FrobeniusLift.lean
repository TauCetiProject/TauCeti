/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import TauCeti.LinearAlgebra.Span.Basic
public import TauCeti.RingTheory.DeltaRing.PowerSeries
public import TauCeti.RingTheory.DisplayFrame.Basic
public import TauCeti.RingTheory.PowerSeries.Jacobson
public import TauCeti.RingTheory.WittVector.Frobenius
public import TauCeti.RingTheory.WittVector.TeichmullerCoeff
public import TauCeti.RingTheory.WittVector.Units

/-!
# The `p`-frame of a `p`-torsion-free ring with a Frobenius lift

Let `S` be a commutative ring in which `p` is a non-zero-divisor and lies in the Jacobson radical,
and let `φ` be a ring endomorphism of `S` lifting the `p`-th power map modulo `p`. Then
`(S, p S, φ, φ₁)` with `φ₁ (p a) = φ a` is a `p`-frame (`TauCeti.DisplayFrame.ofFrobeniusLift`):
`φ₁` is well defined because `p` is a non-zero-divisor, so that `a ↦ p a` identifies `S` with
`p S` (`LinearEquiv.toSpanSingletonOfInjective`), and `φ₁ p = 1` generates `S`.

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

* `TauCeti.DisplayFrame.ofFrobeniusLift_divFrobenius_natCast_mul`: `φ₁ (p a) = φ a`, and its
  instances `TauCeti.DisplayFrame.wittVector_divFrobenius_natCast_mul`,
  `TauCeti.DisplayFrame.powerSeries_divFrobenius_natCast_mul` and
  `TauCeti.DisplayFrame.wittVectorPowerSeries_divFrobenius_natCast_mul`.
* `TauCeti.DisplayFrame.isPFrame_ofFrobeniusLift`: these frames are `p`-frames, with frame
  constant `p` (`TauCeti.DisplayFrame.constant_ofFrobeniusLift`, and its instances
  `TauCeti.DisplayFrame.constant_wittVector`, `TauCeti.DisplayFrame.constant_powerSeries` and
  `TauCeti.DisplayFrame.constant_wittVectorPowerSeries`).

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

/-- The `p`-frame `(S, p S, φ, φ₁)` with `φ₁ (p a) = φ a`, for a ring `S` in which `p` is a
non-zero-divisor lying in the Jacobson radical and a Frobenius lift `φ` of `S`. -/
noncomputable def ofFrobeniusLift (hp : IsRegular (p : S)) (hjac : (p : S) ∈ Ring.jacobson S)
    (φ : S →+* S) (hφ : DeltaRing.IsFrobeniusLift p φ) : DisplayFrame p (Ideal.span {(p : S)}) where
  frobenius := φ
  divFrobenius :=
    φ.toSemilinearMap ∘ₛₗ (LinearEquiv.toSpanSingletonOfInjective (p : S) hp.right).symm.toLinearMap
  isFrobeniusLift := hφ
  sup_span_le_jacobson := by
    rwa [sup_idem, Ideal.span_le, Set.singleton_subset_iff]
  span_range_divFrobenius := by
    refine Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span ⟨LinearEquiv.toSpanSingletonOfInjective (p : S) hp.right 1, ?_⟩) isUnit_one
    simp

variable (hp : IsRegular (p : S)) (hjac : (p : S) ∈ Ring.jacobson S) (φ : S →+* S)
  (hφ : DeltaRing.IsFrobeniusLift p φ)

@[simp]
theorem ofFrobeniusLift_frobenius : (ofFrobeniusLift hp hjac φ hφ).frobenius = φ :=
  (rfl)

/-- The divided Frobenius of `ofFrobeniusLift` divides by `p` and then applies `φ`. -/
theorem ofFrobeniusLift_divFrobenius_apply (x : Ideal.span {(p : S)}) :
    (ofFrobeniusLift hp hjac φ hφ).divFrobenius x =
      φ ((LinearEquiv.toSpanSingletonOfInjective (p : S) hp.right).symm x) :=
  (rfl)

/-- The divided Frobenius of `ofFrobeniusLift` sends `p a` to `φ a`. -/
@[simp]
theorem ofFrobeniusLift_divFrobenius_natCast_mul (a : S) :
    (ofFrobeniusLift hp hjac φ hφ).divFrobenius
      ⟨p * a, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self _)⟩ = φ a := by
  have : (⟨p * a, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self _)⟩ :
      Ideal.span {(p : S)}) =
        ⟨a • (p : S), Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)⟩ :=
    Subtype.ext (mul_comm _ _)
  rw [this, ofFrobeniusLift_divFrobenius_apply,
    LinearEquiv.toSpanSingletonOfInjective_symm_mk_smul]

/-- The divided Frobenius of `ofFrobeniusLift` is determined by `p φ₁ x = φ x`. -/
theorem natCast_mul_ofFrobeniusLift_divFrobenius (x : Ideal.span {(p : S)}) :
    p * (ofFrobeniusLift hp hjac φ hφ).divFrobenius x = φ x := by
  have h := congrArg φ
    (LinearEquiv.toSpanSingletonOfInjective_symm_apply_smul (p : S) hp.right x)
  rw [smul_eq_mul, map_mul, map_natCast] at h
  rw [ofFrobeniusLift_divFrobenius_apply, mul_comm, h]

/-- `ofFrobeniusLift` is a `p`-frame. -/
theorem isPFrame_ofFrobeniusLift : (ofFrobeniusLift hp hjac φ hφ).IsPFrame := by
  rw [isPFrame_iff]
  intro x
  rw [natCast_mul_ofFrobeniusLift_divFrobenius, ofFrobeniusLift_frobenius]

/-- The frame constant of `ofFrobeniusLift` is `p`. -/
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
  ofFrobeniusLift (isRegular_iff_mem_nonZeroDivisors.mpr WittVector.p_mem_nonZeroDivisors)
    WittVector.natCast_mem_jacobson WittVector.frobenius ⟨WittVector.natCast_dvd_frobenius_sub_pow⟩

/-- The Witt frame is the `p`-frame `ofFrobeniusLift` of the Witt-vector Frobenius. -/
theorem wittVector_eq_ofFrobeniusLift :
    wittVector p R =
      ofFrobeniusLift (isRegular_iff_mem_nonZeroDivisors.mpr WittVector.p_mem_nonZeroDivisors)
        WittVector.natCast_mem_jacobson WittVector.frobenius
        ⟨WittVector.natCast_dvd_frobenius_sub_pow⟩ :=
  (rfl)

@[simp]
theorem wittVector_frobenius : (wittVector p R).frobenius = WittVector.frobenius :=
  (rfl)

/-- The Witt frame is a `p`-frame. -/
theorem isPFrame_wittVector : (wittVector p R).IsPFrame :=
  isPFrame_ofFrobeniusLift ..

/-- The frame constant of the Witt frame is `p`. -/
@[simp]
theorem constant_wittVector : (wittVector p R).constant = p :=
  constant_ofFrobeniusLift ..

variable {p R}

/-- The divided Frobenius of the Witt frame sends `p a` to `F a`. -/
@[simp]
theorem wittVector_divFrobenius_natCast_mul (a : WittVector p R) :
    (wittVector p R).divFrobenius
      ⟨p * a, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self _)⟩ =
        WittVector.frobenius a :=
  ofFrobeniusLift_divFrobenius_natCast_mul ..

/-- The divided Frobenius of the Witt frame is determined by `p φ₁ x = F x`. -/
theorem natCast_mul_wittVector_divFrobenius (x : Ideal.span {(p : WittVector p R)}) :
    p * (wittVector p R).divFrobenius x = WittVector.frobenius (x : WittVector p R) :=
  natCast_mul_ofFrobeniusLift_divFrobenius ..

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
  rw [this, wittVector_divFrobenius_natCast_mul, WittVector.frobenius_frobeniusEquiv_symm]

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

/-- The power-series frame is the `p`-frame `ofFrobeniusLift` of its Frobenius lift. -/
theorem powerSeries_eq_ofFrobeniusLift (hp' : IsRegular (p : A⟦X⟧))
    (hjac' : (p : A⟦X⟧) ∈ Ring.jacobson A⟦X⟧) :
    powerSeries hpA hjac σ hσ =
      ofFrobeniusLift hp' hjac'
        ((PowerSeries.map σ).comp (PowerSeries.expand p hp.out.ne_zero : A⟦X⟧ →ₐ[A] A⟦X⟧))
        hσ.powerSeries :=
  (rfl)

/-- The Frobenius of `powerSeries` applies `σ` to the coefficients and substitutes `u ^ p` for
`u`. -/
theorem powerSeries_frobenius_apply (f : A⟦X⟧) :
    (powerSeries hpA hjac σ hσ).frobenius f =
      PowerSeries.map σ (PowerSeries.expand p hp.out.ne_zero f) :=
  (rfl)

@[simp]
theorem powerSeries_frobenius_C (a : A) :
    (powerSeries hpA hjac σ hσ).frobenius (PowerSeries.C a) = PowerSeries.C (σ a) := by
  rw [powerSeries_frobenius_apply, PowerSeries.expand_C, PowerSeries.map_C]

@[simp]
theorem powerSeries_frobenius_X :
    (powerSeries hpA hjac σ hσ).frobenius PowerSeries.X = PowerSeries.X ^ p := by
  rw [powerSeries_frobenius_apply, PowerSeries.expand_X, map_pow, PowerSeries.map_X]

/-- The power-series frame `A⟦u⟧` is a `p`-frame. -/
theorem isPFrame_powerSeries : (powerSeries hpA hjac σ hσ).IsPFrame :=
  isPFrame_ofFrobeniusLift ..

/-- The frame constant of the power-series frame `A⟦u⟧` is `p`. -/
@[simp]
theorem constant_powerSeries : (powerSeries hpA hjac σ hσ).constant = p :=
  constant_ofFrobeniusLift ..

/-- The reduction `u ↦ 0`, a strict homomorphism from the frame `A⟦u⟧` to the frame `A`. -/
noncomputable def powerSeriesConstantCoeff :
    Hom (powerSeries hpA hjac σ hσ) (ofFrobeniusLift hpA hjac σ hσ) :=
  Hom.ofFrobeniusLift PowerSeries.constantCoeff fun f ↦ by
    simpa using PowerSeries.coeff_map σ 0 (PowerSeries.expand p hp.out.ne_zero f)

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

/-- The divided Frobenius of `powerSeries` is determined by `p φ₁ x = φ x`. -/
theorem natCast_mul_powerSeries_divFrobenius (x : Ideal.span {(p : A⟦X⟧)}) :
    p * (powerSeries hpA hjac σ hσ).divFrobenius x = (powerSeries hpA hjac σ hσ).frobenius x :=
  natCast_mul_ofFrobeniusLift_divFrobenius ..

end PowerSeries

section WittVectorPowerSeries

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p] [PerfectRing R p]

/-- The Breuil–Kisin frame `(W(R)⟦u⟧, p W(R)⟦u⟧, φ, φ / p)` of a perfect ring `R` of
characteristic `p`, with `φ` the Witt-vector Frobenius on coefficients and `φ(u) = u ^ p`. -/
noncomputable def wittVectorPowerSeries : DisplayFrame p (Ideal.span {(p : (WittVector p R)⟦X⟧)}) :=
  powerSeries (isRegular_iff_mem_nonZeroDivisors.mpr WittVector.p_mem_nonZeroDivisors)
    WittVector.natCast_mem_jacobson WittVector.frobenius ⟨WittVector.natCast_dvd_frobenius_sub_pow⟩

/-- The Breuil–Kisin frame is the power-series frame over the Witt frame's Frobenius lift. -/
theorem wittVectorPowerSeries_eq_powerSeries :
    wittVectorPowerSeries p R =
      powerSeries (isRegular_iff_mem_nonZeroDivisors.mpr WittVector.p_mem_nonZeroDivisors)
        WittVector.natCast_mem_jacobson WittVector.frobenius
        ⟨WittVector.natCast_dvd_frobenius_sub_pow⟩ :=
  (rfl)

/-- The Breuil–Kisin frame `W(R)⟦u⟧` is a `p`-frame. -/
theorem isPFrame_wittVectorPowerSeries : (wittVectorPowerSeries p R).IsPFrame :=
  isPFrame_powerSeries ..

/-- The frame constant of the Breuil–Kisin frame `W(R)⟦u⟧` is `p`. -/
@[simp]
theorem constant_wittVectorPowerSeries : (wittVectorPowerSeries p R).constant = p :=
  constant_powerSeries ..

/-- The Frobenius of the Breuil–Kisin frame applies the Witt-vector Frobenius to the coefficients
and substitutes `u ^ p` for `u`. -/
theorem wittVectorPowerSeries_frobenius_apply (f : (WittVector p R)⟦X⟧) :
    (wittVectorPowerSeries p R).frobenius f =
      PowerSeries.map WittVector.frobenius (PowerSeries.expand p (Fact.out : p.Prime).ne_zero f) :=
  powerSeries_frobenius_apply ..

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

/-- The divided Frobenius of the Breuil–Kisin frame sends `p f` to `φ f`. -/
@[simp]
theorem wittVectorPowerSeries_divFrobenius_natCast_mul (f : (WittVector p R)⟦X⟧) :
    (wittVectorPowerSeries p R).divFrobenius
      ⟨p * f, Ideal.mul_mem_right f _ (Ideal.mem_span_singleton_self _)⟩ =
        (wittVectorPowerSeries p R).frobenius f :=
  powerSeries_divFrobenius_natCast_mul ..

/-- The divided Frobenius of the Breuil–Kisin frame is determined by `p φ₁ x = φ x`. -/
theorem natCast_mul_wittVectorPowerSeries_divFrobenius
    (x : Ideal.span {(p : (WittVector p R)⟦X⟧)}) :
    p * (wittVectorPowerSeries p R).divFrobenius x = (wittVectorPowerSeries p R).frobenius x :=
  natCast_mul_powerSeries_divFrobenius ..

/-- The divided Frobenius of the Breuil–Kisin frame sends `p u` to `u ^ p`. -/
theorem wittVectorPowerSeries_divFrobenius_natCast_mul_X :
    (wittVectorPowerSeries p R).divFrobenius
      ⟨(p : (WittVector p R)⟦X⟧) * PowerSeries.X,
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)⟩ =
        PowerSeries.X ^ p := by
  rw [wittVectorPowerSeries_divFrobenius_natCast_mul, wittVectorPowerSeries_frobenius_X]

end WittVectorPowerSeries

end TauCeti.DisplayFrame
