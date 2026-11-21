/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Complete

/-!
# Functoriality and reduction modulo `p` of truncated Witt vectors

This file supplies the basic structure of the ring `W_n(R) = TruncatedWittVector p n R` used to
study modules over it with a Frobenius.

A ring homomorphism `f : R →+* S` induces a ring homomorphism `W_n(R) →+* W_n(S)` acting on Witt
coordinates by `f`, compatibly with truncation from `W(R)`. For `R` of characteristic `p` the
Witt-vector Frobenius of `W_n(R)` is `TruncatedWittVector.map (frobenius R p)`
(`TruncatedWittVector.map_frobenius_truncate`), and for perfect `R`
it is the automorphism `TruncatedWittVector.mapEquiv (frobeniusEquiv R p)`.

For `n ≠ 0` the zeroth coordinate is a ring homomorphism `W_n(R) →+* R`. When `R` has
characteristic `p`, the ring `W_n(R)` has characteristic `p ^ n`, and when moreover `R` is perfect,
the kernel of the zeroth coordinate is the ideal `(p)`, so that `W_n(R) ⧸ (p) ≃+* R`. These are the
truncated analogues of `WittVector.ker_constantCoeff` and `WittVector.quotientPEquiv`.

## Main definitions

* `TruncatedWittVector.map`: the ring homomorphism `W_n(R) →+* W_n(S)` induced by `R →+* S`.
* `TruncatedWittVector.mapEquiv`: the ring isomorphism induced by a ring isomorphism.
* `TruncatedWittVector.constantCoeff`: the zeroth coordinate `W_n(R) →+* R`, for `n ≠ 0`.
* `TruncatedWittVector.quotientPEquiv`: the isomorphism `W_n(R) ⧸ (p) ≃+* R` for a perfect ring
  `R` of characteristic `p` and `n ≠ 0`.

## Main results

* `TruncatedWittVector.charP`: `W_n(R)` has characteristic `p ^ n` when `R` has
  characteristic `p`.
* `TruncatedWittVector.ker_constantCoeff`: for perfect `R` of characteristic `p`, the kernel of
  the zeroth coordinate is `(p)`.
* `TruncatedWittVector.charP_quotient` and `TruncatedWittVector.perfectRing_quotient`: for
  `n ≠ 0`, `W_n(R) ⧸ (p)` has characteristic `p`, and it is perfect when `R` is.
-/

public section

namespace TruncatedWittVector

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ} {R S T : Type*} [CommRing R] [CommRing S]
  [CommRing T]

section Map

/-- The ring homomorphism of truncated Witt vectors induced by a ring homomorphism `f`, acting on
Witt coordinates by `f`. -/
noncomputable def map (f : R →+* S) : TruncatedWittVector p n R →+* TruncatedWittVector p n S :=
  (WittVector.truncate n).liftOfSurjective (WittVector.truncate_surjective p n R)
    ⟨(WittVector.truncate n).comp (WittVector.map f), fun x hx ↦ by
      rw [WittVector.mem_ker_truncate] at hx
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, WittVector.mem_ker_truncate]
      intro i hi
      rw [WittVector.map_coeff, hx i hi, map_zero]⟩

@[simp]
theorem map_truncate (f : R →+* S) (x : WittVector p R) :
    map f (WittVector.truncate n x) = WittVector.truncate n (WittVector.map f x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

@[simp]
theorem coeff_map (f : R →+* S) (x : TruncatedWittVector p n R) (i : Fin n) :
    (map f x).coeff i = f (x.coeff i) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [WittVector.map_coeff]

@[simp]
theorem map_id : map (RingHom.id R) = RingHom.id (TruncatedWittVector p n R) :=
  RingHom.ext fun x ↦ ext fun i ↦ by simp

theorem map_map (g : S →+* T) (f : R →+* S) (x : TruncatedWittVector p n R) :
    map g (map f x) = map (g.comp f) x :=
  ext fun i ↦ by simp

/-- The Witt vector Frobenius of `W(R)` descends to `TruncatedWittVector.map (frobenius R p)` on
`W_n(R)` for `R` of characteristic `p`. -/
theorem map_frobenius_truncate [CharP R p] (x : WittVector p R) :
    map (frobenius R p) (WittVector.truncate n x) =
      WittVector.truncate n (WittVector.frobenius x) := by
  rw [map_truncate, WittVector.frobenius_eq_map_frobenius]

/-- The ring isomorphism of truncated Witt vectors induced by a ring isomorphism `e`, acting on
Witt coordinates by `e`. -/
noncomputable def mapEquiv (e : R ≃+* S) :
    TruncatedWittVector p n R ≃+* TruncatedWittVector p n S :=
  RingEquiv.ofRingHom (map e) (map e.symm)
    (RingHom.ext fun x ↦ ext fun i ↦ by simp) (RingHom.ext fun x ↦ ext fun i ↦ by simp)

@[simp]
theorem mapEquiv_apply (e : R ≃+* S) (x : TruncatedWittVector p n R) :
    mapEquiv e x = map e x :=
  (rfl)

@[simp]
theorem mapEquiv_symm (e : R ≃+* S) : (mapEquiv e).symm = mapEquiv (p := p) (n := n) e.symm :=
  (rfl)

end Map

section CharP

variable (p n R) in
/-- Truncated Witt vectors of length `n` over a ring of characteristic `p` have characteristic
`p ^ n`. -/
instance charP [CharP R p] : CharP (TruncatedWittVector p n R) (p ^ n) := by
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  have := charP_zmod p n
  refine charP_of_injective_ringHom (f := map (ZMod.castHom (dvd_refl p) R)) ?_ (p ^ n)
  intro x y hxy
  ext i
  have h := congr_arg (coeff i) hxy
  rw [coeff_map, coeff_map] at h
  exact (ZMod.castHom (dvd_refl p) R).injective h

end CharP

section ConstantCoeff

variable [NeZero n]

/-- The zeroth Witt coordinate, as a ring homomorphism `W_n(R) →+* R` for `n ≠ 0`. -/
noncomputable def constantCoeff : TruncatedWittVector p n R →+* R :=
  (WittVector.truncate n).liftOfSurjective (WittVector.truncate_surjective p n R)
    ⟨WittVector.constantCoeff, fun x hx ↦ by
      rw [WittVector.mem_ker_truncate] at hx
      simpa using hx 0 (Nat.pos_of_neZero n)⟩

theorem constantCoeff_truncate (x : WittVector p R) :
    constantCoeff (WittVector.truncate n x) = x.coeff 0 :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

@[simp]
theorem constantCoeff_apply (x : TruncatedWittVector p n R) : constantCoeff x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [constantCoeff_truncate]

theorem constantCoeff_map (f : R →+* S) (x : TruncatedWittVector p n R) :
    constantCoeff (map f x) = f (constantCoeff x) := by
  simp

theorem constantCoeff_surjective :
    Function.Surjective (constantCoeff : TruncatedWittVector p n R → R) := fun r ↦ by
  obtain ⟨x, rfl⟩ := WittVector.constantCoeff_surjective p r
  exact ⟨WittVector.truncate n x, constantCoeff_truncate x⟩

variable [CharP R p]

/-- For `n ≠ 0`, the reduction modulo `p` of `W_n(R)` has characteristic `p`. -/
instance charP_quotient :
    CharP (TruncatedWittVector p n R ⧸ Ideal.span {(p : TruncatedWittVector p n R)}) p := by
  have : Nontrivial (TruncatedWittVector p n R) :=
    CharP.nontrivial_of_char_ne_one (v := p ^ n) (Nat.one_lt_pow (NeZero.ne n) hp.out.one_lt).ne'
  refine CharP.quotient _ p fun hu ↦ not_isUnit_zero (M₀ := TruncatedWittVector p n R) ?_
  simpa [← Nat.cast_pow, CharP.cast_eq_zero] using hu.pow n

variable [PerfectRing R p]

/-- For a perfect ring `R` of characteristic `p`, the kernel of the zeroth coordinate of `W_n(R)`
is the ideal `(p)`. -/
theorem ker_constantCoeff :
    RingHom.ker (constantCoeff : TruncatedWittVector p n R →+* R) =
      Ideal.span {(p : TruncatedWittVector p n R)} := by
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
    rw [RingHom.mem_ker, constantCoeff_truncate,
      ← WittVector.mem_span_p_iff_coeff_zero_eq_zero] at hx
    simpa [Ideal.map_span] using Ideal.mem_map_of_mem (WittVector.truncate n) hx
  · simp

/-- For a perfect ring `R` of characteristic `p` and `n ≠ 0`, the zeroth coordinate induces an
isomorphism `W_n(R) ⧸ (p) ≃+* R`. -/
noncomputable def quotientPEquiv :
    TruncatedWittVector p n R ⧸ Ideal.span {(p : TruncatedWittVector p n R)} ≃+* R :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surjective)

@[simp]
theorem quotientPEquiv_mk (x : TruncatedWittVector p n R) :
    quotientPEquiv (Ideal.Quotient.mk _ x) = constantCoeff x := by
  simp [quotientPEquiv, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- For a perfect ring `R` of characteristic `p` and `n ≠ 0`, the reduction modulo `p` of `W_n(R)`
is perfect, being isomorphic to `R`. -/
instance perfectRing_quotient :
    PerfectRing (TruncatedWittVector p n R ⧸ Ideal.span {(p : TruncatedWittVector p n R)}) p := by
  let e := (quotientPEquiv (p := p) (n := n) (R := R))
  refine ⟨?_⟩
  have h : (fun x ↦ x ^ p) = e.symm ∘ (fun y : R ↦ y ^ p) ∘ e := funext fun x ↦ by simp
  rw [h]
  exact e.symm.bijective.comp (PerfectRing.bijective_frobenius.comp e.bijective)

end ConstantCoeff

end TruncatedWittVector
