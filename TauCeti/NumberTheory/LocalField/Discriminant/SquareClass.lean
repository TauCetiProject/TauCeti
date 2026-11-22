/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Discriminant
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic

/-!
# The discriminant of an integral basis of an extension of local fields

Let `L/K` be a finite separable extension of nonarchimedean local fields and `b` an
`𝒪[K]`-basis of `𝒪[L]`. Its discriminant `Algebra.discr 𝒪[K] b` generates the local discriminant
ideal `𝔩(L/K) = 𝓂[K] ^ δ(L/K)` (`TauCeti.span_discr_eq_discriminantIdeal`), and its image in `K`
is the discriminant of the `K`-basis of `L` obtained from `b` by localization, so its square class
is `TauCeti.discriminantClass K L`.

Conversely these two invariants determine the discriminant of an integral basis up to the square of
a unit of `𝒪[K]`: an element `x` of `𝒪[K]` is `u ^ 2 * Algebra.discr 𝒪[K] b` for a unit `u` exactly
when it generates `𝔩(L/K)` and has square class `TauCeti.discriminantClass K L`. The ideal alone
determines the discriminant up to a unit; the square class then fixes that unit up to squares,
because a unit of `𝒪[K]` that is a square in `K` is the square of a unit of `𝒪[K]`.

## Main results

* `TauCeti.exists_eq_sq_mul_discr_iff`: `x = u ^ 2 * discr b` for a unit `u` of `𝒪[K]` exactly
  when `(x) = 𝔩(L/K)` and `x` has square class `TauCeti.discriminantClass K L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §§2–3.
* J. W. Jones and D. P. Roberts, *A database of local fields*, J. Symbolic Comput. 41 (2006),
  80–97 (arXiv:math/0309309).
-/

public section

open ValuativeRel IsLocalRing Module
open scoped nonZeroDivisors

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]
  [FiniteDimensional K L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The discriminant ideal and the discriminant square class determine the discriminant of an
integral basis up to the square of an integral unit.** For an `𝒪[K]`-basis `b` of `𝒪[L]`, an
element `x` of `𝒪[K]` is `u ^ 2 * Algebra.discr 𝒪[K] b` for a unit `u` of `𝒪[K]` exactly when `x`
generates `𝔩(L/K)` and its image in `K` is a unit of square class `TauCeti.discriminantClass K L`.
-/
theorem exists_eq_sq_mul_discr_iff (b : Basis ι 𝒪[K] 𝒪[L]) (x : 𝒪[K]) :
    (∃ u : 𝒪[K]ˣ, x = u ^ 2 * Algebra.discr 𝒪[K] b) ↔
      Ideal.span {x} = discriminantIdeal K L ∧
        ∃ v : Kˣ, (v : K) = algebraMap 𝒪[K] K x ∧ squareClass v = discriminantClass K L := by
  set d := Algebra.discr 𝒪[K] b
  -- The `K`-basis of `L` obtained from `b` has discriminant the image `D` of `d`.
  let b' := b.localizationLocalization K 𝒪[K]⁰ L
  have hd : algebraMap 𝒪[K] K d = Algebra.discr K b' := by
    rw [Algebra.discr_localizationLocalization]
  set D := (Algebra.discr_isUnit_of_basis K b').unit
  have hD : (D : K) = algebraMap 𝒪[K] K d := by rw [hd, IsUnit.unit_spec]
  have hclass : squareClass D = discriminantClass K L := (discriminantClass_eq b').symm
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨by rw [Ideal.span_singleton_mul_left_unit (u.isUnit.pow 2),
      span_discr_eq_discriminantIdeal], Units.map (algebraMap 𝒪[K] K).toMonoidHom u ^ 2 * D,
      by simp [hD], ?_⟩
    rw [squareClass_sq_mul, hclass]
  · rintro ⟨hx, v, hv, hcl⟩
    -- The ideal determines `x = d * w` for a unit `w` of `𝒪[K]`.
    obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp
      ((span_discr_eq_discriminantIdeal b).trans hx.symm)
    -- The square class makes `x * d = w * d ^ 2` a square `r ^ 2` in `K`, so `w = t ^ 2`.
    obtain ⟨r, hr⟩ := (squareClass_eq_iff_isSquare_mul v D).mp (hcl.trans hclass.symm)
    have hd0 : algebraMap 𝒪[K] K d ≠ 0 := by rw [← hD]; exact D.ne_zero
    set t := (r : K) / algebraMap 𝒪[K] K d
    have ht : t ^ 2 = algebraMap 𝒪[K] K w := by
      have hr' : algebraMap 𝒪[K] K x * algebraMap 𝒪[K] K d = r * r := by
        rw [← hv, ← hD, ← Units.val_mul, hr, Units.val_mul]
      rw [← hw, map_mul] at hr'
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hd0), sq, ← hr']
      ring
    -- A square root in `K` of a unit of the integrally closed ring `𝒪[K]` lies in `𝒪[K]`.
    obtain ⟨t', htt'⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (IsIntegral.of_pow two_pos (ht ▸ isIntegral_algebraMap))
    have ht' : t' ^ 2 = w := IsFractionRing.injective 𝒪[K] K (by rw [map_pow, htt', ht])
    have hu : IsUnit t' := (isUnit_pow_iff two_ne_zero).mp (ht' ▸ w.isUnit)
    exact ⟨hu.unit, by rw [IsUnit.unit_spec, ht', ← hw, mul_comm]⟩

end TauCeti
