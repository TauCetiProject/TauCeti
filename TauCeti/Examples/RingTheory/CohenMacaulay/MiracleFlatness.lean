/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.CohenMacaulay.TrivSqZeroExt
import TauCeti.RingTheory.Flat.TrivSqZeroExt
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Tests: miracle flatness needs a Cohen–Macaulay target

Miracle flatness (Stacks, Lemma 10.128.1 (00R4)) says that a local homomorphism `A → S` of
Noetherian local rings with `A` regular, `S` Cohen–Macaulay and
`dim S = dim A + dim S ⧸ 𝔪_A S` is flat. The Cohen–Macaulay hypothesis cannot be dropped.

For `A = k⟦x, y⟧` and `S = A[z] ⧸ (z², xz, yz)`, the map `A → S` is finite and local, `S` has
dimension two and its closed fibre `k[z] ⧸ (z²)` has dimension zero, so the dimension formula
holds; but `S` has depth zero, so it is not Cohen–Macaulay, and it is not flat over `A`. Here
`S` is the trivial square-zero extension `A ⊕ κ(A)`, with `z = (0, 1)`, and `A = k⟦x⟧⟦y⟧`.
-/

open IsLocalRing TrivSqZeroExt

namespace TauCeti

section Presentation

open Polynomial

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- *test_flat_needs_cohenMacaulay*: if `𝔪 = (x, y)`, then `A ⊕ κ(A)` is the ring
`A[z] ⧸ (z², xz, yz)`, with `z = (0, 1)`. -/
example {x y : A} (hxy : maximalIdeal A = Ideal.span {x, y}) :
    Nonempty ((A[X] ⧸ (Ideal.span {X ^ 2, C x * X, C y * X} : Ideal A[X])) ≃ₐ[A]
      TrivSqZeroExt A (A ⧸ maximalIdeal A)) := by
  let φ := aeval (R := A) (inr 1 : TrivSqZeroExt A (A ⧸ maximalIdeal A))
  -- The value of a polynomial at `z` only sees its first two coefficients, as `z² = 0`.
  have hφp (p : A[X]) : φ p = inl (p.coeff 0) + inr (Ideal.Quotient.mk _ (p.coeff 1)) := by
    have h := aeval_add_of_sq_eq_zero p 0 (inr 1 : TrivSqZeroExt A (A ⧸ maximalIdeal A))
      (by rw [sq, inr_mul_inr])
    rw [zero_add, ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero', coeff_derivative] at h
    simpa [φ, algebraMap_eq_inl, inl_mul_inr, Algebra.smul_def] using h
  have hφ : Function.Surjective φ := fun s ↦ by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective s.snd
    exact ⟨C s.fst + C b * X, by ext <;> simp [hφp, hb]⟩
  -- A polynomial lies in the kernel iff its constant coefficient is zero and its linear
  -- coefficient lies in `𝔪 = (x, y)`.
  have hker : RingHom.ker φ = Ideal.span {X ^ 2, C x * X, C y * X} := by
    refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.2 ?_)
    · rw [RingHom.mem_ker, hφp, TrivSqZeroExt.ext_iff] at hp
      simp only [fst_add, fst_inl, fst_inr, add_zero, fst_zero, snd_add, snd_inl, snd_inr,
        zero_add, snd_zero, Ideal.Quotient.eq_zero_iff_mem, hxy, Ideal.mem_span_pair] at hp
      obtain ⟨h0, a, b, hab⟩ := hp
      -- `p = p₂ z² + a xz + b yz`, where `p = p₂ z² + p₁ z + p₀`.
      have hp : p = C a * (C x * X) + C b * (C y * X) + p.divX.divX * X ^ 2 := by
        conv_lhs => rw [← divX_mul_X_add p, ← divX_mul_X_add p.divX]
        rw [coeff_divX, zero_add, ← hab, h0]
        simp only [map_add, map_mul, map_zero]
        ring
      rw [hp]
      refine add_mem (add_mem ?_ ?_) ?_ <;> refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      all_goals simp
    · have hx : x ∈ maximalIdeal A := hxy ▸ Ideal.subset_span (by simp)
      have hy : y ∈ maximalIdeal A := hxy ▸ Ideal.subset_span (by simp)
      rintro _ (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, RingHom.mem_ker, hφp] <;>
        ext <;> simp [coeff_X, coeff_X_pow, Ideal.Quotient.eq_zero_iff_mem, hx, hy]
  exact ⟨(Ideal.quotientEquivAlgOfEq A hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hφ)⟩

end Presentation

section General

variable (A : Type*) [CommRing A] [IsRegularLocalRing A]

/-- *test_flat_needs_cohenMacaulay*: `A → A ⊕ κ(A)` is a finite local homomorphism of
Noetherian local rings. -/
example : Module.Finite A (TrivSqZeroExt A (A ⧸ maximalIdeal A)) ∧
    IsLocalRing (TrivSqZeroExt A (A ⧸ maximalIdeal A)) ∧
    IsLocalHom (algebraMap A (TrivSqZeroExt A (A ⧸ maximalIdeal A))) ∧
    IsNoetherianRing (TrivSqZeroExt A (A ⧸ maximalIdeal A)) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- *test_flat_needs_cohenMacaulay*: the dimension formula of miracle flatness holds for
`A → A ⊕ κ(A)`, since the closed fibre has dimension zero. -/
example : ringKrullDim (TrivSqZeroExt A (A ⧸ maximalIdeal A)) = ringKrullDim A +
    ringKrullDim (TrivSqZeroExt A (A ⧸ maximalIdeal A) ⧸
      (maximalIdeal A).map (algebraMap A (TrivSqZeroExt A (A ⧸ maximalIdeal A)))) := by
  rw [ringKrullDim_quotient_map_maximalIdeal_eq_zero, add_zero, ringKrullDim_eq]

/-- *test_flat_needs_cohenMacaulay*: over a regular local ring of positive dimension,
`A ⊕ κ(A)` has depth zero, is not Cohen–Macaulay and is not flat over `A`. -/
example (hd : 0 < ringKrullDim A) :
    depth (ModuleCat.of (TrivSqZeroExt A (A ⧸ maximalIdeal A))
      (TrivSqZeroExt A (A ⧸ maximalIdeal A))) = 0 ∧
    ¬ Module.IsCohenMacaulay (TrivSqZeroExt A (A ⧸ maximalIdeal A))
      (TrivSqZeroExt A (A ⧸ maximalIdeal A)) ∧
    ¬ Module.Flat A (TrivSqZeroExt A (A ⧸ maximalIdeal A)) := by
  -- The residue field has depth zero.
  have hκ : depth (ModuleCat.of A (A ⧸ maximalIdeal A)) = 0 :=
    depth_eq_zero_iff_nontrivial_linearMap.2
      ⟨⟨LinearMap.id, 0, fun h ↦ by simpa using LinearMap.congr_fun h 1⟩⟩
  exact ⟨depth_eq_zero hκ, not_isCohenMacaulay hκ hd.ne',
    not_flat fun h ↦ (ringKrullDim_eq_zero_of_isField h ▸ hd).false⟩

end General

section PowerSeries

open _root_.PowerSeries

variable (k : Type*) [Field k]

/-- *test_flat_needs_cohenMacaulay*: `A = k⟦x⟧⟦y⟧` is regular of dimension two, with maximal
ideal `(x, y)`, and `A ⊕ κ(A)` also has dimension two. -/
example : IsRegularLocalRing k⟦X⟧⟦X⟧ ∧ ringKrullDim k⟦X⟧⟦X⟧ = 2 ∧
    maximalIdeal k⟦X⟧⟦X⟧ = Ideal.span {C X, X} ∧
    ringKrullDim (TrivSqZeroExt k⟦X⟧⟦X⟧ (k⟦X⟧⟦X⟧ ⧸ maximalIdeal k⟦X⟧⟦X⟧)) = 2 :=
  ⟨inferInstance, PowerSeries.ringKrullDim_of_isDiscreteValuationRing,
    PowerSeries.maximalIdeal_eq_span_C_X irreducible_X,
    ringKrullDim_eq.trans PowerSeries.ringKrullDim_of_isDiscreteValuationRing⟩

end PowerSeries

end TauCeti
