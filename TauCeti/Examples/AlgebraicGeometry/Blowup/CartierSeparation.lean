/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.CommRing
import TauCeti.AlgebraicGeometry.Blowup.CartierSeparation
import TauCeti.RingTheory.Ideal.Colon

/-!
# Examples: Cartier separation

Concrete checks of Cartier separation (`TauCeti.AlgebraicGeometry.Blowup.CartierSeparation`):

* On `𝔸²_k = Spec k[X, Y]`, blowing up `(X, Y)` separates the strict transforms of the two
  coordinate axes `(X)` and `(Y)`, producing disjoint effective Cartier divisors.
* On `𝔸¹_k = Spec k[t]`, for `D₁ = 2[0] = (t²)` and `D₂ = 3[0] = (t³)`, the blowup along
  `(t²) ⊔ (t³) = (t²)` is an isomorphism, with `D'₁ = ⊤` and `D'₂ = p* (t)`.
* On the nonreduced scheme `Spec ℚ[e, t]/(e²) = Spec (DualNumber ℚ)[t]`, `(t)` is effective
  Cartier while `(e)` is not; for `D₁ = (t)` and `D₂ = (t²)`, the blowup along `(t)` is an
  isomorphism with residual ideals `⊤` and `p* (t)`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti TauCeti.AlgebraicGeometry

universe u

-- Check 1: On `𝔸²_k = Spec k[X, Y]`, blowing up `(X, Y)` separates the strict transforms of the two
-- coordinate axes `(X)` and `(Y)`, producing disjoint effective Cartier divisors.
example (k : Type u) [CommRing k] :
    let R := MvPolynomial (Fin 2) k
    let D₁ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (MvPolynomial.X 0)})
    let D₂ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (MvPolynomial.X 1)})
    (D₁.blowupSupResidualLeft D₂).IsEffectiveCartier ∧
      (D₁.blowupSupResidualRight D₂).IsEffectiveCartier ∧
      Disjoint (D₁.blowupSupResidualLeft D₂).support (D₁.blowupSupResidualRight D₂).support := by
  intro R D₁ D₂
  have hX (i : Fin 2) : IsSMulRegular R (MvPolynomial.X i) :=
    MvPolynomial.isRegular_X.left.isSMulRegular
  have hD₁ : D₁.IsEffectiveCartier := isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv (hX 0)
  have hD₂ : D₂.IsEffectiveCartier := isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv (hX 1)
  exact ⟨hD₁.blowupSupResidualLeft D₂, hD₂.blowupSupResidualRight D₁,
    disjoint_support_blowupSupResidualLeft_blowupSupResidualRight D₁ D₂⟩

-- Check 2: On `𝔸¹_k = Spec k[t]`, for `D₁ = 2[0] = (t²)` and `D₂ = 3[0] = (t³)`, the blowup along
-- `(t²) ⊔ (t³) = (t²)` is an isomorphism, with `D'₁ = ⊤` (empty) and `D'₂ = p* (t)`.
example (k : Type u) [CommRing k] :
    let R := Polynomial k
    let D₁ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.X ^ 2)})
    let D₂ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.X ^ 3)})
    IsIso (D₁ ⊔ D₂).blowupToBase ∧
      D₁.blowupSupResidualLeft D₂ = ⊤ ∧
      D₁.blowupSupResidualRight D₂ =
        (ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv Polynomial.X})).comap
          (D₁ ⊔ D₂).blowupToBase := by
  intro R D₁ D₂
  have hX : IsSMulRegular R Polynomial.X := Polynomial.monic_X.isRegular.left.isSMulRegular
  have hD₁ : D₁.IsEffectiveCartier :=
    isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv (hX.pow 2)
  have hle : D₂ ≤ D₁ := fun U ↦ Ideal.map_mono <| by
    rw [Ideal.span_singleton_le_span_singleton]
    exact map_dvd (Scheme.ΓSpecIso (.of R)).inv.hom ⟨Polynomial.X, by ring⟩
  refine ⟨hD₁.isIso_blowupToBase_sup_of_le hle, blowupSupResidualLeft_eq_top_of_le hle, ?_⟩
  rw [blowupSupResidualRight_eq_comap_colon_of_le hD₁.locallyPrincipal hle]
  congr 1
  rw [ofIdealTop_colon_ofIdealTop]
  refine congrArg ofIdealTop ?_
  rw [pow_succ, map_mul, ← Ideal.span_singleton_mul_span_singleton, Ideal.colon_span]
  exact Ideal.span_singleton_mul_colon_singleton
    (Scheme.isSMulRegular_ΓSpecIso_inv (hX.pow 2)).isLeftRegular _

-- Check 3: On the nonreduced scheme `Spec ℚ[e, t]/(e²) = Spec (DualNumber ℚ)[t]`, `(t)` is
-- effective Cartier while `(e)` is not; for `D₁ = (t)` and `D₂ = (t²)`, the blowup along `(t)` is
-- an isomorphism with residual ideals `⊤` and `p* (t)` and cross-sum
-- `p* (t) * D'₂ = p* (t²) * D'₁`.
example :
    let R := Polynomial (DualNumber ℚ)
    let Dt : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv Polynomial.X})
    let Dt2 : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.X ^ 2)})
    let De : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.C DualNumber.eps)})
    Dt.IsEffectiveCartier ∧ ¬ De.IsEffectiveCartier ∧
      IsIso (Dt ⊔ Dt2).blowupToBase ∧
      Dt.blowupSupResidualLeft Dt2 = ⊤ ∧
      Dt.blowupSupResidualRight Dt2 = Dt.comap (Dt ⊔ Dt2).blowupToBase ∧
      Dt.comap (Dt ⊔ Dt2).blowupToBase * Dt.blowupSupResidualRight Dt2 =
        Dt2.comap (Dt ⊔ Dt2).blowupToBase * Dt.blowupSupResidualLeft Dt2 := by
  intro R Dt Dt2 De
  have hX : IsSMulRegular R Polynomial.X := Polynomial.monic_X.isRegular.left.isSMulRegular
  have hDt : Dt.IsEffectiveCartier := isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv hX
  have hDe : ¬ De.IsEffectiveCartier := by
    intro h
    obtain ⟨x⟩ : Nonempty (Spec (.of R)) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
    obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff De).mp h x
    have hDe2 : De ^ 2 = ⊥ := by
      dsimp only [De]
      rw [← ofIdealTop_pow, Ideal.span_singleton_pow, sq, ← map_mul, ← map_mul,
        DualNumber.eps_mul_eps, map_zero, map_zero, Ideal.span_singleton_zero]
      ext U : 2
      simp
    have ha2 : a * a = 0 := by
      have hmem : a * a ∈ (De ^ 2).ideal U := by
        rw [ideal_pow, Pi.pow_apply, sq, hUa, Ideal.span_singleton_mul_span_singleton]
        exact Ideal.subset_span rfl
      simpa only [hDe2, ideal_bot, Pi.bot_apply, Ideal.mem_bot] using hmem
    have ha0 : a = 0 := ha (ha2.trans (mul_zero a).symm)
    have h10 : (1 : Γ(Spec (.of R), U)) = 0 := ha (by simp [ha0])
    have hg := congrArg ((Spec (.of R)).presheaf.germ U x hxU) h10
    rw [map_one, map_zero] at hg
    exact one_ne_zero hg
  have hle : Dt2 ≤ Dt := fun U ↦ Ideal.map_mono <| by
    rw [Ideal.span_singleton_le_span_singleton]
    exact map_dvd (Scheme.ΓSpecIso (.of R)).inv.hom ⟨Polynomial.X, by ring⟩
  refine ⟨hDt, hDe, hDt.isIso_blowupToBase_sup_of_le hle,
    blowupSupResidualLeft_eq_top_of_le hle, ?_,
    comap_mul_blowupSupResidualRight_eq Dt Dt2⟩
  rw [blowupSupResidualRight_eq_comap_colon_of_le hDt.locallyPrincipal hle]
  congr 1
  rw [ofIdealTop_colon_ofIdealTop]
  refine congrArg ofIdealTop ?_
  rw [sq, map_mul, ← Ideal.span_singleton_mul_span_singleton, Ideal.colon_span]
  exact Ideal.span_singleton_mul_colon_singleton
    (Scheme.isSMulRegular_ΓSpecIso_inv hX).isLeftRegular _
