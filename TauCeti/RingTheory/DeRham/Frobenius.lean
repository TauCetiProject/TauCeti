/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeRham.Differential

/-!
# Frobenius linearity of the de Rham differential

`TauCeti.DeRham.d_pow_smul_of_natCast_eq_zero` gives Frobenius linearity in prime
characteristic. It uses `TauCeti.DeRham.d_elementary` and `Derivation.leibniz_pow` to show
that the differential commutes with multiplication by powers whose exponent vanishes in the
ring. This is the scalar identity for the action through relative Frobenius in Bhatt,
*p-adic derived de Rham cohomology*, Notation 3.1.
-/

public section

namespace TauCeti.DeRham

open KaehlerDifferential

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

/-- If `m` vanishes in `B`, the de Rham differential commutes with multiplication by
`b ^ m`. In prime characteristic this is linearity for the action through Frobenius. -/
theorem d_pow_smul_of_natCast_eq_zero {m : ℕ} (b : B) (ω : Forms A B n) (hm : (m : B) = 0) :
    d A B n (b ^ m • ω) = b ^ m • d A B n ω := by
  have hD : D A B (b ^ m) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, hm, zero_smul]
  have hcomm :
      d A B n ∘ₗ DistribSMul.toLinearMap A (Forms A B n) (b ^ m) =
        DistribSMul.toLinearMap A (Forms A B (n + 1)) (b ^ m) ∘ₗ d A B n := by
    refine forms_hom_ext fun c v => ?_
    have hsmul : b ^ m • elementary A c v = elementary A (b ^ m * c) v := by
      simp only [elementary_def, mul_smul]
    simp only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply, hsmul,
      d_elementary, Derivation.leibniz, hD, smul_zero, add_zero]
    exact (exteriorPower.ιMulti B (n + 1)).map_vecCons_smul _ _ _
  simpa only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply] using
    LinearMap.congr_fun hcomm ω

end TauCeti.DeRham
