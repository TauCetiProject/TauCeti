/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.DeRham.LieDerivative
public import TauCeti.RingTheory.Kaehler.DeRham.Polynomial.Basic

/-!
# Lie-derivative variable support on multivariate polynomial de Rham forms

For a commutative `R`-algebra `B` and an `R`-derivation `D` of `MvPolynomial σ B` that sends
`B`-constants `algebraMap B _ b` to elements killed by the relative Kähler differential
`KaehlerDifferential.D B (MvPolynomial σ B)` (so `D.deRhamLieDeriv hB` is defined),
`TauCeti.KaehlerDeRham.deRhamLieDeriv_mem_supportedForms` shows that `D.deRhamLieDeriv hB` maps
`supportedForms B s` into `supportedForms B t` whenever `s ⊆ t` and `D` maps
`MvPolynomial.supported B s` into `MvPolynomial.supported B t`.

## Main results

* `TauCeti.KaehlerDeRham.deRhamLieDeriv_mem_supportedForms`: variable-support preservation/transfer
  for `Derivation.deRhamLieDeriv` on `MvPolynomial σ B`.
-/

public section

namespace TauCeti.KaehlerDeRham

open _root_.ExteriorAlgebra _root_.KaehlerDifferential MvPolynomial

/-- If an `R`-derivation `D` sends `B`-constants `algebraMap B _ b` to elements killed by the
relative Kähler differential `KaehlerDifferential.D B (MvPolynomial σ B)` and maps polynomials
supported on `s` into polynomials supported on `t ⊇ s`, then `D.deRhamLieDeriv hB` maps
`supportedForms B s` into `supportedForms B t`. -/
theorem deRhamLieDeriv_mem_supportedForms {R B σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)}
    (hB : ∀ b : B, KaehlerDifferential.D B (MvPolynomial σ B) (D (algebraMap B _ b)) = 0)
    {s t : Set σ} (hst : s ⊆ t)
    (hD : ∀ p ∈ MvPolynomial.supported B s, D p ∈ MvPolynomial.supported B t)
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) : D.deRhamLieDeriv hB α ∈ supportedForms B t := by
  induction hα using supportedForms_induction with
  | mem_algebraMap p hp =>
    rw [Derivation.deRhamLieDeriv_algebraMap]
    exact algebraMap_mem_supportedForms (hD p hp)
  | mem_ι_D_X i hi =>
    rw [Derivation.deRhamLieDeriv_ι, Derivation.kaehlerLieDeriv_D]
    have hXi : (X i : MvPolynomial σ B) ∈ MvPolynomial.supported B s := by
      rw [MvPolynomial.supported_eq_adjoin_X]
      exact Algebra.subset_adjoin ⟨i, hi, rfl⟩
    exact ι_D_mem_supportedForms (hD (X i) hXi)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.deRhamLieDeriv_mul]
    exact add_mem (mul_mem ihx (supportedForms_mono hst hy))
      (mul_mem (supportedForms_mono hst hx) ihy)

end TauCeti.KaehlerDeRham
