/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Tower
import TauCeti.LinearAlgebra.Dimension.Localization
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.FreeQuotient

/-!
# The rationalization of the completed multiplicative module

For a finite extension `L` of `ℚ_[p]`, the completed multiplicative module
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` of `TauCeti.padicCompletionUnits` has `ℤ_p`-rank `[L : ℚ_p] + 1`
(`TauCeti.finrank_padicCompletionUnits`), so its rationalization `A(L) ⊗[ℤ_p] ℚ_p` is a
`ℚ_p`-vector space of dimension `[L : ℚ_p] + 1`. This file records that dimension and draws its
consequence for the Galois structure of the rationalization.

Over a finite Galois layer `L/K` of `p`-adic fields with group `G = Gal(L/K)` and
`N = [K : ℚ_p]`, the rationalization is the `ℚ_p[G]`-module `ℚ_p[G]^N ⊕ ℚ_p` (NSW (7.4.4)(i)); as
a `ℤ_p[G]`-module it is written `(ℤ_p[G]^N × ℤ_p[G] ⧸ I_G) ⊗[ℤ_p] ℚ_p`, with the trivial module
`ℤ_p[G] ⧸ I_G` in place of `ℚ_p` so that no second module structure is installed on `ℚ_p`. The
dimension count is where the Galois hypothesis enters: the right side has dimension
`N · #G + 1`, the left `[L : ℚ_p] + 1 = N · [L : K] + 1`, and these agree exactly when
`#Aut_K(L) = [L : K]`. So over a layer whose automorphism group is smaller than its degree, no
`ℤ_p[G]`-linear isomorphism between the two sides exists
(`TauCeti.not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt`). Finiteness of
`Aut_K(L)` is therefore not a substitute for `L/K` being Galois in the decomposition; the
non-Galois cubic `ℚ₅(∛5)` of `TauCeti.NonGaloisCubic` is an explicit instance.

## Main results

* `TauCeti.finrank_padicCompletionUnits_tensorRat`: `A(L) ⊗[ℤ_p] ℚ_p` has `ℤ_p`-rank, hence
  `ℚ_p`-dimension, `[L : ℚ_p] + 1`.
* `TauCeti.not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt`: over a finite
  layer `L/K` of `p`-adic fields with `#Aut_K(L) < [L : K]`, `A(L) ⊗ ℚ_p` is not
  `ℤ_p[Aut_K(L)]`-isomorphic to `(ℤ_p[Aut_K(L)]^N × ℤ_p[Aut_K(L)] ⧸ I) ⊗ ℚ_p`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.4.4) and the proof of
  (7.4.1).
-/

public section

namespace TauCeti

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

section Dimension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L]

/-- **The dimension of the rationalization of `A(L)`.** For a finite extension `L` of `ℚ_[p]`,
the `ℤ_p`-rank of `A(L) ⊗[ℤ_p] ℚ_p` is `[L : ℚ_p] + 1`. Since `ℤ_p` acts on this `ℚ_p`-vector
space through `ℚ_p`, this is also its `ℚ_p`-dimension. -/
theorem finrank_padicCompletionUnits_tensorRat :
    Module.finrank ℤ_[p] (Additive ↑(padicCompletionUnits p L) ⊗[ℤ_[p]] ℚ_[p]) =
      Module.finrank ℚ_[p] L + 1 := by
  rw [IsLocalization.finrank_tensorProduct (nonZeroDivisors ℤ_[p]) ℚ_[p] le_rfl,
    finrank_padicCompletionUnits]

end Dimension

/-- **Rejection test for the Galois hypothesis of the rational decomposition.** Let `L/K` be a
finite layer of `p`-adic fields whose automorphism group `Aut_K(L)` has fewer elements than the
degree `[L : K]`, as happens for a non-Galois layer. Then `A(L) ⊗ ℚ_p` is **not**
`ℤ_p[Aut_K(L)]`-isomorphic to `(ℤ_p[Aut_K(L)]^N × ℤ_p[Aut_K(L)] ⧸ I) ⊗ ℚ_p`, for `N = [K : ℚ_p]`
and `I` the augmentation ideal: the left side has `ℚ_p`-dimension `[L : ℚ_p] + 1 = N · [L : K] + 1`
and the right side `N · #Aut_K(L) + 1`. So the Galois hypothesis of the decomposition
`A(L) ⊗ ℚ_p ≃ ℚ_p[Gal(L/K)]^N ⊕ ℚ_p` cannot be weakened to finiteness of the automorphism
group. -/
theorem not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt
    {L : Type*} [Field L] {K : Type*} [Field K] [Algebra K L] [Algebra ℚ_[p] L]
    [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K L]
    (h : Nat.card (L ≃ₐ[K] L) < Module.finrank K L) :
    ¬ Nonempty ((Additive ↑(padicCompletionUnits p L) ⊗[ℤ_[p]] ℚ_[p])
      ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      (((Fin (Module.finrank ℚ_[p] K) → MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) ×
        (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸
          RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L)))) ⊗[ℤ_[p]] ℚ_[p])) := by
  rintro ⟨e⟩
  have := Module.Finite.left ℚ_[p] K L
  have := Module.Finite.right ℚ_[p] K L
  have hfinrank := (e.restrictScalars ℤ_[p]).finrank_eq
  rw [finrank_padicCompletionUnits_tensorRat,
    IsLocalization.finrank_tensorProduct (nonZeroDivisors ℤ_[p]) ℚ_[p] le_rfl,
    MonoidAlgebra.finrank_pi_prod_quotient_ker_augmentation,
    ← Module.finrank_mul_finrank ℚ_[p] K L] at hfinrank
  have hpos : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have := Nat.mul_lt_mul_of_pos_left h hpos
  omega

end TauCeti
