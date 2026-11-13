/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.Algebra.Homology.DG.Coalgebra.Defs
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coassoc
public import TauCeti.LinearAlgebra.TensorCoalgebra.Grading

/-!
# The bar construction of an `A∞` algebra as a differential graded coalgebra

The reduced bar construction `Tᶜ(sA) = ⨁_{n ≥ 1} (sA)^{⊗ n}` of an `A∞` algebra `A`, with reduced
deconcatenation and the bar differential `b`, is a noncounital differential graded coalgebra
(`TauCeti.AInfinityAlgebra.isNonCounitalDGCoalgebra_bar`).  Its grading is the total degree of
the suspended letters, and the Koszul-signed co-Leibniz rule of a noncounital differential graded
coalgebra is the twist-parameter-one co-Leibniz rule of `b`, because the Koszul twist of the total
grading is the letterwise twist (`TauCeti.ReducedTensorWords.koszulTwist_grading`).

Consequently the cobar construction applies to it:
`TauCeti.IsNonCounitalDGCoalgebra.isDGAlgebra_cobarDifferential` makes
`Ω Tᶜ(sA) = T(s⁻¹ Tᶜ(sA))`, with the cobar differential `TauCeti.cobarDifferential`, a
differential graded algebra.  Since `Tᶜ(sA)` is
the coaugmentation coideal of the bar construction of the augmented algebra `R ⊕ A`, this is the
enveloping differential graded algebra `Ω B (R ⊕ A)` of that augmented `A∞` algebra.

## Main results

* `TauCeti.AInfinityAlgebra.isNonCounitalDGCoalgebra_bar`: the reduced bar construction of an
  `A∞` algebra is a noncounital differential graded coalgebra.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for the bar and cobar constructions of augmented `A∞` algebras.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti.AInfinityAlgebra

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- **The reduced bar construction of an `A∞` algebra is a noncounital differential graded
coalgebra**: the suspended tensor words `Tᶜ(sA)`, graded by total degree, with reduced
deconcatenation and the bar differential. -/
theorem isNonCounitalDGCoalgebra_bar (𝒜 : AInfinityAlgebra R A) :
    IsNonCounitalDGCoalgebra (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential where
  coassoc := ReducedTensorWords.deconcatenation_coassoc R A
  isHomogeneous_comul := ReducedTensorWords.isHomogeneous_deconcatenation _
  map_mem hc := by
    rw [ReducedTensorWords.grading_piece] at hc ⊢
    exact 𝒜.isHomogeneous_barDifferential.map_mem hc
  sq_zero c := LinearMap.congr_fun 𝒜.barDifferential_sq c
  comul_differential := by
    rw [ReducedTensorWords.koszulTwist_grading, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.add_comp]
    exact ReducedTensorWords.isGradedCoderivation_iff.1 𝒜.isGradedCoderivation_barDifferential

end TauCeti.AInfinityAlgebra
