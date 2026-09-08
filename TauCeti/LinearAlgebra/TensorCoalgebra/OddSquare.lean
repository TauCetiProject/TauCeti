/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Odd squares of homogeneous tensor-coalgebra coderivations

A homogeneous endomorphism of the reduced tensor coalgebra whose degree `r` and twist parameter
`q` satisfy `(-1)^(q * r) = -1` is odd: it anticommutes with the letterwise Koszul involution of
parameter `q`. Consequently the square of such a graded coderivation is an ordinary coderivation,
whose vanishing can then be checked with the existing Taylor-component criterion. The degree-one
case `q = r = 1` is the one the `A∞` sign audit consumes.

Homogeneity is genuinely needed: `TauCeti.ReducedTensorWords.IsGradedCoderivation G q` is the
`q`-twisted co-Leibniz identity alone and does not by itself constrain degrees. The oddness comes
from `TauCeti.LinearMap.IsHomogeneous.map_koszulTwist_comp`, which turns the usual calculation on
a homogeneous word into an equality of endomorphisms.

## Main results

* `TauCeti.LinearMap.IsHomogeneous.anticommute_map_koszulTwist`: a homogeneous endomorphism of
  reduced tensor words anticommutes with the letterwise Koszul involution as soon as the sign
  `(-1)^(q * r)` of its degree against the twist parameter is `-1`.
* `TauCeti.LinearMap.IsHomogeneous.anticommute_map_koszulTwist_one`: the degree-one case, at twist
  parameter one.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation.isCoderivation_comp_self_of_isHomogeneous`:
  the square of such a homogeneous graded coderivation is an ordinary coderivation.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation.isCoderivation_comp_self_of_isHomogeneous_one`:
  the degree-one case, at twist parameter one.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace LinearMap.IsHomogeneous

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- A homogeneous endomorphism of degree `r` anticommutes with the letterwise Koszul twist of
parameter `q`, provided the sign `(-1)^(q * r)` it commutes past that twist with is `-1`. -/
theorem anticommute_map_koszulTwist {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} {q r : ℤ}
    (hb : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1) :
    b ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q) +
        ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ b = 0 := by
  have h := hb.map_koszulTwist_comp q
  rw [hqr] at h
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hz
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  -- reduced tensor words form only an `AddCommMonoid`, so the two terms cancel through the
  -- scalar identity `1 + (-1) = 0` rather than through additive inverses
  rw [hz]
  module

/-- A homogeneous endomorphism of degree one anticommutes with the letterwise Koszul twist of
parameter one. -/
theorem anticommute_map_koszulTwist_one {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) 1) :
    b ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1) +
        ReducedTensorWords.map (R := R) (G.koszulTwist 1) ∘ₗ b = 0 :=
  hb.anticommute_map_koszulTwist (by norm_num)

end LinearMap.IsHomogeneous

namespace ReducedTensorWords.IsGradedCoderivation

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The square of a homogeneous graded coderivation is an ordinary coderivation as soon as the
sign `(-1)^(q * r)` of its degree `r` against the twist parameter `q` is `-1`: homogeneity then
supplies the anticommutation with the Koszul twist that cancels the two mixed terms in the
co-Leibniz expansion. A caller holding homogeneity of the letter component instead obtains
`hhom` from `TauCeti.ReducedTensorWords.IsGradedCoderivation.isHomogeneous`. -/
theorem isCoderivation_comp_self_of_isHomogeneous {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} {q r : ℤ}
    (hb : IsGradedCoderivation G q b)
    (hhom : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1) :
    IsCoderivation R (b ∘ₗ b) :=
  hb.isCoderivation_comp_self (hhom.anticommute_map_koszulTwist hqr)

/-- The square of a homogeneous degree-one graded coderivation is an ordinary coderivation. -/
theorem isCoderivation_comp_self_of_isHomogeneous_one {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G 1 b)
    (hhom : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) 1) :
    IsCoderivation R (b ∘ₗ b) :=
  hb.isCoderivation_comp_self_of_isHomogeneous hhom (by norm_num)

end ReducedTensorWords.IsGradedCoderivation

end TauCeti
