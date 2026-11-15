/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Holomorphic stalks satisfy the Rückert hypotheses

For a finite-dimensional complex normed space `E` and `(x₀, w₀) : E × ℂ`, vertical evaluation of
polynomials `evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies the abstract
Rückert hypotheses (`RingHom.IsRueckert`) with respect to the set of Weierstrass polynomials,
namely the polynomials over `𝒪_{E, x₀}` distinguished at the maximal ideal `𝔪_{x₀}`:

* `evalVertical x₀ w₀` is injective (`evalVertical_injective`), and monic factors of Weierstrass
  polynomials remain Weierstrass polynomials (`Polynomial.IsDistinguishedAt.of_dvd`) since the
  maximal ideal `𝔪_{x₀}` is prime and therefore radical;
* Weierstrass division detects divisibility by a Weierstrass polynomial
  (`evalVertical_dvd_iff_of_isDistinguishedAt`) and represents every germ modulo a Weierstrass
  polynomial by a polynomial over the base stalk
  (`existsUnique_weierstrassDivision_of_isDistinguishedAt`);
* for every nonzero germ `f` at `(x₀, w₀)`, some continuous linear automorphism `L` of `E × ℂ`
  makes the centered pullback `L.holomorphicStalkCenteredEquiv (x₀, w₀) f` regular in the last
  variable (`exists_map_residue_verticalPowerSeries_ne_zero`), and Weierstrass preparation
  (`existsUnique_weierstrassPreparation`) then writes that pullback as a unit multiple of a
  Weierstrass polynomial.

As immediate consequences before inducting on dimension, a Weierstrass polynomial generates a
prime ideal (or is a prime element) in `𝒪_{E × ℂ, (x₀, w₀)}` if and only if it does so in
`(𝒪_{E, x₀})[X]`, and irreducibility, relative primality, and squarefreeness of
`evalVertical x₀ w₀ P` descend to `P`.

## Main results

* `TauCeti.holomorphicStructureSheaf.exists_map_residue_verticalPowerSeries_ne_zero`: every nonzero
  holomorphic germ on `E × ℂ` becomes regular in the last variable after a centered linear
  automorphism fixing the base point (without assuming `E` is finite-dimensional).
* `TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`: `evalVertical x₀ w₀` satisfies
  `RingHom.IsRueckert` for the polynomials distinguished at `𝔪_{x₀}`.
* `TauCeti.holomorphicStructureSheaf.isPrime_span_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.prime_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.irreducible_of_irreducible_evalVertical_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.isRelPrime_of_isRelPrime_evalVertical_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.squarefree_of_squarefree_evalVertical_of_isDistinguishedAt`:
  primality, irreducibility, relative primality, and squarefreeness descent for Weierstrass
  polynomials.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Ch. II, §2.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Ch. 2, §2.2.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open Filter Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every nonzero holomorphic germ at `(x₀, w₀) : E × ℂ` becomes regular in the last variable
after pulling back along a centered linear automorphism `(x, w) ↦ (x₀, w₀) + L ((x, w) - (x₀, w₀))`
fixing `(x₀, w₀)` (without assuming `E` is finite-dimensional). -/
theorem exists_map_residue_verticalPowerSeries_ne_zero {x₀ : E} {w₀ : ℂ}
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : f ≠ 0) :
    ∃ L : (E × ℂ) ≃L[ℂ] E × ℂ,
      (verticalPowerSeries x₀ w₀ (L.holomorphicStalkCenteredEquiv (x₀, w₀) f)).map
        (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 := by
  obtain ⟨F, hF, hfF⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) f
  have hF0 : ¬F =ᶠ[𝓝 (x₀, w₀)] 0 := (eq_zero_iff_of_toFilterGerm_eq (hfF _ le_rfl)).not.1 hf
  obtain ⟨L, hord⟩ := hF.exists_continuousLinearEquiv_analyticOrderAt_add_sub_ne_top hF0
  exact ⟨L, (map_residue_verticalPowerSeries_ne_zero_iff
    (L.toFilterGerm_holomorphicStalkCenteredEquiv_of_eq (hfF _ le_rfl))).2 hord⟩

section FiniteDimensional

variable [FiniteDimensional ℂ E]

/-- **Holomorphic stalks satisfy the Rückert hypotheses.** On `E × ℂ` with `E` finite-dimensional,
vertical polynomial evaluation `evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}`
satisfies `RingHom.IsRueckert` with respect to the polynomials distinguished at the maximal ideal
of `𝒪_{E, x₀}`. -/
theorem isRueckert_evalVertical (x₀ : E) (w₀ : ℂ) :
    (evalVertical x₀ w₀).IsRueckert
      {P | P.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))} where
  injective := evalVertical_injective x₀ w₀
  monic hw := hw.monic
  mem_of_dvd hw hp hpw := hw.of_dvd (Ideal.IsPrime.isRadical inferInstance) hp hpw
  dvd_iff hw p := (evalVertical_dvd_iff_of_isDistinguishedAt hw).symm
  exists_dvd_sub hw b := by
    obtain ⟨⟨q, r⟩, ⟨_, hb⟩, _⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hw b
    exact ⟨r, q, by linear_combination hb⟩
  exists_mul_eq {b} hb := by
    obtain ⟨L, hL⟩ := exists_map_residue_verticalPowerSeries_ne_zero hb
    obtain ⟨⟨P, u⟩, ⟨hP, hu, hfac⟩, _⟩ := existsUnique_weierstrassPreparation hL
    refine ⟨L.holomorphicStalkCenteredEquiv (x₀, w₀), hu.unit⁻¹, P, hP, ?_⟩
    rw [hfac, mul_comm (evalVertical x₀ w₀ P) u, ← mul_assoc, IsUnit.val_inv_mul, one_mul]

/-- For a distinguished polynomial `P` over `𝒪_{E, x₀}`, the principal ideal
`Ideal.span {evalVertical x₀ w₀ P}` in `𝒪_{E × ℂ, (x₀, w₀)}` is prime if and only if
`Ideal.span {P}` in `(𝒪_{E, x₀})[X]` is prime. -/
theorem isPrime_span_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (Ideal.span {evalVertical x₀ w₀ P}).IsPrime ↔ (Ideal.span {P}).IsPrime :=
  (isRueckert_evalVertical x₀ w₀).isPrime_span_apply_iff hP

/-- A distinguished polynomial `P` over `𝒪_{E, x₀}` is prime in `(𝒪_{E, x₀})[X]` if and only if
`evalVertical x₀ w₀ P` is prime in `𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem prime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Prime (evalVertical x₀ w₀ P) ↔ Prime P :=
  (isRueckert_evalVertical x₀ w₀).prime_apply_iff hP

/-- If `evalVertical x₀ w₀ P` is irreducible in `𝒪_{E × ℂ, (x₀, w₀)}` for a distinguished
polynomial `P` over `𝒪_{E, x₀}`, then `P` is irreducible in `(𝒪_{E, x₀})[X]`. -/
theorem irreducible_of_irreducible_evalVertical_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hirr : Irreducible (evalVertical x₀ w₀ P)) : Irreducible P :=
  (isRueckert_evalVertical x₀ w₀).irreducible_of_irreducible_apply hP hirr

/-- If `evalVertical x₀ w₀ P` and `evalVertical x₀ w₀ Q` are relatively prime in
`𝒪_{E × ℂ, (x₀, w₀)}` for a distinguished polynomial `P` and an arbitrary polynomial `Q` over
`𝒪_{E, x₀}`, then `P` and `Q` are relatively prime in `(𝒪_{E, x₀})[X]`. -/
theorem isRelPrime_of_isRelPrime_evalVertical_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hrel : IsRelPrime (evalVertical x₀ w₀ P) (evalVertical x₀ w₀ Q)) : IsRelPrime P Q :=
  (isRueckert_evalVertical x₀ w₀).isRelPrime_of_isRelPrime_apply hP hrel

/-- If `evalVertical x₀ w₀ P` is squarefree in `𝒪_{E × ℂ, (x₀, w₀)}` for a distinguished
polynomial `P` over `𝒪_{E, x₀}`, then `P` is squarefree in `(𝒪_{E, x₀})[X]`. -/
theorem squarefree_of_squarefree_evalVertical_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hsq : Squarefree (evalVertical x₀ w₀ P)) : Squarefree P :=
  (isRueckert_evalVertical x₀ w₀).squarefree_of_squarefree_apply hP hsq

end FiniteDimensional

end TauCeti.holomorphicStructureSheaf
