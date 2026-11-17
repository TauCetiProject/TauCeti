/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rueckert

/-!
# Holomorphic stalks are unique factorization domains

At every point `x` of a finite-dimensional complex manifold `X` without boundary, the stalk
`𝒪_{X, x}` of holomorphic germs is a unique factorization domain (Rückert's factoriality theorem).
Because every unique factorization domain is integrally closed in its fraction field, every
holomorphic stalk is integrally closed as well.

The proof applies `stalk_induction` to `UniqueFactorizationMonoid`:

* for `Fin 0 → ℂ`, evaluation at the base point (`evalEquiv`) identifies the stalk with the field
  `ℂ`;
* for `Fin (n + 1) → ℂ ≃L[ℂ] (Fin n → ℂ) × ℂ`, vertical evaluation
  `(𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies the Rückert hypotheses for Weierstrass
  polynomials (`isRueckert_evalVertical`), and Rückert's factorial descent
  (`RingHom.IsRueckert.uniqueFactorizationMonoid`) passes unique factorization from `Fin n → ℂ`
  to `(Fin n → ℂ) × ℂ`.

Pulling back along an extended chart composed with a linear equivalence onto `Fin (finrank ℂ E) → ℂ`
transfers factoriality to any finite-dimensional complex manifold without boundary (allowing the
model space `E` to live in any universe and assuming only `[IsManifold I 1 X]`, upgraded to `ω`
by Hartogs–Cauchy analyticity). The comparison `smoothStalkIso` then transfers unique
factorization to the stalks of Mathlib's native complex-smooth structure sheaf. Finally, because
the base stalk is factorial, irreducibility, relative primality, and squarefreeness of a
Weierstrass polynomial in `𝒪_{E × ℂ, (x₀, w₀)}` coincide with those in `(𝒪_{E, x₀})[X]`.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`: holomorphic stalks on a
  finite-dimensional complex manifold without boundary are unique factorization domains.
* `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: stalks of the
  complex-smooth structure sheaf on a finite-dimensional complex manifold without boundary are
  unique factorization domains.
* `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.isRelPrime_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.squarefree_evalVertical_iff_of_isDistinguishedAt`:
  irreducibility, relative primality, and squarefreeness of a distinguished polynomial over
  `𝒪_{E, x₀}` in `(𝒪_{E, x₀})[X]` coincide with those of its vertical evaluation in
  `𝒪_{E × ℂ, (x₀, w₀)}`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Ch. II, Propositions 2.9 and 2.11,
  Theorem 2.10.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B,
  Theorem 9.
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Ch. 2, §2.2.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open Polynomial
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- **Rückert's factoriality theorem.** The stalk of holomorphic functions at any point of a
finite-dimensional complex manifold without boundary is a unique factorization domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  stalk_induction (P := fun R _ ↦ UniqueFactorizationMonoid R) inferInstance
    (fun e hR ↦ e.toMulEquiv.uniqueFactorizationMonoid hR) (fun h _ ↦ h.uniqueFactorizationMonoid) x

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorization domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end Manifold

section WeierstrassComparison

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {x₀ : E} {w₀ : ℂ}

/-- **Irreducibility of Weierstrass polynomials.** Over a finite-dimensional complex normed space
`E`, a polynomial `P` distinguished at the maximal ideal of `𝒪_{E, x₀}` is irreducible in
`(𝒪_{E, x₀})[X]` if and only if its vertical evaluation `evalVertical x₀ w₀ P` is irreducible in
`𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem irreducible_evalVertical_iff_of_isDistinguishedAt
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P :=
  (isRueckert_evalVertical x₀ w₀).irreducible_apply_iff hP

/-- **Relative primality for Weierstrass polynomials.** Over a finite-dimensional complex normed
space `E`, for a polynomial `P` distinguished at the maximal ideal of `𝒪_{E, x₀}` and any
polynomial `Q` over `𝒪_{E, x₀}`, the evaluations `evalVertical x₀ w₀ P` and
`evalVertical x₀ w₀ Q` are relatively prime in `𝒪_{E × ℂ, (x₀, w₀)}` if and only if `P` and `Q`
are relatively prime in `(𝒪_{E, x₀})[X]`. -/
theorem isRelPrime_evalVertical_iff_of_isDistinguishedAt
    {P Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    IsRelPrime (evalVertical x₀ w₀ P) (evalVertical x₀ w₀ Q) ↔ IsRelPrime P Q :=
  (isRueckert_evalVertical x₀ w₀).isRelPrime_apply_iff hP

/-- **Squarefreeness of Weierstrass polynomials.** Over a finite-dimensional complex normed space
`E`, a polynomial `P` distinguished at the maximal ideal of `𝒪_{E, x₀}` is squarefree in
`(𝒪_{E, x₀})[X]` if and only if its vertical evaluation `evalVertical x₀ w₀ P` is squarefree in
`𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem squarefree_evalVertical_iff_of_isDistinguishedAt
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Squarefree (evalVertical x₀ w₀ P) ↔ Squarefree P :=
  (isRueckert_evalVertical x₀ w₀).squarefree_apply_iff hP

end WeierstrassComparison

end TauCeti.holomorphicStructureSheaf
