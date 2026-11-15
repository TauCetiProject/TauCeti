/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rueckert

import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Holomorphic stalks are unique factorization domains

At every point `x` of a finite-dimensional complex manifold `X` without boundary, the stalk
`𝒪_{X, x}` of holomorphic germs is a unique factorization domain (Rückert's factoriality theorem).
Because every unique factorization domain is integrally closed in its fraction field, every
holomorphic stalk is integrally closed as well.

The proof inducts on the complex dimension `n` of the model space:

* for `n = 0`, evaluation at the base point identifies the stalk with the field `ℂ`;
* for `n + 1`, a continuous linear isomorphism identifies the model with `(Fin n → ℂ) × ℂ`;
  vertical evaluation `(𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies the Rückert hypotheses
  for Weierstrass polynomials (`isRueckert_evalVertical`), and Rückert's factorial descent
  (`RingHom.IsRueckert.uniqueFactorizationMonoid`) passes unique factorization from `Fin n → ℂ`
  to `(Fin n → ℂ) × ℂ`.

Pulling back along an extended chart composed with a linear equivalence onto a model in `Type`
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

open Filter Module Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section NormedSpace

/-- On a zero-dimensional complex normed space, evaluation at the base point identifies the
holomorphic stalk with `ℂ`, so the stalk is a unique factorization domain. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq_zero {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (hV : finrank ℂ V = 0)
    (x : V) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) := by
  have hV' : ∀ y : V, y = x := fun y ↦
    (finrank_zero_iff_forall_zero.1 hV y).trans (finrank_zero_iff_forall_zero.1 hV x).symm
  refine (RingEquiv.ofBijective (eval 𝓘(ℂ, V) V x)
    ⟨(RingHom.injective_iff_ker_eq_bot _).2 <| eq_bot_iff.2 fun s hs ↦ ?_,
      eval_surjective _ _ x⟩).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance
  obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
  refine (eq_zero_iff_of_toFilterGerm_eq (hφ _ le_rfl)).2 (Eventually.of_forall fun y ↦ ?_)
  rw [hV' y, ← eval_eq_of_toFilterGerm_eq (hφ _ le_rfl), RingHom.mem_ker.1 hs, Pi.zero_apply]

/-- Holomorphic stalks of a finite-dimensional complex normed space are unique factorization
domains, by induction on the dimension through Weierstrass preparation and Rückert's descent. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ x : V,
        UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x)
  | 0, _, _, _, _, hV, x => uniqueFactorizationMonoid_stalk_of_finrank_eq_zero hV x
  | n + 1, V, _, _, _, hV, x => by
    let e : V ≃L[ℂ] (Fin n → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hV])
    have := uniqueFactorizationMonoid_stalk_of_finrank_eq n (Fin n → ℂ) (by simp) (e x).1
    have hex : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ) ((Fin n → ℂ) × ℂ)).presheaf.stalk
          (e x)) :=
      (isRueckert_evalVertical (e x).1 (e x).2).uniqueFactorizationMonoid
    exact (e.holomorphicStalkEquiv x).toMulEquiv.uniqueFactorizationMonoid hex

end NormedSpace

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- **Rückert's factoriality theorem.** The stalk of holomorphic functions at any point of a
finite-dimensional complex manifold without boundary is a unique factorization domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  obtain ⟨E', _, _, _, ⟨e⟩⟩ : ∃ (E' : Type) (_ : NormedAddCommGroup E') (_ : NormedSpace ℂ E')
      (_ : FiniteDimensional ℂ E'), Nonempty (E ≃L[ℂ] E') :=
    ⟨Fin (finrank ℂ E) → ℂ, inferInstance, inferInstance, inferInstance,
      ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩⟩
  have hmodel := uniqueFactorizationMonoid_stalk_of_finrank_eq _ E' rfl ((e ∘ extChartAt I x) x)
  exact (RingEquiv.ofBijective _
    (stalkPullback_comp_extChartAt_bijective x e)).toMulEquiv.uniqueFactorizationMonoid hmodel

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
