/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import TauCeti.FieldTheory.Galois.ConjugateFields
import TauCeti.FieldTheory.GaloisGroups.Symmetric.Realization
import TauCeti.GroupTheory.AlmostConjugate.GassmannPair
import TauCeti.NumberTheory.NumberField.ArithmeticEquivalence.Basic
import TauCeti.NumberTheory.NumberField.SplittingField

/-!
# Nonisomorphic arithmetically equivalent number fields

Realizing `S₁₆` as a Galois group over `ℚ`
(`TauCeti.exists_monic_int_polynomial_hasFullSymmetricGaloisGroup`) and pulling back the
non-conjugate almost-conjugate pair of order `16` in `S₁₆` (`TauCeti.exists_S16_gassmann_pair`)
yields two nonisomorphic number fields with the same Dedekind zeta coefficients
(`TauCeti.exists_dedekindZetaCoeff_eq_not_isomorphic`), since fixed fields of subgroups of a finite
Galois extension are isomorphic exactly when the subgroups are conjugate
(`Subgroup.nonempty_fixedField_algEquiv_iff_exists_map_conj_eq`).

## Main results

* `TauCeti.exists_dedekindZetaCoeff_eq_not_isomorphic`: existence of two nonisomorphic number
  fields with the same Dedekind zeta coefficients.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

namespace TauCeti

/-- **Nonisomorphic number fields with the same zeta function** (Gassmann). There exist two number
fields with the same number of integral ideals of every absolute norm that are not isomorphic. -/
theorem exists_dedekindZetaCoeff_eq_not_isomorphic :
    ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : NumberField K) (_ : NumberField L),
      (∀ n : ℕ, dedekindZetaCoeff K n = dedekindZetaCoeff L n) ∧ IsEmpty (K ≃+* L) := by
  -- Realize `S₁₆` as the Galois group of a splitting field `E / ℚ`.
  obtain ⟨f, -, hdeg, -, hsym⟩ :=
    exists_monic_int_polynomial_hasFullSymmetricGaloisGroup 16 (by decide)
  let g : Polynomial ℚ := f.map (Int.castRingHom ℚ)
  have hgdeg : g.natDegree = 16 := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hdeg]
  have : IsGalois ℚ g.SplittingField := IsGalois.of_separable_splitting_field hsym.separable
  obtain ⟨e₀⟩ := hsym.nonempty_mulEquiv
  let e : (g.SplittingField ≃ₐ[ℚ] g.SplittingField) ≃* Equiv.Perm (Fin 16) :=
    e₀.trans (Equiv.permCongrHom (finCongr hgdeg))
  -- Pull back the non-conjugate Gassmann pair from `S₁₆` to `Gal(E / ℚ)`.
  obtain ⟨H₀, K₀, -, -, hac₀, hnc₀⟩ := exists_S16_gassmann_pair
  let H : Subgroup (g.SplittingField ≃ₐ[ℚ] g.SplittingField) :=
    H₀.comap (e : (g.SplittingField ≃ₐ[ℚ] g.SplittingField) →* Equiv.Perm (Fin 16))
  let K : Subgroup (g.SplittingField ≃ₐ[ℚ] g.SplittingField) :=
    K₀.comap (e : (g.SplittingField ≃ₐ[ℚ] g.SplittingField) →* Equiv.Perm (Fin 16))
  have hac : H.AlmostConjugate K := hac₀.comap e
  have hnc : ¬ ∃ σ : g.SplittingField ≃ₐ[ℚ] g.SplittingField, H.map (MulAut.conj σ) = K :=
    fun h ↦ hnc₀ ((Subgroup.exists_map_conj_comap_eq_iff e H₀ K₀).mp h)
  -- Their fixed fields are arithmetically equivalent by Gassmann's theorem and nonisomorphic.
  refine ⟨↥(IntermediateField.fixedField H), ↥(IntermediateField.fixedField K),
    inferInstance, inferInstance, inferInstance, inferInstance,
    H.dedekindZetaCoeff_fixedField_eq_of_almostConjugate K hac, ⟨fun φ ↦ ?_⟩⟩
  have halg : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ] ↥(IntermediateField.fixedField K) :=
    AlgEquiv.ofRingEquiv (f := φ) fun q ↦ by
      simp [eq_ratCast]
  exact hnc ((Subgroup.nonempty_fixedField_algEquiv_iff_exists_map_conj_eq H K).mp ⟨halg⟩)

end TauCeti
