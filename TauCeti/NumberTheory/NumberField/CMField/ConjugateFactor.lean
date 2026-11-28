/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
public import TauCeti.RingTheory.RamificationInertia.ConjugateFactors

/-!
# Contraction of primes selected by a conjugate factor

In a CM field, suppose `z · conj z` vanishes to order one at every prime above a given
rational prime. Among the primes above each prime of the maximal real subfield, precisely
one contains `z`. Contraction thus reindexes the chosen residue factors by primes of the
real subfield. In particular this applies to a factor `z · conj z = p` of a completely
split rational prime `p`.

This realizes the conjugate-pair selection used in `New.Data.isSplitLevel_piNPlaces`
and `New.Data.card_piNPlaces` in `grh/src/New/UpperBound/Objects/Columns.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`, by contraction
rather than by counting pairs.
-/

public section

open NumberField NumberField.IsCMField
open scoped Pointwise

namespace Ideal

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- If `z · conj z` belongs to each prime over `p` but not its square, contraction identifies
those primes containing `z` with the primes over `p` in the maximal real subfield. -/
noncomputable def primesOverConjugateFactorEquiv (p : Ideal ℤ) (z : 𝓞 E)
    (hz : ∀ P : p.primesOver (𝓞 E),
      z * ringOfIntegersComplexConj E z ∈ P.val ∧
      z * ringOfIntegersComplexConj E z ∉ P.val ^ 2) :
    {P : p.primesOver (𝓞 E) // z ∈ P.val} ≃ p.primesOver (𝓞 (maximalRealSubfield E)) := by
  classical
  let R := 𝓞 (maximalRealSubfield E)
  let f (P : {P : p.primesOver (𝓞 E) // z ∈ P.val}) : p.primesOver R :=
    ⟨P.val.val.under R, inferInstance, inferInstance⟩
  let c := (ringOfIntegersComplexConj E).restrictScalars ℤ
  let e := primesOverEquivSumOfConjugateFactors p c z hz
  have he₀ (P : {P : p.primesOver (𝓞 E) // z ∈ P.val}) : (e (.inl P)).val = P.val.val :=
    congrArg Subtype.val (primesOverEquivSumOfConjugateFactors_apply_inl p c z hz P)
  have he₁ (P : {P : p.primesOver (𝓞 E) // z ∈ P.val}) :
      (e (.inr P)).val = complexConj E • P.val.val :=
    (congrArg Subtype.val (primesOverEquivSumOfConjugateFactors_apply_inr p c z hz P)).trans
      (coe_smul_primesOver c P.val)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro P Q heq
    have hu : P.val.val.under R = Q.val.val.under R := congrArg Subtype.val heq
    obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R (𝓞 E)
      (E ≃ₐ[maximalRealSubfield E] E) _ _ hu
    have hcard : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 :=
      (IsGalois.card_aut_eq_finrank _ _).trans (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    by_cases hσ₁ : σ = 1
    · exact Subtype.ext (Subtype.ext (by simpa [hσ₁] using hσ.symm))
    have hσc := ExistsUnique.unique (Nat.card_eq_two_iff' 1 |>.mp hcard) hσ₁ (complexConj_ne_one E)
    have hsame : e (.inl Q) = e (.inr P) :=
      Subtype.ext ((he₀ Q).trans ((hσc ▸ hσ).trans (he₁ P).symm))
    exact (Sum.inl_ne_inr (e.injective hsame)).elim
  · intro Q
    obtain ⟨P⟩ : Nonempty (Q.val.primesOver (𝓞 E)) := inferInstance
    let P' : p.primesOver (𝓞 E) := ⟨P.val, P.property.1, Ideal.LiesOver.trans P.val Q.val p⟩
    obtain ⟨S | S, hS⟩ := e.surjective P'
    · have hmap : S.val.val = P.val := (he₀ S).symm.trans (congrArg Subtype.val hS)
      exact ⟨S, Subtype.ext ((congrArg (under R) hmap).trans P.property.2.over.symm)⟩
    · have hmap : complexConj E • S.val.val = P.val :=
        (he₁ S).symm.trans (congrArg Subtype.val hS)
      exact ⟨S, Subtype.ext ((under_smul R S.val.val (complexConj E)).symm.trans
        ((congrArg (under R) hmap).trans P.property.2.over.symm))⟩

/-- The reindexing of the chosen primes is contraction of the ideal. -/
@[simp] theorem primesOverConjugateFactorEquiv_apply (p : Ideal ℤ) (z : 𝓞 E)
    (hz : ∀ P : p.primesOver (𝓞 E),
      z * ringOfIntegersComplexConj E z ∈ P.val ∧
      z * ringOfIntegersComplexConj E z ∉ P.val ^ 2)
    (P : {P : p.primesOver (𝓞 E) // z ∈ P.val}) :
    (primesOverConjugateFactorEquiv p z hz P).val =
      P.val.val.under (𝓞 (maximalRealSubfield E)) := (rfl)

end Ideal
