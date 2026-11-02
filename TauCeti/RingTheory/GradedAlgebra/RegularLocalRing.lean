/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.GradedAlgebra.Cotangent
import Mathlib.Algebra.Module.SpanRankOperations
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Ideal
import TauCeti.RingTheory.Ideal.Cotangent.Localization

/-!
# Connected graded algebras that are regular at the vertex

Let `A` be an `ℕ`-graded algebra over a field `k` which is *connected*: its degree-zero part
consists of the scalars. Write `A₊` for the irrelevant ideal, the vertex of `Spec A`. If the local
ring `A_{A₊}` is regular of dimension `n`, then `A` is a polynomial algebra over `k` on `n`
homogeneous elements of positive degree.

Every element of `A` is a scalar modulo `A₊`
(`TauCeti.GradedAlgebra.exists_sub_algebraMap_mem_irrelevant`), so `A ⧸ A₊` is `k` and `A₊` is
maximal (`TauCeti.GradedAlgebra.isMaximal_toIdeal_irrelevant`). Localization then identifies the
cotangent space `A₊ ⧸ A₊²` with the cotangent space of `A_{A₊}`
(`Ideal.cotangentLocalizationEquiv`), compatibly with the identification of `k` with the
residue field. So whenever the maximal ideal of `A_{A₊}` is finitely generated, the cotangent space
`A₊ ⧸ A₊²` is finite-dimensional, of dimension the minimal number of generators of that maximal
ideal (`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg`). In the regular
case this number is `n`, while `A` has Krull dimension at least `n`, the dimension of its
localization, and at most the dimension of its cotangent space
(`TauCeti.GradedAlgebra.ringKrullDim_le_finrank_cotangent`). So the cotangent space has dimension
exactly `n`, and `A` is a polynomial algebra on `n` homogeneous
generators (`TauCeti.GradedAlgebra.exists_bijective_aeval_of_finrank_cotangent_le`).

No Noetherian hypothesis on `A` is needed: finite generation is a consequence.

For the invariants of a finite linear group this gives the last step of the homological proof of
the Chevalley–Shephard–Todd theorem: once the invariant ring is known to be regular at its
vertex, it is a polynomial algebra on homogeneous basic invariants.

## Main results

* `TauCeti.GradedAlgebra.finite_cotangent_of_fg`: if the maximal ideal of `A_{A₊}` is finitely
  generated, the cotangent space `A₊ ⧸ A₊²` is finite-dimensional over `k`.
* `TauCeti.GradedAlgebra.finrank_cotangent_le_spanFinrank`: its dimension is then at most the
  minimal number of generators of the maximal ideal of `A_{A₊}`.
* `TauCeti.GradedAlgebra.exists_bijective_aeval_of_isRegularLocalRing`: a connected graded algebra
  over a field whose localization at the irrelevant ideal is a regular local ring of dimension
  `n` is a polynomial algebra on `n` homogeneous elements of positive degree.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), § 18.
* W. Bruns, J. Herzog, *Cohen–Macaulay Rings*, Cambridge University Press (1993), Sections 1.5
  and 2.2.
-/

public section

open IsLocalRing

namespace TauCeti.GradedAlgebra

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- The cotangent space `A₊ ⧸ A₊²` over `k` has the same rank as the cotangent space of the
localization `A_{A₊}` over its residue field: localization identifies the two cotangent spaces
(`Ideal.cotangentLocalizationEquiv`), semilinearly for the identification of `k` with the residue
field. -/
private theorem rank_cotangent_eq (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    Module.rank k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent =
      Module.rank (ResidueField (Localization.AtPrime P))
        (CotangentSpace (Localization.AtPrime P)) := by
  have := (Ideal.Quotient.mk P).domain_nontrivial
  have : P.IsMaximal := hP ▸ isMaximal_toIdeal_irrelevant 𝒜 h𝒜
  have he := (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).bijective
  subst hP
  refine rank_eq_of_equiv_equiv (R' := ResidueField (Localization.AtPrime _))
    (fun c : k ↦ IsLocalization.AtPrime.equivQuotMaximalIdeal _ _ (algebraMap k _ c))
    (Ideal.cotangentLocalizationEquiv _ (Localization.AtPrime _)).toAddEquiv
    (he.comp ⟨(algebraMap k _).injective, surjective_algebraMap_quotient_irrelevant 𝒜 h𝒜⟩)
    fun c x ↦ ?_
  -- `c` acts on `A₊ ⧸ A₊²` through its image in `A ⧸ A₊`.
  have hc : c • x = algebraMap k (A ⧸ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) c • x := by
    rw [IsScalarTower.algebraMap_apply k A, algebraMap_smul, algebraMap_smul]
  rw [LinearEquiv.coe_toAddEquiv, hc]
  exact Ideal.cotangentLocalizationEquiv_smul _ _ _ _

/-- If the maximal ideal of the localization of a connected graded algebra at the irrelevant ideal
`A₊` is finitely generated, then the cotangent space `A₊ ⧸ A₊²` is finite-dimensional over `k`. -/
theorem finite_cotangent_of_fg (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (hfg : (maximalIdeal (Localization.AtPrime P)).FG) :
    Module.Finite k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent := by
  have : Module.Finite (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P)) :=
    Module.Finite.iff_fg.2 hfg
  have : Module.Finite (Localization.AtPrime P) (CotangentSpace (Localization.AtPrime P)) :=
    Module.Finite.of_surjective _ (Ideal.toCotangent_surjective _)
  have : Module.Finite (ResidueField (Localization.AtPrime P))
      (CotangentSpace (Localization.AtPrime P)) :=
    Module.Finite.of_restrictScalars_finite (Localization.AtPrime P) _ _
  rw [← Module.rank_lt_aleph0_iff, rank_cotangent_eq 𝒜 h𝒜 P hP]
  exact Module.rank_lt_aleph0 _ _

/-- If the maximal ideal of the localization of a connected graded algebra at the irrelevant ideal
`A₊` is finitely generated, then the dimension of the cotangent space `A₊ ⧸ A₊²` over `k` is at
most the minimal number of generators of that maximal ideal. -/
theorem finrank_cotangent_le_spanFinrank (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (hfg : (maximalIdeal (Localization.AtPrime P)).FG) :
    Module.finrank k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent ≤
      (maximalIdeal (Localization.AtPrime P)).spanFinrank := by
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg, Module.finrank,
    rank_cotangent_eq 𝒜 h𝒜 P hP, Module.finrank]

/-- **A connected graded algebra regular at its vertex is a polynomial algebra.** Let `A` be an
`ℕ`-graded algebra over a field `k` whose degree-zero part consists of the scalars. If its
localization at the irrelevant ideal `A₊` is a regular local ring of dimension `n`, then there are
`n` homogeneous elements of positive degree `f₁, …, fₙ` such that `k[X₁, …, Xₙ] → A`,
`Xᵢ ↦ fᵢ`, is an isomorphism.

The prime `P` is any prime equal to `A₊`, so that the statement applies to an ideal presented in
another form. -/
theorem exists_bijective_aeval_of_isRegularLocalRing (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    [IsRegularLocalRing (Localization.AtPrime P)] {n : ℕ}
    (hn : ringKrullDim (Localization.AtPrime P) = n) :
    ∃ f : Fin n → A, (∀ i, ∃ d, 0 < d ∧ f i ∈ 𝒜 d) ∧
      Function.Bijective (MvPolynomial.aeval (R := k) f) := by
  have hfg := IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime P))
  have := finite_cotangent_of_fg 𝒜 h𝒜 P hP hfg
  -- Compare dimensions: `n ≤ dim A ≤ dim_k (A₊ ⧸ A₊²) ≤ spanFinrank 𝔪 = n`.
  have hnA : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [← hn, IsLocalization.AtPrime.ringKrullDim_eq_height P]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  have hcot : Module.finrank k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent ≤ n := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime P)
    rw [hn] at this
    exact (finrank_cotangent_le_spanFinrank 𝒜 h𝒜 P hP hfg).trans (by exact_mod_cast this.le)
  have hcotn : Module.finrank k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent = n :=
    le_antisymm hcot (by exact_mod_cast hnA.trans (ringKrullDim_le_finrank_cotangent 𝒜 h𝒜))
  have h := exists_bijective_aeval_of_finrank_cotangent_le 𝒜 h𝒜 (by rwa [hcotn])
  rwa [hcotn] at h

end TauCeti.GradedAlgebra
