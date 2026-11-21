/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RingHom.StandardSyntomic
import Mathlib.RingTheory.Unramified.LocalStructure
import TauCeti.RingTheory.Extension.Cotangent.Rank
import TauCeti.RingTheory.Extension.Cotangent.StandardEtale
import TauCeti.RingTheory.KrullDimension.GoingDown
import TauCeti.RingTheory.Syntomic.KrullDimension
import TauCeti.RingTheory.Syntomic.LocalCriterion

/-!
# Descent of standard syntomic algebras along étale maps of the source

Being a local complete intersection over a field descends along étale maps of the source. If `A`
is of finite type over a field `k` and `B` is an étale `A`-algebra which is locally standard
syntomic of relative dimension `n` over `k`, then every prime of `A` under a prime of `B` has a
standard syntomic neighbourhood
(`TauCeti.exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_etale`). When
`B` is faithfully flat over `A`, it follows that `A` is locally standard syntomic of relative
dimension `n` over `k`
(`TauCeti.locally_isStandardSyntomicOfRelativeDimension_of_etale_of_faithfullyFlat`). This is the
affine input for descending syntomicity, and with it nodality of relative curves, along étale
covers of the source.

The proof bounds the number of equations needed near a prime of `A`. Present `A` as
`k[x₁, …, x_m] ⧸ I`, and shrink `B` around a prime `Q` until it is standard étale over `A`, with
presentation `A[y, w] ⧸ (f, w g - 1)`, and standard syntomic over `k`. Presenting `B` over `k` by
the generators `x, y, w`, the fibre of the conormal module at `Q` has dimension two more than that
of `I` (`Algebra.Generators.finrank_tensor_cotangent_comp_of_isStandardEtale`), and comparison with
the standard syntomic presentation of `B` bounds the fibre of `I` at `Q` by `m - n`. The image of
`Spec B → Spec A` is an open neighbourhood of `Q ∩ A`, and on it heights are at most
`dim B ≤ n`, since flat maps satisfy going down
(`TauCeti.exists_notMem_forall_height_le_ringKrullDim_of_hasGoingDown`).
The presentation criterion
`TauCeti.exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_finrank_le`
then gives the standard syntomic neighbourhood.

## Main results

* `TauCeti.exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_etale`: every
  prime of `A` under a prime of an étale, locally standard syntomic `A`-algebra has a standard
  syntomic neighbourhood.
* `TauCeti.locally_isStandardSyntomicOfRelativeDimension_of_etale_of_faithfullyFlat`: local
  complete intersections over a field descend along faithfully flat étale maps.

## References

* The Stacks Project, Descent, Section *Properties of morphisms local in the syntomic topology on
  the source*: syntomicity is local on the source for the syntomic, hence the étale, topology.
-/

public section

open TensorProduct

namespace TauCeti

universe u

variable {n : ℕ} {k A B : Type u} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- The case of `exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_etale`
where `B` is standard étale over `A` and standard syntomic over `k`. -/
private theorem exists_notMem_isStandardSyntomicOfRelativeDimension_of_isStandardEtale
    [Algebra.FiniteType k A] [Algebra.IsStandardEtale A B]
    [Algebra.IsStandardSyntomicOfRelativeDimension n k B] (Q : Ideal B) [Q.IsPrime] :
    ∃ g ∉ Q.comap (algebraMap A B),
      Algebra.IsStandardSyntomicOfRelativeDimension n k (Localization.Away g) := by
  have : Algebra.FinitePresentation k A :=
    (Algebra.FinitePresentation.of_finiteType (R := k)).mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation k A
  -- The point `F = κ(Q)`, with its algebra structures over `A` and `k[ι]`.
  let F := Q.ResidueField
  let : Algebra A F := ((algebraMap B F).comp (algebraMap A B)).toAlgebra
  let : Algebra P.Ring F := ((algebraMap A F).comp (algebraMap P.Ring A)).toAlgebra
  have : IsScalarTower A B F := .of_algebraMap_eq' rfl
  have : IsScalarTower P.Ring A F := .of_algebraMap_eq' rfl
  have hF (r : P.Ring) (hr : algebraMap P.Ring A r ∈ Q.comap (algebraMap A B)) :
      algebraMap P.Ring F r = 0 := by
    rw [IsScalarTower.algebraMap_apply P.Ring A F, IsScalarTower.algebraMap_apply A B F]
    exact Ideal.algebraMap_residueField_eq_zero.mpr (Ideal.mem_comap.mp hr)
  -- Compare the presentation of `B` through the standard étale coordinates with a standard
  -- syntomic presentation of `B`: the kernel of `P` needs at most `#ι - n` generators near `Q`.
  have hfin : Module.finrank F (F ⊗[P.Ring] P.ker) + n ≤
      Nat.card (Fin (Algebra.Presentation.ofFinitePresentationVars k A)) := by
    obtain ⟨ι', σ', _, _, P', hP'⟩ :=
      (‹Algebra.IsStandardSyntomicOfRelativeDimension n k B›).exists_presentation
    let Pe := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := A) (S := B)).some
    have : Module.Finite A P.toExtension.Cotangent := Algebra.Extension.Cotangent.finite P.fg_ker
    have h1 := (Pe.toSubmersivePresentation.toGenerators.comp P.toGenerators
      ).finrank_tensor_cotangent_add_card_le F P'
    rw [Algebra.Generators.finrank_tensor_cotangent_comp_of_isStandardEtale P.toGenerators
      Pe.toSubmersivePresentation F, P.toGenerators.finrank_tensor_cotangent F] at h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, hP'] at h1 ⊢
    omega
  have hdimB : ringKrullDim B ≤ n :=
    ringKrullDim_le_of_locally_isStandardSyntomicOfRelativeDimension (RingHom.locally_of
      (isStandardSyntomicOfRelativeDimension_respectsIso n) (algebraMap k B)
      (isStandardSyntomicOfRelativeDimension_algebraMap.mpr inferInstance))
  obtain ⟨a, ha, hdim⟩ := exists_notMem_forall_height_le_ringKrullDim_of_hasGoingDown (A := A) Q
  exact exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_finrank_le
    P.toGenerators _ F hF hfin ha fun p hp hap ↦ WithBot.coe_le_coe.mp ((hdim p hp hap).trans hdimB)

/-- **Local complete intersections descend along étale maps.** Let `A` be a finite type algebra
over a field `k`, and `B` an étale `A`-algebra which is locally standard syntomic of relative
dimension `n` over `k`. Then every prime of `A` under a prime `Q` of `B` has a neighbourhood
`A[1/g]` which is standard syntomic of relative dimension `n` over `k`. -/
theorem exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_etale
    [Algebra.FiniteType k A] [Algebra.Etale A B]
    (h : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n) (algebraMap k B))
    (Q : Ideal B) [Q.IsPrime] :
    ∃ g ∉ Q.comap (algebraMap A B),
      Algebra.IsStandardSyntomicOfRelativeDimension n k (Localization.Away g) := by
  -- A standard étale neighbourhood `B₁ = B[1/t₁]` of `Q`, still locally standard syntomic.
  obtain ⟨t₁, ht₁, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let B₁ := Localization.Away t₁
  let Q₁ := Q.map (algebraMap B B₁)
  have : Q₁.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers t₁) B₁ Q
    inferInstance ((Ideal.disjoint_powers_iff_notMem _ ‹Q.IsPrime›.isRadical).mpr ht₁)
  have h₁ : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n) (algebraMap k B₁) := by
    rw [IsScalarTower.algebraMap_eq k B B₁]
    exact RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget
      (isStandardSyntomicOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      _ t₁ _ h
  -- A standard syntomic neighbourhood `B₂ = B₁[1/t₂]` of `Q₁`, still standard étale.
  obtain ⟨t₂, hdisj, _⟩ :=
    exists_disjoint_powers_isStandardSyntomicOfRelativeDimension_of_locally h₁ Q₁
      ‹Q₁.IsPrime›.ne_top
  let B₂ := Localization.Away t₂
  have : Algebra.IsStandardEtale A B₂ := .of_isLocalizationAway t₂
  let Q₂ := Q₁.map (algebraMap B₁ B₂)
  have : Q₂.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ Q₁ inferInstance hdisj.symm
  have hQ : Q₂.under A = Q.under A := by
    have e₂ : Q₂.under B₁ = Q₁ :=
      IsLocalization.under_map_of_isPrime_disjoint (.powers t₂) B₂ inferInstance hdisj.symm
    have e₁ : Q₁.under B = Q :=
      IsLocalization.under_map_of_isPrime_disjoint (.powers t₁) B₁ inferInstance
        ((Ideal.disjoint_powers_iff_notMem _ ‹Q.IsPrime›.isRadical).mpr ht₁)
    rw [← Ideal.under_under (B := B₁), e₂, ← Ideal.under_under (B := B), e₁]
  rw [← Ideal.under_def, ← hQ]
  exact exists_notMem_isStandardSyntomicOfRelativeDimension_of_isStandardEtale Q₂

/-- **Local complete intersections descend along étale covers.** Let `A` be a finite type algebra
over a field `k`, and `B` a faithfully flat étale `A`-algebra. If `B` is locally standard syntomic
of relative dimension `n` over `k`, then so is `A`. -/
theorem locally_isStandardSyntomicOfRelativeDimension_of_etale_of_faithfullyFlat
    [Algebra.FiniteType k A] [Algebra.Etale A B] [Module.FaithfullyFlat A B]
    (h : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n) (algebraMap k B)) :
    RingHom.Locally (IsStandardSyntomicOfRelativeDimension n) (algebraMap k A) := by
  refine locally_isStandardSyntomicOfRelativeDimension_of_forall_isMaximal fun m hm ↦ ?_
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B)
    ⟨m, hm.isPrime⟩
  have hQm : Q.asIdeal.comap (algebraMap A B) = m := by
    rw [← PrimeSpectrum.comap_asIdeal, hQ]
  obtain ⟨g, hg, hstd⟩ :=
    exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_etale (A := A) h
      Q.asIdeal
  exact ⟨g, hQm ▸ hg, hstd⟩

end TauCeti
