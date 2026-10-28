/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ClosedImmersion.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ClosedImmersion.Mono
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.GlueMorphisms

/-!
# The factorisation property of closed immersions

Let `(A, A⁺)` be a Huber pair with `A` complete and Hausdorff, `J ⊆ A` a closed ideal, and
suppose the structure presheaves of `Spa(A, A⁺)` and `Spa(A ⧸ J, (A ⧸ J)⁺)` are sheaves, so that
the quotient morphism `i : Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)` is a closed immersion of adic
spaces. This file proves its universal property: a morphism `f : X ⟶ Spa(A, A⁺)` out of an adic
space `X` factors through `i` exactly when its global-sections map `A → 𝒪_X(X)`
(`TauCeti.ValuationSpectrum.presentationLimitAppTop`) kills `J`, and the factorisation is then
unique. This is the closed-subspace counterpart of the universal property of `Spec (A ⧸ J)` in
algebraic geometry.

* Necessity holds for every source: the global-sections map of `i` is the quotient map
  `A → A ⧸ J` up to the identification of `A ⧸ J` with the global sections of
  `Spa(A ⧸ J, (A ⧸ J)⁺)`, so it kills `J`, and so does that of every `g ≫ i`.
* Uniqueness holds because `i` is a monomorphism of sheafy pre-adic spaces
  (`TauCeti.SheafyPreAdicSpace.mono_of_isClosedImmersion`).
* For existence, cover `X` by its open affinoid subspaces `U ≅ Spa(B, B⁺)`, with `B` complete and
  Hausdorff (`TauCeti.PreAdicSpace.isAffinoid_iff_exists_complete`). The restriction of `f` to
  `U` is a morphism of affinoid spectra whose ring map `A → B` kills `J`, so it factors through
  `i` (`TauCeti.ValuationSpectrum.exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq`).
  Since `i` is a monomorphism, these local factorisations glue
  (`TauCeti.SheafyPreAdicSpace.exists_comp_eq_of_iSup_eq_top`).

## Main results

* `TauCeti.ValuationSpectrum.le_ker_presentationLimitAppTop_comp_quotientComap`: the
  global-sections map of a morphism factoring through `i` kills `J`.
* `TauCeti.ValuationSpectrum.existsUnique_comp_presentationLimitPreAdicSpaceQuotientComap_eq`:
  a morphism out of an adic space whose global-sections map kills `J` factors uniquely through
  `i`.
* `TauCeti.ValuationSpectrum.exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq_iff`: a
  morphism out of an adic space factors through `i` exactly when its global-sections map
  kills `J`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.38, §8.1 and
  §8.3.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition PreAdicSpace

universe u

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] {X : PreAdicSpace.{u}}

section Huber

variable [IsHuberRing A] (P : PairOfDefinition A) (S : Pair A)
  (hS : P.ringOfDefinition ≤ S.plus) (J : Ideal A) (hJ : IsClosed (J : Set A))
  (hsheafJ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
    (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))

include hJ in
/-- **A morphism factoring through the quotient morphism kills `J` on global sections.** For a
closed ideal `J` of a complete Hausdorff Huber ring `A`, the global-sections map
`A → 𝒪_X(X)` of `g ≫ i`, for the quotient morphism `i : Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)`, kills
`J`. -/
theorem le_ker_presentationLimitAppTop_comp_quotientComap
    (g : X ⟶ presentationLimitPreAdicSpace (P.quotient J) (S.quotient J).plus
      (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
      (P.quotient_ringOfDefinition_le_quotient_plus hS J)) :
    J ≤ RingHom.ker (presentationLimitAppTop P S.plus _ hS
      (g ≫ presentationLimitPreAdicSpaceQuotientComap S P hS J hsheafJ)) := by
  -- `A ⧸ J` is again complete and Hausdorff, so the global-sections map of the quotient morphism
  -- is recovered as the quotient map `A → A ⧸ J`
  let _ : UniformSpace (A ⧸ J) := IsTopologicalAddGroup.rightUniformSpace _
  have _ : IsUniformAddGroup (A ⧸ J) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (A ⧸ J) := QuotientAddGroup.completeSpace_right _ J.toAddSubgroup
  have _ : T1Space (A ⧸ J) := (Ideal.Quotient.t1Space_iff J).mpr hJ
  refine le_trans ?_ (ker_presentationLimitAppTop_le_comp P S.plus _ hS g _)
  rw [← ker_presentationLimitHomRingHom, presentationLimitPreAdicSpaceQuotientComap_def,
    presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap, Ideal.mk_ker]

include hJ in
/-- **The factorisation property of the quotient morphism.** Let `A` be a complete Hausdorff Huber
ring and `J` a closed ideal, and suppose `Spa(A, A⁺)` and `Spa(A ⧸ J, (A ⧸ J)⁺)` are sheafy. Then
a morphism `f : X ⟶ Spa(A, A⁺)` out of an adic space whose global-sections map `A → 𝒪_X(X)` kills
`J` factors uniquely through the quotient morphism `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)`. -/
theorem existsUnique_comp_presentationLimitPreAdicSpaceQuotientComap_eq
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hX : isAdic X)
    (f : X ⟶ presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      hS)
    (hf : J ≤ RingHom.ker (presentationLimitAppTop P S.plus _ hS f)) :
    ∃! g, g ≫ presentationLimitPreAdicSpaceQuotientComap S P hS J hsheafJ = f := by
  let i := presentationLimitPreAdicSpaceQuotientComap S P hS J hsheafJ
  let Y : SheafyPreAdicSpace.{u} := ⟨presentationLimitPreAdicSpace P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hS, hsheaf⟩
  let Z : SheafyPreAdicSpace.{u} := ⟨presentationLimitPreAdicSpace (P.quotient J)
    (S.quotient J).plus (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
    (P.quotient_ringOfDefinition_le_quotient_plus hS J), hsheafJ⟩
  let X' : SheafyPreAdicSpace.{u} := ⟨X, hX.isSheafy⟩
  let i' : Z ⟶ Y := ObjectProperty.homMk i
  have : Mono i' := SheafyPreAdicSpace.mono_of_isClosedImmersion i'
    (isClosedImmersion_presentationLimitPreAdicSpaceQuotientComap S P hS J hsheafJ hJ)
  -- on each open affinoid subspace `U ≅ Spa(B, B⁺)`, the restriction of `f` factors through `i`
  have hloc (U : X.affinoidOpens) : ∃ g : X.restrict U.1.isOpenEmbedding ⟶ Z.obj,
      g ≫ i = X.ofRestrict U.1.isOpenEmbedding ≫ f := by
    obtain ⟨B, _, _, _, _, _, _, _, T, P', hT, ⟨e⟩⟩ := (isAffinoid_iff_exists_complete _).mp U.2
    have hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus) :=
      ObjectProperty.prop_of_iso isSheafy e (isSheafy_restrict _ hX.isSheafy)
    have hf' : J ≤ RingHom.ker (presentationLimitHomPairHom P P' S T hS hT
        ((e.inv ≫ X.ofRestrict U.1.isOpenEmbedding) ≫ f)).toRingHom := by
      rw [presentationLimitHomPairHom_toRingHom, ker_presentationLimitHomRingHom]
      exact hf.trans (ker_presentationLimitAppTop_le_comp P S.plus _ hS _ f)
    obtain ⟨g, hg⟩ := exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq P P' S T hS hT J
      hsheafJ hsheafT _ hf'
    exact ⟨e.hom ≫ g, by rw [Category.assoc, hg, Category.assoc, e.hom_inv_id_assoc]⟩
  choose g hg using hloc
  -- the local factorisations glue, since `i` is a monomorphism of sheafy pre-adic spaces
  obtain ⟨g', hg'⟩ := SheafyPreAdicSpace.exists_comp_eq_of_iSup_eq_top i'
    (ObjectProperty.homMk f : X' ⟶ Y) (fun U : X.affinoidOpens ↦ U.1)
    ((sSup_eq_iSup' _).symm.trans ((isLocallyAffinoid_iff_sSup_eq_top X).mp hX.isLocallyAffinoid))
    g hg
  refine ⟨g'.hom, congrArg InducedCategory.Hom.hom hg', fun g'' hg'' ↦ ?_⟩
  -- uniqueness: `i` is a monomorphism
  have h : (ObjectProperty.homMk g'' : X' ⟶ Z) ≫ i' = g' ≫ i' := by
    ext1
    exact hg''.trans (congrArg InducedCategory.Hom.hom hg').symm
  exact congrArg InducedCategory.Hom.hom ((cancel_mono i').mp h)

include hJ in
/-- **Morphisms into the closed subspace cut out by `J`.** Let `A` be a complete Hausdorff Huber
ring and `J` a closed ideal, and suppose `Spa(A, A⁺)` and `Spa(A ⧸ J, (A ⧸ J)⁺)` are sheafy. A
morphism `f : X ⟶ Spa(A, A⁺)` out of an adic space factors through the quotient morphism
`Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)` exactly when its global-sections map `A → 𝒪_X(X)` kills `J`;
the factorisation is then unique
(`existsUnique_comp_presentationLimitPreAdicSpaceQuotientComap_eq`). -/
theorem exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq_iff
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hX : isAdic X)
    (f : X ⟶ presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      hS) :
    (∃ g, g ≫ presentationLimitPreAdicSpaceQuotientComap S P hS J hsheafJ = f) ↔
      J ≤ RingHom.ker (presentationLimitAppTop P S.plus _ hS f) := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun hf ↦
    (existsUnique_comp_presentationLimitPreAdicSpaceQuotientComap_eq P S hS J hJ hsheafJ hsheaf hX
      f hf).exists⟩
  subst hg
  exact le_ker_presentationLimitAppTop_comp_quotientComap P S hS J hJ hsheafJ g

end Huber

end TauCeti.ValuationSpectrum

end
