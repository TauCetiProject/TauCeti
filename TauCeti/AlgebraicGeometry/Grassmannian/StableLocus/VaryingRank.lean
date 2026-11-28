/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.StableLocus
public import TauCeti.RingTheory.Grassmannian.VaryingRank
public import TauCeti.AlgebraicGeometry.Scheme.LocallyConstant
import TauCeti.AlgebraicGeometry.Limits.Sigma

/-!
# Classifying stable quotients of varying rank

A finite projective quotient need not have constant rank. Its clopen rank fibres decompose the
coefficient ring into a finite product. On each factor its kernel gives a point of the native
fixed-rank stable Grassmannian. These classifying maps assemble into a morphism to the finite
coproduct of stable Grassmannians.

The construction retains arbitrary, possibly nonreduced test algebras. Only the quotient stalk
ranks need a specified bound; a finite flat ambient module of bounded stalk rank supplies such a
bound. The finite index set includes ranks whose fibres are empty, with zero factor rings.

This file constructs the classifying morphism and characterizes its restrictions to the
canonical rank factors. The converse construction from an arbitrary morphism to the coproduct
is not asserted here.

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*, §1.1,
  for stable quotient Grassmannians in finite lattice charts.
* The Stacks Project, Tags 00EE and 089R, for clopen decompositions and quotient Grassmannians.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct PrimeSpectrum Submodule

attribute [local instance] Module.finitePresentation_of_projective

namespace Module.Grassmannian

variable {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A]

section ClassifyingMap

variable (d : ℕ) (t : Module.End R M)

/-- The finite coproduct of the stable quotient Grassmannians of ranks from zero to `d`. -/
noncomputable abbrev schemeStableLocusCoproduct : Scheme.{u} :=
  ∐ fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme

/-- The structure morphism of the finite coproduct of stable quotient Grassmannians. -/
noncomputable def schemeStableLocusCoproductToSpec :
    schemeStableLocusCoproduct d t ⟶ Spec (.of R) :=
  Sigma.desc fun r : Fin (d + 1) ↦
    (schemeStableLocus (r : ℕ) t).subschemeι ≫ toSpec R M r

/-- The structure morphism restricts to the native structure morphism on each rank summand. -/
@[reassoc (attr := simp)]
theorem ι_schemeStableLocusCoproductToSpec (r : Fin (d + 1)) :
    Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r ≫
        schemeStableLocusCoproductToSpec d t =
      (schemeStableLocus (r : ℕ) t).subschemeι ≫ toSpec R M r :=
  Sigma.ι_comp_desc _ _

section RankCover

variable {P : Type*} [AddCommGroup P] [Module A P]
  (N : Submodule A P) [Module.Finite A (P ⧸ N)] [Module.Projective A (P ⧸ N)]
  (hd : ∀ p : PrimeSpectrum A, Module.rankAtStalk (P ⧸ N) p ≤ d)

/-- The canonical morphism from the disjoint union of quotient-rank factors to `Spec A`.
It is an isomorphism when `d` bounds the quotient stalk ranks. -/
noncomputable def stableQuotientRankCover :
    (∐ fun r : Fin (d + 1) ↦ Spec (.of (quotientRankRing N r))) ⟶ Spec (.of A) :=
  LocallyConstant.specCover
    ⟨_, Module.isLocallyConstant_rankAtStalk (R := A) (M := P ⧸ N)⟩
    ⟨Fin.val, Fin.val_injective⟩

/-- Restriction of the rank-factor cover to a summand is the canonical coefficient map. -/
@[reassoc (attr := simp)]
theorem ι_stableQuotientRankCover (r : Fin (d + 1)) :
    Sigma.ι _ r ≫ stableQuotientRankCover d N =
      Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r))) :=
  LocallyConstant.ι_specCover
    ⟨_, Module.isLocallyConstant_rankAtStalk (R := A) (M := P ⧸ N)⟩
    ⟨Fin.val, Fin.val_injective⟩ r

include hd in
/-- The canonical rank-factor cover is an isomorphism onto `Spec A`. -/
theorem isIso_stableQuotientRankCover : IsIso (stableQuotientRankCover d N) := by
  apply LocallyConstant.isIso_specCover
    ⟨_, Module.isLocallyConstant_rankAtStalk (R := A) (M := P ⧸ N)⟩
    ⟨Fin.val, Fin.val_injective⟩
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨_, Nat.lt_succ_of_le (hd p)⟩, rfl⟩

end RankCover

variable (N : Submodule A (A ⊗[R] M)) [Module.Finite A ((A ⊗[R] M) ⧸ N)]
  [Module.Projective A ((A ⊗[R] M) ⧸ N)]
  (hd : ∀ p : PrimeSpectrum A, Module.rankAtStalk ((A ⊗[R] M) ⧸ N) p ≤ d)

/-- The classifying morphism of a stable kernel with finite projective, possibly varying-rank
quotient, obtained from the classifying morphisms on its canonical rank factors. -/
noncomputable def stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) :
    Spec (.of A) ⟶ schemeStableLocusCoproduct d t :=
  have := isIso_stableQuotientRankCover d N hd
  inv (stableQuotientRankCover d N) ≫ Limits.Sigma.map fun r : Fin (d + 1) ↦
    (schemeStableLocusHomEquiv (r : ℕ) t (quotientRankRing N r)
      ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val

/-- On the rank-`r` factor the classifying morphism is the native fixed-rank classifying map
followed by the inclusion of the rank-`r` summand. -/
@[reassoc]
theorem specMap_comp_stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : Fin (d + 1)) :
    Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r))) ≫
        stableQuotientToScheme d t N hd hN =
      (schemeStableLocusHomEquiv (r : ℕ) t (quotientRankRing N r)
        ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val ≫
          Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r := by
  have := isIso_stableQuotientRankCover d N hd
  rw [← ι_stableQuotientRankCover d N r]
  simp only [stableQuotientToScheme, Category.assoc, IsIso.hom_inv_id_assoc,
    Sigma.ι_map]

/-- The rank-`r` factor is the scheme-theoretic pullback of the rank-`r` summand along the
varying-rank classifying morphism. -/
theorem isPullback_specMap_stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : Fin (d + 1)) :
    IsPullback
      (schemeStableLocusHomEquiv (r : ℕ) t (quotientRankRing N r)
        ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val
      (Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r))))
      (Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r)
      (stableQuotientToScheme d t N hd hN) := by
  have := isIso_stableQuotientRankCover d N hd
  exact (isPullback_sigmaι_sigmaι_sigmaMap
    (fun r : Fin (d + 1) ↦
      (schemeStableLocusHomEquiv (r : ℕ) t (quotientRankRing N r)
        ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val) r).of_iso
    (Iso.refl _) (Iso.refl _) (asIso (stableQuotientRankCover d N)) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [stableQuotientToScheme])

/-- The inverse image of the rank-`r` summand is exactly the quotient-rank-`r` fibre. -/
@[simp]
theorem stableQuotientToScheme_preimage_range_ι
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : Fin (d + 1)) :
    stableQuotientToScheme d t N hd hN ⁻¹'
        Set.range (Sigma.ι (fun r : Fin (d + 1) ↦
          (schemeStableLocus (r : ℕ) t).subscheme) r) =
      {p | Module.rankAtStalk ((A ⊗[R] M) ⧸ N) p = r} := by
  have h := isPullback_specMap_stableQuotientToScheme d t N hd hN r
  have hrange :
      (Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r)))).opensRange =
        stableQuotientToScheme d t N hd hN ⁻¹ᵁ
          (Sigma.ι (fun r : Fin (d + 1) ↦
            (schemeStableLocus (r : ℕ) t).subscheme) r).opensRange := by
    simpa only [h.isoPullback_hom_snd, Scheme.Hom.opensRange_pullbackSnd] using
      Scheme.Hom.opensRange_comp_of_isIso h.isoPullback.hom (pullback.snd _ _)
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_preimage, ← hrange]
  simp only [Ideal.Quotient.algebraMap_eq, LocallyConstant.opensRange_specMap_fiberRing]
  exact coe_basicOpen_fiberIdempotent
    (Module.isLocallyConstant_rankAtStalk (R := A) (M := (A ⊗[R] M) ⧸ N)) (r : ℕ)

/-- The varying-rank classifying morphism lies over the ground ring. -/
@[reassoc (attr := simp)]
theorem stableQuotientToScheme_toSpec
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) :
    stableQuotientToScheme d t N hd hN ≫ schemeStableLocusCoproductToSpec d t =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  have := isIso_stableQuotientRankCover d N hd
  apply (cancel_epi (stableQuotientRankCover d N)).1
  apply Sigma.hom_ext
  intro r
  rw [ι_stableQuotientRankCover_assoc, ι_stableQuotientRankCover_assoc,
    specMap_comp_stableQuotientToScheme_assoc]
  simp only [schemeStableLocusCoproductToSpec, Sigma.ι_comp_desc]
  rw [(schemeStableLocusHomEquiv (r : ℕ) t (quotientRankRing N r) _).property,
    ← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The classifying morphism is uniquely specified by its native fixed-rank restrictions on
the canonical quotient-rank factors. -/
theorem eq_stableQuotientToScheme_iff
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A))
    (f : Spec (.of A) ⟶ schemeStableLocusCoproduct d t) :
    f = stableQuotientToScheme d t N hd hN ↔
      ∀ r : Fin (d + 1),
        Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r))) ≫ f =
          (schemeStableLocusHomEquiv (r : ℕ) t (quotientRankRing N r)
            ⟨quotientRankPoint N r,
              quotientRankPoint_mem_invtSubmodule N hN r⟩).val ≫
                Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r := by
  have := isIso_stableQuotientRankCover d N hd
  rw [← cancel_epi (stableQuotientRankCover d N), Sigma.hom_ext_iff]
  simp only [ι_stableQuotientRankCover_assoc, specMap_comp_stableQuotientToScheme]

end ClassifyingMap

end Module.Grassmannian
