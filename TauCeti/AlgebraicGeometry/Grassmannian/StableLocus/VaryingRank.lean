/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.StableLocus
public import TauCeti.RingTheory.Grassmannian.VaryingRank
public import TauCeti.AlgebraicGeometry.Scheme.Rank
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

variable (N : Submodule A (A ⊗[R] M)) [Module.Finite A ((A ⊗[R] M) ⧸ N)]
  [Module.Projective A ((A ⊗[R] M) ⧸ N)]
  (hd : ∀ p : PrimeSpectrum A, Module.rankAtStalk ((A ⊗[R] M) ⧸ N) p ≤ d)

/-- The classifying morphism of a stable kernel with finite projective, possibly varying-rank
quotient, obtained from the classifying morphisms on its canonical rank factors. -/
noncomputable def stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) :
    Spec (.of A) ⟶ schemeStableLocusCoproduct d t :=
  have := Module.isIso_rankSpecCover A ((A ⊗[R] M) ⧸ N) d hd
  inv (Module.rankSpecCover A ((A ⊗[R] M) ⧸ N) d) ≫ Limits.Sigma.map fun r : Fin (d + 1) ↦
    (schemeStableLocusHomEquiv (r : ℕ) t (Module.rankRing A ((A ⊗[R] M) ⧸ N) r)
      ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val

/-- On the rank-`r` factor the classifying morphism is the native fixed-rank classifying map
followed by the inclusion of the rank-`r` summand. -/
@[reassoc]
theorem specMap_comp_stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : Fin (d + 1)) :
    Spec.map (CommRingCat.ofHom (algebraMap A (Module.rankRing A ((A ⊗[R] M) ⧸ N) r))) ≫
        stableQuotientToScheme d t N hd hN =
      (schemeStableLocusHomEquiv (r : ℕ) t (Module.rankRing A ((A ⊗[R] M) ⧸ N) r)
        ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val ≫
          Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r := by
  have := Module.isIso_rankSpecCover A ((A ⊗[R] M) ⧸ N) d hd
  rw [← Module.ι_rankSpecCover A ((A ⊗[R] M) ⧸ N) d r]
  simp only [stableQuotientToScheme, Category.assoc, IsIso.hom_inv_id_assoc,
    Sigma.ι_map]

/-- The rank-`r` factor is the scheme-theoretic pullback of the rank-`r` summand along the
varying-rank classifying morphism. -/
theorem isPullback_specMap_stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : Fin (d + 1)) :
    IsPullback
      (schemeStableLocusHomEquiv (r : ℕ) t (Module.rankRing A ((A ⊗[R] M) ⧸ N) r)
        ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val
      (Spec.map (CommRingCat.ofHom (algebraMap A (Module.rankRing A ((A ⊗[R] M) ⧸ N) r))))
      (Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r)
      (stableQuotientToScheme d t N hd hN) := by
  have := Module.isIso_rankSpecCover A ((A ⊗[R] M) ⧸ N) d hd
  exact (isPullback_sigmaι_sigmaι_sigmaMap
    (fun r : Fin (d + 1) ↦
      (schemeStableLocusHomEquiv (r : ℕ) t (Module.rankRing A ((A ⊗[R] M) ⧸ N) r)
        ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val) r).of_iso
    (Iso.refl _) (Iso.refl _) (asIso (Module.rankSpecCover A ((A ⊗[R] M) ⧸ N) d)) (Iso.refl _)
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
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Module.rankRing A ((A ⊗[R] M) ⧸ N) r)))).opensRange =
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
  have := Module.isIso_rankSpecCover A ((A ⊗[R] M) ⧸ N) d hd
  apply (cancel_epi (Module.rankSpecCover A ((A ⊗[R] M) ⧸ N) d)).1
  apply Sigma.hom_ext
  intro r
  rw [Module.ι_rankSpecCover_assoc, Module.ι_rankSpecCover_assoc,
    specMap_comp_stableQuotientToScheme_assoc]
  simp only [schemeStableLocusCoproductToSpec, Sigma.ι_comp_desc]
  rw [(schemeStableLocusHomEquiv (r : ℕ) t (Module.rankRing A ((A ⊗[R] M) ⧸ N) r) _).property,
    ← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The classifying morphism is uniquely specified by its native fixed-rank restrictions on
the canonical quotient-rank factors. -/
theorem eq_stableQuotientToScheme_iff
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A))
    (f : Spec (.of A) ⟶ schemeStableLocusCoproduct d t) :
    f = stableQuotientToScheme d t N hd hN ↔
      ∀ r : Fin (d + 1),
        Spec.map (CommRingCat.ofHom (algebraMap A (Module.rankRing A ((A ⊗[R] M) ⧸ N) r))) ≫ f =
          (schemeStableLocusHomEquiv (r : ℕ) t (Module.rankRing A ((A ⊗[R] M) ⧸ N) r)
            ⟨quotientRankPoint N r,
              quotientRankPoint_mem_invtSubmodule N hN r⟩).val ≫
                Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r := by
  have := Module.isIso_rankSpecCover A ((A ⊗[R] M) ⧸ N) d hd
  rw [← cancel_epi (Module.rankSpecCover A ((A ⊗[R] M) ⧸ N) d), Sigma.hom_ext_iff]
  simp only [Module.ι_rankSpecCover_assoc, specMap_comp_stableQuotientToScheme]

end ClassifyingMap

end Module.Grassmannian
