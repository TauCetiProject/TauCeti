/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.StableLocus
public import TauCeti.RingTheory.Grassmannian.VaryingRank
import TauCeti.AlgebraicGeometry.Limits.Coproduct

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
  Sigma.desc fun r : Fin (d + 1) ↦
    Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r)))

/-- Restriction of the rank-factor cover to a summand is the canonical coefficient map. -/
@[reassoc (attr := simp)]
theorem ι_stableQuotientRankCover (r : Fin (d + 1)) :
    Sigma.ι _ r ≫ stableQuotientRankCover d N =
      Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r))) :=
  Sigma.ι_comp_desc _ _

include hd in
/-- The canonical rank-factor cover is an isomorphism onto `Spec A`. -/
theorem isIso_stableQuotientRankCover : IsIso (stableQuotientRankCover d N) := by
  let F := fun r : Fin (d + 1) ↦ Spec (.of (quotientRankRing N r))
  let f := RingHom.pi fun r : ULift.{u} (Fin (d + 1)) ↦
    algebraMap A (quotientRankRing N (Equiv.ulift.{u} r : Fin (d + 1)))
  have hf : Function.Bijective f := by
    have h := (Equiv.piCongrLeft (fun r : Fin (d + 1) ↦ quotientRankRing N r)
      Equiv.ulift.{u}).symm.bijective.comp (bijective_pi_quotientRankRing N hd)
    have heq : ⇑f =
        (Equiv.piCongrLeft (fun r : Fin (d + 1) ↦ quotientRankRing N r)
          Equiv.ulift.{u}).symm ∘
            (RingHom.pi fun r : Fin (d + 1) ↦ algebraMap A (quotientRankRing N r)) := by
      funext a r
      dsimp only [f]
      simp only [Function.comp_apply, Equiv.piCongrLeft_symm_apply,
        RingHom.pi_apply]
    rwa [heq]
  have : IsIso (Spec.map (CommRingCat.ofHom f)) := isIso_SpecMap_iff.mpr hf
  have heq : (Sigma.reindex Equiv.ulift.{u} F).hom ≫ stableQuotientRankCover d N =
      sigmaSpec.{u, u} (fun r : ULift.{u} (Fin (d + 1)) ↦
        .of (quotientRankRing N (Equiv.ulift.{u} r : Fin (d + 1)))) ≫
        Spec.map (CommRingCat.ofHom f) := by
    apply Sigma.hom_ext
    intro r
    dsimp only [F]
    rw [Sigma.ι_reindex_hom_assoc, ι_stableQuotientRankCover]
    dsimp only [Function.comp_def]
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g))
    apply RingHom.ext
    intro a
    simp only [f, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.pi_apply]
  have : IsIso ((Sigma.reindex Equiv.ulift.{u} F).hom ≫ stableQuotientRankCover d N) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (Sigma.reindex Equiv.ulift.{u} F).hom _

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
  inv (stableQuotientRankCover d N) ≫ Sigma.desc fun r : Fin (d + 1) ↦
    (schemeStableLocusHomEquiv (r : ℕ) t (quotientRankRing N r)
      ⟨quotientRankPoint N r, quotientRankPoint_mem_invtSubmodule N hN r⟩).val ≫
        Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r

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
    Sigma.ι_comp_desc]

/-- The inverse image of the rank-`r` summand is exactly the quotient-rank-`r` fibre. -/
@[simp]
theorem stableQuotientToScheme_preimage_range_ι
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : Fin (d + 1)) :
    stableQuotientToScheme d t N hd hN ⁻¹'
        Set.range (Sigma.ι (fun r : Fin (d + 1) ↦
          (schemeStableLocus (r : ℕ) t).subscheme) r) =
      {p | Module.rankAtStalk ((A ⊗[R] M) ⧸ N) p = r} := by
  have := isIso_stableQuotientRankCover d N hd
  ext p
  obtain ⟨x, rfl⟩ := (stableQuotientRankCover d N).surjective p
  obtain ⟨s, x, rfl⟩ : ∃ (s : Fin (d + 1))
      (y : Spec (.of (quotientRankRing N s))),
        Sigma.ι (fun s : Fin (d + 1) ↦ Spec (.of (quotientRankRing N s))) s y = x :=
    (sigmaOpenCover fun s : Fin (d + 1) ↦ Spec (.of (quotientRankRing N s))).exists_eq x
  rw [← Scheme.Hom.comp_apply, ι_stableQuotientRankCover]
  have hmap := congrArg (fun f ↦ f x)
    (specMap_comp_stableQuotientToScheme d t N hd hN s)
  simp only [Scheme.Hom.comp_apply] at hmap
  rw [Set.mem_preimage, hmap, TauCeti.AlgebraicGeometry.sigmaι_apply_mem_range_sigmaι_iff]
  have hrank : Module.rankAtStalk ((A ⊗[R] M) ⧸ N)
      (Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N s))) x) = s := by
    rw [Spec.map_apply, CommRingCat.hom_ofHom]
    exact (Module.rankAtStalk_baseChange (M := (A ⊗[R] M) ⧸ N) x).symm.trans
      (rankAtStalk_quotientRankRing_tensor_quotient N s x)
  exact Fin.ext_iff.trans (congrArg (· = (r : ℕ)) hrank).symm.to_iff

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
