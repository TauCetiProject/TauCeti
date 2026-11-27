/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.StableLocus
public import TauCeti.RingTheory.Grassmannian.VaryingRank
import Mathlib.AlgebraicGeometry.Limits

/-!
# Classifying stable quotients of varying rank

A finite projective quotient need not have constant rank. Its clopen rank fibres decompose the
coefficient ring into a finite product. On each factor its kernel gives a point of the native
fixed-rank stable Grassmannian. These classifying maps assemble into a morphism to the finite
coproduct of stable Grassmannians.

The construction retains arbitrary, possibly nonreduced test algebras. The ambient module may
be any finite flat module with a specified bound on its stalk ranks; finite free modules are a
special case. The finite index set includes ranks whose fibres are empty, with zero factor rings.

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

variable [Module.Finite R M] (N : Submodule A (A ⊗[R] M))
  [Module.Projective A ((A ⊗[R] M) ⧸ N)] [Module.Flat R M]
  (hd : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p ≤ d)

/-- The canonical morphism from the disjoint union of quotient-rank factors to `Spec A`.
It is an isomorphism when `d` bounds the ambient stalk ranks. -/
noncomputable def stableQuotientRankCover :
    (∐ fun r : ULift.{u} (Fin (d + 1)) ↦ Spec (.of (quotientRankRing N r.down))) ⟶ Spec (.of A) :=
  sigmaSpec (fun r : ULift.{u} (Fin (d + 1)) ↦ .of (quotientRankRing N r.down)) ≫
    Spec.map (CommRingCat.ofHom (RingHom.pi fun r : ULift.{u} (Fin (d + 1)) ↦
      algebraMap A (quotientRankRing N r.down)))

omit [Module.Flat R M] in
/-- Restriction of the rank-factor cover to a summand is the canonical coefficient map. -/
@[reassoc (attr := simp)]
theorem ι_stableQuotientRankCover (r : ULift.{u} (Fin (d + 1))) :
    Sigma.ι _ r ≫ stableQuotientRankCover d N =
      Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r.down))) := by
  simp only [stableQuotientRankCover, ι_sigmaSpec_assoc, ← Spec.map_comp]
  rfl

include hd in
/-- The canonical rank-factor cover is an isomorphism onto `Spec A`. -/
theorem isIso_stableQuotientRankCover : IsIso (stableQuotientRankCover d N) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.pi fun r : ULift.{u} (Fin (d + 1)) ↦
      algebraMap A (quotientRankRing N r.down)))) :=
    isIso_SpecMap_iff.mpr (bijective_pi_quotientRankRing N hd)
  unfold stableQuotientRankCover
  infer_instance

/-- The classifying morphism of a stable kernel with finite projective, possibly varying-rank
quotient, obtained from the classifying morphisms on its canonical rank factors. -/
noncomputable def stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) :
    Spec (.of A) ⟶ schemeStableLocusCoproduct d t :=
  have := isIso_stableQuotientRankCover d N hd
  inv (stableQuotientRankCover d N) ≫ Sigma.desc fun r : ULift.{u} (Fin (d + 1)) ↦
    (schemeStableLocusHomEquiv (r.down : ℕ) t (quotientRankRing N r.down)
      ⟨quotientRankPoint N r.down, quotientRankPoint_mem_invtSubmodule N hN r.down⟩).val ≫
        Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r.down

/-- On the rank-`r` factor the classifying morphism is the native fixed-rank classifying map
followed by the inclusion of the rank-`r` summand. -/
@[reassoc]
theorem specMap_comp_stableQuotientToScheme
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A)) (r : ULift.{u} (Fin (d + 1))) :
    Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r.down))) ≫
        stableQuotientToScheme d t N hd hN =
      (schemeStableLocusHomEquiv (r.down : ℕ) t (quotientRankRing N r.down)
        ⟨quotientRankPoint N r.down, quotientRankPoint_mem_invtSubmodule N hN r.down⟩).val ≫
          Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r.down := by
  have := isIso_stableQuotientRankCover d N hd
  rw [← ι_stableQuotientRankCover d N r]
  simp only [stableQuotientToScheme, Category.assoc, IsIso.hom_inv_id_assoc,
    Sigma.ι_comp_desc]

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
  rw [(schemeStableLocusHomEquiv (r.down : ℕ) t (quotientRankRing N r.down) _).property,
    ← Spec.map_comp]
  congr 1

/-- The classifying morphism is uniquely specified by its native fixed-rank restrictions on
the canonical quotient-rank factors. -/
theorem eq_stableQuotientToScheme_iff
    (hN : N ∈ Module.End.invtSubmodule (t.baseChange A))
    (f : Spec (.of A) ⟶ schemeStableLocusCoproduct d t) :
    f = stableQuotientToScheme d t N hd hN ↔
      ∀ r : ULift.{u} (Fin (d + 1)),
        Spec.map (CommRingCat.ofHom (algebraMap A (quotientRankRing N r.down))) ≫ f =
          (schemeStableLocusHomEquiv (r.down : ℕ) t (quotientRankRing N r.down)
            ⟨quotientRankPoint N r.down,
              quotientRankPoint_mem_invtSubmodule N hN r.down⟩).val ≫
                Sigma.ι (fun r : Fin (d + 1) ↦ (schemeStableLocus (r : ℕ) t).subscheme) r.down := by
  have := isIso_stableQuotientRankCover d N hd
  rw [← cancel_epi (stableQuotientRankCover d N), Sigma.hom_ext_iff]
  simp only [ι_stableQuotientRankCover_assoc, specMap_comp_stableQuotientToScheme]

end ClassifyingMap

end Module.Grassmannian
