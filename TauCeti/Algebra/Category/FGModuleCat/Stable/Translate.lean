/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.MatlisDuality.Injective
public import TauCeti.Algebra.Category.FGModuleCat.Stable.Comparison
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.StableEquivalence

/-!
# The Auslander–Reiten translate on the stable quotients of finitely generated modules

For an Artin algebra, the Auslander–Reiten translate identifies the projective and injective
stable quotients of the canonical exact structure on finitely generated modules. The comparison
with `TauCeti.stableTranslateEquivalence` identifies this equivalence with the transpose followed
by Matlis duality in the ambient stable quotients.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Lemma IV.1.8 and Proposition IV.1.9, p. 106.
-/

public section

open CategoryTheory TauCeti

universe u v w

namespace FGModuleCat

variable (R : Type v) [CommRing R] [IsArtinianRing R]
  (A : Type u) [Ring A] [Algebra R A] [Module.Finite R A]
  (E : Type (max v w)) [AddCommGroup E] [Module R E] [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

include hE in
/-- The Auslander–Reiten translate is an equivalence from the projective stable quotient of the
abelian exact structure on finitely generated modules to its injective stable quotient. -/
noncomputable def stableTranslateEquivalence :
    letI : IsArtinianRing A := IsArtinianRing.of_finite R A
    (ExactStructure.abelian (FGModuleCat.{max u v w} A)).ProjectiveStableCategory ≌
      (ExactStructure.abelian (FGModuleCat.{max u v w} A)).InjectiveStableCategory := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite R A
  letI := enoughInjectives_of_artinAlgebra.{v, u, w} R A
  exact ((projectiveStableEquivalence.{u, max u v w} A).trans
    (TauCeti.stableTranslateEquivalence.{u, max v w} R A E hE)).trans
      (injectiveStableEquivalence.{u, max u v w} A).symm

/-- Transport along the projective and injective comparisons identifies the translate with
`TauCeti.stableTranslateEquivalence` in the ambient stable quotients. -/
noncomputable def stableTranslateEquivalenceCompInjectiveStableEquivalenceIso :
    letI : IsArtinianRing A := IsArtinianRing.of_finite R A
    letI := enoughInjectives_of_artinAlgebra.{v, u, w} R A
    (stableTranslateEquivalence R A E hE).functor ⋙
      (injectiveStableEquivalence.{u, max u v w} A).functor ≅
      (projectiveStableEquivalence.{u, max u v w} A).functor ⋙
        (TauCeti.stableTranslateEquivalence.{u, max v w} R A E hE).functor := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite R A
  letI := enoughInjectives_of_artinAlgebra.{v, u, w} R A
  unfold stableTranslateEquivalence
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (injectiveStableEquivalence.{u, max u v w} A).counitIso ≪≫
    Functor.rightUnitor _

instance :
    letI : IsArtinianRing A := IsArtinianRing.of_finite R A
    (stableTranslateEquivalence R A E hE).functor.Additive := by
  let : IsArtinianRing A := IsArtinianRing.of_finite R A
  let := enoughInjectives_of_artinAlgebra.{v, u, w} R A
  have := finite_of_forall_isMaximal hE
  unfold stableTranslateEquivalence
  simp only [Equivalence.trans_functor, Equivalence.symm_functor,
    TauCeti.stableTranslateEquivalence_functor]
  infer_instance

end FGModuleCat
