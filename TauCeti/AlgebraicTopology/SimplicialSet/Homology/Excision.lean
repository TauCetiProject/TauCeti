/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# Relative chains and complementary simplices

This file uses the coproduct presentation of relative chains to give a criterion for a map of
pairs to induce an isomorphism: the map must biject the simplices of the ambient simplicial sets
that do not come from their respective subspaces, in every degree.

The criterion isolates the algebraic step in singular-homology excision. For the cover by the
complement of the excised set and the interior of the subspace, the complementary small simplices
are exactly the complementary simplices of the excised pair.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of excision.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I, Section 9.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe w v u

namespace SSetPair

/-- The simplices of the ambient simplicial set of a pair that do not come from its subspace. -/
abbrev RelativeSimplex (P : SSetPair.{w}) (n : ℕ) :=
  ((Set.range (P.hom.app (Opposite.op (SimplexCategory.mk n))))ᶜ :
    Set (P.right.obj (Opposite.op (SimplexCategory.mk n))))

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C)
  (e : ∀ n, P.RelativeSimplex n ≃ P'.RelativeSimplex n)
  (he : ∀ n (x : P.RelativeSimplex n),
    (e n x).1 = f.right.app (Opposite.op (SimplexCategory.mk n)) x.1)

open Classical in
/-- The degree-`n` relative chains identify with the coproduct indexed by the complementary
simplices. -/
private noncomputable def relativeChainComplexXIso (P : SSetPair.{w}) (n : ℕ) :
    (P.chainComplex R).X n ≅ ∐ fun (_ : P.RelativeSimplex n) ↦ R :=
  IsColimit.coconePointUniqueUpToIso
    (P.isColimitCokernelCoforkChainComplexX R n)
    (isColimitSigmaConstCokernelCofork R
      (P.hom.app (Opposite.op (SimplexCategory.mk n))))

@[reassoc]
private lemma chainComplexπ_f_relativeChainComplexXIso_hom (P : SSetPair.{w}) (n : ℕ) :
    (P.chainComplexπ R).f n ≫ (relativeChainComplexXIso R P n).hom =
      (sigmaConstCokernelCofork R
        (P.hom.app (Opposite.op (SimplexCategory.mk n)))).π := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (P.isColimitCokernelCoforkChainComplexX R n)
    (isColimitSigmaConstCokernelCofork R
      (P.hom.app (Opposite.op (SimplexCategory.mk n)))) WalkingParallelPair.one

@[reassoc]
private lemma sigmaConstCokernelCofork_π_relativeChainComplexXIso_inv
    (P : SSetPair.{w}) (n : ℕ) :
    (sigmaConstCokernelCofork R
          (P.hom.app (Opposite.op (SimplexCategory.mk n)))).π ≫
        (relativeChainComplexXIso R P n).inv =
      (P.chainComplexπ R).f n := by
  exact IsColimit.comp_coconePointUniqueUpToIso_inv
    (P.isColimitCokernelCoforkChainComplexX R n)
    (isColimitSigmaConstCokernelCofork R
      (P.hom.app (Opposite.op (SimplexCategory.mk n)))) WalkingParallelPair.one

@[reassoc]
private lemma ιChainComplex_chainComplexπ_f_relativeChainComplexXIso_hom (P : SSetPair.{w})
    (n : ℕ) (x : P.right.obj (Opposite.op (SimplexCategory.mk n)))
    (hx : x ∉ Set.range (P.hom.app (Opposite.op (SimplexCategory.mk n)))) :
    P.right.ιChainComplex x ≫ (P.chainComplexπ R).f n ≫
        (relativeChainComplexXIso R P n).hom =
      Sigma.ι (fun (_ : P.RelativeSimplex n) ↦ R) ⟨x, hx⟩ := by
  rw [chainComplexπ_f_relativeChainComplexXIso_hom]
  exact ι_sigmaConstCokernelCofork_π R _ x hx

@[reassoc]
private lemma ι_relativeChainComplexXIso_inv (P : SSetPair.{w}) (n : ℕ)
    (x : P.RelativeSimplex n) :
    Sigma.ι (fun (_ : P.RelativeSimplex n) ↦ R) x ≫
        (relativeChainComplexXIso R P n).inv =
      P.right.ιChainComplex x.1 ≫ (P.chainComplexπ R).f n := by
  rw [← ι_sigmaConstCokernelCofork_π_assoc R _ x.1 x.2,
    sigmaConstCokernelCofork_π_relativeChainComplexXIso_inv]
  rfl

omit [Preadditive C] in
@[reassoc]
private lemma ι_reindex_relativeSimplexEquiv (n : ℕ) (x : P.RelativeSimplex n) :
    Sigma.ι (fun (_ : P.RelativeSimplex n) ↦ R) x ≫
        (Sigma.reindex (e n) (fun _ ↦ R)).hom =
      Sigma.ι (fun (_ : P'.RelativeSimplex n) ↦ R) (e n x) := by
  change Sigma.ι ((fun (_ : P'.RelativeSimplex n) ↦ R) ∘ e n) x ≫
      (Sigma.reindex (e n) (fun _ ↦ R)).hom = _
  exact Sigma.ι_reindex_hom (e n) (fun (_ : P'.RelativeSimplex n) ↦ R) x

@[reassoc]
private lemma chainComplexπ_f_comp_chainComplexMap_f (n : ℕ) :
    (P.chainComplexπ R).f n ≫ (SSetPair.chainComplexMap f R).f n =
      (SSet.chainComplexMap f.right R).f n ≫ (P'.chainComplexπ R).f n :=
  congrArg (fun g ↦ g.f n) (((chainComplexFunctorπ C).app R).naturality f).symm

include he in
private lemma chainComplexMap_f_eq (n : ℕ) :
    (SSetPair.chainComplexMap f R).f n =
      (relativeChainComplexXIso R P n).hom ≫
        (Sigma.reindex (e n) (fun _ ↦ R)).hom ≫
        (relativeChainComplexXIso R P' n).inv := by
  classical
  apply (cancel_epi ((P.chainComplexπ R).f n)).1
  rw [chainComplexπ_f_comp_chainComplexMap_f]
  ext x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  by_cases hx : x ∈ Set.range (P.hom.app (Opposite.op (SimplexCategory.mk n)))
  · obtain ⟨a, rfl⟩ := hx
    have hval : f.right.app (Opposite.op (SimplexCategory.mk n))
        (P.hom.app (Opposite.op (SimplexCategory.mk n)) a) =
          P'.hom.app (Opposite.op (SimplexCategory.mk n))
            (f.left.app (Opposite.op (SimplexCategory.mk n)) a) :=
      by simpa using (ConcreteCategory.congr_hom (NatTrans.congr_app f.w _) a).symm
    rw [hval, ← SSet.ι_chainComplexMap_f, Category.assoc,
      P'.chainComplex_condition_f, comp_zero]
    have hz : P.right.ιChainComplex
          (P.hom.app (Opposite.op (SimplexCategory.mk n)) a) ≫
            (P.chainComplexπ R).f n = 0 := by
      rw [← SSet.ι_chainComplexMap_f, Category.assoc,
        P.chainComplex_condition_f, comp_zero]
    rw [← Category.assoc, hz, zero_comp]
  · have hx' : f.right.app (Opposite.op (SimplexCategory.mk n)) x ∉
        Set.range (P'.hom.app (Opposite.op (SimplexCategory.mk n))) := by
      intro hmem
      apply (e n ⟨x, hx⟩).2
      rw [he n ⟨x, hx⟩]
      exact hmem
    rw [ιChainComplex_chainComplexπ_f_relativeChainComplexXIso_hom_assoc R P n x hx,
      ι_reindex_relativeSimplexEquiv_assoc, ι_relativeChainComplexXIso_inv]
    rw [← he n ⟨x, hx⟩]

include e he

/-- A map of simplicial-set pairs that bijects the ambient simplices outside the subspaces in
every degree induces an isomorphism of relative chain complexes. -/
theorem isIso_chainComplexMap_of_relativeSimplex_equiv :
    IsIso (SSetPair.chainComplexMap f R) := by
  let _ : ∀ n, IsIso ((SSetPair.chainComplexMap f R).f n) := fun n ↦
    chainComplexMap_f_eq f R e he n ▸ inferInstance
  exact HomologicalComplex.Hom.isIso_of_components _

variable [CategoryWithHomology C]

/-- A map of simplicial-set pairs that bijects the ambient simplices outside the subspaces
induces an isomorphism on relative homology. -/
theorem isIso_homologyMap_of_relativeSimplex_equiv (n : ℕ) :
    IsIso (SSetPair.homologyMap f R n) := by
  let _ := isIso_chainComplexMap_of_relativeSimplex_equiv f R e he
  infer_instance

end SSetPair

namespace SSet.Subcomplex

variable {X : SSet.{w}} (A B : X.Subcomplex)

/-- The pair consisting of `A ∩ B` as a subcomplex of `A`. -/
abbrev interPair : SSetPair.{w} :=
  SSetPair.of (homOfLE (inf_le_left : A ⊓ B ≤ A))

/-- The canonical map `(A, A ∩ B) ⟶ (X, B)` of simplicial-set pairs. -/
def excisionMap : interPair A B ⟶ B.pair :=
  SSetPair.homMk (homOfLE (inf_le_right : A ⊓ B ≤ B)) A.ι

@[simp]
lemma excisionMap_left : (excisionMap A B).left = homOfLE (inf_le_right : A ⊓ B ≤ B) :=
  (rfl)

@[simp]
lemma excisionMap_right : (excisionMap A B).right = A.ι := (rfl)

variable {A B}

/-- If `A` and `B` cover a simplicial set, the simplices of `A` outside `A ∩ B` correspond
exactly to the simplices of the ambient simplicial set outside `B`. -/
def excisionRelativeSimplexEquiv (h : A ⊔ B = ⊤) (n : ℕ) :
    (interPair A B).RelativeSimplex n ≃ B.pair.RelativeSimplex n where
  toFun x := ⟨x.1.1, by
    rintro ⟨b, hb⟩
    apply x.2
    refine ⟨⟨x.1.1, x.1.2, ?_⟩, ?_⟩
    · exact hb ▸ b.2
    · apply Subtype.ext
      rfl⟩
  invFun x := ⟨⟨x.1, by
    have hx : x.1 ∈ (A ⊔ B).obj (Opposite.op (SimplexCategory.mk n)) := by
      rw [h]
      trivial
    rcases hx with hxA | hxB
    · exact hxA
    · exact (x.2 ⟨⟨x.1, hxB⟩, rfl⟩).elim⟩, by
    rintro ⟨z, hz⟩
    apply x.2
    refine ⟨⟨x.1, ?_⟩, rfl⟩
    exact congrArg Subtype.val hz ▸ z.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

@[simp]
lemma excisionRelativeSimplexEquiv_apply_val (h : A ⊔ B = ⊤) (n : ℕ)
    (x : (interPair A B).RelativeSimplex n) :
    (excisionRelativeSimplexEquiv h n x).1 = x.1.1 := (rfl)

@[simp]
lemma excisionRelativeSimplexEquiv_symm_apply_val (h : A ⊔ B = ⊤) (n : ℕ)
    (x : B.pair.RelativeSimplex n) :
    ((excisionRelativeSimplexEquiv h n).symm x).1.1 = x.1 := (rfl)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (R : C)

/-- **Simplicial chain excision.** If two subcomplexes cover a simplicial set, inclusion induces
an isomorphism from the chains of `(A, A ∩ B)` to the chains of `(X, B)`. -/
theorem isIso_chainComplexMap_excisionMap (h : A ⊔ B = ⊤) :
    IsIso (SSetPair.chainComplexMap (excisionMap A B) R) :=
  SSetPair.isIso_chainComplexMap_of_relativeSimplex_equiv (excisionMap A B) R
    (excisionRelativeSimplexEquiv h) (by
      intro n x
      rw [excisionRelativeSimplexEquiv_apply_val, excisionMap_right]
      rfl)

variable [CategoryWithHomology C]

/-- **Simplicial homology excision.** If two subcomplexes cover a simplicial set, inclusion
induces an isomorphism from `Hₙ(A, A ∩ B)` to `Hₙ(X, B)`. -/
theorem isIso_homologyMap_excisionMap (h : A ⊔ B = ⊤) (n : ℕ) :
    IsIso (SSetPair.homologyMap (excisionMap A B) R n) := by
  let _ := isIso_chainComplexMap_excisionMap R h
  infer_instance

end SSet.Subcomplex
