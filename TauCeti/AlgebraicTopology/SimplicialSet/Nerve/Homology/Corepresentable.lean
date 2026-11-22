/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Category homology with free corepresentable coefficients

For an object `X` of `C` and an object `V` of `A`, the free corepresentable coefficient functor
`(evaluationLeftAdjoint A X).obj V` sends `c` to `∐_{X ⟶ c} V`; it is the left adjoint of
evaluation at `X` applied to `V`. For `A = ModuleCat R` and `V = R` it is the free module functor
`R[C(X, -)]`, written as a coproduct of copies of `R` indexed by `C(X, c)`.

The category chain complex of this functor is contractible onto `V` in degree zero. A summand of
its simplicial object in degree `n` is indexed by a string `σ = (c₀ ⟶ ⋯ ⟶ cₙ)` and an arrow
`f : X ⟶ c₀`. Prepending `f` to `σ` (`CategoryTheory.ComposableArrows.precomp`) and moving the
coefficient to the summand of `𝟙 X` is an extra degeneracy, in the sense of Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy`, of the simplicial object augmented to `V`. Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` then gives the chain homotopy
equivalence `TauCeti.categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint` with
`(ChainComplex.single₀ A).obj V`, hence the vanishing of higher category homology
`TauCeti.isZero_categoryHomology_succ_evaluationLeftAdjoint`: for `A = ModuleCat R` and `V = R`
this is `Hₙ₊₁(C, R[C(X, -)]) = 0`.

These coefficient functors are projective when `V` is, and every coefficient functor is a
quotient of a coproduct of them (`TauCeti.CategoryTheory.Preadditive.Projective.FunctorCategory`).
So category homology vanishes in positive degrees on the building blocks of projective
resolutions of coefficient functors, as needed to compare it with the left derived functors of
the colimit.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory* (1967), Appendix II, §3.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, §3.5.
-/

public section

noncomputable section

open CategoryTheory Category Limits Opposite Simplicial

universe u v u' v'

namespace TauCeti

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [∀ a b : C, HasCoproductsOfShape (a ⟶ b) A]

section Coefficients

variable (X : C) (V : A)

/-- The inclusion of `V` into `((evaluationLeftAdjoint A X).obj V).obj c = ∐_{X ⟶ c} V` as the
summand of `f : X ⟶ c`. -/
private def ιCoeff {c : C} (f : X ⟶ c) : V ⟶ ((evaluationLeftAdjoint A X).obj V).obj c :=
  Sigma.ι (fun _ : X ⟶ c ↦ V) f

/-- A morphism out of `((evaluationLeftAdjoint A X).obj V).obj c`, given on each summand. -/
private def descCoeff {c : C} {T : A} (φ : (X ⟶ c) → (V ⟶ T)) :
    ((evaluationLeftAdjoint A X).obj V).obj c ⟶ T :=
  Sigma.desc φ

@[reassoc] private lemma ιCoeff_descCoeff {c : C} {T : A} (φ : (X ⟶ c) → (V ⟶ T))
    (f : X ⟶ c) : ιCoeff X V f ≫ descCoeff X V φ = φ f :=
  Sigma.ι_comp_desc _ _

@[reassoc] private lemma ιCoeff_map {c d : C} (f : X ⟶ c) (g : c ⟶ d) :
    ιCoeff X V f ≫ ((evaluationLeftAdjoint A X).obj V).map g = ιCoeff X V (f ≫ g) :=
  Sigma.ι_comp_desc _ _

private lemma coeff_hom_ext {c : C} {T : A} {g h : ((evaluationLeftAdjoint A X).obj V).obj c ⟶ T}
    (w : ∀ f : X ⟶ c, ιCoeff X V f ≫ g = ιCoeff X V f ≫ h) : g = h :=
  Sigma.hom_ext _ _ w

end Coefficients

variable [HasCoproducts.{max u v} A]

/-- The simplicial object of `(evaluationLeftAdjoint A X).obj V`, augmented to `V` by sending
every coefficient summand to `V` by the identity. -/
private def augmented (X : C) (V : A) : SimplicialObject.Augmented A :=
  SimplicialObject.augment (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)) V
    (descCategorySimplicial _ fun _ ↦ descCoeff X V fun _ ↦ 𝟙 V) fun i g₁ g₂ ↦ by
      induction i using SimplexCategory.rec
      ext σ
      refine coeff_hom_ext X V fun f ↦ ?_
      -- Every summand is sent to `V` by the identity, whichever vertex `g` selects.
      have h (g : ⦋0⦌ ⟶ ⦋_⦌) : ιCoeff X V f ≫ ιCategorySimplicial _ σ ≫
          (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)).map g.op ≫
            descCategorySimplicial _ (fun _ ↦ descCoeff X V fun _ ↦ 𝟙 V) = 𝟙 V :=
        (congrArg (ιCoeff X V f ≫ ·) ((ιCategorySimplicial_map_assoc _ g σ _).trans
          (assoc _ _ _))).trans <|
          (ιCoeff_map_assoc X V _ _ _).trans <|
            (congrArg (ιCoeff X V (f ≫ σ.map (homOfLE (Fin.zero_le _))) ≫ ·)
              (ιCategorySimplicial_desc _ _ ((nerve C).map g.op σ))).trans
              (ιCoeff_descCoeff X V _ _)
      exact (h g₁).trans (h g₂).symm

/-- The summand inclusion at `σ.precomp f` and the identity of `X`. -/
private def ιPrecomp (X : C) (V : A) {n : ℕ} (σ : ComposableArrows C n) (f : X ⟶ σ.obj 0) :
    V ⟶ (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)) _⦋n + 1⦌ :=
  ιCoeff X V (𝟙 X) ≫ ιCategorySimplicial ((evaluationLeftAdjoint A X).obj V) (σ.precomp f)

/-- The extra degeneracy: prepend the coefficient arrow `f : X ⟶ σ.obj 0` to `σ`, moving the
coefficient to the summand of the identity of `X`. -/
private def extraDegeneracyS (X : C) (V : A) (n : ℕ) :
    (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)) _⦋n⦌ ⟶
      (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)) _⦋n + 1⦌ :=
  descCategorySimplicial _ fun σ ↦ descCoeff X V fun f ↦ ιPrecomp X V σ f

@[reassoc] private lemma ι_extraDegeneracyS (X : C) (V : A) {n : ℕ}
    (σ : ComposableArrows C n) (f : X ⟶ σ.obj 0) :
    ιCoeff X V f ≫ ιCategorySimplicial ((evaluationLeftAdjoint A X).obj V) σ ≫
      extraDegeneracyS X V n = ιPrecomp X V σ f := by
  rw [extraDegeneracyS, ιCategorySimplicial_desc, ιCoeff_descCoeff]

private lemma ιPrecomp_δ_zero (X : C) (V : A) {n : ℕ} (σ : ComposableArrows C n)
    (f : X ⟶ σ.obj 0) :
    ιPrecomp X V σ f ≫ (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)).δ 0 =
      ιCoeff X V f ≫ ιCategorySimplicial ((evaluationLeftAdjoint A X).obj V) σ :=
  (assoc _ _ _).trans <| (congrArg (ιCoeff X V (𝟙 X) ≫ ·)
    (ιCategorySimplicial_δ_zero _ (σ.precomp f))).trans <|
      (ιCoeff_map_assoc X V _ _ _).trans (congrArg (ιCoeff X V · ≫ _) (id_comp f))

/-- Deleting the vertex `j + 1` of a prepended string is the prepended summand of the face
`δ j σ`, with `f` composed with the arrow of `σ` to its new first vertex. -/
private lemma ιPrecomp_δ_succ (X : C) (V : A) {n : ℕ} (j : Fin (n + 2))
    (σ : ComposableArrows C (n + 1)) (f : X ⟶ σ.obj 0) :
    ιPrecomp X V σ f ≫ (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)).δ j.succ =
      ιPrecomp X V ((nerve C).δ j σ) (f ≫ σ.map (homOfLE (Fin.zero_le (j.succAbove 0)))) :=
  (assoc _ _ _).trans <| congrArg (ιCoeff X V (𝟙 X) ≫ ·) <|
    (ιCategorySimplicial_δ_succ _ j (σ.precomp f)).trans <|
      (ιCategorySimplicial_congr _ (nerve.δ_succ_precomp j σ f) rfl).trans (id_comp _)

/-- Repeating the vertex `i + 1` of a prepended string is the prepended summand of the
degeneracy `σ i σ`. -/
private lemma ιPrecomp_σ_succ (X : C) (V : A) {n : ℕ} (i : Fin (n + 1))
    (σ : ComposableArrows C n) (f : X ⟶ σ.obj 0) :
    ιPrecomp X V σ f ≫ (categorySimplicialObject ((evaluationLeftAdjoint A X).obj V)).σ i.succ =
      ιPrecomp X V ((nerve C).σ i σ) f :=
  (assoc _ _ _).trans <| congrArg (ιCoeff X V (𝟙 X) ≫ ·) <|
    (ιCategorySimplicial_σ _ i.succ (σ.precomp f)).trans <|
      (ιCategorySimplicial_congr _ (nerve.σ_succ_precomp i σ f) rfl).trans (id_comp _)

private lemma augmented_hom_app_zero (X : C) (V : A) :
    (augmented X V).hom.app (op ⦋0⦌) =
      descCategorySimplicial _ fun _ ↦ descCoeff X V fun _ ↦ 𝟙 V :=
  SimplicialObject.augment_hom_zero _ _ _ _

private lemma ιCoeff_ιCategorySimplicial_augmented_hom_app_zero (X : C) (V : A) {c : C}
    (f : X ⟶ c) :
    ιCoeff X V f ≫ ιCategorySimplicial ((evaluationLeftAdjoint A X).obj V) (.mk₀ c) ≫
      (augmented X V).hom.app (op ⦋0⦌) = 𝟙 V :=
  (congrArg (ιCoeff X V f ≫ ιCategorySimplicial ((evaluationLeftAdjoint A X).obj V) (.mk₀ c) ≫ ·)
    (augmented_hom_app_zero X V)).trans <|
      (congrArg (ιCoeff X V f ≫ ·) (ιCategorySimplicial_desc _ _ (.mk₀ c))).trans
        (ιCoeff_descCoeff X V _ _)

/-- Prepending the coefficient arrow is an extra degeneracy of the augmented simplicial object of
`(evaluationLeftAdjoint A X).obj V`. -/
private def extraDegeneracy (X : C) (V : A) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmented X V) where
  s' := ιCoeff X V (𝟙 X) ≫ ιCategorySimplicial _ (.mk₀ X)
  s := extraDegeneracyS X V
  s'_comp_ε := (assoc _ _ _).trans (ιCoeff_ιCategorySimplicial_augmented_hom_app_zero X V (𝟙 X))
  s₀_comp_δ₁ := by
    refine categorySimplicialObject_hom_ext (M := (evaluationLeftAdjoint A X).obj V) fun σ ↦ ?_
    refine coeff_hom_ext X V fun f ↦ ?_
    obtain ⟨c, rfl⟩ := ComposableArrows.mk₀_surjective σ
    refine (ι_extraDegeneracyS_assoc X V _ f _).trans <| (assoc _ _ _).trans <|
      (congrArg (ιCoeff X V (𝟙 X) ≫ ·) <| (ιCategorySimplicial_δ_succ _ 0 _).trans <|
        (ιCategorySimplicial_congr _ (ComposableArrows.ext₀ rfl :
          (nerve C).δ (Fin.succ 0) ((ComposableArrows.mk₀ c).precomp f) = .mk₀ X) rfl).trans
            (id_comp _)).trans ?_
    exact (id_comp _).symm.trans <|
      (congrArg (· ≫ _) (ιCoeff_ιCategorySimplicial_augmented_hom_app_zero X V f).symm).trans <|
        (assoc _ _ _).trans (congrArg (ιCoeff X V f ≫ ·) (assoc _ _ _))
  s_comp_δ₀ n := by
    refine categorySimplicialObject_hom_ext (M := (evaluationLeftAdjoint A X).obj V) fun σ ↦ ?_
    refine coeff_hom_ext X V fun f ↦ ?_
    exact (ι_extraDegeneracyS_assoc X V σ f _).trans <| (ιPrecomp_δ_zero X V σ f).trans <|
      congrArg (ιCoeff X V f ≫ ·) (comp_id _).symm
  s_comp_δ n i := by
    refine categorySimplicialObject_hom_ext (M := (evaluationLeftAdjoint A X).obj V) fun σ ↦ ?_
    refine coeff_hom_ext X V fun f ↦ ?_
    refine (ι_extraDegeneracyS_assoc X V σ f _).trans <| (ιPrecomp_δ_succ X V i σ f).trans ?_
    induction i using Fin.cases with
    | zero =>
      -- The new first vertex of `δ 0 σ` is the vertex `(0 : Fin _).succAbove 0 = 1` of `σ`.
      exact (ι_extraDegeneracyS X V _ _).symm.trans <|
        (ιCoeff_map_assoc X V f _ _).symm.trans <| congrArg (ιCoeff X V f ≫ ·)
          ((assoc _ _ _).symm.trans (ιCategorySimplicial_δ_zero_assoc _ σ _).symm)
    | succ k =>
      -- The new first vertex of `δ k.succ σ` is the vertex `k.succ.succAbove 0 = 0` of `σ`.
      have hk : (f ≫ σ.map (homOfLE (Fin.zero_le (k.succ.succAbove 0))) : X ⟶ σ.obj 0) = f :=
        (congrArg (f ≫ σ.map ·) (Subsingleton.elim _ (𝟙 _))).trans (by rw [σ.map_id, comp_id])
      exact (congrArg (ιPrecomp X V ((nerve C).δ k.succ σ)) hk).trans <|
        (ι_extraDegeneracyS X V ((nerve C).δ k.succ σ) f).symm.trans <|
          congrArg (ιCoeff X V f ≫ ·) (ιCategorySimplicial_δ_succ_assoc _ k σ _).symm
  s_comp_σ n i := by
    refine categorySimplicialObject_hom_ext (M := (evaluationLeftAdjoint A X).obj V) fun σ ↦ ?_
    refine coeff_hom_ext X V fun f ↦ ?_
    exact (ι_extraDegeneracyS_assoc X V σ f _).trans <| (ιPrecomp_σ_succ X V i σ f).trans <|
      (ι_extraDegeneracyS X V ((nerve C).σ i σ) f).symm.trans <| congrArg (ιCoeff X V f ≫ ·)
        (ιCategorySimplicial_σ_assoc _ i σ _).symm

variable [Preadditive A]

section HomotopyEquiv

variable [HasZeroObject A]

/-- The category chain complex of the free corepresentable coefficient functor
`(evaluationLeftAdjoint A X).obj V`, `c ↦ ∐_{X ⟶ c} V`, is chain homotopy equivalent to `V`
concentrated in degree zero. -/
def categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint (X : C) (V : A) :
    HomotopyEquiv (categoryChainComplex ((evaluationLeftAdjoint A X).obj V))
      ((ChainComplex.single₀ A).obj V) :=
  -- `categoryChainComplex` is by definition the alternating face map complex of
  -- `categorySimplicialObject`, the simplicial object augmented in `augmented X V`.
  (extraDegeneracy X V).homotopyEquiv

/-- In degree zero, the homotopy equivalence sends every coefficient summand `V` to `V` by the
identity. -/
@[simp] lemma categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint_hom_f_zero (X : C)
    (V : A) :
    (categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint X V).hom.f 0 =
      descCategoryChainComplex₀ _ fun c ↦ Sigma.desc fun _ : X ⟶ c ↦ 𝟙 V := by
  refine (AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero (augmented X V)).trans <|
    (augmented_hom_app_zero X V).trans ?_
  refine categorySimplicialObject_hom_ext (M := (evaluationLeftAdjoint A X).obj V) fun σ ↦ ?_
  obtain ⟨c, rfl⟩ := ComposableArrows.mk₀_surjective σ
  exact (ιCategorySimplicial_desc _ _ _).trans <| (ιCategoryChainComplex₀_desc₀
    ((evaluationLeftAdjoint A X).obj V) (fun c ↦ Sigma.desc fun _ : X ⟶ c ↦ 𝟙 V) c).symm.trans
      (congrArg (· ≫ _) (ιCategoryChainComplex_eq _ _))

/-- In degree zero, the homotopy inverse is the summand inclusion of `V` at the identity of `X`. -/
@[simp] lemma categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint_inv_f_zero (X : C)
    (V : A) :
    dsimp% (categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint X V).inv.f 0 =
      Sigma.ι (fun _ : X ⟶ X ↦ V) (𝟙 X) ≫
        ιCategoryChainComplex₀ ((evaluationLeftAdjoint A X).obj V) X := by
  rw [categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
  exact (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _).trans
    (congrArg (ιCoeff X V (𝟙 X) ≫ ·) (ιCategoryChainComplex_eq _ _).symm)

end HomotopyEquiv

/-- Category homology with free corepresentable coefficients `c ↦ ∐_{X ⟶ c} V` vanishes in
positive degrees. -/
theorem isZero_categoryHomology_succ_evaluationLeftAdjoint [CategoryWithHomology A] (X : C)
    (V : A) (n : ℕ) : IsZero (categoryHomology ((evaluationLeftAdjoint A X).obj V) (n + 1)) := by
  have : HasZeroObject A := Preadditive.hasZeroObject_of_hasCoproduct.{max u v} A
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 V (n + 1)
    (Nat.succ_ne_zero n)).of_iso
      ((categoryChainComplexHomotopyEquivSingle₀EvaluationLeftAdjoint X V).toHomologyIso (n + 1))

end TauCeti
