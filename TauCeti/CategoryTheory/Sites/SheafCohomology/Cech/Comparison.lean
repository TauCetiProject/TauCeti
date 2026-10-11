/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import TauCeti.Algebra.Homology.ShortComplex.Limit
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.MayerVietoris

/-!
# Comparing the Čech acyclicity of two families

Let `C` be a category with finite products and a terminal object `T`, and let `P` be a presheaf
on `C` with values in an abelian category with exact products. For two families `U` and `V` of
objects, suppose that the restriction of `V` to every finite product of members of `U` is acyclic
for `P`, and that the restriction of `U` to every finite product of members of `V` is acyclic.
Then `U` is acyclic for `P` exactly when `V` is
(`quasiIso_cechAugmentation_iff_of_quasiIso_prod`). Here a family `U` is acyclic for `P` when the
augmented Čech complex `0 ⟶ P(T) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact, and its restriction to an
object `X` is the family `U` with the presheaf `P(X × -)`.

For open covers of a space this is the classical comparison of the Čech cohomology of two covers
each of which is acyclic on the finite intersections of members of the other. Its main use is for
a cover `U` with a refinement `V`: then the restriction of `U` to every finite intersection of
members of `V` has a member containing everything, so it is acyclic, and acyclicity passes from
`V` to `U` as soon as `V` is acyclic on the finite intersections of members of `U`
(`quasiIso_cechAugmentation_of_quasiIso_prod_of_hom`). This is how acyclicity passes from
standard covers, which refine every finite cover of an affinoid by rational subsets, to all such
covers in the proof of Tate's acyclicity theorem.

The proof resolves `P` by the presheaves `Y ↦ Čᵏ(V, P(Y × -))`. This resolution is exact at `T`
and at the finite products of members of `U`, by the hypotheses on `V`. Each term is a product of
restrictions of `P` to finite products of members of `V`, hence acyclic for `U`
(`quasiIso_cechAugmentation_pi`), so `quasiIso_cechAugmentation_of_resolution` applies. This
replaces the usual double complex argument by dimension shifting along the resolution.

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_pi`: a product of acyclic presheaves is
  acyclic, when products of that shape are exact.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_quasiIso_prod`: two families each
  acyclic on the finite products of members of the other are acyclic together.
* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_quasiIso_prod_of_hom`: in a thin category,
  a family is acyclic if some acyclic refinement of it is acyclic on the finite products of its
  members.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Appendix A, for acyclic covers,
  and the proof of Theorem 8.28, which passes from standard covers to arbitrary rational covers.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §8.1.4, for the
  comparison of the Čech cohomology of a covering and a refinement, as used in rigid geometry.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)

/-! ### Products of acyclic presheaves -/

/-- **Products of acyclic presheaves are acyclic.** If products indexed by `J` are exact in `A`,
a product of presheaves whose augmented Čech complexes for `U` are exact has an exact augmented
Čech complex for `U`. -/
theorem quasiIso_cechAugmentation_pi {J : Type w} [HasExactLimitsOfShape (Discrete J) A]
    (G : J → Cᵒᵖ ⥤ A) (hG : ∀ j, QuasiIso (cechAugmentation U hT (G j))) :
    QuasiIso (cechAugmentation U hT (∏ᶜ G)) := by
  -- both the Čech complex and the complex concentrated in degree `0` preserve the product
  have h : cechAugmentation U hT (∏ᶜ G) ≫ piComparison (cechComplexFunctor U) G =
      piComparison ((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A) G ≫
        Limits.Pi.map fun j ↦ cechAugmentation U hT (G j) := by
    ext1 j
    rw [Category.assoc, Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
      piComparison_comp_π_assoc, cechAugmentation_naturality, Functor.comp_map, evaluation_obj_map]
  rw [← quasiIso_iff_comp_right _ (piComparison (cechComplexFunctor U) G), h,
    quasiIso_iff_comp_left]
  exact quasiIso_pi_map _ hG

/-! ### Comparing two families

The proof that acyclicity passes from `V` to `U` resolves `P` by the Čech complexes of the
restricted presheaves `P(Y × -)` for `V`: in degree `k` this is the presheaf
`Y ↦ ∏_b P(Y × V (b 0) × ⋯ × V (b k))`, which is acyclic for `U` by the hypothesis on `U`, and the
resolution is exact at `T` and on the finite products of members of `U` by the hypotheses on `V`.
`quasiIso_cechAugmentation_of_resolution` then applies. -/

section Comparison

variable (P : Cᵒᵖ ⥤ A)

/-- The presheaves `P(Y × -)`, as a presheaf in `Y`. -/
private abbrev restrictionFunctor : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A :=
  prod.functor.op ⋙ Functor.opHom C C ⋙ (Functor.whiskeringRight Cᵒᵖ Cᵒᵖ A).obj P

/-- The projections `X × T ⟶ X` onto the first factor. -/
private def prodTerminalIso : prod.functor.flip.obj T ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦
    ({ hom := prod.fst
       inv := prod.lift (𝟙 X) (hT.from X)
       hom_inv_id := prod.hom_ext (by simp) (hT.hom_ext _ _) } : X ⨯ T ≅ X))
    fun f ↦ prod.map_fst f (𝟙 T)

/-- The projections `T × X ⟶ X` onto the second factor. -/
private def terminalProdIso : prod.functor.obj T ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦
    ({ hom := prod.snd
       inv := prod.lift (hT.from X) (𝟙 X)
       hom_inv_id := prod.hom_ext (hT.hom_ext _ _) (by simp) } : T ⨯ X ≅ X))
    fun f ↦ prod.map_snd (𝟙 T) f

/-- The isomorphism `P(Y × T) ≅ P(Y)` of presheaves in `Y`. -/
private def restrictionFunctorTerminalIso :
    restrictionFunctor P ⋙ (evaluation Cᵒᵖ A).obj (op T) ≅ P :=
  -- evaluating `P(Y × -)` at `T` is `P(- × T)` by unfolding the composite
  (Functor.isoWhiskerRight (NatIso.op (prodTerminalIso hT)).symm P ≪≫
    Functor.isoWhiskerRight (Functor.opId C) P ≪≫ Functor.leftUnitor P :
      (prod.functor.flip.obj T).op ⋙ P ≅ P)

/-- The isomorphism `P(T × X) ≅ P(X)` of presheaves in `X`. -/
private def terminalRestrictionIso : (prod.functor.obj T).op ⋙ P ≅ P :=
  Functor.isoWhiskerRight (NatIso.op (terminalProdIso hT)).symm P ≪≫
    Functor.isoWhiskerRight (Functor.opId C) P ≪≫ Functor.leftUnitor P

/-- The isomorphism `P(Y × X) ≅ P(X × Y)` of presheaves in `Y` induced by the braiding. -/
private def restrictionBraidingIso (X : C) :
    (prod.functor.flip.obj X).op ⋙ P ≅ (prod.functor.obj X).op ⋙ P :=
  Functor.isoWhiskerRight (NatIso.op (NatIso.ofComponents (fun Y ↦ prod.braiding X Y)
    fun f ↦ braid_natural (𝟙 X) f)) P

variable {κ : Type w} (V : κ → C)

/-- The augmentation of the Čech complex for `V`, as a natural transformation in the presheaf. -/
private def cechAugmentationNatTrans :
    (evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A ⟶ cechComplexFunctor (A := A) V where
  app Q := cechAugmentation V hT Q
  naturality _ _ α := (cechAugmentation_naturality V hT _ α).symm

/-- In degree `k`, the Čech complex of `P(Y × -)` for `V` is the product, over
`b : Fin (k + 1) → κ`, of the presheaves `P(Y × V (b 0) × ⋯ × V (b k))` in `Y`. -/
private def cechTermIso (k : ℕ) :
    (restrictionFunctor P ⋙ cechComplexFunctor V) ⋙ HomologicalComplex.eval A _ k ≅
      ∏ᶜ fun b : Fin (k + 1) → κ ↦ (prod.functor.flip.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P :=
  NatIso.ofComponents (fun Y ↦ (piObjIso (fun b : Fin (k + 1) → κ ↦
    (prod.functor.flip.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P) Y).symm) fun {Y Y'} f ↦ by
    refine (Iso.comp_inv_eq _).2 ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine (Iso.eq_inv_comp _).2 ?_
    refine Pi.hom_ext _ _ fun b ↦ ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans (congrArg _ (cechComplexFunctor_map_f_π V _ _ k b)) ?_
    -- the factors of the Čech term are the values of the product, up to unfolding
    let G := fun b : Fin (k + 1) → κ ↦ (prod.functor.flip.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P
    have key (b : Fin (k + 1) → κ) :
        (piObjIso G Y).hom ≫ Pi.π (fun s ↦ (G s).obj Y) b ≫ (G b).map f =
          (∏ᶜ G).map f ≫ (piObjIso G Y').hom ≫ Pi.π (fun s ↦ (G s).obj Y') b := by
      rw [piObjIso_hom_comp_π_assoc, piObjIso_hom_comp_π, NatTrans.naturality]
    exact key b

variable [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → κ)) A]

/-- If `V` is acyclic for `P`, the restriction of `V` to every finite product of members of `U`
is acyclic, and the restriction of `U` to every finite product of members of `V` is acyclic, then
`U` is acyclic for `P`. -/
private lemma quasiIso_cechAugmentation_of_quasiIso_prod
    (hV : QuasiIso (cechAugmentation V hT P))
    (hVU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      QuasiIso (cechAugmentation V hT ((prod.functor.obj (∏ᶜ fun j ↦ U (a j))).op ⋙ P)))
    (hUV : ∀ (n : ℕ) (b : Fin (n + 1) → κ),
      QuasiIso (cechAugmentation U hT ((prod.functor.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P))) :
    QuasiIso (cechAugmentation U hT P) := by
  rw [← quasiIso_cechAugmentation_iff_of_iso U hT _ (restrictionFunctorTerminalIso hT P)]
  -- resolve `P(- × T) ≅ P` by the Čech complexes of the presheaves `P(Y × -)` for `V`
  refine quasiIso_cechAugmentation_of_resolution U hT
    (P := restrictionFunctor P ⋙ (evaluation Cᵒᵖ A).obj (op T))
    (Functor.whiskerLeft (restrictionFunctor P) (cechAugmentationNatTrans hT V)) ?_ hVU
    fun k ↦ ?_
  · exact (quasiIso_cechAugmentation_iff_of_iso V hT _ (terminalRestrictionIso hT P)).2 hV
  · rw [quasiIso_cechAugmentation_iff_of_iso U hT _ (cechTermIso P V k)]
    exact quasiIso_cechAugmentation_pi U hT _ fun b ↦
      (quasiIso_cechAugmentation_iff_of_iso U hT _ (restrictionBraidingIso P _)).2 (hUV k b)

/-- **Comparison of the Čech acyclicity of two families.** In a category with finite products and
a terminal object `T`, let `P` be a presheaf with values in an abelian category with exact
products, and let `U` and `V` be two families. Suppose that `V` is acyclic for `P(X × -)` for
every product `X` of finitely many members of `U`, and that `U` is acyclic for `P(X × -)` for
every product `X` of finitely many members of `V`; for open covers, the restriction of each cover
to every finite intersection of members of the other is acyclic. Then `U` is acyclic for `P` if
and only if `V` is. -/
theorem quasiIso_cechAugmentation_iff_of_quasiIso_prod
    (hVU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      QuasiIso (cechAugmentation V hT ((prod.functor.obj (∏ᶜ fun j ↦ U (a j))).op ⋙ P)))
    (hUV : ∀ (n : ℕ) (b : Fin (n + 1) → κ),
      QuasiIso (cechAugmentation U hT ((prod.functor.obj (∏ᶜ fun j ↦ V (b j))).op ⋙ P))) :
    QuasiIso (cechAugmentation U hT P) ↔ QuasiIso (cechAugmentation V hT P) :=
  ⟨fun hU ↦ quasiIso_cechAugmentation_of_quasiIso_prod V hT P U hU hUV hVU,
    fun hV ↦ quasiIso_cechAugmentation_of_quasiIso_prod U hT P V hV hVU hUV⟩

/-- **Acyclicity from an acyclic refinement.** In a thin category with finite products and a
terminal object `T`, let `P` be a presheaf with values in an abelian category with exact
products, and let `V` be a family each of whose members maps to a member of the family `U`; for
open covers, `V` refines `U`. If `V` is acyclic for `P`, and the restriction of `V` to every
finite product of members of `U` is acyclic, then `U` is acyclic for `P`. -/
theorem quasiIso_cechAugmentation_of_quasiIso_prod_of_hom [Quiver.IsThin C]
    (hV : QuasiIso (cechAugmentation V hT P))
    (hVU : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      QuasiIso (cechAugmentation V hT ((prod.functor.obj (∏ᶜ fun j ↦ U (a j))).op ⋙ P)))
    (hrefine : ∀ j, ∃ i, Nonempty (V j ⟶ U i)) :
    QuasiIso (cechAugmentation U hT P) := by
  refine (quasiIso_cechAugmentation_iff_of_quasiIso_prod U hT P V hVU fun n b ↦ ?_).2 hV
  -- `V (b 0) × ⋯ × V (b n)` lies in `V (b 0)`, which lies in a member of `U`
  obtain ⟨i, ⟨g⟩⟩ := hrefine (b 0)
  exact quasiIso_cechAugmentation_prod_of_hom U hT P _ (Pi.π _ 0 ≫ g)

end Comparison

end TauCeti.CategoryTheory
