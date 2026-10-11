/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Opposite

/-!
# Short exact coefficient sequences and Čech acyclicity

The Čech complex preserves short exact sequences of presheaves when the coefficient category
has products and its products of the required sizes are exact. The exactness requirement is
automatic for finite families in an abelian category, and for arbitrary families of abelian
groups. Exactness here is objectwise exactness of presheaves, not exactness only after
sheafification. For finite families, the exact-product hypothesis is supplied by locally
enabling `Abelian.hasFiniteBiproducts`.

Only the values at finite products of members matter: a sequence of presheaves that is short
exact after evaluation at each such product has a short exact sequence of Čech complexes
(`shortExact_map_cechComplexFunctor`). For an open cover, this asks for exactness only on the
finite intersections of members.

For a short exact coefficient sequence, acyclicity of its middle and right terms implies
acyclicity of its left term. This is the coefficient-sequence descent used when iterating
Mayer-Vietoris sequences for Laurent covers: the middle term is the pair of restrictions and
the right term is the restriction to the intersection.

The comparison uses Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃`, applied to
opposite complexes, rather than a separate five-lemma argument.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Appendix A and Lemma 8.34(i).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

section Preservation

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

/-- Evaluation of the Čech complex in degree `n` is the product of the evaluations at
`U (a 0) × ⋯ × U (a n)`. -/
private def cechEvalIso (n : ℕ) :
    cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      (Functor.whiskeringLeft (Discrete (Fin (n + 1) → ι)) Cᵒᵖ A).obj
        (Discrete.functor (fun a ↦ op (∏ᶜ fun j ↦ U (a j)))) ⋙ lim :=
  NatIso.ofComponents (fun P ↦
    let e : ((cechComplexFunctor U).obj P).X n ≅
        ∏ᶜ (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) := Iso.refl _
    e ≪≫ HasLimit.isoOfNatIso
      (F := Discrete.functor (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))))
      (G := Discrete.functor (fun a : Fin (n + 1) → ι ↦ op (∏ᶜ fun j ↦ U (a j))) ⋙ P)
      (Discrete.compNatIsoDiscrete _ P).symm) (fun α ↦ by
    apply limit.hom_ext
    intro a
    -- The Čech term and the product use definitionally equal diagrams with different
    -- chosen-limit instances; `erw` also normalizes those instances.
    erw [Iso.trans_hom, Iso.trans_hom, Iso.refl_hom, Iso.refl_hom,
      Category.id_comp, Category.id_comp]
    dsimp only [Functor.comp_map, HomologicalComplex.eval_map,
      Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map]
    erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, Category.assoc, limMap_π,
      HasLimit.isoOfNatIso_hom_π_assoc]
    simp only [Discrete.compNatIsoDiscrete, Iso.symm_hom, Discrete.natIso_inv_app,
      Iso.refl_inv]
    erw [Category.comp_id, Category.id_comp]
    convert cechComplexFunctor_map_f_π U _ α n a.as using 1
    rfl)

section FiniteLimits

variable [HasFiniteLimits A]

/-- The Čech complex functor preserves finite limits. -/
instance preservesFiniteLimits_cechComplexFunctor : PreservesFiniteLimits (cechComplexFunctor
    (A := A) U) where
  preservesFiniteLimits J _ _ := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    exact preservesLimitsOfShape_of_natIso (cechEvalIso U n).symm

end FiniteLimits

section FiniteColimits

variable [HasFiniteColimits A]
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]

/-- With exact products, the Čech complex functor preserves finite colimits. -/
instance preservesFiniteColimits_cechComplexFunctor : PreservesFiniteColimits (cechComplexFunctor
    (A := A) U) where
  preservesFiniteColimits J _ _ := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    exact preservesColimitsOfShape_of_natIso (cechEvalIso U n).symm

end FiniteColimits

end Preservation

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)
  [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]

/-- **The Čech complexes of a coefficient sequence that is short exact on the members.** If a
sequence of presheaves becomes short exact after evaluation at every finite product
`U (a 0) × ⋯ × U (a n)` of members of the family `U`, then its sequence of Čech complexes for `U`
is short exact. No exactness is required at other objects: for an open cover, only the
intersections of members matter. -/
theorem shortExact_map_cechComplexFunctor (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hS : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ A).obj (op (∏ᶜ fun j ↦ U (a j))))).ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  -- in degree `n`, the sequence of Čech complexes is the product of the evaluations of `S`
  have h := (ShortComplex.shortExact_of_forall_evaluation (S.map ((Functor.whiskeringLeft
    (Discrete (Fin (n + 1) → ι)) Cᵒᵖ A).obj (Discrete.functor fun a ↦ op (∏ᶜ fun j ↦ U (a j)))))
      fun a ↦ hS n a.as).map_of_exact lim
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (cechEvalIso U n).symm) h

variable {T : C} (hT : IsTerminal T)

/-- The augmentation is a morphism from the coefficient sequence, concentrated in degree zero,
to its sequence of Čech complexes. -/
private def cechAugmentationShortComplexHom (S : ShortComplex (Cᵒᵖ ⥤ A)) :
    S.map ((evaluation Cᵒᵖ A).obj (op T) ⋙
      HomologicalComplex.single A (ComplexShape.up ℕ) 0) ⟶
        S.map (cechComplexFunctor U) where
  τ₁ := cechAugmentation U hT S.X₁
  τ₂ := cechAugmentation U hT S.X₂
  τ₃ := cechAugmentation U hT S.X₃
  comm₁₂ := cechAugmentation_naturality U hT S.X₁ S.f
  comm₂₃ := cechAugmentation_naturality U hT S.X₂ S.g

/-- **Čech acyclicity descends to the kernel of an objectwise short exact coefficient
sequence.** If a family is acyclic for the middle and right presheaves of a short exact
sequence, then it is acyclic for the left presheaf as well. -/
theorem quasiIso_cechAugmentation_of_shortExact (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hS : S.ShortExact) (h₂ : QuasiIso (cechAugmentation U hT S.X₂))
    (h₃ : QuasiIso (cechAugmentation U hT S.X₃)) :
    QuasiIso (cechAugmentation U hT S.X₁) := by
  let φ := cechAugmentationShortComplexHom U hT S
  let F := HomologicalComplex.opFunctor A (ComplexShape.up ℕ)
  have hsource := hS.map_of_exact ((evaluation Cᵒᵖ A).obj (op T) ⋙
    HomologicalComplex.single A (ComplexShape.up ℕ) 0)
  have htarget := hS.map_of_exact (cechComplexFunctor U)
  have h₂' : QuasiIso φ.τ₂ := h₂
  have h₃' : QuasiIso φ.τ₃ := h₃
  -- Opposite complexes reverse the coefficient sequence, so Mathlib's right-term
  -- comparison proves the required left-term comparison.
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (F.mapShortComplex.map (ShortComplex.opMap φ))
    (htarget.op.map_of_exact F) (hsource.op.map_of_exact F)
    ((HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₃).mpr h₃')
    ((HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₂).mpr h₂')
  exact (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₁).mp h

end TauCeti.CategoryTheory
