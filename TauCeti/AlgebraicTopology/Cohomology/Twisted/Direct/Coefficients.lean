/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# The coefficient sequence of cohomology with local coefficients

A short exact sequence of local systems gives a short exact sequence of their direct singular
cochain complexes. In each degree these are products of the fibres at the initial vertices of
singular simplices. Products of surjective module maps are surjective, so no projectivity or
flatness hypothesis on the fibres is necessary.

The resulting connecting map `CategoryTheory.ShortComplex.ShortExact.cohomologyδ` goes from
`Hⁿ(X; L₃)` to `Hⁿ⁺¹(X; L₁)`. The three exactness statements, naturality in short exact
sequences, and injectivity of `H⁰(X; L₁) ⟶ H⁰(X; L₂)` give the coefficient long exact sequence.
Here cochains take values in the local system itself; no dual coefficient system is used.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Section III.1.

The connecting maps and their exactness use Mathlib's homology-sequence construction.
-/

public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}

/-- A short exact sequence of local systems induces a short exact sequence of direct singular
cochain complexes, without projectivity assumptions on any of the fibres. -/
lemma _root_.CategoryTheory.ShortComplex.ShortExact.map_cochainComplexFunctor
    {S : ShortComplex (LocalCoefficientSystem.{u, v, w} R X)} (hS : S.ShortExact) :
    (S.map (cochainComplexFunctor R X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have h (σ : (TopCat.toSSet.obj X) _⦋n⦌) :=
    hS.map_of_exact ((evaluation (FundamentalGroupoid X) (ModuleCat.{w} R)).obj (initialVertex σ))
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    ShortComplex.map_f, ShortComplex.map_g, cochainComplexFunctor,
    HomologicalComplex.eval_obj, HomologicalComplex.eval_map]
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).2
    intro c hc
    have hcσ (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
        S.g.app (initialVertex σ) (cochainComplexEval S.X₂ n σ c) = 0 := by
      have he := congrArg (cochainComplexEval S.X₃ n σ) hc
      simpa only [cochainComplexFunctor, ShortComplex.map_g,
        HomologicalComplex.eval_map, cochainComplexCoefficientMap_eval.{u, v, w}, map_zero] using he
    choose b hb using fun σ ↦ (ShortComplex.moduleCat_exact_iff _).1 (h σ).exact _ (hcσ σ)
    refine ⟨(cochainComplexXIso S.X₁ n).inv b, ?_⟩
    apply cochainComplex_ext
    intro σ
    simpa only [cochainComplexFunctor, ShortComplex.map_f, HomologicalComplex.eval_map,
      cochainComplexCoefficientMap_eval.{u, v, w}, cochainComplexXIso_inv_eval.{u, v, w},
      ShortComplex.map_X₂, ShortComplex.map_X₃, evaluation_obj_map, evaluation_obj_obj] using hb σ
  · apply (ModuleCat.mono_iff_injective _).2
    intro c d hcd
    apply cochainComplex_ext
    intro σ
    apply (h σ).moduleCat_injective_f
    simpa only [cochainComplexFunctor, ShortComplex.map_f, HomologicalComplex.eval_map,
      cochainComplexCoefficientMap_eval.{u, v, w}, ShortComplex.map_X₂,
      evaluation_obj_map, evaluation_obj_obj] using congrArg (cochainComplexEval S.X₂ n σ) hcd
  · apply (ModuleCat.epi_iff_surjective _).2
    intro c
    choose b hb using fun σ ↦ (h σ).moduleCat_surjective_g (cochainComplexEval S.X₃ n σ c)
    refine ⟨(cochainComplexXIso S.X₂ n).inv b, ?_⟩
    apply cochainComplex_ext
    intro σ
    simpa only [cochainComplexFunctor, ShortComplex.map_g, HomologicalComplex.eval_map,
      cochainComplexCoefficientMap_eval.{u, v, w}, cochainComplexXIso_inv_eval.{u, v, w},
      ShortComplex.map_X₂, ShortComplex.map_X₃, evaluation_obj_map, evaluation_obj_obj] using hb σ

end TauCeti.LocalCoefficientSystem

namespace CategoryTheory.ShortComplex

open TauCeti.LocalCoefficientSystem

/-- Consecutive coefficient maps of a short complex compose to zero on direct cohomology. -/
@[reassoc (attr := simp)]
lemma cohomologyCoefficientMap_comp_eq_zero
    {R : Type u} [Ring R] {X : TopCat.{v}}
    (S : ShortComplex (TauCeti.LocalCoefficientSystem.{u, v, w} R X)) (n : ℕ) :
    cohomologyCoefficientMap S.f n ≫ cohomologyCoefficientMap S.g n = 0 := by
  simp only [cohomologyCoefficientMap_eq]
  exact ((S.map (cochainComplexFunctor R X)).map
    (HomologicalComplex.homologyFunctor _ _ n)).zero

end CategoryTheory.ShortComplex

namespace CategoryTheory.ShortComplex.ShortExact

open TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  {S T : ShortComplex (TauCeti.LocalCoefficientSystem.{u, v, w} R X)} (hS : S.ShortExact)

include hS

/-- The coefficient connecting morphism `Hⁿ(X; L₃) ⟶ Hᵐ(X; L₁)` for `n + 1 = m`, using
cochains with values in the local systems themselves. -/
def cohomologyδ (n m : ℕ) (h : n + 1 = m) :
    cohomology S.X₃ n ⟶ cohomology S.X₁ m :=
  (hS.map_cochainComplexFunctor).δ n m h

/-- The coefficient connecting map is the homology connecting map of the induced short exact
sequence of direct cochain complexes. -/
lemma cohomologyδ_eq_δ (n m : ℕ) (h : n + 1 = m) :
    hS.cohomologyδ n m h = (hS.map_cochainComplexFunctor).δ n m h := (rfl)

/-- The connecting map followed by the first coefficient map is zero. -/
@[reassoc (attr := simp)]
lemma cohomologyδ_comp (n m : ℕ) (h : n + 1 = m) :
    hS.cohomologyδ n m h ≫ cohomologyCoefficientMap S.f m = 0 := by
  simpa only [cohomologyδ, cohomologyCoefficientMap_eq, cochainComplexFunctor,
    ShortComplex.map_f, ShortComplex.map_g] using
    (hS.map_cochainComplexFunctor).δ_comp n m h

/-- The second coefficient map followed by the connecting map is zero. -/
@[reassoc (attr := simp)]
lemma comp_cohomologyδ (n m : ℕ) (h : n + 1 = m) :
    cohomologyCoefficientMap S.g n ≫ hS.cohomologyδ n m h = 0 := by
  simpa only [cohomologyδ, cohomologyCoefficientMap_eq, cochainComplexFunctor,
    ShortComplex.map_f, ShortComplex.map_g] using
    (hS.map_cochainComplexFunctor).comp_δ n m h

/-- Exactness at `Hᵐ(X; L₁)` in the coefficient long exact sequence. -/
lemma cohomology_exact₁ (n m : ℕ) (h : n + 1 = m) :
    (ShortComplex.mk _ _ (hS.cohomologyδ_comp n m h)).Exact := by
  simpa only [cohomologyδ, cohomologyCoefficientMap_eq, cochainComplexFunctor,
    ShortComplex.map_f, ShortComplex.map_g] using
    (hS.map_cochainComplexFunctor).homology_exact₁ n m h

/-- Exactness at `Hⁿ(X; L₂)` in the coefficient long exact sequence. -/
lemma cohomology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (S.cohomologyCoefficientMap_comp_eq_zero n)).Exact := by
  simpa only [cohomologyδ, cohomologyCoefficientMap_eq, cochainComplexFunctor,
    ShortComplex.map_f, ShortComplex.map_g] using
    (hS.map_cochainComplexFunctor).homology_exact₂ n

/-- Exactness at `Hⁿ(X; L₃)` in the coefficient long exact sequence. -/
lemma cohomology_exact₃ (n m : ℕ) (h : n + 1 = m) :
    (ShortComplex.mk _ _ (hS.comp_cohomologyδ n m h)).Exact := by
  simpa only [cohomologyδ, cohomologyCoefficientMap_eq, cochainComplexFunctor,
    ShortComplex.map_f, ShortComplex.map_g] using
    (hS.map_cochainComplexFunctor).homology_exact₃ n m h

/-- A morphism of short exact local-system sequences commutes with the connecting maps. -/
@[reassoc]
lemma cohomologyδ_naturality (hT : T.ShortExact) (φ : S ⟶ T)
    (n m : ℕ) (h : n + 1 = m) :
    hS.cohomologyδ n m h ≫ cohomologyCoefficientMap φ.τ₁ m =
      cohomologyCoefficientMap φ.τ₃ n ≫ hT.cohomologyδ n m h := by
  simpa only [cohomologyδ, cohomologyCoefficientMap_eq, cochainComplexFunctor,
    ShortComplex.map_f, ShortComplex.map_g, Functor.mapShortComplex_obj,
    Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₃] using
    HomologicalComplex.HomologySequence.δ_naturality
      ((cochainComplexFunctor R X).mapShortComplex.map φ)
      (hS.map_cochainComplexFunctor) (hT.map_cochainComplexFunctor) n m h

end CategoryTheory.ShortComplex.ShortExact
