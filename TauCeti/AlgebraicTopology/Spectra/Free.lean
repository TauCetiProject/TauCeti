/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import TauCeti.AlgebraicTopology.Spectra.SymmetricSpectrum
public import TauCeti.CategoryTheory.Monoidal.Mod.Free

/-!
# Free symmetric spectra

Evaluation of a symmetric spectrum at level `n` has a left adjoint `F_n`.
First freely place a pointed simplicial set in a symmetric sequence at level `n`,
using the coproduct indexed by bijections out of `Fin n`, and then take the free
module over the sphere sequence. Thus the permutation actions and the iterated
structure maps are those of the native sphere-module carrier.

The adjunction is obtained by composing Mathlib's `evaluationAdjunctionRight`,
the equivalence between Day functors and ordinary functors, and the free-module
adjunction. These are point-set constructions, without a model structure or a
claim about derived mapping spaces. Free spectra supply the cells for level and
stable model structures.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc.
  13 (2000), Section 2.2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.SymmetricSpectrum

open scoped DayFunctor

/-- Evaluation of a sphere module at the standard finite set `Fin n`. -/
noncomputable abbrev evaluation (n : ℕ) : SymmetricSpectrum ⥤ PointedSSet.{0} where
  obj E := E.X.functor.obj (FiniteBijection.mk n)
  map f := f.hom.natTrans.app (FiniteBijection.mk n)

/-- The free symmetric spectrum `F_n K`: freely adjoin the symmetric action in
level `n`, then freely adjoin the sphere action. -/
noncomputable abbrev free (n : ℕ) : PointedSSet.{0} ⥤ SymmetricSpectrum :=
  evaluationLeftAdjoint PointedSSet.{0} (FiniteBijection.mk n) ⋙
    (DayFunctor.equiv FiniteBijection PointedSSet.{0}).inverse ⋙
      freeMod SymmetricSequence.sphere

/-- The free spectrum in level `n` is left adjoint to level-`n` evaluation. -/
noncomputable def freeEvaluationAdjunction (n : ℕ) : free n ⊣ evaluation n :=
  ((evaluationAdjunctionRight PointedSSet.{0} (FiniteBijection.mk n)).comp
    (DayFunctor.equiv FiniteBijection PointedSSet.{0}).symm.toAdjunction).comp
      (freeModAdjunction SymmetricSequence.sphere)

/-- The universal generator of `F_n K` in level `n`. -/
noncomputable def freeι (n : ℕ) (K : PointedSSet.{0}) :
    K ⟶ (evaluation n).obj ((free n).obj K) :=
  (freeEvaluationAdjunction n).unit.app K

/-- The generator is the identity-bijection summand followed by the sphere-unit inclusion. -/
lemma freeι_eq (n : ℕ) (K : PointedSSet.{0}) :
    freeι n K =
      Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) (𝟙 _) ≫
        (freeModι SymmetricSequence.sphere
          ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).inverse.obj
            ((evaluationLeftAdjoint PointedSSet.{0} (FiniteBijection.mk n)).obj K))).natTrans.app
              (FiniteBijection.mk n) := by
  simp only [freeι, freeEvaluationAdjunction, Adjunction.comp_unit_app,
    evaluationAdjunctionRight_unit_app, freeModAdjunction_unit_app]
  -- Normalize the tautological Day-functor wrapper to compare components of the composed unit.
  -- Its simps lemmas cannot match the freeModObj instance indexed by the composite functor
  -- against the wrapped sequence at implicit transparency. Compare the identity composite directly.
  dsimp [CategoryTheory.evaluation, DayFunctor.equiv]
  exact congrArg (fun f ↦ f ≫ _) (Category.comp_id _)

/-- Extension of a level-`n` map to a spectrum map from `F_n K`. -/
noncomputable def freeDesc {n : ℕ} {K : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : K ⟶ (evaluation n).obj E) : (free n).obj K ⟶ E :=
  ((freeEvaluationAdjunction n).homEquiv K E).symm f

/-- A free-spectrum extension agrees with the original map on the generator. -/
@[simp↓, reassoc (attr := simp)]
lemma freeι_desc {n : ℕ} {K : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : K ⟶ (evaluation n).obj E) :
    dsimp% freeι n K ≫ (evaluation n).map (freeDesc E f) = f := by
  simpa only [freeι, freeDesc, Adjunction.homEquiv_unit] using
    ((freeEvaluationAdjunction n).homEquiv K E).apply_symm_apply f

/-- Every map from a free spectrum is recovered by extension of its generator. -/
@[simp↓]
lemma freeDesc_ι {n : ℕ} {K : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : (free n).obj K ⟶ E) :
    dsimp% freeDesc E (freeι n K ≫ (evaluation n).map f) = f := by
  simpa only [freeι, freeDesc, Adjunction.homEquiv_unit] using
    ((freeEvaluationAdjunction n).homEquiv K E).symm_apply_apply f

/-- The universal generator is natural in the pointed simplicial set. -/
@[reassoc (attr := simp)]
lemma freeι_naturality {n : ℕ} {K L : PointedSSet.{0}} (f : K ⟶ L) :
    f ≫ freeι n L = freeι n K ≫ (evaluation n).map ((free n).map f) := by
  simpa only [freeι, Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] using
    (freeEvaluationAdjunction n).unit.naturality f

/-- Extension from a free spectrum commutes with post-composition. -/
@[simp, reassoc]
lemma freeDesc_comp {n : ℕ} {K : PointedSSet.{0}} {E E' : SymmetricSpectrum}
    (f : K ⟶ (evaluation n).obj E) (g : E ⟶ E') :
    freeDesc E f ≫ g = freeDesc E' (f ≫ (evaluation n).map g) := by
  simpa only [freeDesc] using
    ((freeEvaluationAdjunction n).homEquiv_naturality_right_symm f g).symm

/-- Extension from a free spectrum commutes with pre-composition on generators. -/
@[simp, reassoc]
lemma free_map_freeDesc {n : ℕ} {K L : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : K ⟶ L) (g : L ⟶ (evaluation n).obj E) :
    dsimp% (free n).map f ≫ freeDesc E g = freeDesc E (f ≫ g) := by
  simpa only [freeDesc] using
    (dsimp% ((freeEvaluationAdjunction n).homEquiv_naturality_left_symm f g).symm)

/-- Maps out of a free spectrum are determined by the universal generator. -/
@[ext]
lemma free_hom_ext {n : ℕ} {K : PointedSSet.{0}} {E : SymmetricSpectrum}
    {f g : (free n).obj K ⟶ E}
    (h : freeι n K ≫ (evaluation n).map f = freeι n K ≫ (evaluation n).map g) :
    f = g := by
  apply ((freeEvaluationAdjunction n).homEquiv K E).injective
  simpa only [Adjunction.homEquiv_unit, freeι] using h

end TauCeti.SymmetricSpectrum
