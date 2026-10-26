/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Coproducts
public import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Basic

/-!
# The two support sequences of the zigzag braid tensor action

The highest nonzero term of a two-term bimodule complex is a subcomplex, and its
lowest term is the quotient. Totalized tensoring with a module complex gives a short
exact sequence, split in every cochain degree. The two supported rows are identified
by the canonical two-summand totalization isomorphism.

For the positive braid complex the outer complexes are the regular tensor action and
the vertex tensor action shifted cohomologically by one. For the inverse complex they
are the internally shifted vertex action shifted cohomologically by minus one, and the
regular action. The internal shift by minus two and these cohomological shifts are
separate. The sequences are objects of a functor category, so their chain maps are
natural in the module complex. No boundedness or flatness assumption on that complex
is needed for these degreewise split sequences.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Functor

universe u v w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "c" => ComplexShape.up ℤ

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private abbrev Bimod :=
  GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece

private abbrev Mod :=
  GradedModuleCat.{max v u w} (Γ).piece

private abbrev tensor :
    Bimod k G ⥤
      Mod.{u, v, w} k G ⥤ Mod.{u, v, w} k G :=
  GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ

private def positiveSupport (i : V) : TwoTermSupport (Bimod k G) where
  K := zigzagBraidComplex k G i
  a := -1
  b := 0
  A := zigzagGradedBraidBimodule k G i
  B := zigzagGradedBimodule k G
  low := zigzagBraidComplexXIso₀ k G i
  high := zigzagBraidComplexXIso₁ k G i
  ne := by decide
  outgoing j := zigzagBraidComplex_d_eq_zero₀ i j (by decide)
  incoming j := zigzagBraidComplex_d_eq_zero₁ i j (by decide)
  support j := isZero_zigzagBraidComplex_X i

private def inverseSupport (i : V) : TwoTermSupport (Bimod k G) where
  K := zigzagBraidInverseComplex k G i
  a := 0
  b := 1
  A := zigzagGradedBimodule k G
  B := (GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)
  low := zigzagBraidInverseComplexXIso₀ k G i
  high := zigzagBraidInverseComplexXIso₁ k G i
  ne := by decide
  outgoing j := zigzagBraidInverseComplex_d_eq_zero₀ i j (by decide)
  incoming j := zigzagBraidInverseComplex_d_eq_zero₁ i j (by decide)
  support j := isZero_zigzagBraidInverseComplex_X i

/-- The natural two-support sequence of the positive braid tensor action has outer functors
`T_Z` and `T_U[1]`. The maps are chain maps, natural in every module complex. -/
def zigzagBraidTensorSupportSequence (i : V) :
    ShortComplex (CochainComplex
      (GradedModuleCat.{max v u w} (Γ).piece) ℤ ⥤
        CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframed (positiveSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1))

/-- The natural two-support sequence of the inverse braid tensor action has outer functors
`T_(U{-2})[-1]` and `T_Z`, with distinct internal and cohomological shifts. -/
def zigzagBraidInverseTensorSupportSequence (i : V) :
    ShortComplex (CochainComplex
      (GradedModuleCat.{max v u w} (Γ).piece) ℤ ⥤
        CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframed (inverseSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
      ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))

@[simp]
theorem zigzagBraidTensorSupportSequence_X₁ (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₁ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          (zigzagGradedBimodule k G)) c := by
  simpa only [zigzagBraidTensorSupportSequence, positiveSupport,
    mapBifunctorLeft_eq_map₂HomologicalComplex_obj] using
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframed_X₁ (positiveSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)))

@[simp]
theorem zigzagBraidTensorSupportSequence_X₂ (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₂ =
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidComplex k G i) := by
  simpa only [zigzagBraidTensorSupportSequence, positiveSupport,
    mapBifunctorLeft_eq_map₂HomologicalComplex_obj] using
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframed_X₂ (positiveSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)))

@[simp]
theorem zigzagBraidTensorSupportSequence_X₃ (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₃ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          (zigzagGradedBraidBimodule k G i)) c ⋙
        shiftFunctor (CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (1 : ℤ) := by
  simpa only [zigzagBraidTensorSupportSequence, positiveSupport,
    mapBifunctorLeft_eq_map₂HomologicalComplex_obj, neg_neg] using
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframed_X₃ (positiveSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)))

@[simp]
theorem zigzagBraidInverseTensorSupportSequence_X₁ (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₁ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i))) c ⋙
        shiftFunctor (CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (-1 : ℤ) := by
  simpa only [zigzagBraidInverseTensorSupportSequence, inverseSupport,
    mapBifunctorLeft_eq_map₂HomologicalComplex_obj] using
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframed_X₁ (inverseSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
        ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)))

@[simp]
theorem zigzagBraidInverseTensorSupportSequence_X₂ (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₂ =
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidInverseComplex k G i) := by
  simpa only [zigzagBraidInverseTensorSupportSequence, inverseSupport,
    mapBifunctorLeft_eq_map₂HomologicalComplex_obj] using
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframed_X₂ (inverseSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
        ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)))

@[simp]
theorem zigzagBraidInverseTensorSupportSequence_X₃ (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₃ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          (zigzagGradedBimodule k G)) c := by
  simpa only [zigzagBraidInverseTensorSupportSequence, inverseSupport,
    mapBifunctorLeft_eq_map₂HomologicalComplex_obj] using
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframed_X₃ (inverseSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
        ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)))

/-- The positive support sequence is short exact in the functor category. -/
theorem zigzagBraidTensorSupportSequence_shortExact (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).ShortExact :=
  ShortComplex.shortExact_of_iso
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframedIso (positiveSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)))
    ((tensor.{u, v, w} k G).mapTwoTermSupport_shortExact (positiveSupport k G i))

/-- The inverse support sequence is short exact in the functor category. -/
theorem zigzagBraidInverseTensorSupportSequence_shortExact (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).ShortExact :=
  ShortComplex.shortExact_of_iso
    ((tensor.{u, v, w} k G).mapTwoTermSupportReframedIso (inverseSupport k G i)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
        ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
      ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)))
    ((tensor.{u, v, w} k G).mapTwoTermSupport_shortExact (inverseSupport k G i))

/-- The positive support sequence has its canonical splitting after evaluating at a
module complex and a cochain degree. -/
def zigzagBraidTensorSupportSequenceDegreewiseSplitting (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    (((zigzagBraidTensorSupportSequence.{u, v, w} k G i).map ((evaluation _ _).obj N)).map
      (eval (GradedModuleCat.{max v u w} (Γ).piece) c j)).Splitting :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframedDegreewiseSplitting (positiveSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)) N j

/-- The actual positive totalization degree is the biproduct of its two public endpoints. -/
def zigzagBraidTensorSupportSequenceDegreewiseIso (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₂.obj N).X j ≅
      ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₁.obj N).X j ⊞
        ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₃.obj N).X j :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframedDegreewiseIso (positiveSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)) N j

/-- The positive support inclusion is the first biproduct inclusion in each degree. -/
@[reassoc (attr := simp)]
theorem zigzagBraidTensorSupportSequence_f_degreewiseIso_hom (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    (((zigzagBraidTensorSupportSequence.{u, v, w} k G i).f.app N).f j) ≫
        (zigzagBraidTensorSupportSequenceDegreewiseIso.{u, v, w} k G i N j).hom = biprod.inl :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframed_f_degreewiseIso_hom (positiveSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)) N j

/-- The positive support projection is the second biproduct projection in each degree. -/
@[reassoc (attr := simp)]
theorem zigzagBraidTensorSupportSequence_degreewiseIso_hom_snd (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    (zigzagBraidTensorSupportSequenceDegreewiseIso.{u, v, w} k G i N j).hom ≫ biprod.snd =
      (((zigzagBraidTensorSupportSequence.{u, v, w} k G i).g.app N).f j) :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframed_degreewiseIso_hom_snd (positiveSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G))
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso (zigzagGradedBraidBimodule k G i) (-1)) N j

/-- The inverse support sequence has its canonical splitting after evaluating at a
module complex and a cochain degree. -/
def zigzagBraidInverseTensorSupportSequenceDegreewiseSplitting (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    (((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).map ((evaluation _ _).obj N)).map
      (eval (GradedModuleCat.{max v u w} (Γ).piece) c j)).Splitting :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframedDegreewiseSplitting (inverseSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
      ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)) N j

/-- The actual inverse totalization degree is the biproduct of its two public endpoints. -/
def zigzagBraidInverseTensorSupportSequenceDegreewiseIso (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₂.obj N).X j ≅
      ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₁.obj N).X j ⊞
        ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₃.obj N).X j :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframedDegreewiseIso (inverseSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
      ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)) N j

/-- The inverse support inclusion is the first biproduct inclusion in each degree. -/
@[reassoc (attr := simp)]
theorem zigzagBraidInverseTensorSupportSequence_f_degreewiseIso_hom (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    (((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).f.app N).f j) ≫
        (zigzagBraidInverseTensorSupportSequenceDegreewiseIso.{u, v, w} k G i N j).hom =
      biprod.inl :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframed_f_degreewiseIso_hom (inverseSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
      ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)) N j

/-- The inverse support projection is the second biproduct projection in each degree. -/
@[reassoc (attr := simp)]
theorem zigzagBraidInverseTensorSupportSequence_degreewiseIso_hom_snd (i : V)
    (N : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (j : ℤ) :
    (zigzagBraidInverseTensorSupportSequenceDegreewiseIso.{u, v, w} k G i N j).hom ≫ biprod.snd =
      (((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).g.app N).f j) :=
  (tensor.{u, v, w} k G).mapTwoTermSupportReframed_degreewiseIso_hom_snd (inverseSupport k G i)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowNatIso
      ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
    ((tensor.{u, v, w} k G).mapBifunctorSingleRowZeroNatIso (zigzagGradedBimodule k G)) N j

end TauCeti
