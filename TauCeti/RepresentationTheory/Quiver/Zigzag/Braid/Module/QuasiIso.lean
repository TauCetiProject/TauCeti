/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Module.Exactness
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Module.Support
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Quasi-isomorphisms under the two zigzag braid tensor actions

Tensoring with either the positive or inverse braid complex preserves quasi-isomorphisms
between arbitrary unbounded cochain complexes of graded zigzag modules. Each tensor functor
defines a morphism of the quasi-isomorphism localizer, hence induces a functor between any
supplied localizations, including chosen derived categories.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "c" => ComplexShape.up ℤ

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private abbrev tensor :=
  GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ

/-- The totalized positive braid tensor action preserves quasi-isomorphisms. -/
theorem quasiIso_zigzagBraidTensor_map (i : V)
    {K L : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((Functor.map₂CochainComplex
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ)).obj
        (zigzagBraidComplex k G i)).map f) := by
  -- Evaluate the support sequence along f. Fixed-term tensor functors preserve homology,
  -- and shifts preserve quasi-isomorphisms, so the two outer comparison maps are
  -- quasi-isomorphisms. The short-exact middle-map theorem then handles the totalized map.
  let S := zigzagBraidTensorSupportSequence.{u, v, w} k G i
  let φ := S.mapNatTrans ((evaluation _ _).map f)
  have hK := (zigzagBraidTensorSupportSequence_shortExact.{u, v, w} k G i).map_of_exact
    ((evaluation _ _).obj K)
  have hL := (zigzagBraidTensorSupportSequence_shortExact.{u, v, w} k G i).map_of_exact
    ((evaluation _ _).obj L)
  suffices h : QuasiIso φ.τ₂ by
    dsimp only [φ, ShortComplex.mapNatTrans, S] at h
    -- The comparison φ.τ₂ evaluates S.X₂ along f. Component/evaluation equations alone
    -- leave HasHomology arguments indexed by the evaluated short-complex endpoints.
    -- Reset the whole QuasiIso type so the public X₂ rewrite has a well-typed motive.
    change QuasiIso ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₂.map f) at h
    rw [zigzagBraidTensorSupportSequence_X₂.{u, v, w} k G i] at h
    exact h
  apply HomologySequence.quasiIso_τ₂ φ hK hL
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
    -- The comparison φ.τ₁ evaluates S.X₁ along f. Component/evaluation equations alone
    -- leave HasHomology arguments indexed by the evaluated short-complex endpoints.
    -- Reset the whole QuasiIso type so the public X₁ rewrite has a well-typed motive.
    change QuasiIso ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₁.map f)
    rw [zigzagBraidTensorSupportSequence_X₁.{u, v, w} k G i]
    let : ((tensor.{u, v, w} k G).obj (zigzagGradedBimodule k G)).PreservesHomology :=
      preservesHomology_zigzagGradedBimoduleTensor.{u, max v u w, w} k G
    infer_instance
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
    -- The comparison φ.τ₃ evaluates S.X₃ along f. Component/evaluation equations alone
    -- leave HasHomology arguments indexed by the evaluated short-complex endpoints.
    -- Reset the whole QuasiIso type so the public X₃ rewrite has a well-typed motive.
    change QuasiIso ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₃.map f)
    rw [zigzagBraidTensorSupportSequence_X₃.{u, v, w} k G i]
    let : ((tensor.{u, v, w} k G).obj
        (zigzagGradedBraidBimodule k G i)).PreservesHomology :=
      preservesHomology_zigzagGradedBraidBimoduleTensor.{u, max v u w, w} k G i
    simp only [Functor.comp_map]
    infer_instance

/-- The totalized inverse braid tensor action preserves quasi-isomorphisms. -/
theorem quasiIso_zigzagBraidInverseTensor_map (i : V)
    {K L : CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((Functor.map₂CochainComplex
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ)).obj
        (zigzagBraidInverseComplex k G i)).map f) := by
  -- Use the inverse support sequence with the same outer-to-middle comparison.
  let S := zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i
  let φ := S.mapNatTrans ((evaluation _ _).map f)
  have hK :=
    (zigzagBraidInverseTensorSupportSequence_shortExact.{u, v, w} k G i).map_of_exact
      ((evaluation _ _).obj K)
  have hL :=
    (zigzagBraidInverseTensorSupportSequence_shortExact.{u, v, w} k G i).map_of_exact
      ((evaluation _ _).obj L)
  suffices h : QuasiIso φ.τ₂ by
    dsimp only [φ, ShortComplex.mapNatTrans, S] at h
    -- The comparison φ.τ₂ evaluates S.X₂ along f. Component/evaluation equations alone
    -- leave HasHomology arguments indexed by the evaluated short-complex endpoints.
    -- Reset the whole QuasiIso type so the public X₂ rewrite has a well-typed motive.
    change QuasiIso ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₂.map f) at h
    rw [zigzagBraidInverseTensorSupportSequence_X₂.{u, v, w} k G i] at h
    exact h
  apply HomologySequence.quasiIso_τ₂ φ hK hL
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
    -- The comparison φ.τ₁ evaluates S.X₁ along f. Component/evaluation equations alone
    -- leave HasHomology arguments indexed by the evaluated short-complex endpoints.
    -- Reset the whole QuasiIso type so the public X₁ rewrite has a well-typed motive.
    change QuasiIso ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₁.map f)
    rw [zigzagBraidInverseTensorSupportSequence_X₁.{u, v, w} k G i]
    let : ((tensor.{u, v, w} k G).obj ((GradedModuleCat.shiftFunctor (-2)).obj
        (zigzagGradedBraidBimodule k G i))).PreservesHomology :=
      preservesHomology_zigzagGradedBraidBimoduleTensor_shift.{u, max v u w, w} k G i (-2)
    simp only [Functor.comp_map]
    infer_instance
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
    -- The comparison φ.τ₃ evaluates S.X₃ along f. Component/evaluation equations alone
    -- leave HasHomology arguments indexed by the evaluated short-complex endpoints.
    -- Reset the whole QuasiIso type so the public X₃ rewrite has a well-typed motive.
    change QuasiIso ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₃.map f)
    rw [zigzagBraidInverseTensorSupportSequence_X₃.{u, v, w} k G i]
    let : ((tensor.{u, v, w} k G).obj (zigzagGradedBimodule k G)).PreservesHomology :=
      preservesHomology_zigzagGradedBimoduleTensor.{u, max v u w, w} k G
    infer_instance

/-- The positive braid tensor functor defines a morphism of the quasi-isomorphism localizer. -/
def zigzagBraidTensorLocalizerMorphism (i : V) :
    LocalizerMorphism
      (HomologicalComplex.quasiIso (GradedModuleCat.{max v u w} (Γ).piece) c)
      (HomologicalComplex.quasiIso (GradedModuleCat.{max v u w} (Γ).piece) c) where
  functor := (Functor.map₂CochainComplex
    (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ)).obj
      (zigzagBraidComplex k G i)
  map _ _ f hf := by
    let : QuasiIso f := hf
    exact quasiIso_zigzagBraidTensor_map.{u, v, w} k G i f

/-- The inverse braid tensor functor defines a morphism of the quasi-isomorphism localizer. -/
def zigzagBraidInverseTensorLocalizerMorphism (i : V) :
    LocalizerMorphism
      (HomologicalComplex.quasiIso (GradedModuleCat.{max v u w} (Γ).piece) c)
      (HomologicalComplex.quasiIso (GradedModuleCat.{max v u w} (Γ).piece) c) where
  functor := (Functor.map₂CochainComplex
    (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ)).obj
      (zigzagBraidInverseComplex k G i)
  map _ _ f hf := by
    let : QuasiIso f := hf
    exact quasiIso_zigzagBraidInverseTensor_map.{u, v, w} k G i f

@[simp]
theorem zigzagBraidTensorLocalizerMorphism_functor (i : V) :
    (zigzagBraidTensorLocalizerMorphism.{u, v, w} k G i).functor =
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidComplex k G i) := (rfl)

@[simp]
theorem zigzagBraidInverseTensorLocalizerMorphism_functor (i : V) :
    (zigzagBraidInverseTensorLocalizerMorphism.{u, v, w} k G i).functor =
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidInverseComplex k G i) := (rfl)

end TauCeti
