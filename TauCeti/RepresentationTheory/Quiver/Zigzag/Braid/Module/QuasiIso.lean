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

Compare the positive and inverse support sequences along a quasi-isomorphism of module
complexes. The fixed-term tensor functors preserve homology, and cohomological shifts
preserve quasi-isomorphisms. The outer maps of each comparison are therefore
quasi-isomorphisms. The existing middle-map theorem for short exact sequences proves
the same for the actual totalized tensor map.

The localizer morphisms below record the input for descending these two functors to
the derived category. Compatibility with the existing homotopy autoequivalences,
descent of their inverse and braid isomorphisms, and supplied-equivalence transfer
require further steps.
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
  let S := zigzagBraidTensorSupportSequence.{u, v, w} k G i
  let φ := S.mapNatTrans ((evaluation _ _).map f)
  have hK := (zigzagBraidTensorSupportSequence_shortExact.{u, v, w} k G i).map_of_exact
    ((evaluation _ _).obj K)
  have hL := (zigzagBraidTensorSupportSequence_shortExact.{u, v, w} k G i).map_of_exact
    ((evaluation _ _).obj L)
  suffices h : QuasiIso φ.τ₂ by
    dsimp only [φ, ShortComplex.mapNatTrans, S] at h
    change QuasiIso ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₂.map f) at h
    rw [zigzagBraidTensorSupportSequence_X₂.{u, v, w} k G i] at h
    exact h
  apply HomologySequence.quasiIso_τ₂ φ hK hL
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
    change QuasiIso ((zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₁.map f)
    rw [zigzagBraidTensorSupportSequence_X₁.{u, v, w} k G i]
    let : ((tensor.{u, v, w} k G).obj (zigzagGradedBimodule k G)).PreservesHomology :=
      preservesHomology_zigzagGradedBimoduleTensor.{u, max v u w, w} k G
    infer_instance
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
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
    change QuasiIso ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₂.map f) at h
    rw [zigzagBraidInverseTensorSupportSequence_X₂.{u, v, w} k G i] at h
    exact h
  apply HomologySequence.quasiIso_τ₂ φ hK hL
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
    change QuasiIso ((zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₁.map f)
    rw [zigzagBraidInverseTensorSupportSequence_X₁.{u, v, w} k G i]
    let : ((tensor.{u, v, w} k G).obj ((GradedModuleCat.shiftFunctor (-2)).obj
        (zigzagGradedBraidBimodule k G i))).PreservesHomology :=
      preservesHomology_zigzagGradedBraidBimoduleTensor_shift.{u, max v u w, w} k G i (-2)
    simp only [Functor.comp_map]
    infer_instance
  · dsimp only [φ, ShortComplex.mapNatTrans, S]
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
