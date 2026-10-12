/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.CoaugmentedBar
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.CoalgHom

/-!
# A-infinity morphisms on coaugmented bar constructions

An `A∞` morphism is stored as a map of reduced bar coalgebras. Its coaugmented bar map fixes
the empty word and acts by the stored map on positive-length words. It is a coalgebra morphism
which intertwines the coaugmented bar differentials. Identity and composition are preserved.
These facts let module and bimodule bar constructions use the coaugmented coalgebra without
changing the notion of `A∞` morphism.

The bar convention follows B. Keller, *Introduction to A-infinity algebras and modules*,
Sections 3.4 and 3.6.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {CC : AInfinityAlgebra R C}

/-- The map of coaugmented bar constructions induced by an `A∞` morphism. -/
noncomputable def coaugmentedBarMap (f : AInfinityHom AA BB) :
    TensorWords R A →ₗ[R] TensorWords R B :=
  ReducedTensorWords.coaugmentedMap f.barMap

/-- The coaugmented bar map preserves the coaugmentation of the ground ring. -/
@[simp]
theorem coaugmentedBarMap_algebraMap (f : AInfinityHom AA BB) (r : R) :
    f.coaugmentedBarMap (algebraMap R (TensorWords R A) r) =
      algebraMap R (TensorWords R B) r :=
  ReducedTensorWords.coaugmentedMap_algebraMap f.barMap r

/-- The coaugmented bar map fixes the empty word. -/
@[simp]
theorem coaugmentedBarMap_one (f : AInfinityHom AA BB) :
    f.coaugmentedBarMap (1 : TensorWords R A) = 1 :=
  ReducedTensorWords.coaugmentedMap_one f.barMap

/-- The coaugmented bar map is the stored bar map on positive-length words. -/
@[simp]
theorem coaugmentedBarMap_reducedInclusion (f : AInfinityHom AA BB)
    (w : ReducedTensorWords R A) :
    f.coaugmentedBarMap (TensorWords.reducedInclusion R A w) =
      TensorWords.reducedInclusion R B (f.barMap w) :=
  ReducedTensorWords.coaugmentedMap_reducedInclusion f.barMap w

/-- Projecting the coaugmented bar map recovers the stored reduced bar map. -/
@[simp]
theorem reducedProjection_comp_coaugmentedBarMap (f : AInfinityHom AA BB) :
    TensorWords.reducedProjection R B ∘ₗ f.coaugmentedBarMap =
      f.barMap ∘ₗ TensorWords.reducedProjection R A :=
  ReducedTensorWords.reducedProjection_comp_coaugmentedMap f.barMap

/-- The coaugmented bar map preserves the counit. -/
@[simp]
theorem counit_comp_coaugmentedBarMap (f : AInfinityHom AA BB) :
    TensorWords.counit R B ∘ₗ f.coaugmentedBarMap = TensorWords.counit R A :=
  ReducedTensorWords.counit_comp_coaugmentedMap f.barMap

/-- The coaugmented bar map is a coalgebra morphism. -/
noncomputable def coaugmentedBarCoalgHom (f : AInfinityHom AA BB) :
    TensorWords R A →ₗc[R] TensorWords R B :=
  ReducedTensorWords.coaugmentedCoalgHom f.isCoalgHom_barMap

/-- The coalgebra morphism underlying map is the coaugmented bar map. -/
@[simp]
theorem coaugmentedBarCoalgHom_toLinearMap (f : AInfinityHom AA BB) :
    (f.coaugmentedBarCoalgHom : TensorWords R A →ₗ[R] TensorWords R B) =
      f.coaugmentedBarMap := by
  exact ReducedTensorWords.coaugmentedCoalgHom_toLinearMap f.isCoalgHom_barMap

/-- The coaugmented bar map has degree zero for the suspended total gradings. -/
theorem isHomogeneous_coaugmentedBarMap (f : AInfinityHom AA BB) :
    LinearMap.IsHomogeneous f.coaugmentedBarMap
      (TensorWords.gradedPiece (AA.grading.shift 1))
      (TensorWords.gradedPiece (BB.grading.shift 1)) 0 :=
  ReducedTensorWords.isHomogeneous_coaugmentedMap f.isHomogeneous_barMap

/-- The coaugmented bar map intertwines the square-zero bar differentials. -/
@[simp]
theorem coaugmentedBarDifferential_comp_coaugmentedBarMap
    (f : AInfinityHom AA BB) :
    BB.coaugmentedBarDifferential ∘ₗ f.coaugmentedBarMap =
      f.coaugmentedBarMap ∘ₗ AA.coaugmentedBarDifferential := by
  apply TensorWords.linearMap_ext R A
  intro n x
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : TensorWords.of R A 0 (PiTensorProduct.tprod R x) =
        algebraMap R (TensorWords R A)
          ((TensorPower.algebraMap₀ (R := R) (M := A)).symm
            (PiTensorProduct.tprod R x)) := by
      rw [TensorWords.algebraMap_apply, LinearEquiv.apply_symm_apply]
    rw [hzero, LinearMap.comp_apply, LinearMap.comp_apply]
    simp [Algebra.algebraMap_eq_smul_one]
  · rw [← TensorWords.reducedInclusion_of R A ⟨n, hn⟩
        (PiTensorProduct.tprod R x),
      LinearMap.comp_apply, LinearMap.comp_apply,
      coaugmentedBarMap_reducedInclusion]
    have hB := LinearMap.congr_fun BB.coaugmentedBarDifferential_comp_reducedInclusion
      (f.barMap (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R x)))
    have hA := LinearMap.congr_fun AA.coaugmentedBarDifferential_comp_reducedInclusion
      (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R x))
    simp only [LinearMap.comp_apply] at hA hB
    rw [hB, hA, coaugmentedBarMap_reducedInclusion,
      f.barDifferential_barMap]

/-- The identity `A∞` morphism induces the identity on coaugmented bars. -/
@[simp]
theorem coaugmentedBarMap_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).coaugmentedBarMap = LinearMap.id := by
  rw [coaugmentedBarMap, barMap_id,
    ReducedTensorWords.coaugmentedMap_id]

/-- Composition of `A∞` morphisms induces composition on coaugmented bars. -/
@[simp]
theorem coaugmentedBarMap_comp (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (g.comp f).coaugmentedBarMap = g.coaugmentedBarMap ∘ₗ f.coaugmentedBarMap := by
  rw [coaugmentedBarMap, barMap_comp,
    ReducedTensorWords.coaugmentedMap_comp]
  rfl

/-- The identity `A∞` morphism induces the identity coalgebra morphism on coaugmented bars. -/
@[simp]
theorem coaugmentedBarCoalgHom_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).coaugmentedBarCoalgHom =
      CoalgHom.id R (TensorWords R A) := by
  apply CoalgHom.linearMapOfClass_injective
  simp

/-- Composition of `A∞` morphisms induces composition of coaugmented coalgebra morphisms. -/
@[simp]
theorem coaugmentedBarCoalgHom_comp (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (g.comp f).coaugmentedBarCoalgHom =
      g.coaugmentedBarCoalgHom.comp f.coaugmentedBarCoalgHom := by
  apply CoalgHom.linearMapOfClass_injective
  simp

end AInfinityHom

end TauCeti
