/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.GradedCoderivation

/-!
# Coaugmenting morphisms of reduced tensor coalgebras

A morphism of reduced tensor coalgebras extends uniquely to a morphism of their coaugmented
tensor coalgebras which sends the empty word to the empty word. On positive length it agrees
with the original morphism. This supplies the coalgebra map on the full bar construction of
an `A∞` morphism.

The construction uses the canonical splitting of tensor words into the empty word and the
positive-length words. The two extra cuts in the coproduct of a positive-length word account
for the coaugmentation terms.

The bar convention follows E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic
bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace ReducedTensorWords

universe uR uM uN

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Extend a reduced tensor-coalgebra map by sending the empty word to the empty word. -/
noncomputable def coaugmentedMap (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    TensorWords R M →ₗ[R] TensorWords R N :=
  Algebra.linearMap R (TensorWords R N) ∘ₗ TensorWords.counit R M +
    TensorWords.reducedInclusion R N ∘ₗ F ∘ₗ TensorWords.reducedProjection R M

/-- The coaugmented map sends a scalar multiple of the empty word to the same scalar
multiple of the target empty word. -/
@[simp]
theorem coaugmentedMap_algebraMap (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (r : R) :
    coaugmentedMap F (algebraMap R (TensorWords R M) r) =
      algebraMap R (TensorWords R N) r := by
  have hp : TensorWords.reducedProjection R M
      (algebraMap R (TensorWords R M) r) = 0 := by
    rw [TensorWords.algebraMap_apply, TensorWords.reducedProjection_of_zero]
  simp only [coaugmentedMap, LinearMap.add_apply, LinearMap.comp_apply,
    TensorWords.counit_algebraMap, hp, map_zero, add_zero, Algebra.linearMap_apply]

/-- The empty word maps to the empty word. -/
@[simp]
theorem coaugmentedMap_one (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    coaugmentedMap F (1 : TensorWords R M) = 1 := by
  simpa using coaugmentedMap_algebraMap F (1 : R)

/-- The extension agrees with the reduced map on positive-length words. -/
@[simp]
theorem coaugmentedMap_reducedInclusion
    (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (w : ReducedTensorWords R M) :
    coaugmentedMap F (TensorWords.reducedInclusion R M w) =
      TensorWords.reducedInclusion R N (F w) := by
  simp [coaugmentedMap]

/-- Projecting the coaugmented map recovers the reduced map of the projected input. -/
@[simp]
theorem reducedProjection_comp_coaugmentedMap
    (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    TensorWords.reducedProjection R N ∘ₗ coaugmentedMap F =
      F ∘ₗ TensorWords.reducedProjection R M := by
  apply LinearMap.ext
  intro w
  simp [coaugmentedMap, TensorWords.algebraMap_apply]

/-- Coaugmenting preserves the counit. -/
@[simp]
theorem counit_comp_coaugmentedMap
    (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    TensorWords.counit R N ∘ₗ coaugmentedMap F = TensorWords.counit R M := by
  rw [coaugmentedMap]
  simp only [LinearMap.comp_add, ← LinearMap.comp_assoc,
    TensorWords.counit_comp_algebraMap, TensorWords.counit_comp_reducedInclusion,
    LinearMap.id_comp, LinearMap.zero_comp, add_zero]

/-- A linear map out of tensor words is determined by its values on the empty word and
on positive-length words. -/
theorem coaugmentedMap_unique
    (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (H : TensorWords R M →ₗ[R] TensorWords R N)
    (hzero : H ∘ₗ Algebra.linearMap R (TensorWords R M) =
      Algebra.linearMap R (TensorWords R N))
    (hpos : H ∘ₗ TensorWords.reducedInclusion R M =
      TensorWords.reducedInclusion R N ∘ₗ F) :
    H = coaugmentedMap F := by
  apply LinearMap.ext
  intro w
  have hw := TensorWords.reducedInclusion_reducedProjection_add_algebraMap_counit R M w
  conv_lhs => rw [← hw]
  have he := LinearMap.congr_fun hzero (TensorWords.counit R M w)
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply] at he
  rw [map_add, ← LinearMap.comp_apply, hpos, LinearMap.comp_apply, he]
  simp only [coaugmentedMap, LinearMap.add_apply, LinearMap.comp_apply]
  rw [Algebra.linearMap_apply, add_comm]

/-- The coaugmented extension of the identity is the identity. -/
@[simp]
theorem coaugmentedMap_id :
    coaugmentedMap (LinearMap.id : ReducedTensorWords R M →ₗ[R] _) = LinearMap.id := by
  apply Eq.symm
  apply coaugmentedMap_unique
  · rw [LinearMap.id_comp]
  · rw [LinearMap.id_comp, LinearMap.comp_id]

/-- Coaugmented extension respects composition of reduced maps. -/
@[simp]
theorem coaugmentedMap_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (G : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R P)
    (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    coaugmentedMap (G ∘ₗ F) = coaugmentedMap G ∘ₗ coaugmentedMap F := by
  apply Eq.symm
  apply coaugmentedMap_unique
  · apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    simp
  · apply LinearMap.ext
    intro w
    simp only [LinearMap.comp_apply]
    simp

/-- Coaugmenting a reduced coalgebra morphism preserves deconcatenation, including both
degenerate cuts. -/
theorem deconcatenation_comp_coaugmentedMap
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) :
    TensorWords.deconcatenation R N ∘ₗ coaugmentedMap F =
      TensorProduct.map (coaugmentedMap F) (coaugmentedMap F) ∘ₗ
        TensorWords.deconcatenation R M := by
  apply TensorWords.linearMap_ext R M
  intro n x
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : TensorWords.of R M 0 (PiTensorProduct.tprod R x) =
        algebraMap R (TensorWords R M)
          ((TensorPower.algebraMap₀ (R := R) (M := M)).symm
            (PiTensorProduct.tprod R x)) := by
      rw [TensorWords.algebraMap_apply, LinearEquiv.apply_symm_apply]
    rw [hzero, LinearMap.comp_apply, LinearMap.comp_apply,
      coaugmentedMap_algebraMap]
    simp [TensorWords.deconcatenation_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul']
  · rw [← TensorWords.reducedInclusion_of R M ⟨n, hn⟩
        (PiTensorProduct.tprod R x)]
    simp only [LinearMap.comp_apply, coaugmentedMap_reducedInclusion]
    rw [TensorWords.deconcatenation_comp_reducedInclusion_apply,
      TensorWords.deconcatenation_comp_reducedInclusion_apply]
    simp only [map_add, TensorProduct.map_tmul, coaugmentedMap_reducedInclusion,
      coaugmentedMap_one]
    rw [hF.deconcatenation_apply]
    congr 1
    have hcomp : TensorWords.reducedInclusion R N ∘ₗ F =
        coaugmentedMap F ∘ₗ TensorWords.reducedInclusion R M := by
      apply LinearMap.ext
      intro w
      exact (coaugmentedMap_reducedInclusion F w).symm
    have hmap :
        TensorProduct.map (TensorWords.reducedInclusion R N)
            (TensorWords.reducedInclusion R N) ∘ₗ TensorProduct.map F F =
          TensorProduct.map (coaugmentedMap F) (coaugmentedMap F) ∘ₗ
            TensorProduct.map (TensorWords.reducedInclusion R M)
              (TensorWords.reducedInclusion R M) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hcomp]
    exact LinearMap.congr_fun hmap _

/-- The coaugmented map is a coalgebra morphism. -/
noncomputable def coaugmentedCoalgHom
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) : TensorWords R M →ₗc[R] TensorWords R N where
  toLinearMap := coaugmentedMap F
  counit_comp := counit_comp_coaugmentedMap F
  map_comp_comul := by
    simpa only [TensorWords.comul_eq_deconcatenation] using
      (deconcatenation_comp_coaugmentedMap hF).symm

/-- The linear map underlying the coaugmented coalgebra morphism is the extension. -/
@[simp]
theorem coaugmentedCoalgHom_toLinearMap
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) :
    (coaugmentedCoalgHom hF : TensorWords R M →ₗ[R] TensorWords R N) =
      coaugmentedMap F := by
  rw [coaugmentedCoalgHom]
  exact CoalgHom.coe_linearMap_mk _ _

/-- Coaugmenting the identity reduced coalgebra map gives the identity coalgebra morphism. -/
@[simp]
theorem coaugmentedCoalgHom_id :
    coaugmentedCoalgHom (isCoalgHom_id M) =
      CoalgHom.id R (TensorWords R M) := by
  apply CoalgHom.linearMapOfClass_injective
  simp

/-- Coaugmenting a composite of reduced coalgebra maps gives the composite morphism. -/
@[simp]
theorem coaugmentedCoalgHom_comp {P : Type*} [AddCommMonoid P] [Module R P]
    {G : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R P}
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hG : IsCoalgHom R G) (hF : IsCoalgHom R F) :
    coaugmentedCoalgHom (hG.comp hF) =
      (coaugmentedCoalgHom hG).comp (coaugmentedCoalgHom hF) := by
  apply CoalgHom.linearMapOfClass_injective
  simp


end ReducedTensorWords

namespace ReducedTensorWords

universe vR vM vN

variable {R : Type vR} {M : Type vM} {N : Type vN}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A degree-zero reduced coalgebra map extends to a degree-zero map on coaugmented
tensor words. The empty word has degree zero. -/
theorem isHomogeneous_coaugmentedMap
    {G : InternalGrading R M} {H : InternalGrading R N}
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : LinearMap.IsHomogeneous F
      (ReducedTensorWords.gradedPiece G) (ReducedTensorWords.gradedPiece H) 0) :
    LinearMap.IsHomogeneous (coaugmentedMap F)
      (TensorWords.gradedPiece G) (TensorWords.gradedPiece H) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  rw [add_zero]
  refine TensorWords.gradedPiece_induction
    (motive := fun w ↦ coaugmentedMap F w ∈ TensorWords.gradedPiece H D)
    hz ?_ ?_ ?_ ?_
  · intro n 𝒟 x hx hD
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hone : TensorWords.of R M 0 (PiTensorProduct.tprod R x) =
          (1 : TensorWords R M) := by
        have hx0 : x = fun i : Fin 0 ↦ i.elim0 := funext fun i ↦ i.elim0
        rw [hx0]
        exact (TensorWords.one_eq_of_zero (R := R) (M := M)).symm
      have hD0 : D = 0 := by simpa using hD.symm
      rw [hone, coaugmentedMap_one, hD0]
      have hmem := TensorWords.mem_gradedPiece_of_tprod H
        (fun i : Fin 0 ↦ i.elim0) (fun _ ↦ (0 : ℤ)) (by intro i; exact i.elim0)
      simpa [← TensorWords.one_eq_of_zero] using hmem
    · rw [← TensorWords.reducedInclusion_of R M ⟨n, hn⟩
          (PiTensorProduct.tprod R x), coaugmentedMap_reducedInclusion]
      apply TensorWords.mem_gradedPiece_of_reducedInclusion
      have hmem := ReducedTensorWords.mem_gradedPiece_of_tprod G hn x 𝒟 hx
      simpa only [hD, add_zero] using hF.map_mem hmem
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact Submodule.add_mem _ hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

end ReducedTensorWords

end TauCeti
