/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Unitization.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
public import TauCeti.Analysis.VonNeumannAlgebra.Cyclic

/-!
# GNS von Neumann algebras under unitization

Conjugation by the unitization GNS unitary identifies the von Neumann algebras generated
by the original representation and the representation of the unitization. The canonical
vector of a tracial positive functional is separating because its right orbit is dense
and the right action lies in the commutant.
-/

public section

open scoped ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →P[ℂ] ℂ)

/-- Unitary transport identifies the von Neumann algebras generated before and after
unitization. -/
@[simp]
theorem mapLinearIsometryEquiv_gnsEquivUnitization :
    VonNeumannAlgebra.mapLinearIsometryEquiv τ.gnsEquivUnitization τ.gnsVonNeumannAlgebra =
      τ.unitization.gnsVonNeumannAlgebra := by
  rw [PositiveLinearMap.gnsVonNeumannAlgebra_def τ.toPositiveLinearMap,
    VonNeumannAlgebra.mapLinearIsometryEquiv_adjoin, ← Set.range_comp]
  simp only [Function.comp_def, gnsEquivUnitization_conjStarAlgEquiv]
  rw [PositiveLinearMap.gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom,
    VonNeumannAlgebra.adjoin_range_unitization]
  exact congrArg (fun f : A → _ => VonNeumannAlgebra.adjoin (Set.range f))
    (funext fun a => (PositiveLinearMap.gnsStarAlgHom_apply _ (a : Unitization ℂ A)).symm)

/-- The canonical vector of a tracial positive functional is separating for its generated
von Neumann algebra. -/
theorem isSeparating_gnsNonUnitalVector (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    τ.gnsVonNeumannAlgebra.IsSeparating τ.gnsNonUnitalVector := by
  rw [VonNeumannAlgebra.isSeparating_iff_isCyclic_commutant, VonNeumannAlgebra.isCyclic_iff]
  refine (τ.denseRange_gnsRightNonUnitalStarAlgHom_gnsNonUnitalVector hτ).mono ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨_, τ.gnsRightNonUnitalStarAlgHom_mem_commutant hτ b, rfl⟩

end PositiveContinuousLinearMap
