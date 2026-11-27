/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Unitization.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
public import TauCeti.Analysis.VonNeumannAlgebra.Cyclic
import Mathlib.Algebra.Algebra.Subalgebra.Unitization

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
  let π := τ.unitization.gnsStarAlgHom
  have hrestrict : ⇑(Unitization.starLift.symm π) =
      fun a : A => τ.unitization.gnsNonUnitalStarAlgHom (a : Unitization ℂ A) := by
    funext a
    simp [π, PositiveLinearMap.gnsStarAlgHom_apply]
  have hπ := congrArg StarAlgHom.range (Unitization.starLift.apply_symm_apply π).symm
  rw [Unitization.starLift_range] at hπ
  have hcoe : (π.range : Set _) = Set.range π := by
    rw [StarAlgHom.range_eq_map_top]
    simp
  have hrange : Set.range τ.unitization.gnsStarAlgHom =
      (StarAlgebra.adjoin ℂ (Set.range fun a : A => τ.unitization.gnsNonUnitalStarAlgHom
        (a : Unitization ℂ A)) : Set _) := by
    simpa only [hcoe, NonUnitalStarAlgHom.coe_range, hrestrict] using
      congrArg SetLike.coe hπ
  rw [PositiveLinearMap.gnsVonNeumannAlgebra_def τ.toPositiveLinearMap,
    VonNeumannAlgebra.mapLinearIsometryEquiv_adjoin, ← Set.range_comp,
    PositiveLinearMap.gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom, hrange,
    VonNeumannAlgebra.adjoin_starAlgebraAdjoin]
  simp only [Function.comp_def, gnsEquivUnitization_conjStarAlgEquiv]

/-- The canonical vector of a tracial positive functional is separating for its generated
von Neumann algebra. -/
theorem isSeparating_gnsNonUnitalVector (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    τ.gnsVonNeumannAlgebra.IsSeparating τ.gnsNonUnitalVector := by
  rw [VonNeumannAlgebra.isSeparating_iff_isCyclic_commutant, VonNeumannAlgebra.isCyclic_iff]
  refine (τ.denseRange_gnsRightNonUnitalStarAlgHom_gnsNonUnitalVector hτ).mono ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨_, τ.gnsRightNonUnitalStarAlgHom_mem_commutant hτ b, rfl⟩

end PositiveContinuousLinearMap
