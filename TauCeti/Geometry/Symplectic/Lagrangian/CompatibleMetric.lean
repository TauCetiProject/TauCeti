/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic

/-!
# Lagrangian subspaces for an orthogonal complex structure

Let `J` be an orthogonal almost complex structure on a real inner product space `V`, with
symplectic form `ω = ⟪J ·, ·⟫` (`TauCeti.AlmostComplexStructure.symplecticForm`). The symplectic
complement of a subspace `W` is the orthogonal complement of its image `J W`, so in finite
dimension `W` is Lagrangian exactly when `Wᗮ = J W`.

## Main declarations

* `TauCeti.AlmostComplexStructure.orthogonal_symplecticForm`: `W^ω = (J W)ᗮ`.
* `TauCeti.AlmostComplexStructure.isLagrangian_symplecticForm_iff_orthogonal_eq`: `W` is
  Lagrangian exactly when `Wᗮ = J W`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.3 (Lagrangian subspaces and compatible complex structures).
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫_ℝ = ⟪v, w⟫_ℝ)
include hJ

/-- For an orthogonal complex structure `J`, the symplectic complement of a subspace `W` for
`ω = ⟪J ·, ·⟫` is the orthogonal complement of its image `J W`. -/
theorem orthogonal_symplecticForm (W : Submodule ℝ V) :
    (J.symplecticForm hJ).orthogonal W = (W.map J.toLinearMap)ᗮ := by
  ext x
  simp [SymplecticForm.mem_orthogonal_iff, Submodule.mem_orthogonal]

/-- For an orthogonal complex structure `J` on a finite-dimensional space, a subspace `W` is
Lagrangian for `ω = ⟪J ·, ·⟫` exactly when its orthogonal complement is its image `J W`. -/
theorem isLagrangian_symplecticForm_iff_orthogonal_eq [FiniteDimensional ℝ V] {W : Submodule ℝ V} :
    (J.symplecticForm hJ).IsLagrangian W ↔ Wᗮ = W.map J.toLinearMap := by
  rw [SymplecticForm.isLagrangian_iff, SymplecticForm.isIsotropic_iff_le,
    SymplecticForm.isCoisotropic_iff_le, and_comm, ← le_antisymm_iff,
    orthogonal_symplecticForm hJ]
  constructor
  · intro h
    rw [← Submodule.orthogonal_orthogonal (W.map J.toLinearMap), h]
  · intro h
    rw [← h, Submodule.orthogonal_orthogonal]

end TauCeti.AlmostComplexStructure
