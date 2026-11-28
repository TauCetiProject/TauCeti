/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Determinant
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Unique

/-!
# The determinant on adelic points of `GL₁`

Functoriality of adelic points along a morphism of affine groups `φ : G → G'` is precomposition
with the coordinate map `φ* : O(G') → O(G)`, `BialgHom.mapDomain`, which is continuous for the
point topologies (`BialgHom.continuous_mapDomain`). For the determinant `det : GL₁ → 𝔾ₘ`, read
through the identifications `GL₁(𝔸_K) ≃ GL (Fin 1) 𝔸_K ≃ 𝔸_Kˣ` and `𝔾ₘ(𝔸_K) ≃ Hom(ℤ, 𝔸_Kˣ)`, the
adelic determinant point map is the identity on the ideles: the `𝔾ₘ` unit of the determinant of a
point is the entry of its one-by-one matrix.
-/

public section

open NumberField TauCeti

namespace TauCeti.Examples.AdelicDeterminant

variable (K : Type*) [Field K] [NumberField K]

/-- The adelic determinant point map of `GL₁` is continuous. -/
example : Continuous (GeneralLinear.determinantPoints K 1 (A := AdeleRing (𝓞 K) K)) :=
  (BialgHom.continuous_mapDomain (GeneralLinear.determinantCoordinateMap K 1).hom).congr fun f ↦ by
    ext x
    rw [GeneralLinear.determinantPoints_apply_apply, BialgHom.mapDomain_apply_apply]

/-- For `GL₁`, the `𝔾ₘ` unit of the adelic determinant of a point is the idele given by the
entry of its one-by-one matrix. -/
example (f : AdelicPoints (𝓞 K) K (GeneralLinear.coordinateHopfAlgebra K 1)) :
    DiagonalizableGroup.pointsMulEquiv (GeneralLinear.determinantPoints K 1 f)
        (Multiplicative.ofAdd (1 : ℤ)) =
      Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv (Fin 1) (AdeleRing (𝓞 K) K)
        (GeneralLinear.pointsMulEquiv 1 f) := by
  rw [GeneralLinear.pointsMulEquiv_determinantPoints]
  ext
  simp [Matrix.det_unique]

/-- Starting from an idele `u`, the adelic `GL₁` point with matrix `(u)` has determinant unit
`u`: under the identifications above, the determinant is the identity on the ideles. -/
example (u : (AdeleRing (𝓞 K) K)ˣ) :
    DiagonalizableGroup.pointsMulEquiv
        (GeneralLinear.determinantPoints K 1 ((GeneralLinear.pointsMulEquiv (R := K) 1).symm
          ((Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv (Fin 1)
            (AdeleRing (𝓞 K) K)).symm u)))
        (Multiplicative.ofAdd (1 : ℤ)) = u := by
  rw [GeneralLinear.pointsMulEquiv_determinantPoints_symm_apply]
  ext
  simp [Matrix.det_unique]

end TauCeti.Examples.AdelicDeterminant
