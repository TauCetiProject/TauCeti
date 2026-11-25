/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.RankOne
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# Checks for the rank-one Grassmannian of `R²`

For `M = R²` with basis `e₀, e₁`, the rank-one Grassmannian `G(1, R²)` over `Spec R` is covered by
the two charts at `e₀` and `e₁`. Inside the chart at `e₀` the chart at `e₁` is the complement of
the origin `u_{e₀}(e₁) = 0`, and on the overlap the coordinate `u_{e₁}(e₀)` of the chart at `e₁`
is the inverse of `u_{e₀}(e₁)`: the charts are glued along `t ↦ t⁻¹`, not along the identity
(which would give the affine line with a doubled origin). The rank-one identification makes
`G(1, R²)` the projective line `Proj (Sym R²)` over `Spec R`.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra

namespace TauCeti.Grassmannian.RankOne

open Module.Grassmannian Module.Grassmannian.ChartAlgebra

variable (R : Type) [CommRing R]

/-- The basis vector `eᵢ` of `R²`. -/
abbrev e (i : Fin 2) : Fin 2 → R := Pi.single i 1

/-- **The two standard charts cover `G(1, R²)`.** -/
theorem chart_e₀_sup_chart_e₁ :
    (chartι R (fun _ : Fin 1 ↦ e R 0)).opensRange ⊔
      (chartι R (fun _ : Fin 1 ↦ e R 1)).opensRange = ⊤ := by
  have h (i : Fin 2) : SymmetricAlgebra.ι R (Fin 2 → R) (e R i) = projectiveLine.coord R i := by
    fin_cases i <;> simp [projectiveLine.ι_eq_smul_coord_add_smul_coord R 0]
  rw [← toProj_preimage_basicOpen, ← toProj_preimage_basicOpen, ← Scheme.Hom.preimage_sup, h, h,
    projectiveLine.basicOpen_coord_sup_eq_top, Scheme.Hom.preimage_top]

/-- **The overlap is the complement of the origin.** Inside the chart of `G(1, R²)` at `e₀`, the
chart at `e₁` is the basic open set of the coordinate `u_{e₀}(e₁)`. -/
example :
    chartι R (fun _ : Fin 1 ↦ e R 0) ⁻¹ᵁ (chartι R (fun _ : Fin 1 ↦ e R 1)).opensRange =
      PrimeSpectrum.basicOpen (universalLinearMap R (fun _ : Fin 1 ↦ e R 0) (e R 1) 0) := by
  rw [chartι_preimage_opensRange_chartι, transitionDet_rankOne]

/-- **The charts are glued along `t ↦ t⁻¹`.** On the overlap of the charts at `e₀` and `e₁`, the
coordinate `u_{e₀}(e₁)` of the chart at `e₀` times the coordinate `u_{e₁}(e₀)` of the chart at
`e₁`, carried along the transition isomorphism, is `1`. -/
theorem coordinate_mul_transition_coordinate :
    algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ e R 0))
        (OverlapAlgebra R (fun _ : Fin 1 ↦ e R 0) (fun _ : Fin 1 ↦ e R 1))
        (universalLinearMap R (fun _ : Fin 1 ↦ e R 0) (e R 1) 0) *
      transitionAlgEquiv R (fun _ : Fin 1 ↦ e R 0) (fun _ : Fin 1 ↦ e R 1)
        (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ e R 1))
          (OverlapAlgebra R (fun _ : Fin 1 ↦ e R 1) (fun _ : Fin 1 ↦ e R 0))
          (universalLinearMap R (fun _ : Fin 1 ↦ e R 1) (e R 0) 0)) = 1 := by
  rw [← algebraMap_universalLinearMap_eq_mul_transitionAlgEquiv, universalLinearMap_self_zero,
    map_one]

/-- **`G(1, R²)` is the projective line** `Proj (Sym R²)` over `Spec R`. -/
noncomputable example : scheme R (Fin 2 → R) 1 ≅ Proj (homogeneousSubmodule R (Fin 2 → R)) :=
  toProjIso R

example : (toProjIso R).hom ≫ projToSpec R (Fin 2 → R) = toSpec R (Fin 2 → R) 1 :=
  toProjIso_hom_projToSpec R

end TauCeti.Grassmannian.RankOne
