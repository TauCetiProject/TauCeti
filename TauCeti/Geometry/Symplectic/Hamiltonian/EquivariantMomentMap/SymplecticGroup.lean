/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.SymplecticGroup
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Linear
public import TauCeti.Geometry.Symplectic.Matrix

/-!
# The moment map of the linear symplectic group

The real symplectic group `Sp(2n, ℝ) = Matrix.symplecticGroup (Fin n) ℝ` is a Lie group
(`TauCeti.Lie.symplecticGroup_lieGroup`), and it acts linearly on `V = Fin n ⊕ Fin n → ℝ` by
`g • v = g *ᵥ v`, preserving the standard symplectic form `ω(u, w) = u ⬝ᵥ J w`
(`TauCeti.stdSumSymplecticForm`). This file computes the moment map of this action and proves that
it is coadjoint-equivariant at group level.

* **Smooth action.** The action is smooth, as a bilinear map composed with the smooth inclusion
  `ι : Sp(2n, ℝ) → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ`
  (`TauCeti.Lie.contMDiff_val_symplecticGroup`).
* **Fundamental vector fields.** The fundamental vector field of `ξ` in the Lie algebra is the
  linear vector field `v ↦ A v` of the matrix `A = dι(ξ)`
  (`TauCeti.fundamentalLinearMap_symplecticGroup`), and `A` lies in the symplectic Lie algebra
  `sp (Fin n) ℝ` (`TauCeti.mvfderiv_val_symplecticGroup_mem_sp`).
* **The moment map.** The quadratic moment map of the action
  (`TauCeti.SymplecticForm.linearActionMomentMap`) is

  `μ(v)(ξ) = ½ ω(A v, v)`, `A = dι(ξ)`

  (`TauCeti.linearActionMomentMap_symplecticGroup_apply`): the moment map `μ_A(v) = ½ ω(A v, v)`
  of the symplectic Lie algebra, read on the Lie algebra of the group. It is a
  coadjoint-equivariant group-level moment map
  (`TauCeti.isEquivariantMomentMap_linearActionMomentMap_symplecticGroup`).
* **Equivariance in matrices.** Under `dι` the adjoint action is conjugation,
  `dι(Ad_g ξ) = g A g⁻¹` (`TauCeti.Lie.mvfderiv_val_symplecticGroup_adjointContinuousLinearMap`), so
  coadjoint equivariance `μ(g v) = Ad*_g μ(v)` reads

  `μ(g v)(A) = μ(v)(g⁻¹ A g)`

  (`TauCeti.linearActionMomentMap_symplecticGroup_smul_apply`), which also follows directly from
  `ω(g x, g y) = ω(x, y)`.

## Main results

* `TauCeti.isEquivariantMomentMap_linearActionMomentMap_symplecticGroup`: the moment map of the
  linear action of `Sp(2n, ℝ)` on `(Fin n ⊕ Fin n → ℝ, ω)` is coadjoint-equivariant.
* `TauCeti.linearActionMomentMap_symplecticGroup_apply`,
  `TauCeti.linearActionMomentMap_symplecticGroup_smul_apply`: the formulas `½ ω(A v, v)` and
  `μ(g v)(A) = μ(v)(g⁻¹ A g)`.

## References

* E. Meinrenken, *Symplectic Geometry*, lecture notes, University of Toronto, 2000,
  Proposition 7.20 (the moment map of the linear symplectic group).
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the moment map of a linear symplectic action).
-/

public section

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator Manifold ContDiff

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti

variable {n : ℕ}

/-- **The fundamental vector fields of the symplectic group are linear.** The fundamental vector
field of `ξ` in the Lie algebra of `Sp(2n, ℝ)`, acting on `Fin n ⊕ Fin n → ℝ`, is `v ↦ A v` for
the matrix `A = dι(ξ)`, the differential at `1` of the inclusion `ι` into the matrices. -/
theorem fundamentalLinearMap_symplecticGroup
    (ξ : GroupLieAlgebra 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ) (symplecticGroup (Fin n) ℝ)) :
    fundamentalLinearMap 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ) (symplecticGroup (Fin n) ℝ)
        (Fin n ⊕ Fin n → ℝ) ξ =
      toLin' (mvfderiv 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ)
        (fun g : symplecticGroup (Fin n) ℝ ↦ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        1 ξ) := by
  refine LinearMap.ext fun v ↦ ?_
  -- The orbit map of `v` is the inclusion followed by the linear map `A ↦ A *ᵥ v`.
  let L : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ →L[ℝ] Fin n ⊕ Fin n → ℝ :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip v)
  have horbit : (fun g : symplecticGroup (Fin n) ℝ ↦ g • v) =
      L ∘ fun g : symplecticGroup (Fin n) ℝ ↦
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
    funext g
    simp [L, Submonoid.smul_def]
  rw [fundamentalLinearMap_apply, horbit, L.mvfderiv_comp_apply
    ((Lie.contMDiff_val_symplecticGroup (Fin n) ℝ).mdifferentiableAt (by simp)), toLin'_apply]
  -- `L A` is `A *ᵥ v` by definition; `simp` does not see through the tangent-space type of `A`.
  rfl

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The differential at `1` of the inclusion of `Sp(2n, ℝ)` into the matrices takes values in the
symplectic Lie algebra `sp (Fin n) ℝ`. -/
theorem mvfderiv_val_symplecticGroup_mem_sp
    (ξ : GroupLieAlgebra 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ) (symplecticGroup (Fin n) ℝ)) :
    mvfderiv 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ)
        (fun g : symplecticGroup (Fin n) ℝ ↦ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        1 ξ ∈ LieAlgebra.Symplectic.sp (Fin n) ℝ := by
  rw [← toLin'_mem_skewAdjointLieSubalgebra_stdSymplecticBilinForm_iff,
    ← fundamentalLinearMap_symplecticGroup, ← stdSumSymplecticForm_toBilinForm]
  exact (stdSumSymplecticForm n).fundamentalLinearMap_mem_skewAdjointLieSubalgebra
    stdSumSymplecticForm_smul_smul ξ

/-- **The moment map of the linear symplectic group.** For the linear action of `Sp(2n, ℝ)` on
`(Fin n ⊕ Fin n → ℝ, ω)`, the quadratic moment map is `μ(v)(ξ) = ½ ω(A v, v)` for the matrix
`A = dι(ξ) ∈ sp (Fin n) ℝ`. -/
theorem linearActionMomentMap_symplecticGroup_apply (v : Fin n ⊕ Fin n → ℝ)
    (ξ : GroupLieAlgebra 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ) (symplecticGroup (Fin n) ℝ)) :
    (stdSumSymplecticForm n).linearActionMomentMap 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ)
        (symplecticGroup (Fin n) ℝ) v ξ =
      stdSumSymplecticForm n (mvfderiv 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ)
        (fun g : symplecticGroup (Fin n) ℝ ↦ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        1 ξ *ᵥ v) v / 2 := by
  rw [SymplecticForm.linearActionMomentMap_apply, fundamentalLinearMap_symplecticGroup,
    toLin'_apply]

variable (n) in
/-- **The moment map of the linear symplectic group is equivariant.** The quadratic moment map
`μ(v)(ξ) = ½ ω(dι(ξ) v, v)` of the linear action of `Sp(2n, ℝ)` on `(Fin n ⊕ Fin n → ℝ, ω)` is a
coadjoint-equivariant group-level moment map: `μ(g v) = Ad*_g μ(v)`. -/
theorem isEquivariantMomentMap_linearActionMomentMap_symplecticGroup :
    (stdSumSymplecticForm n).constSmooth.IsEquivariantMomentMap
      ((stdSumSymplecticForm n).linearActionMomentMap 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ)
        (symplecticGroup (Fin n) ℝ)) :=
  (stdSumSymplecticForm n).isEquivariantMomentMap_linearActionMomentMap
    stdSumSymplecticForm_smul_smul

/-- **Coadjoint equivariance in matrices.** For the linear action of `Sp(2n, ℝ)` on
`(Fin n ⊕ Fin n → ℝ, ω)`, the moment map satisfies `μ(g v)(A) = μ(v)(g⁻¹ A g)` for `A = dι(ξ)`:
`½ ω(A g v, g v) = ½ ω(g⁻¹ A g v, v)`, because `g` preserves `ω`. -/
theorem linearActionMomentMap_symplecticGroup_smul_apply (g : symplecticGroup (Fin n) ℝ)
    (v : Fin n ⊕ Fin n → ℝ)
    (ξ : GroupLieAlgebra 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ) (symplecticGroup (Fin n) ℝ)) :
    (stdSumSymplecticForm n).linearActionMomentMap 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ)
        (symplecticGroup (Fin n) ℝ) (g • v) ξ =
      stdSumSymplecticForm n
        ((((g⁻¹ : symplecticGroup (Fin n) ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) *
          mvfderiv 𝓘(ℝ, Lie.SymplecticGroupModel (Fin n) ℝ)
            (fun g : symplecticGroup (Fin n) ℝ ↦ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
            1 ξ *
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) *ᵥ v) v / 2 := by
  -- Apply `g⁻¹`, which preserves `ω`, to both arguments of `ω(A (g v), g v)`.
  rw [linearActionMomentMap_symplecticGroup_apply, ← stdSumSymplecticForm_smul_smul g⁻¹,
    inv_smul_smul]
  simp only [Submonoid.smul_def, smul_eq_mulVec, mulVec_mulVec, Matrix.mul_assoc]

end TauCeti
