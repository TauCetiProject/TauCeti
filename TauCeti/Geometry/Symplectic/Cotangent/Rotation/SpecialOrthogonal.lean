/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Unitary.SpecialOrthogonal
public import TauCeti.Geometry.Symplectic.Cotangent.Rotation
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The moment map of the cotangent-lifted special orthogonal group

The special orthogonal group `SO(n) = Matrix.specialOrthogonalGroup n ℝ` is a Lie group
(`TauCeti.Geometry.Manifold.Instances.Unitary.Special`) acting smoothly on `ℝⁿ = n → ℝ` by matrix
multiplication, `g • v = g *ᵥ v`. Its cotangent lift to the manifold `T*ℝⁿ` has the group-level
moment map `⟨μ(q, p), ξ⟩ = p(ξ_V(q))` (`TauCeti.CotangentBundle.momentMap`), which is
coadjoint-equivariant (`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap`). This file
identifies it with the rotation moment map `A ↦ p(A q)` of `so(n)` (`TauCeti.rotationMomentMap`):

`μ(q, p) = rotationMomentMap (q, p) ∘ Ψ`

in the global coordinates `T*ℝⁿ ≃ ℝⁿ × (ℝⁿ)*`, where `Ψ` is the identification of the Lie algebra
of `SO(n)` with `so(n)` by the differential of the inclusion into the matrices
(`TauCeti.specialOrthogonalLieAlgebraEquiv`). Since the rotation moment map is the restriction of
the moment map `TauCeti.cotangentMomentMap` of `gl(n)` along `so(n) → gl(n)`
(`TauCeti.rotationMomentMap_eq_comp`), so is `μ`. The proof computes the fundamental vector fields:
the orbit map `g ↦ g *ᵥ v` is the inclusion of `SO(n)` followed by the linear map `A ↦ A *ᵥ v`, so
`ξ_V(v) = Ψ(ξ) *ᵥ v`.

In dimension three, through the hat map `u ↦ (v ↦ u ⨯₃ v)` (`TauCeti.soThreeEquiv`), the moment
map is the angular momentum: `⟨μ(q, p), ξ⟩ = u ⬝ᵥ (q ⨯₃ p)` when `Ψ(ξ) = û`
(`TauCeti.cotangentAngularMomentum`). The same statements for the orthogonal group `O(V)` of a
Euclidean space are `TauCeti.CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp` and
`TauCeti.CotangentBundle.momentMap_unitary_apply_eq_inner_angularMomentum`. Read in the dual of
the Lie algebra of `SO(3)`, identified with `ℝ³` by `TauCeti.specialOrthogonalThreeDualEquiv`,
this says `μ(q, p) = ν_(q ⨯₃ p)`. In the coordinates `T*ℝⁿ ≃ ℝⁿ × (ℝⁿ)*` a rotation `g` acts by
`(q, p) ↦ (g q, p ∘ g⁻¹)`, so in dimension three the angular momentum is equivariant:
`(g q) ⨯₃ (g p) = g (q ⨯₃ p)`.

## Main results

* `TauCeti.CotangentBundle.momentMap_specialOrthogonalGroup_eq_rotationMomentMap_comp`: the
  moment map of the cotangent-lifted action of `SO(n)` on `T*ℝⁿ` is the rotation moment map.
* `momentMap_specialOrthogonalGroup_apply_eq_dotProduct_cotangentAngularMomentum`, in the
  namespace `TauCeti.CotangentBundle`: for `SO(3)` the moment map is the angular momentum
  `q ⨯₃ p`; `TauCeti.CotangentBundle.momentMap_specialOrthogonalGroup_eq` is the same statement
  in the dual of the Lie algebra, `μ(q, p) = ν_(q ⨯₃ p)`.
* `TauCeti.CotangentBundle.fst_modelSpaceDiffeomorph_smul`,
  `TauCeti.CotangentBundle.snd_modelSpaceDiffeomorph_smul_apply`: the cotangent-lifted action of
  `SO(n)` in coordinates.
* `TauCeti.CotangentBundle.cotangentAngularMomentum_smul`: the angular momentum is equivariant.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 11.4 and 12.1 (the angular momentum as the momentum
  map of cotangent-lifted rotations).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.4.
-/

public section

noncomputable section

open LieAlgebra.Orthogonal Manifold
open scoped Matrix Manifold Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal
  LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace CotangentBundle

/-- **The moment map of the cotangent-lifted action of `SO(n)` is the rotation moment map.** The
special orthogonal group `SO(n)` acts on `ℝⁿ = n → ℝ` by matrix multiplication. The moment map
`⟨μ(q, p), ξ⟩ = p(ξ_V(q))` of its cotangent lift to `T*ℝⁿ` is, in the global coordinates
`T*ℝⁿ ≃ ℝⁿ × (ℝⁿ)*`, the rotation moment map `A ↦ p(A q)` (`TauCeti.rotationMomentMap`), read
through the identification of the Lie algebra of `SO(n)` with `so(n)`
(`TauCeti.specialOrthogonalLieAlgebraEquiv`). In particular it is the restriction of the moment
map `TauCeti.cotangentMomentMap` of `gl(n)` along `so(n) → gl(n)`
(`TauCeti.rotationMomentMap_eq_comp`). -/
theorem momentMap_specialOrthogonalGroup_eq_rotationMomentMap_comp
    (z : CotangentBundle 𝓘(ℝ, n → ℝ) (n → ℝ)) :
    momentMap (Matrix.specialUnitaryGroup.model n ℝ)
        (Matrix.specialOrthogonalGroup n ℝ) z =
      (rotationMomentMap n (modelSpaceDiffeomorph (n → ℝ) z)).comp
        (specialOrthogonalLieAlgebraEquiv n).toLinearMap := by
  refine momentMap_eq_rotationMomentMap_comp (fun ξ ↦ LinearMap.ext fun v ↦ ?_) z
  -- The orbit map of `v` is the inclusion of `SO(n)` followed by the linear map `A ↦ A *ᵥ v`.
  let L : Matrix n n ℝ →L[ℝ] (n → ℝ) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip v)
  have horbit : (fun g : Matrix.specialOrthogonalGroup n ℝ ↦ g • v) =
      L ∘ (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) := by
    funext g
    simp [L, Submonoid.smul_def, Matrix.mulVecBilin_apply]
  have hval : MDifferentiableAt (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ)
      (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 :=
    Matrix.specialUnitaryGroup.contMDiff_val.mdifferentiableAt (by simp)
  rw [fundamentalLinearMap_apply, horbit,
    mvfderiv_comp_apply_of_differentiableAt L.differentiableAt hval, L.fderiv]
  simp only [L, LinearMap.coe_toContinuousLinearMap', LieModule.toEnd_apply_apply,
    LieSubalgebra.coe_bracket_of_module]
  rw [LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, coe_specialOrthogonalLieAlgebraEquiv_apply,
    mvfderiv_apply_eq_mfderiv_apply]
  -- Both sides are `X *ᵥ v` for the differential `X` of the inclusion, a vector of the tangent
  -- space of the matrices at `1`, on which the matrix lemmas do not fire syntactically.
  rfl

/-- **The moment map of the cotangent-lifted action of `SO(3)` is the angular momentum.** For the
element `ξ` of the Lie algebra of `SO(3)` whose infinitesimal rotation is `v ↦ u ⨯₃ v`, that is,
with `ξ` corresponding to `û` under `TauCeti.specialOrthogonalLieAlgebraEquiv` and the hat map
`TauCeti.soThreeEquiv`, the moment map of the cotangent lift to `T*ℝ³` is
`⟨μ(q, p), ξ⟩ = u ⬝ᵥ (q ⨯₃ p)` (`TauCeti.cotangentAngularMomentum`). -/
theorem momentMap_specialOrthogonalGroup_apply_eq_dotProduct_cotangentAngularMomentum
    (z : CotangentBundle 𝓘(ℝ, Fin 3 → ℝ) (Fin 3 → ℝ))
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model (Fin 3) ℝ)
      (Matrix.specialOrthogonalGroup (Fin 3) ℝ)) :
    momentMap (Matrix.specialUnitaryGroup.model (Fin 3) ℝ)
        (Matrix.specialOrthogonalGroup (Fin 3) ℝ) z ξ =
      (soThreeEquiv ℝ).symm (specialOrthogonalLieAlgebraEquiv (Fin 3) ξ) ⬝ᵥ
        cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) := by
  rw [momentMap_specialOrthogonalGroup_eq_rotationMomentMap_comp, LinearMap.comp_apply,
    LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, ← rotationMomentMap_soThreeEquiv,
    LinearEquiv.apply_symm_apply]

/-! ### The action in coordinates -/

section Coordinates

open _root_.Matrix

/-- The differential of the rotation `v ↦ g v` of `ℝⁿ` is `g`. -/
private theorem mfderiv_smul_specialOrthogonalGroup (g : Matrix.specialOrthogonalGroup n ℝ)
    (x w : n → ℝ) :
    mfderiv 𝓘(ℝ, n → ℝ) 𝓘(ℝ, n → ℝ) (fun v : n → ℝ ↦ g • v) x w = g • w := by
  have h : (fun v : n → ℝ ↦ g • v) =
      ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' (g : Matrix n n ℝ))) := by
    funext v
    simp [Submonoid.smul_def]
  rw [h, (LinearMap.toContinuousLinearMap
    (Matrix.toLin' (g : Matrix n n ℝ))).hasMFDerivAt.mfderiv, Submonoid.smul_def,
    smul_eq_mulVec]
  -- The map is applied to `w` in the tangent space `TangentSpace 𝓘(ℝ, ℝⁿ) x`, which is `ℝⁿ` by
  -- definition but blocks rewriting with the matrix lemmas; there `toLin' g w = g *ᵥ w`.
  rfl

/-- In the coordinates `T*ℝⁿ ≃ ℝⁿ × (ℝⁿ)*`, the rotation `g` moves the base point `q` to `g q`. -/
theorem fst_modelSpaceDiffeomorph_smul (g : Matrix.specialOrthogonalGroup n ℝ)
    (z : CotangentBundle 𝓘(ℝ, n → ℝ) (n → ℝ)) :
    (modelSpaceDiffeomorph (n → ℝ) (g • z)).1 =
      (g : Matrix n n ℝ) *ᵥ (modelSpaceDiffeomorph (n → ℝ) z).1 := by
  rw [modelSpaceDiffeomorph_apply, modelSpaceDiffeomorph_apply, proj_smul, Submonoid.smul_def,
    smul_eq_mulVec]

/-- In the coordinates `T*ℝⁿ ≃ ℝⁿ × (ℝⁿ)*`, the rotation `g` moves the covector `p` to
`p ∘ g⁻¹`. -/
theorem snd_modelSpaceDiffeomorph_smul_apply (g : Matrix.specialOrthogonalGroup n ℝ)
    (z : CotangentBundle 𝓘(ℝ, n → ℝ) (n → ℝ)) (w : n → ℝ) :
    (modelSpaceDiffeomorph (n → ℝ) (g • z)).2 w =
      (modelSpaceDiffeomorph (n → ℝ) z).2
        (((g⁻¹ : Matrix.specialOrthogonalGroup n ℝ) : Matrix n n ℝ) *ᵥ w) := by
  have h := smul_snd_apply g z w
  rw [mfderiv_smul_specialOrthogonalGroup, Submonoid.smul_def, smul_eq_mulVec] at h
  rw [modelSpaceDiffeomorph_apply, modelSpaceDiffeomorph_apply]
  exact h

/-! ### The moment map and the action in coordinates for `SO(3)` -/

/-- The rotation group `SO(3)`. -/
local notation "SO₃" => Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- The cotangent bundle `T*ℝ³`. -/
local notation "T*ℝ³" => CotangentBundle 𝓘(ℝ, Fin 3 → ℝ) (Fin 3 → ℝ)

/-- **The moment map of the cotangent-lifted rotations is the angular momentum**, read in the dual
of the Lie algebra of `SO(3)`: `μ(q, p) = ν_(q ⨯₃ p)`. -/
theorem momentMap_specialOrthogonalGroup_eq (z : T*ℝ³) :
    momentMap (Matrix.specialUnitaryGroup.model (Fin 3) ℝ) SO₃ z =
      specialOrthogonalThreeDualEquiv
        (cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z)) := by
  ext ξ
  rw [momentMap_specialOrthogonalGroup_apply_eq_dotProduct_cotangentAngularMomentum,
    specialOrthogonalThreeDualEquiv_apply, dotProduct_comm]

/-- **The angular momentum is equivariant**: rotating a covector `p` at `q` by `g ∈ SO(3)` rotates
its angular momentum, `(g q) ⨯₃ (g p) = g (q ⨯₃ p)`. -/
theorem cotangentAngularMomentum_smul (g : SO₃) (z : T*ℝ³) :
    cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) (g • z)) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) := by
  rw [cotangentAngularMomentum_apply, cotangentAngularMomentum_apply]
  -- The covector `g • p` is `p ∘ g⁻¹`, whose vector is `g` applied to that of `p`, as `g⁻¹ = gᵀ`.
  have hsnd : (fun i ↦ (modelSpaceDiffeomorph (Fin 3 → ℝ) (g • z)).2 (Pi.single i 1)) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        fun i ↦ (modelSpaceDiffeomorph (Fin 3 → ℝ) z).2 (Pi.single i 1) := by
    funext i
    rw [snd_modelSpaceDiffeomorph_smul_apply, coe_specialOrthogonalGroup_inv, mulVec_single_one,
      col_transpose]
    conv_lhs => rw [pi_eq_sum_univ' ((g : Matrix (Fin 3) (Fin 3) ℝ).row i)]
    simp only [mulVec, dotProduct, row_apply]
    exact (map_sum (modelSpaceDiffeomorph (Fin 3 → ℝ) z).2 _ _).trans
      (Finset.sum_congr rfl fun j _ ↦ map_smul _ _ _)
  rw [hsnd, fst_modelSpaceDiffeomorph_smul,
    mulVec_cross_mulVec_of_mem_specialOrthogonalGroup g.property]

end Coordinates

end CotangentBundle

end TauCeti
