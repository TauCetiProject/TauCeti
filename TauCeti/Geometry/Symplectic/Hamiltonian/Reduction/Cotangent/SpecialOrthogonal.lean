/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
public import TauCeti.Geometry.Symplectic.Cotangent.Rotation.SpecialOrthogonal
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.LinearAlgebra.Matrix.CrossProduct
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# Reduction of `T*ℝ³` by the rotations at a nonzero angular momentum

The rotation group `SO(3)` acts on `ℝ³` and, by the cotangent lift, on `T*ℝ³`, with the
coadjoint-equivariant moment map `μ(q, p) = ν_(q ⨯₃ p)`, the angular momentum read in the dual of
the Lie algebra of `SO(3)` (`TauCeti.CotangentBundle.momentMap_specialOrthogonalGroup_eq`). This
file works out the Marsden–Weinstein–Meyer reduction of `T*ℝ³` at a nonzero value `c = ν_ℓ`,
`ℓ ≠ 0`: a value that is not fixed by the coadjoint action, so that the stabilizer `G_c` is a
proper subgroup and the level is not coisotropic.

* **The stabilizer.** Since the angular momentum is equivariant, `q ⨯₃ p ↦ g (q ⨯₃ p)`
  (`TauCeti.CotangentBundle.cotangentAngularMomentum_smul`), the stabilizer of `c = μ(q, p)` is
  the group of rotations about the axis `q ⨯₃ p`
  (`mem_stabilizer_coadjointRepresentation_momentMap_specialOrthogonalGroup_iff`), a copy of
  `SO(2)` when `q ⨯₃ p ≠ 0`. Its Lie algebra `𝔤_c` is the line of infinitesimal rotations about
  `ℓ` (`TauCeti.finrank_lieAnnihilator_specialOrthogonalThreeDualEquiv`).
* **Freeness and regularity.** A rotation fixing `(q, p)` with `q ⨯₃ p ≠ 0` fixes `q`, `q ⨯₃ p`
  and their cross product, a basis of `ℝ³`, so it is the identity
  (`stabilizer_specialOrthogonalGroup_eq_bot`). Hence every nonzero value is a regular value
  (`differential_surjective_momentMap_specialOrthogonalGroup`), and `G_c` acts freely on the level
  `Z = μ⁻¹(c)` (`isCancelSMul_levelSubMulAction_specialOrthogonalGroup`); `SO(3)` is compact, so it
  acts properly.
* **The level.** The tangent space `T_z Z = ker dμ_z` of the level has dimension `6 - 3 = 3`
  (`finrank_ker_differential_momentMap_specialOrthogonalGroup`), and so does its symplectic
  complement `(T_z Z)^ω = 𝔤 · z`, the orbit tangent space
  (`finrank_orbitTangent_specialOrthogonalGroup`). The null directions `T_z Z ∩ (T_z Z)^ω` of the
  form on the level are the line `𝔤_c · z`
  (`finrank_ker_differential_inf_orthogonal_momentMap_specialOrthogonalGroup`). Since `c` is not
  coadjoint-fixed, `dμ_z(ξ_M) = ⁅ξ, c⁆ ≠ 0` for `ξ` not parallel to `ℓ`, so `(T_z Z)^ω ⊄ T_z Z`:
  **the level is not coisotropic**
  (`not_isCoisotropic_ker_differential_momentMap_specialOrthogonalGroup`).
* **The reduced space.** The reduced space `Z / G_c` of the Marsden–Weinstein–Meyer theorem is
  modelled on a space of dimension `dim T*ℝ³ - dim 𝔰𝔬(3) - dim 𝔤_c = 6 - 3 - 1 = 2`
  (`finrank_quotientModelSpace_specialOrthogonalGroup`).

All declarations are in the namespace `TauCeti.CotangentBundle`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 11.4 and 12.1 (the angular momentum as the momentum
  map of cotangent-lifted rotations).
* E. Meinrenken, *Symplectic geometry*, lecture notes, University of Toronto, Theorem 8.3 and
  Remark 8.4 (reduction at values that are not coadjoint-fixed).
-/

public section

noncomputable section

open Module Matrix
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal
  LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti

/-- The rotation group `SO(3)`. -/
local notation "SO₃" => Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- The model of the rotation group `SO(3)`. -/
local notation "I₃" => Matrix.specialUnitaryGroup.model (Fin 3) ℝ

/-- The Lie algebra of the rotation group `SO(3)`. -/
local notation "𝔰𝔬₃" => GroupLieAlgebra I₃ SO₃

namespace CotangentBundle

/-- The cotangent bundle `T*ℝ³`. -/
local notation "T*ℝ³" => CotangentBundle 𝓘(ℝ, Fin 3 → ℝ) (Fin 3 → ℝ)

/-! ### The coadjoint stabilizers and the free points -/

/-- **The stabilizer `G_c` of a value `c = μ(q, p)` is the group of rotations about the axis
`q ⨯₃ p`**: an element `g` of `SO(3)` fixes `c` under the coadjoint action exactly when
`g (q ⨯₃ p) = q ⨯₃ p`. For `q ⨯₃ p ≠ 0` it is a circle, a copy of `SO(2)`. -/
theorem mem_stabilizer_coadjointRepresentation_momentMap_specialOrthogonalGroup_iff {g : SO₃}
    {z : T*ℝ³} :
    g ∈ (Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer (momentMap I₃ SO₃ z) ↔
      (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
          cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) =
        cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) := by
  rw [Representation.mem_stabilizer, ← momentMap_smul, momentMap_specialOrthogonalGroup_eq,
    momentMap_specialOrthogonalGroup_eq, specialOrthogonalThreeDualEquiv.injective.eq_iff,
    cotangentAngularMomentum_smul]

/-- **The rotations act freely at nonzero angular momentum**: a rotation fixing a covector `p` at
`q` with `q ⨯₃ p ≠ 0` fixes `q`, `q ⨯₃ p` and their cross product, a basis of `ℝ³`, so it is the
identity. -/
theorem stabilizer_specialOrthogonalGroup_eq_bot {z : T*ℝ³}
    (hz : cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) ≠ 0) :
    MulAction.stabilizer SO₃ z = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ ?_
  have hgz : g • z = z := MulAction.mem_stabilizer_iff.1 hg
  have hgq : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (modelSpaceDiffeomorph (Fin 3 → ℝ) z).1 =
      (modelSpaceDiffeomorph (Fin 3 → ℝ) z).1 := by
    rw [← fst_modelSpaceDiffeomorph_smul, hgz]
  have hgℓ : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
      cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) =
        cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) := by
    rw [← cotangentAngularMomentum_smul, hgz]
  have hqℓ : (modelSpaceDiffeomorph (Fin 3 → ℝ) z).1 ⬝ᵥ
      cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) = 0 := by
    rw [cotangentAngularMomentum_apply, dot_self_cross]
  have hq0 : (modelSpaceDiffeomorph (Fin 3 → ℝ) z).1 ≠ 0 := fun h ↦ hz (by
    rw [cotangentAngularMomentum_apply, h, map_zero, LinearMap.zero_apply])
  generalize (modelSpaceDiffeomorph (Fin 3 → ℝ) z).1 = q at hgq hqℓ hq0
  generalize cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) = ℓ at hz hgℓ hqℓ
  -- `g` fixes the rows of the matrix `B` with rows `q`, `ℓ` and `q ⨯₃ ℓ`, so `B gᵀ = B`.
  have hgqℓ : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (q ⨯₃ ℓ) = q ⨯₃ ℓ := by
    rw [← mulVec_cross_mulVec_of_mem_specialOrthogonalGroup g.property, hgq, hgℓ]
  let B : Matrix (Fin 3) (Fin 3) ℝ := ![q, ℓ, q ⨯₃ ℓ]
  have hB : B * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = B * 1 := by
    rw [mul_one]
    ext i j
    have hrow : (B * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) i j =
        ((g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ B i) j := by
      simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
    rw [hrow]
    fin_cases i
    · exact congrFun hgq j
    · exact congrFun hgℓ j
    · exact congrFun hgqℓ j
  -- Since `q ⊥ ℓ`, the determinant of `B` is the triple product `|q|² |ℓ|² ≠ 0`.
  have hdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero, ← triple_product_eq_det, cross_cross_eq_smul_sub_smul',
      dotProduct_sub, dotProduct_smul, dotProduct_smul, hqℓ, smul_zero, sub_zero, smul_eq_mul]
    exact mul_ne_zero (mt dotProduct_self_eq_zero.1 hz) (mt dotProduct_self_eq_zero.1 hq0)
  have hgT := ((Matrix.isUnit_iff_isUnit_det B).2 hdet).mul_left_cancel hB
  exact Subtype.ext (by simpa using congrArg Matrix.transpose hgT)

/-! ### The level at a nonzero angular momentum -/

/-- The model space `ℝ³ × (ℝ³)*` of `T*ℝ³` has dimension `6`. -/
private theorem finrank_cotangentModel :
    finrank ℝ ((Fin 3 → ℝ) × ((Fin 3 → ℝ) →L[ℝ] ℝ)) = 6 := by
  simp [finrank_prod, ContinuousLinearMap.dual_finrank_eq]

/-- A point where the moment map does not vanish has nonzero angular momentum. -/
private theorem cotangentAngularMomentum_ne_zero {z : T*ℝ³} (hz : momentMap I₃ SO₃ z ≠ 0) :
    cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) ≠ 0 := fun h0 ↦
  hz (by rw [momentMap_specialOrthogonalGroup_eq, h0, map_zero])

/-- **The rotations act locally freely at nonzero angular momentum**: the isotropy algebra of a
covector `p` at `q` with `q ⨯₃ p ≠ 0` is zero. -/
theorem isotropy_fundamental_specialOrthogonalGroup_eq_bot {z : T*ℝ³}
    (hz : cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) ≠ 0) :
    (InfinitesimalAction.fundamental I₃ SO₃
      (𝓘(ℝ, Fin 3 → ℝ).prod 𝓘(ℝ, (Fin 3 → ℝ) →L[ℝ] ℝ)) T*ℝ³).isotropy z = ⊥ :=
  Lie.isotropy_eq_bot_of_stabilizer_eq_bot (stabilizer_specialOrthogonalGroup_eq_bot hz)

/-- **The orbits of the rotations at nonzero angular momentum are three-dimensional.** By
`TauCeti.SmoothTwoForm.IsMomentMap.orthogonal_ker_differential`, the orbit tangent space `𝔤 · z`
is the symplectic complement `(T_z Z)^ω` of the tangent space `T_z Z = ker dμ_z` of the level. -/
theorem finrank_orbitTangent_specialOrthogonalGroup {z : T*ℝ³}
    (hz : cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) ≠ 0) :
    finrank ℝ ((InfinitesimalAction.fundamental I₃ SO₃
      (𝓘(ℝ, Fin 3 → ℝ).prod 𝓘(ℝ, (Fin 3 → ℝ) →L[ℝ] ℝ)) T*ℝ³).orbitTangent z) = 3 := by
  rw [InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ _
    (isotropy_fundamental_specialOrthogonalGroup_eq_bot hz),
    finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three]

section Level

variable (h : (symplecticForm 𝓘(ℝ, Fin 3 → ℝ) (Fin 3 → ℝ)).IsEquivariantMomentMap
  (momentMap I₃ SO₃))

/-- The cotangent symplectic form of `T*ℝ³` is nondegenerate at every point. -/
private theorem nondegenerate_bilinFormAt (z : T*ℝ³) :
    ((symplecticForm 𝓘(ℝ, Fin 3 → ℝ) (Fin 3 → ℝ)).bilinFormAt z).Nondegenerate :=
  isSymplectic_symplecticForm.isNondegenerate.nondegenerate_bilinFormAt z

/-- **Every nonzero value of the moment map is a regular value**: the differential of the moment
map is onto at every point where the moment map does not vanish. -/
theorem differential_surjective_momentMap_specialOrthogonalGroup {z : T*ℝ³}
    (hz : momentMap I₃ SO₃ z ≠ 0) : Function.Surjective (h.differential z) :=
  h.toIsMomentMap.differential_surjective_of_stabilizer_eq_bot (nondegenerate_bilinFormAt z)
    (stabilizer_specialOrthogonalGroup_eq_bot (cotangentAngularMomentum_ne_zero hz))

/-- **The stabilizer `G_c` of a nonzero value `c` acts freely on the level `μ⁻¹(c)`.** -/
theorem isCancelSMul_levelSubMulAction_specialOrthogonalGroup
    {c : Module.Dual ℝ 𝔰𝔬₃} (hc : c ≠ 0) :
    IsCancelSMul ((Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer c) (h.levelSubMulAction c) :=
  h.isCancelSMul_levelSubMulAction fun _ hx ↦
    stabilizer_specialOrthogonalGroup_eq_bot (cotangentAngularMomentum_ne_zero (by rwa [hx]))

/-- **The level of a nonzero angular momentum is three-dimensional**: its tangent space
`ker dμ_z` at a point of nonzero angular momentum has dimension `6 - 3 = 3`. -/
theorem finrank_ker_differential_momentMap_specialOrthogonalGroup {z : T*ℝ³}
    (hz : cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) ≠ 0) :
    finrank ℝ (LinearMap.ker (h.differential z)) = 3 := by
  have hsum := h.toIsMomentMap.finrank_ker_differential_add_finrank (nondegenerate_bilinFormAt z)
    (isotropy_fundamental_specialOrthogonalGroup_eq_bot hz)
  rw [finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three, finrank_cotangentModel] at hsum
  omega

/-- **The null directions of the form on the level are a line**: at a point of nonzero angular
momentum the kernel `T_z Z ∩ (T_z Z)^ω` of the restriction of the symplectic form to the tangent
space `T_z Z = ker dμ_z` of the level is the orbit direction `𝔤_c · z` of the circle `G_c`. -/
theorem finrank_ker_differential_inf_orthogonal_momentMap_specialOrthogonalGroup {z : T*ℝ³}
    (hz : cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) ≠ 0) :
    finrank ℝ ↥(LinearMap.ker (h.differential z) ⊓
      ((symplecticForm 𝓘(ℝ, Fin 3 → ℝ) (Fin 3 → ℝ)).bilinFormAt z).orthogonal
        (LinearMap.ker (h.differential z))) = 1 := by
  rw [h.toIsMomentMap.finrank_ker_differential_inf_orthogonal (nondegenerate_bilinFormAt z)
    (h.momentCocycle_eq_zero z) (isotropy_fundamental_specialOrthogonalGroup_eq_bot hz),
    momentMap_specialOrthogonalGroup_eq, finrank_lieAnnihilator_specialOrthogonalThreeDualEquiv hz]

/-- **The level of a nonzero angular momentum is not coisotropic.** The value `c = ν_(q ⨯₃ p)` is
not fixed by the coadjoint action, so the symplectic complement `(T_z Z)^ω = 𝔤 · z` of the
tangent space of the level is not contained in it: for `ξ` not parallel to `q ⨯₃ p`,
`dμ(ξ_M) = ⁅ξ, c⁆ ≠ 0`. -/
theorem not_isCoisotropic_ker_differential_momentMap_specialOrthogonalGroup {z : T*ℝ³}
    (hz : cotangentAngularMomentum (modelSpaceDiffeomorph (Fin 3 → ℝ) z) ≠ 0) :
    ¬(isSymplectic_symplecticForm.isNondegenerate.symplecticFormAt z).IsCoisotropic
      (LinearMap.ker (h.differential z)) := by
  rw [h.toIsMomentMap.isCoisotropic_ker_differential_iff isSymplectic_symplecticForm.isNondegenerate
    (h.momentCocycle_eq_zero z), momentMap_specialOrthogonalGroup_eq,
    lieAnnihilator_specialOrthogonalThreeDualEquiv_eq_top_iff]
  exact hz

/-! ### The reduced space -/

/-- **The reduced space of a nonzero value has dimension two.** For a nonzero value `c` of the
moment map, with `G_c` given a Lie group structure `d` modelled on `F`, the reduced space
`μ⁻¹(c) / G_c` of the Marsden–Weinstein–Meyer theorem
(`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`, in the namespace
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`) is modelled on a space of dimension
`dim T*ℝ³ - dim 𝔰𝔬(3) - dim 𝔤_c = 6 - 3 - 1 = 2`. -/
theorem finrank_quotientModelSpace_specialOrthogonalGroup {c : Module.Dual ℝ 𝔰𝔬₃} (hc : c ≠ 0)
    {n : ℕ} (hn : finrank ℝ ((Fin 3 → ℝ) × ((Fin 3 → ℝ) →L[ℝ] ℝ)) - finrank ℝ 𝔰𝔬₃ = n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (d : Lie.EmbeddedLieSubgroupData I₃ ((Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer c) F)
    (z : h.levelSubMulAction c) :
    finrank ℝ (ProperSMul.QuotientModelSpace F (Fin n → ℝ)) = 2 := by
  have : ContinuousSMul SO₃ T*ℝ³ := ContMDiffSMul.continuousSMul (I := I₃)
    (I' := 𝓘(ℝ, Fin 3 → ℝ).prod 𝓘(ℝ, (Fin 3 → ℝ) →L[ℝ] ℝ)) ∞
  have : ProperSMul SO₃ T*ℝ³ := properSMul_of_compactSpace _ _
  have := isCancelSMul_levelSubMulAction_specialOrthogonalGroup h hc
  have hz : momentMap I₃ SO₃ z = c := h.mem_levelSubMulAction.1 z.property
  have hsum := h.finrank_quotientModelSpace_add_finrank_add_finrank_lieAnnihilator
    (fun _ hx ↦ differential_surjective_momentMap_specialOrthogonalGroup h (by rwa [hx])) hn d
    isSymplectic_symplecticForm.isNondegenerate z
  rw [← hz, momentMap_specialOrthogonalGroup_eq,
    finrank_lieAnnihilator_specialOrthogonalThreeDualEquiv
      (cotangentAngularMomentum_ne_zero (by rwa [hz])),
    finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three, finrank_cotangentModel] at hsum
  omega

end Level

end CotangentBundle

end TauCeti
