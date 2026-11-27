/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.SpecialOrthogonal
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.Shifting

import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# The shifting construction for the rotations of `T*ℝ³`

The rotation group `SO(3)` acts on `T*ℝ³` by the cotangent lift, with moment map the angular
momentum `μ(q, p) = ν_(q ⨯₃ p)`. For a nonzero value `c`, the shifting theorem
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_shiftingReducedSpaceDiffeomorph`)
identifies the reduced space `μ⁻¹(c) / G_c` with the reduced space at zero of `T*ℝ³ × O⁻`, where
`O = SO(3) ⧸ G_c` is the coadjoint orbit of `c` with the reversed Kirillov–Kostant–Souriau form and
`Ψ(x, o) = μ(x) - ι_O(o)` is the shifting moment map
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_neg_coadjointOrbitForm`). This file counts the
dimensions on the shifted side. The declarations named without a namespace below are in
`TauCeti.CotangentBundle`.

* **The product.** The orbit `O` of `c ≠ 0` is two-dimensional
  (`TauCeti.finrank_quotientModelSpace_stabilizer_specialOrthogonalGroup`), so `T*ℝ³ × O` is
  modelled on a space of dimension `6 + 2 = 8`
  (`finrank_prod_quotientModelSpace_specialOrthogonalGroup`).
* **The zero level.** Zero is a regular value of `Ψ`, so at each point of `Ψ⁻¹(0)` the tangent
  space `ker dΨ` of the level has dimension `8 - 3 = 5`
  (`finrank_ker_differential_prod_neg_coadjointOrbitForm_specialOrthogonalGroup`),
  and the regular-level charts of `Ψ⁻¹(0)` are modelled on `ℝ⁵`
  (`finrank_prod_quotientModelSpace_sub_finrank_specialOrthogonalGroup`).
* **The reduced space.** The stabilizer of `0` is all of `SO(3)`, which acts freely on `Ψ⁻¹(0)`,
  and the reduced space `Ψ⁻¹(0) / SO(3)` is modelled on a space of dimension
  `dim (T*ℝ³ × O) - dim 𝔰𝔬(3) - dim 𝔰𝔬(3) = 8 - 3 - 3 = 2`
  (`finrank_quotientModelSpace_prod_neg_coadjointOrbitForm_specialOrthogonalGroup`).
  This is the dimension `6 - 3 - 1 = 2` of the reduced space `μ⁻¹(c) / G_c` of the unshifted
  reduction (`finrank_quotientModelSpace_specialOrthogonalGroup`), as the
  shifting theorem requires: shifting trades the one-dimensional stabilizer algebra `𝔤_c` for the
  two orbit directions of `O`, which the three-dimensional stabilizer algebra `𝔤_0 = 𝔰𝔬(3)` then
  absorbs.

## References

* E. Meinrenken, *Symplectic geometry*, lecture notes, University of Toronto, 2000,
  Proposition 8.6 (the shifting trick).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 11.4 and 14.2 (the angular momentum and the coadjoint
  orbits of `SO(3)`).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

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

/-- **The product of `T*ℝ³` with a nonzero coadjoint orbit of `SO(3)` is eight-dimensional**: for
`c ≠ 0`, `T*ℝ³ × SO(3) ⧸ G_c` is modelled on a space of dimension `6 + 2 = 8`. -/
theorem finrank_prod_quotientModelSpace_specialOrthogonalGroup {c : Module.Dual ℝ 𝔰𝔬₃}
    (hc : c ≠ 0) :
    finrank ℝ (((Fin 3 → ℝ) × ((Fin 3 → ℝ) →L[ℝ] ℝ)) × Subgroup.QuotientModelSpace I₃
      ((Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer c)) = 8 := by
  simp [finrank_prod, ContinuousLinearMap.dual_finrank_eq,
    finrank_quotientModelSpace_stabilizer_specialOrthogonalGroup hc]

/-- **The regular-level charts of the zero level of the shifting moment map are modelled on
`ℝ⁵`**: for `c ≠ 0`, `dim (T*ℝ³ × SO(3) ⧸ G_c) - dim 𝔰𝔬(3) = 8 - 3 = 5`. This is the equation
`hn₀` that the charts
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace` of `Ψ⁻¹(0)` take. -/
theorem finrank_prod_quotientModelSpace_sub_finrank_specialOrthogonalGroup
    {c : Module.Dual ℝ 𝔰𝔬₃} (hc : c ≠ 0) :
    finrank ℝ (((Fin 3 → ℝ) × ((Fin 3 → ℝ) →L[ℝ] ℝ)) × Subgroup.QuotientModelSpace I₃
      ((Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer c)) - finrank ℝ 𝔰𝔬₃ = 5 := by
  rw [finrank_prod_quotientModelSpace_specialOrthogonalGroup hc,
    finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three]

variable (h : (symplecticForm 𝓘(ℝ, Fin 3 → ℝ) (Fin 3 → ℝ)).IsEquivariantMomentMap
  (momentMap I₃ SO₃))

/-- **The zero level of the shifting moment map is five-dimensional.** For `c ≠ 0` and a point
`(x, o)` of `T*ℝ³ × SO(3) ⧸ G_c` with `μ(x) = ι_O(o)`, the tangent space `ker dΨ` of the level
`Ψ⁻¹(0)` of `Ψ(x, o) = μ(x) - ι_O(o)` has dimension `8 - 3 = 5`. -/
theorem finrank_ker_differential_prod_neg_coadjointOrbitForm_specialOrthogonalGroup
    {c : Module.Dual ℝ 𝔰𝔬₃} (hc : c ≠ 0)
    {p : T*ℝ³ × SO₃ ⧸ (Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer c}
    (hp : momentMap I₃ SO₃ p.1 = (Lie.coadjointRepresentation ℝ I₃ SO₃).orbitMap c p.2) :
    finrank ℝ (LinearMap.ker ((h.prod_neg_coadjointOrbitForm c).differential p)) = 5 := by
  have hsurj := h.forall_differential_surjective_prod_neg_coadjointOrbitForm
    (forall_differential_surjective_momentMap_specialOrthogonalGroup h hc) p (sub_eq_zero.2 hp)
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((h.prod_neg_coadjointOrbitForm c).differential p)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Subspace.dual_finrank_eq,
    finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three, finrank_tangentSpace,
    finrank_prod_quotientModelSpace_specialOrthogonalGroup hc] at hrn
  omega

/-- **The reduced space of the shifted product is two-dimensional.** For `c ≠ 0`, the reduced
space `Ψ⁻¹(0) / SO(3)` at zero of `T*ℝ³ × O⁻`, with `O = SO(3) ⧸ G_c` and
`Ψ(x, o) = μ(x) - ι_O(o)`, is modelled on a space of dimension
`dim (T*ℝ³ × O) - dim 𝔰𝔬(3) - dim 𝔰𝔬(3) = 8 - 3 - 3 = 2`, for any Lie group structure `d₀` on the
stabilizer of zero, modelled on `F₀`. This agrees with the dimension of the reduced space
`μ⁻¹(c) / G_c` (`finrank_quotientModelSpace_specialOrthogonalGroup`). -/
theorem finrank_quotientModelSpace_prod_neg_coadjointOrbitForm_specialOrthogonalGroup
    {c : Module.Dual ℝ 𝔰𝔬₃} (hc : c ≠ 0) {n₀ : ℕ}
    (hn₀ : finrank ℝ (((Fin 3 → ℝ) × ((Fin 3 → ℝ) →L[ℝ] ℝ)) × Subgroup.QuotientModelSpace I₃
      ((Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer c)) - finrank ℝ 𝔰𝔬₃ = n₀)
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
    (d₀ : Lie.EmbeddedLieSubgroupData I₃ ((Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer 0) F₀)
    (p : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    finrank ℝ (ProperSMul.QuotientModelSpace F₀ (Fin n₀ → ℝ)) = 2 := by
  have : ContinuousSMul SO₃ T*ℝ³ := ContMDiffSMul.continuousSMul (I := I₃)
    (I' := 𝓘(ℝ, Fin 3 → ℝ).prod 𝓘(ℝ, (Fin 3 → ℝ) →L[ℝ] ℝ)) ∞
  have : ProperSMul SO₃ (T*ℝ³ × SO₃ ⧸ (Lie.coadjointRepresentation ℝ I₃ SO₃).stabilizer c) :=
    properSMul_of_compactSpace _ _
  have := isCancelSMul_levelSubMulAction_specialOrthogonalGroup h hc
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  have hΨ := h.prod_neg_coadjointOrbitForm c
  have hsum := hΨ.finrank_quotientModelSpace_add_finrank_add_finrank_lieAnnihilator
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm
      (forall_differential_surjective_momentMap_specialOrthogonalGroup h hc)) hn₀ d₀
    (isSymplectic_symplecticForm.isNondegenerate.prod
      c.isSymplectic_coadjointOrbitForm.isNondegenerate.neg) p
  -- The coadjoint stabilizer of `0` is all of `𝔰𝔬(3)`.
  rw [lieAnnihilator_zero, LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq] at hsum
  rw [finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three,
    finrank_prod_quotientModelSpace_specialOrthogonalGroup hc] at hsum
  omega

end CotangentBundle

end TauCeti
