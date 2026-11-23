/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.SU2.LieAlgebra
public import TauCeti.RepresentationTheory.SU2.StandardBasis
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The coadjoint orbits of `SU(2)`

The group `SU(2)` acts on its Lie algebra `𝔰𝔲(2)` by the adjoint representation
`TauCeti.SU2.adjointRepresentation`, and on the dual `𝔰𝔲(2)*` by the **coadjoint representation**
`(Ad*_g ν)(X) = ν (Ad_{g⁻¹} X)` (`TauCeti.SU2.coadjointRepresentation`). In the basis
`-iσ₁/2, -iσ₂/2, -iσ₃/2` of `𝔰𝔲(2)` (`TauCeti.suTwoEquiv`), with `𝔰𝔲(2)*` identified with `ℝ³` by
the dot product, `ν_n = n ⬝ᵥ ·` (`TauCeti.suTwoDualEquiv`), both actions are the rotation
`R_g = toSO3 g` of the double cover `SU(2) → SO(3)`:

`Ad_g (suTwoEquiv x) = suTwoEquiv (R_g x)`, `Ad*_g ν_n = ν_(R_g n)`

(`TauCeti.SU2.adjointRepresentation_suTwoEquiv`,
`TauCeti.SU2.coadjointRepresentation_suTwoDualEquiv`). Since `SO(3)` acts transitively on the
spheres about the origin and `SU(2) → SO(3)` is onto, this computes the orbits and stabilizers of
the coadjoint action:

* **Orbits.** The coadjoint orbit of `ν_n` is the sphere `{ν_m | m ⬝ᵥ m = n ⬝ᵥ n}`
  (`TauCeti.SU2.range_coadjointRepresentation_suTwoDualEquiv`): a two-sphere for `n ≠ 0`, and the
  point `{0}` for `n = 0`. On them the Kirillov–Kostant–Souriau form is the triple product
  `n ⬝ᵥ (ξ ⨯₃ η)` (`TauCeti.kksForm_suTwoDualEquiv_mk`), exactly as on the coadjoint spheres of
  `so(3)`, where the sphere of radius `r > 0` has KKS area `4π r`
  (`TauCeti.integralTopForm_smul_sphereAreaForm`).
* **Stabilizers.** The stabilizer of `ν_(c e₃)`, `c ≠ 0`, is the maximal torus
  `T = {diag(z, z⁻¹)}`
  (`TauCeti.SU2.stabilizer_coadjointRepresentation_suTwoDualEquiv_smul_single_two`): the rotation
  `toSO3 g` induced by `g ∈ SU(2)` fixes the vector `e₃` exactly when `g` commutes with `σ₃`, that
  is, when `g` is diagonal (`TauCeti.SU2.toSO3_mulVec_single_two_eq_self_iff`). The stabilizer of
  any `ν ≠ 0` is a conjugate `g T g⁻¹` of the maximal torus
  (`TauCeti.SU2.exists_stabilizer_coadjointRepresentation_eq_torus_map_conj`), and the stabilizer
  of `0` is all of `SU(2)` (`Representation.stabilizer_zero`).

The kernel of the coadjoint action is exactly the center `{±1}` of `SU(2)`
(`TauCeti.SU2.coadjointRepresentation_eq_one_iff`), so the coadjoint action factors faithfully
through `SO(3) = SU(2) / {±1}` and has the same orbits as the rotation action of `SO(3)` on `ℝ³`.
The two groups differ instead in the periods of their maximal tori: in
`SU(2)` the generator `-iσ₃/2` of `T` has period `4π`, its image in `SO(3)` period `2π`
(`TauCeti.lieExp_smul_suTwoEquiv_single_two_eq_one_iff`,
`TauCeti.toSO3_eq_one_iff_of_coe_eq_lieExp`).

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, American
  Mathematical Society, 2004, Section 1.2 (coadjoint orbits of `SU(2)` and `SO(3)`).
* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Texts
  in Applied Mathematics 17, Springer, 1999, Chapter 14 (coadjoint orbits of `SO(3)` as spheres).
-/

public section

noncomputable section

open Matrix Module Complex
open scoped ContDiff Manifold Matrix.Norms.Operator

namespace TauCeti.SU2

attribute [local instance 100] LieRing.ofAssociativeRing

-- The matrix topology and rational algebra structure under which `SU(2)` is a Lie subgroup of the
-- real Lie group `GL(2, ℂ)`, as in `TauCeti.RepresentationTheory.SU2.StandardBasis`.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal

/-! ### The adjoint and coadjoint representations in coordinates -/

/-- The adjoint action of `g ∈ SU(2)` in the basis `-iσₐ/2` is the rotation `toSO3 g`. -/
@[simp]
theorem adjointRepresentation_suTwoEquiv (g : SU2) (x : Fin 3 → ℝ) :
    adjointRepresentation g (suTwoEquiv x) =
      suTwoEquiv ((toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) :=
  Subtype.ext <| (coe_adjointRepresentation_apply g _).trans (Ad_toUnits_inclusion_suTwoEquiv g x)

/-- The **coadjoint representation** of `SU(2)` on the dual `𝔰𝔲(2)*` of its Lie algebra:
`(Ad*_g ν)(X) = ν (Ad_{g⁻¹} X)`, the dual of the adjoint representation. -/
def coadjointRepresentation : Representation ℝ SU2 (Dual ℝ lieAlgebra) :=
  adjointRepresentation.toRepresentation.dual

@[simp]
theorem coadjointRepresentation_apply (g : SU2) (ν : Dual ℝ lieAlgebra) (X : lieAlgebra) :
    coadjointRepresentation g ν X = ν (adjointRepresentation g⁻¹ X) := by
  rw [coadjointRepresentation, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply]
  -- `ContRepresentation.toRepresentation ρ g` is `ρ g` viewed as a linear map, by definition.
  rfl

/-- **The coadjoint action in coordinates**: `Ad*_g ν_n = ν_(R n)`, where `R = toSO3 g` is the
rotation induced by `g` and `ν_n = n ⬝ᵥ ·` in the basis `-iσₐ/2`. -/
@[simp]
theorem coadjointRepresentation_suTwoDualEquiv (g : SU2) (n : Fin 3 → ℝ) :
    coadjointRepresentation g (suTwoDualEquiv n) =
      suTwoDualEquiv ((toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n) := by
  refine LinearMap.ext fun X ↦ ?_
  obtain ⟨x, rfl⟩ := suTwoEquiv.surjective X
  rw [coadjointRepresentation_apply, adjointRepresentation_suTwoEquiv,
    suTwoDualEquiv_apply_suTwoEquiv, suTwoDualEquiv_apply_suTwoEquiv,
    ← mem_orthogonalGroup_iff_dotProduct_mulVec.mp (toSO3 g).property.1 n, mulVec_mulVec]
  simp [-coe_toSO3, (mem_orthogonalGroup_iff (Fin 3) ℝ).mp (toSO3 g).property.1]

/-! ### Orbits -/

/-- **The coadjoint orbits of `SU(2)` are the spheres about the origin**: the orbit of `ν_n` is
`{ν_m | m ⬝ᵥ m = n ⬝ᵥ n}`. -/
theorem range_coadjointRepresentation_suTwoDualEquiv (n : Fin 3 → ℝ) :
    Set.range (fun g : SU2 ↦ coadjointRepresentation g (suTwoDualEquiv n)) =
      suTwoDualEquiv '' {m | m ⬝ᵥ m = n ⬝ᵥ n} := by
  ext ν
  obtain ⟨m, rfl⟩ := suTwoDualEquiv.surjective ν
  simp only [Set.mem_range, coadjointRepresentation_suTwoDualEquiv,
    suTwoDualEquiv.injective.eq_iff, suTwoDualEquiv.injective.mem_set_image]
  exact exists_toSO3_mulVec_eq_iff

/-- **The kernel of the coadjoint action is the center** `{±1}` of `SU(2)`: the coadjoint action
factors through the double cover `SU(2) → SO(3)`, and the action of `SO(3)` it induces on
`𝔰𝔲(2)*` is faithful. -/
theorem coadjointRepresentation_eq_one_iff {g : SU2} :
    coadjointRepresentation g = 1 ↔ g ∈ Subgroup.center SU2 := by
  rw [← ker_toSO3, MonoidHom.mem_ker]
  constructor
  · intro h
    refine Subtype.ext <| Matrix.toLin'.injective <| LinearMap.ext fun n ↦ ?_
    have hn := LinearMap.congr_fun h (suTwoDualEquiv n)
    rw [coadjointRepresentation_suTwoDualEquiv, one_apply_eq_self,
      suTwoDualEquiv.injective.eq_iff] at hn
    simpa using hn
  · intro h
    refine LinearMap.ext fun ν ↦ ?_
    obtain ⟨n, rfl⟩ := suTwoDualEquiv.surjective ν
    rw [coadjointRepresentation_suTwoDualEquiv, h, OneMemClass.coe_one, one_mulVec,
      one_apply_eq_self]

/-! ### Stabilizers -/

/-- **The stabilizer of `ν_(c e₃)`, `c ≠ 0`, is the maximal torus** `T = {diag(z, z⁻¹)}` of
`SU(2)`. -/
theorem stabilizer_coadjointRepresentation_suTwoDualEquiv_smul_single_two {c : ℝ} (hc : c ≠ 0) :
    coadjointRepresentation.stabilizer (suTwoDualEquiv (c • Pi.single 2 1)) = torus := by
  ext g
  rw [Representation.mem_stabilizer, coadjointRepresentation_suTwoDualEquiv,
    suTwoDualEquiv.injective.eq_iff, mulVec_smul, smul_right_injective _ hc |>.eq_iff,
    toSO3_mulVec_single_two_eq_self_iff]

/-- **The stabilizer of a nonzero point of `𝔰𝔲(2)*` is a maximal torus**: a conjugate `g T g⁻¹` of
the diagonal torus. -/
theorem exists_stabilizer_coadjointRepresentation_eq_torus_map_conj {ν : Dual ℝ lieAlgebra}
    (hν : ν ≠ 0) : ∃ g : SU2, coadjointRepresentation.stabilizer ν = torus.map (MulAut.conj g) := by
  obtain ⟨n, rfl⟩ := suTwoDualEquiv.surjective ν
  have hn : n ≠ 0 := by rintro rfl; exact hν (map_zero _)
  -- Rotate the point `c • e₃` of the positive `e₃`-axis, at the same distance from the origin,
  -- onto `n`.
  have h0 := dotProduct_self_nonneg n
  set c := √(n ⬝ᵥ n)
  have hc : c ≠ 0 := Real.sqrt_ne_zero'.mpr
    (lt_of_le_of_ne h0 (Ne.symm (dotProduct_self_eq_zero.not.mpr hn)))
  obtain ⟨g, hg⟩ := exists_toSO3_mulVec_eq_iff (n := c • Pi.single 2 1) (m := n) |>.mpr <| by
    simp only [c, dotProduct_smul, dotProduct_single, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one]
    exact (Real.mul_self_sqrt h0).symm
  refine ⟨g, ?_⟩
  rw [← hg, ← coadjointRepresentation_suTwoDualEquiv, Representation.stabilizer_conj,
    stabilizer_coadjointRepresentation_suTwoDualEquiv_smul_single_two hc]

end TauCeti.SU2
