/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Algebra.Lie.Orthogonal.CoadjointOrbit
public import TauCeti.RepresentationTheory.SU2.LieAlgebra
public import TauCeti.RepresentationTheory.SU2.StandardBasis

/-!
# The coadjoint orbits of `SU(2)`

The adjoint representation of `SU(2)` on its Lie algebra `𝔰𝔲(2)`
(`TauCeti.SU2.adjointRepresentation`) is, in the basis `-iσₐ/2` of `TauCeti.suTwoEquiv`, the
rotation of `ℝ³` by the double cover `SU(2) → SO(3)` (`TauCeti.SU2.toSO3`):

`Ad_g (suTwoEquiv x) = suTwoEquiv (toSO3 g x)`

(`TauCeti.SU2.adjointRepresentation_suTwoEquiv`). Equivalently, the Lie algebra isomorphism
`𝔰𝔲(2) ≃ so(3)` of `TauCeti.suTwoLieEquivSoThree` intertwines `Ad_g` with the adjoint action of
`toSO3 g` (`TauCeti.SU2.suTwoLieEquivSoThree_adjointRepresentation`). The **coadjoint
representation** `Ad*_g ν = ν ∘ Ad_(g⁻¹)` (`TauCeti.SU2.coadjointRepresentation`) is its dual, and
pulling functionals back along `𝔰𝔲(2) ≃ so(3)` intertwines it with the coadjoint representation of
`SO(3)` through the double cover:

`Ad*_g (ν ∘ e) = (Ad*_(toSO3 g) ν) ∘ e`, where `e = suTwoLieEquivSoThree`

(`TauCeti.SU2.coadjointRepresentation_comp_suTwoLieEquivSoThree`). This is the passage of
coadjoint orbits through the discrete central cover `SU(2) → SO(3) = SU(2) ⧸ {±1}`:

* since `toSO3` is surjective, the coadjoint orbit of `SU(2)` through `ν ∘ e` is the image of the
  coadjoint orbit of `SO(3)` through `ν` (`TauCeti.SU2.range_coadjointRepresentation_comp`);
* the coadjoint stabilizer of `ν ∘ e` is the preimage under `toSO3` of the coadjoint stabilizer of
  `ν` (`TauCeti.SU2.stabilizer_coadjointRepresentation_comp`), so it contains the kernel `{±1}`;
* an element of `SU(2)` acts trivially on `𝔰𝔲(2)*` exactly when it is central
  (`TauCeti.SU2.coadjointRepresentation_eq_one_iff`).

In the dot-product coordinates `ν_n(suTwoEquiv x) = n ⬝ᵥ x` of `TauCeti.suTwoDualEquiv`, which are
those of the invariant inner product `B(X, Y) = -2 tr(XY)` making the basis `-iσₐ/2` orthonormal,
the coadjoint action is the rotation `Ad*_g ν_n = ν_(toSO3 g n)`
(`TauCeti.SU2.coadjointRepresentation_suTwoDualEquiv`). Hence the coadjoint stabilizer of `ν_n` is
the set of `g` whose rotation fixes `n`
(`TauCeti.SU2.mem_stabilizer_coadjointRepresentation_suTwoDualEquiv_iff`), and **the coadjoint orbit
of `SU(2)` through `ν_m` is the sphere of radius `√(m ⬝ᵥ m)`**:

`{Ad*_g ν_m | g ∈ SU(2)} = {ν_p | p ⬝ᵥ p = m ⬝ᵥ m}`

(`TauCeti.SU2.range_coadjointRepresentation_suTwoDualEquiv`). These are the same spheres as the
coadjoint orbits of `SO(3)`
(`TauCeti.range_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv`), while their isotropy
groups are the preimages of those of `SO(3)` and contain the center `{±1}`.
The two groups differ in the period of the torus generator `-iσ₃/2`, which is `4π` in `SU(2)` and
`2π` in `SO(3)` (`TauCeti.lieExp_smul_suTwoEquiv_single_two_eq_one_iff`,
`TauCeti.toSO3_eq_one_iff_of_coe_eq_lieExp`), not in their coadjoint orbits.

The general statements for a homomorphism of Lie groups, through the Lie algebra map of its
differential, are in `TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Map`. They do not apply
here directly: `SU(2)` is the special unitary matrix subgroup, whose Lie algebra is the Lie
subalgebra `TauCeti.SU2.lieAlgebra` of the Lie algebra of `GL(2, ℂ)`, and `SO(3)` is the special
orthogonal matrix group acting on the skew-symmetric matrices `so(3)` by conjugation. This file
proves the corresponding statements for these concrete models, through `suTwoLieEquivSoThree`.

## Main definitions

* `TauCeti.SU2.coadjointRepresentation`: the coadjoint representation of `SU(2)` on `𝔰𝔲(2)*`.

## Main results

* `TauCeti.SU2.adjointRepresentation_suTwoEquiv`: the adjoint action in the basis `-iσₐ/2`.
* `TauCeti.SU2.coadjointRepresentation_comp_suTwoLieEquivSoThree`: the coadjoint actions of `SU(2)`
  and `SO(3)` correspond through the double cover.
* `TauCeti.SU2.range_coadjointRepresentation_comp`,
  `TauCeti.SU2.stabilizer_coadjointRepresentation_comp`: orbits and stabilizers through the
  double cover.
* `TauCeti.SU2.coadjointRepresentation_eq_one_iff`: the kernel of the coadjoint representation is
  the center.
* `TauCeti.SU2.coadjointRepresentation_suTwoDualEquiv`: the coadjoint action in dot-product
  coordinates.
* `TauCeti.SU2.range_coadjointRepresentation_suTwoDualEquiv`: the coadjoint orbits of `SU(2)` are
  the spheres about the origin.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Texts
  in Applied Mathematics 17, Springer, 1999, Sections 9.2 and 14.2 (`SU(2)`, `SO(3)` and their
  coadjoint orbits).
* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

open Matrix Module LieAlgebra.Orthogonal
open scoped Manifold Matrix.Norms.Operator

noncomputable section

-- Select the matrix topology underlying the operator norm used for the general linear Lie group,
-- for which the Lie algebra of `SU(2)` carries the topology of its adjoint representation.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

namespace TauCeti.SU2

/-! ### The adjoint representation in the basis `-iσₐ/2` -/

/-- **The adjoint action of `SU(2)` is the rotation by its image in `SO(3)`** in the basis
`-iσₐ/2`: `Ad_g (suTwoEquiv x) = suTwoEquiv (toSO3 g x)`. -/
@[simp]
theorem adjointRepresentation_suTwoEquiv (g : SU2) (x : Fin 3 → ℝ) :
    adjointRepresentation g (suTwoEquiv x) =
      suTwoEquiv ((toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) :=
  Subtype.ext ((coe_adjointRepresentation_apply g _).trans (Ad_toUnits_inclusion_suTwoEquiv g x))

/-- The isomorphism `𝔰𝔲(2) ≃ so(3)` intertwines the adjoint action of `g ∈ SU(2)` with the adjoint
action of its image `toSO3 g ∈ SO(3)`. -/
theorem suTwoLieEquivSoThree_adjointRepresentation (g : SU2) (X : lieAlgebra) :
    suTwoLieEquivSoThree (adjointRepresentation g X) =
      specialOrthogonalAdjointRepresentation (Fin 3) ℝ (toSO3 g) (suTwoLieEquivSoThree X) := by
  obtain ⟨x, rfl⟩ := suTwoEquiv.surjective X
  simp

/-! ### The coadjoint representation -/

/-- The **coadjoint representation** of `SU(2)` on the dual of its Lie algebra,
`(Ad*_g ν)(X) = ν (Ad_(g⁻¹) X)`, the dual of the adjoint representation. -/
def coadjointRepresentation : Representation ℝ SU2 (Dual ℝ lieAlgebra) :=
  adjointRepresentation.toRepresentation.dual

@[simp]
theorem coadjointRepresentation_apply_apply (g : SU2) (ν : Dual ℝ lieAlgebra) (X : lieAlgebra) :
    coadjointRepresentation g ν X = ν (adjointRepresentation g⁻¹ X) :=
  (rfl)

/-- **The coadjoint actions of `SU(2)` and `SO(3)` correspond through the double cover.** Pulling
a functional `ν` on `so(3)` back along `e : 𝔰𝔲(2) ≃ so(3)` intertwines the coadjoint action of
`toSO3 g` with that of `g`: `Ad*_g (ν ∘ e) = (Ad*_(toSO3 g) ν) ∘ e`. -/
theorem coadjointRepresentation_comp_suTwoLieEquivSoThree (g : SU2)
    (ν : Dual ℝ (so (Fin 3) ℝ)) :
    coadjointRepresentation g (ν ∘ₗ (suTwoLieEquivSoThree : lieAlgebra →ₗ[ℝ] so (Fin 3) ℝ)) =
      specialOrthogonalCoadjointRepresentation (Fin 3) ℝ (toSO3 g) ν ∘ₗ
        (suTwoLieEquivSoThree : lieAlgebra →ₗ[ℝ] so (Fin 3) ℝ) := by
  refine LinearMap.ext fun X ↦ ?_
  simp [suTwoLieEquivSoThree_adjointRepresentation]

/-- **Coadjoint orbits through the double cover.** The coadjoint orbit of `SU(2)` through the
pullback `ν ∘ e` of a functional `ν` on `so(3)` along `e : 𝔰𝔲(2) ≃ so(3)` is the pullback of the
coadjoint orbit of `SO(3)` through `ν`. -/
theorem range_coadjointRepresentation_comp (ν : Dual ℝ (so (Fin 3) ℝ)) :
    Set.range (fun g ↦ coadjointRepresentation g
        (ν ∘ₗ (suTwoLieEquivSoThree : lieAlgebra →ₗ[ℝ] so (Fin 3) ℝ))) =
      (fun μ : Dual ℝ (so (Fin 3) ℝ) ↦
          μ ∘ₗ (suTwoLieEquivSoThree : lieAlgebra →ₗ[ℝ] so (Fin 3) ℝ)) ''
        Set.range (fun h ↦ specialOrthogonalCoadjointRepresentation (Fin 3) ℝ h ν) := by
  rw [← Set.range_comp]
  simp_rw [coadjointRepresentation_comp_suTwoLieEquivSoThree]
  exact toSO3_surjective.range_comp
    (fun h ↦ specialOrthogonalCoadjointRepresentation (Fin 3) ℝ h ν ∘ₗ
      (suTwoLieEquivSoThree : lieAlgebra →ₗ[ℝ] so (Fin 3) ℝ))

/-- **Coadjoint stabilizers through the double cover.** The coadjoint stabilizer in `SU(2)` of the
pullback `ν ∘ e` of a functional `ν` on `so(3)` is the preimage under `toSO3` of the coadjoint
stabilizer of `ν` in `SO(3)`. In particular it contains the kernel `{±1}` of `toSO3`. -/
theorem stabilizer_coadjointRepresentation_comp (ν : Dual ℝ (so (Fin 3) ℝ)) :
    coadjointRepresentation.stabilizer
        (ν ∘ₗ (suTwoLieEquivSoThree : lieAlgebra →ₗ[ℝ] so (Fin 3) ℝ)) =
      ((specialOrthogonalCoadjointRepresentation (Fin 3) ℝ).stabilizer ν).comap toSO3 := by
  ext g
  rw [Subgroup.mem_comap, Representation.mem_stabilizer, Representation.mem_stabilizer,
    coadjointRepresentation_comp_suTwoLieEquivSoThree,
    LinearMap.cancel_right suTwoLieEquivSoThree.toLinearEquiv.surjective]

/-! ### Dot-product coordinates -/

/-- **The coadjoint action of `SU(2)` is the rotation by its image in `SO(3)`**:
`Ad*_g ν_n = ν_(toSO3 g n)` for the functional `ν_n(suTwoEquiv x) = n ⬝ᵥ x`. -/
@[simp]
theorem coadjointRepresentation_suTwoDualEquiv (g : SU2) (n : Fin 3 → ℝ) :
    coadjointRepresentation g (suTwoDualEquiv n) =
      suTwoDualEquiv ((toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n) := by
  rw [← soThreeDualEquiv_comp_suTwoLieEquivSoThree, ← soThreeDualEquiv_comp_suTwoLieEquivSoThree,
    coadjointRepresentation_comp_suTwoLieEquivSoThree,
    specialOrthogonalCoadjointRepresentation_soThreeDualEquiv]

/-- **The coadjoint stabilizer of `ν_n` in `SU(2)`** consists of the elements whose rotation in
`SO(3)` fixes `n`. -/
theorem mem_stabilizer_coadjointRepresentation_suTwoDualEquiv_iff {g : SU2} {n : Fin 3 → ℝ} :
    g ∈ coadjointRepresentation.stabilizer (suTwoDualEquiv n) ↔
      (toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n = n := by
  rw [Representation.mem_stabilizer, coadjointRepresentation_suTwoDualEquiv,
    suTwoDualEquiv.injective.eq_iff]

/-- **The coadjoint orbits of `SU(2)` are the spheres about the origin**: in dot-product
coordinates, the coadjoint orbit through `ν_m` is the sphere of radius `√(m ⬝ᵥ m)`, the same sphere
as the coadjoint orbit of `SO(3)`. For `m = 0` it is the single point `0`. -/
theorem range_coadjointRepresentation_suTwoDualEquiv (m : Fin 3 → ℝ) :
    Set.range (fun g ↦ coadjointRepresentation g (suTwoDualEquiv m)) =
      suTwoDualEquiv '' {p | p ⬝ᵥ p = m ⬝ᵥ m} := by
  rw [← soThreeDualEquiv_comp_suTwoLieEquivSoThree, range_coadjointRepresentation_comp,
    range_specialOrthogonalCoadjointRepresentation_soThreeDualEquiv, Set.image_image]
  simp_rw [soThreeDualEquiv_comp_suTwoLieEquivSoThree]

/-- **The coadjoint orbit test of `SU(2)`**: in dot-product coordinates, `ν_p` lies on the coadjoint
orbit through `ν_m` exactly when `p` and `m` have the same length. -/
theorem suTwoDualEquiv_mem_range_coadjointRepresentation_iff {m p : Fin 3 → ℝ} :
    suTwoDualEquiv p ∈ Set.range (fun g ↦ coadjointRepresentation g (suTwoDualEquiv m)) ↔
      p ⬝ᵥ p = m ⬝ᵥ m := by
  rw [range_coadjointRepresentation_suTwoDualEquiv, suTwoDualEquiv.injective.mem_set_image,
    Set.mem_ofPred_eq]

/-! ### The kernel of the coadjoint representation -/

/-- **The kernel of the coadjoint representation of `SU(2)` is its center `{±1}`**: an element of
`SU(2)` acts trivially on `𝔰𝔲(2)*` exactly when it is central, that is, when its rotation in
`SO(3)` is the identity. So the coadjoint representation factors faithfully through the double
cover `SU(2) → SO(3)`. -/
theorem coadjointRepresentation_eq_one_iff (g : SU2) :
    coadjointRepresentation g = 1 ↔ g ∈ Subgroup.center SU2 := by
  rw [← ker_toSO3, MonoidHom.mem_ker]
  constructor
  · intro h
    -- The rotation `toSO3 g` fixes every vector, so it is the identity matrix.
    refine Subtype.ext (Matrix.toLin'.injective (LinearMap.ext fun n ↦ ?_))
    have hn := LinearMap.congr_fun h (suTwoDualEquiv n)
    rw [coadjointRepresentation_suTwoDualEquiv, one_apply_eq_self,
      suTwoDualEquiv.injective.eq_iff] at hn
    simpa using hn
  · intro h
    refine LinearMap.ext fun ν ↦ ?_
    obtain ⟨n, rfl⟩ := suTwoDualEquiv.surjective ν
    simp [h]

end TauCeti.SU2
