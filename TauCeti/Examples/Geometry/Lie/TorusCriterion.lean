/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.EilenbergMacLane
public import TauCeti.Geometry.Lie.CartanThreeForm
public import TauCeti.Geometry.Lie.Prod
public import TauCeti.RepresentationTheory.SU2.Basic
public import TauCeti.RepresentationTheory.SU2.LieGroup
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup
public import TauCeti.Topology.Algebra.Quaternion.Unitary.HomotopyGroup

/-!
# Checks of the torus criterion on tori, `SU(2)` and `SO(3)`

The torus criterion `TauCeti.Lie.isAspherical_iff_exists_continuousMulEquiv_torus` says that a
compact connected Lie group is aspherical exactly when it is isomorphic, as a topological group,
to a torus `(S¹)ʳ`. This file checks it, and the computations of `π₃` it rests on, on tori and
on the groups `SU(2)`, `SU(2) × SU(2)` and `SO(3)`.

* **Tori.** `Fin r → Circle` is aspherical (`Circle.isAspherical_pi`) and is a torus: both sides
  hold. In particular its third homotopy group vanishes.
* **`SU(2)` and `SU(2) × SU(2)`.** `SU(2)` is the three-sphere
  (`TauCeti.specialUnitaryGroupTwoHomeomorphSphere`), so `π₃(SU(2)) ≅ ℤ`
  (`TauCeti.specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt`), and
  `π₃(SU(2) × SU(2)) ≅ ℤ²`
  (`TauCeti.specialUnitaryGroupTwoProdHomotopyGroupThreeMulEquiv`). Both are
  proved in `TauCeti.Topology.Algebra.Quaternion.Unitary.HomotopyGroup`. The two factors of
  `ℤ²` come from the root subgroups `SU(2) × 1` and `1 × SU(2)`, since the slice inclusion
  `g ↦ (g, 1)` sends a class `a` to the product of `a` with the trivial class
  (`HomotopyGroup.map_prodMk_const`). The two root homomorphisms
  `g ↦ (g, 1)` and `g ↦ (1, g)` of the Lie group `SU(2) × SU(2)` are detected by the Cartan
  three-form: each has injective differential, since the projection to its factor undoes it
  (`TauCeti.Lie.lieMap_fst_lieMap_inl`, `TauCeti.Lie.lieMap_snd_lieMap_inr`), and `𝔰𝔲(2)` is not
  abelian (`TauCeti.SU2.not_isLieAbelian_leftInvariantDerivation`). So each pulls the Cartan
  three-form `ω` of an anisotropic invariant form, such as the Killing form, back to a nonzero
  form `f^*ω` on `𝔰𝔲(2)` (`LinearMap.BilinMap.cartanThreeForm_compLinearMap_ne_zero`), whose
  left-invariant extension is a volume form on `SU(2)` with nonzero integral, and neither
  homomorphism is null-homotopic
  (`ContMDiffMonoidMorphism.not_nullhomotopic_of_injective_lieMap`).
* **`SO(3)`.** `SO(3)` is doubly covered by the simply connected group `Spin(3) ≅ S³`, so the
  torus factor of its finite cover is trivial. A covering map is bijective on the homotopy groups
  in degrees at least two, so `π₃(SO(3)) ≅ π₃(S³) ≅ ℤ` at every base point
  (`TauCeti.specialOrthogonalGroupThreeHomotopyGroupThreeMulEquivInt`), while
  `π₂(SO(3)) = 0` (`TauCeti.subsingleton_homotopyGroup_specialOrthogonalGroup_three`). Hence
  `SO(3)` is not aspherical (`TauCeti.not_isAspherical_specialOrthogonalGroup_three`), and it is
  not a torus, since tori are aspherical: both sides fail.
  The computation of `π₃(SO(3))` and the failure of asphericity are proved with the other
  homotopy groups of `SO(3)` in `TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup`.

The Lie group hypothesis of the criterion is checked on the product `ℕ → Circle` of countably
many circles by `Circle.isEmpty_pi_mulEquiv_pi` and `TauCeti.not_lieGroup_pi_circle`: it is
aspherical but not a torus, and it is not a Lie group.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and the proof of
  Proposition 6.31).
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapters I and V.
-/

public section

noncomputable section

open Matrix
open scoped Topology Topology.Homotopy

namespace TauCeti

/-! ### Tori -/

/-- **Tori**: a torus `Fin r → Circle` is aspherical and is a torus, so both sides of the torus
criterion hold. -/
example (r : ℕ) : IsAspherical (Fin r → Circle) 1 ∧
    ∃ s : ℕ, Nonempty ((Fin r → Circle) ≃ₜ* (Fin s → Circle)) :=
  ⟨Circle.isAspherical_pi 1, r, ⟨ContinuousMulEquiv.refl _⟩⟩

/-- **The third homotopy group of a torus vanishes**, so the Cartan three-form, which vanishes on
a torus, has nothing to detect there. -/
example (r : ℕ) : Subsingleton (π_ 3 (Fin r → Circle) 1) :=
  (Circle.isAspherical_pi 1).subsingleton_homotopyGroup 1

/-! ### The groups `SU(2)` and `SU(2) × SU(2)` -/

/-- **`π₃(SU(2)) ≅ ℤ`**, at every base point: `SU(2)` is the three-sphere, the unit sphere of the
quaternions. -/
example (g : SU2) : Nonempty (π_ 3 SU2 g ≃* Multiplicative ℤ) :=
  ⟨specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt g⟩

/-- **`π₃(SU(2) × SU(2)) ≅ ℤ²`**, at every base point: the homotopy groups of a product are the
products of the homotopy groups of the factors. -/
example (g h : SU2) :
    Nonempty (π_ 3 (SU2 × SU2) (g, h) ≃* Multiplicative ℤ × Multiplicative ℤ) :=
  ⟨specialUnitaryGroupTwoProdHomotopyGroupThreeMulEquiv g h⟩

section RootHomomorphisms

-- Use the operator-norm topology under which `GL(2, ℂ)` is a Lie group, as in
-- `TauCeti.RepresentationTheory.SU2.LieGroup`.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

open scoped ContDiff _root_.Manifold Matrix.Norms.Operator

-- An anisotropic bilinear form `B` on the Lie algebra `𝔤` of `SU(2) × SU(2)` invariant under the
-- adjoint action, such as its negative-definite Killing form or a positive-definite invariant
-- inner product, whose Cartan three-form `ω` the root homomorphisms pull back.
variable (B : LinearMap.BilinForm ℝ (LeftInvariantDerivation
    (𝓘(ℝ, SU2.lieAlgebra.toSubmodule).prod 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
    (GLSpecialUnitary (Fin 2) ℂ × GLSpecialUnitary (Fin 2) ℂ)))
  (hB : ∀ x y z : LeftInvariantDerivation
    (𝓘(ℝ, SU2.lieAlgebra.toSubmodule).prod 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
    (GLSpecialUnitary (Fin 2) ℂ × GLSpecialUnitary (Fin 2) ℂ), B ⁅x, y⁆ z = -B y ⁅x, z⁆)
  (hani : B.toQuadraticMap.Anisotropic)

/-- **The root homomorphism `f : g ↦ (g, 1)` of `SU(2) × SU(2)` is detected by the Cartan
three-form.** Its differential `df` is injective, since the projection to the first factor undoes
it, and `𝔰𝔲(2)` is not abelian, so the Cartan three-form `ω` of an anisotropic invariant form
pulls back along `df` to a nonzero form `f^*ω` on `𝔰𝔲(2)`. Its left-invariant extension to `SU(2)`
is then a volume form with nonzero integral, so `f` is not null-homotopic. -/
example : (B.cartanThreeForm hB).compLinearMap
      (lieMap (ContMDiffMonoidMorphism.inl (I := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
        (I' := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule)) (n := ∞) (G := GLSpecialUnitary (Fin 2) ℂ)
        (G' := GLSpecialUnitary (Fin 2) ℂ))).toLinearMap ≠ 0 ∧
    ¬((ContMDiffMonoidMorphism.inl (I := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
      (I' := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule)) (n := ∞) (G := GLSpecialUnitary (Fin 2) ℂ)
      (G' := GLSpecialUnitary (Fin 2) ℂ) :
        C(GLSpecialUnitary (Fin 2) ℂ, GLSpecialUnitary (Fin 2) ℂ × GLSpecialUnitary (Fin 2) ℂ)
        ).Nullhomotopic) := by
  -- The projection to the factor undoes the inclusion on Lie algebras, so its differential is
  -- injective.
  have hinj : Function.Injective (lieMap (ContMDiffMonoidMorphism.inl
      (I := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule)) (I' := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
      (n := ∞) (G := GLSpecialUnitary (Fin 2) ℂ) (G' := GLSpecialUnitary (Fin 2) ℂ))) :=
    fun X Y h ↦ by simpa using congrArg (lieMap ContMDiffMonoidMorphism.fst) h
  exact ⟨B.cartanThreeForm_compLinearMap_ne_zero hani hinj
      SU2.not_isLieAbelian_leftInvariantDerivation,
    ContMDiffMonoidMorphism.not_nullhomotopic_of_injective_lieMap _ SU2.finrank_lieAlgebra
      SU2.not_isLieAbelian_leftInvariantDerivation hinj⟩

/-- **The root homomorphism `f : g ↦ (1, g)` of `SU(2) × SU(2)` is detected by the Cartan
three-form**, for the same reason: `f^*ω ≠ 0`, and `f` is not null-homotopic. -/
example : (B.cartanThreeForm hB).compLinearMap
      (lieMap (ContMDiffMonoidMorphism.inr (I := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
        (I' := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule)) (n := ∞) (G := GLSpecialUnitary (Fin 2) ℂ)
        (G' := GLSpecialUnitary (Fin 2) ℂ))).toLinearMap ≠ 0 ∧
    ¬((ContMDiffMonoidMorphism.inr (I := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
      (I' := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule)) (n := ∞) (G := GLSpecialUnitary (Fin 2) ℂ)
      (G' := GLSpecialUnitary (Fin 2) ℂ) :
        C(GLSpecialUnitary (Fin 2) ℂ, GLSpecialUnitary (Fin 2) ℂ × GLSpecialUnitary (Fin 2) ℂ)
        ).Nullhomotopic) := by
  -- The projection to the factor undoes the inclusion on Lie algebras, so its differential is
  -- injective.
  have hinj : Function.Injective (lieMap (ContMDiffMonoidMorphism.inr
      (I := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule)) (I' := 𝓘(ℝ, SU2.lieAlgebra.toSubmodule))
      (n := ∞) (G := GLSpecialUnitary (Fin 2) ℂ) (G' := GLSpecialUnitary (Fin 2) ℂ))) :=
    fun X Y h ↦ by simpa using congrArg (lieMap ContMDiffMonoidMorphism.snd) h
  exact ⟨B.cartanThreeForm_compLinearMap_ne_zero hani hinj
      SU2.not_isLieAbelian_leftInvariantDerivation,
    ContMDiffMonoidMorphism.not_nullhomotopic_of_injective_lieMap _ SU2.finrank_lieAlgebra
      SU2.not_isLieAbelian_leftInvariantDerivation hinj⟩

end RootHomomorphisms

/-! ### The rotation group `SO(3)` -/

/-- **`SO(3)` is not a torus**: it is not isomorphic, as a topological group, to any torus
`Fin r → Circle`, since tori are aspherical and `SO(3)` is not. With
`TauCeti.not_isAspherical_specialOrthogonalGroup_three`, both sides of the torus criterion fail
for `SO(3)`. -/
example :
    ¬∃ r : ℕ, Nonempty (specialOrthogonalGroup (Fin 3) ℝ ≃ₜ* (Fin r → Circle)) := by
  rintro ⟨r, ⟨e⟩⟩
  exact not_isAspherical_specialOrthogonalGroup_three 1
    ((Circle.isAspherical_pi 1).of_homotopyEquiv e.toHomeomorph.symm.toHomotopyEquiv 1)

end TauCeti
