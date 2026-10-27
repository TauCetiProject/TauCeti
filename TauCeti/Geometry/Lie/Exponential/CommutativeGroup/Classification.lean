/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import TauCeti.Algebra.Module.ZLattice.Quotient
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Compact connected commutative Lie groups are products of circles

For a compact connected commutative finite-dimensional real Lie group, a basis of the
exponential kernel gives circle coordinates: take the real coordinates of a logarithm modulo
the integral lattice. This identifies the group with a product of circles as topological
groups, with one factor for each dimension of the manifold model.

The basis-dependent equivalences include their values on exponentials, so that circle
coordinates and their inverses can be computed without choosing a logarithm.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori).
-/

public section

noncomputable section

open TauCeti
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]
  [IsMulCommutative G] [IsTopologicalGroup G] [CompactSpace G] [PreconnectedSpace G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

noncomputable local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

namespace Module.Basis

variable {ι : Type*} [Fintype ι]
  (b : Module.Basis ι ℤ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule)

/-- Additive circle coordinates of a compact connected commutative Lie group, specified by a
basis of its exponential kernel. -/
def lieGroupUnitAddTorusEquiv : Additive G ≃ₜ+ UnitAddTorus ι :=
  (lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm.trans b.quotientLatticeEquiv

/-- Exponentiating a Lie algebra element reduces its lattice-basis coordinates modulo one. -/
@[simp]
theorem lieGroupUnitAddTorusEquiv_apply_lieExp (X : LeftInvariantDerivation I G) (i : ι) :
    lieGroupUnitAddTorusEquiv b (Additive.ofMul (lieExp X)) i =
      ((b.ofZLatticeBasis ℝ _).repr X i : UnitAddCircle) := by
  rw [lieGroupUnitAddTorusEquiv, ContinuousAddEquiv.trans_apply,
    lieExpQuotientKerContinuousAddEquiv_symm_apply, Module.Basis.quotientLatticeEquiv_apply_mk]

/-- The inverse additive circle coordinates exponentiate the corresponding real linear
combination of lattice basis vectors. -/
@[simp]
theorem lieGroupUnitAddTorusEquiv_symm_apply (x : ι → ℝ) :
    (lieGroupUnitAddTorusEquiv b).symm (fun i => (x i : UnitAddCircle)) =
      Additive.ofMul (lieExp ((b.ofZLatticeBasis ℝ _).equivFun.symm x)) := by
  apply (lieGroupUnitAddTorusEquiv b).injective
  ext i
  simp only [ContinuousAddEquiv.apply_symm_apply, lieGroupUnitAddTorusEquiv_apply_lieExp,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/-- Circle coordinates of a compact connected commutative Lie group. Each integral period in
the chosen exponential-kernel basis becomes one full turn in the corresponding circle. -/
def lieGroupCircleEquiv : G ≃ₜ* (ι → Circle) :=
  let e := lieGroupUnitAddTorusEquiv b
  let c := Homeomorph.piCongrRight fun _ : ι =>
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  { toFun := fun g => c (e (Additive.ofMul g))
    invFun := fun z => Additive.toMul (e.symm (c.symm z))
    left_inv := fun g => by simp
    right_inv := fun z => by simp
    continuous_toFun := c.continuous.comp (e.continuous.comp continuous_ofMul)
    continuous_invFun := continuous_toMul.comp (e.symm.continuous.comp c.symm.continuous)
    map_mul' := fun x y => by
      rw [ofMul_mul, map_add]
      apply funext
      intro i
      simp only [c, Homeomorph.piCongrRight_apply, AddCircle.homeomorphCircle_apply,
        Pi.add_apply, AddCircle.toCircle_add, Pi.mul_apply] }

/-- Multiplicative circle coordinates are the canonical unit-circle images of additive ones. -/
theorem lieGroupCircleEquiv_apply (g : G) (i : ι) :
    lieGroupCircleEquiv b g i =
      AddCircle.toCircle (lieGroupUnitAddTorusEquiv b (Additive.ofMul g) i) := by
  change (Homeomorph.piCongrRight fun _ : ι =>
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)) _ i = _
  rw [Homeomorph.piCongrRight_apply, AddCircle.homeomorphCircle_apply]

/-- In circle coordinates, the exponential is the coordinatewise complex exponential, with
period one in the chosen lattice basis. -/
@[simp]
theorem lieGroupCircleEquiv_apply_lieExp (X : LeftInvariantDerivation I G) (i : ι) :
    lieGroupCircleEquiv b (lieExp X) i =
      Circle.exp (2 * Real.pi * (b.ofZLatticeBasis ℝ _).repr X i) := by
  rw [lieGroupCircleEquiv_apply, lieGroupUnitAddTorusEquiv_apply_lieExp,
    AddCircle.toCircle_apply_mk]
  simp only [div_one]

/-- The inverse circle coordinates exponentiate the real linear combination of lattice basis
vectors. -/
@[simp]
theorem lieGroupCircleEquiv_symm_apply (x : ι → ℝ) :
    (lieGroupCircleEquiv b).symm (fun i => Circle.exp (2 * Real.pi * x i)) =
      lieExp ((b.ofZLatticeBasis ℝ _).equivFun.symm x) := by
  apply (lieGroupCircleEquiv b).injective
  apply funext
  intro i
  simp only [ContinuousMulEquiv.apply_symm_apply, lieGroupCircleEquiv_apply_lieExp,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end Module.Basis

namespace TauCeti

omit [IsTopologicalGroup G] in
include I in
/-- A compact connected commutative finite-dimensional real Lie group is a product of circles,
with one factor for every dimension of its manifold model. -/
theorem nonempty_continuousMulEquiv_pi_circle :
    Nonempty (G ≃ₜ* (Fin (Module.finrank ℝ E) → Circle)) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let L := (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule
  let _ : Module.Free ℤ L := ZLattice.module_free ℝ L
  let _ : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hdim : Module.finrank ℤ L = Module.finrank ℝ E :=
    (finrank_ker_lieExpAddMonoidHom (I := I) (G := G)).trans
      (finrank_leftInvariantDerivation_eq_modelVectorSpace
        (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)))
  exact ⟨Module.Basis.lieGroupCircleEquiv (Module.finBasisOfFinrankEq ℤ L hdim)⟩

end TauCeti
