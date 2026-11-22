/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.EssImage
public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.TotallyDisconnected
public import TauCeti.Topology.PathSpace.Moore.Covering
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import TauCeti.Algebra.AddCircle

/-!
# The DG local system of a covering map

Let `p : E → B` be a covering map and `b ∈ B`. Unique path lifting is the only lifting function of
`p` on Moore paths, and it is transitive (`IsCoveringMap.isTransitive`), so `p` has the DG local
system `C_*(F)_Φ` of its lifting function (`TauCeti.liftingLocalSystem`): the normalized cubical
chains of the fibre `F = p⁻¹(b)`, with the Moore loops at `b` acting through the lifts. This file
computes it.

The fibre `F` is discrete, so its chains vanish in positive dimensions: the DG local system is
concentrated in degree zero (`IsCoveringMap.isConcentratedInDegreeZero_liftingLocalSystem`), and as
a module it is the free module `F →₀ R` on the points of the fibre
(`IsCoveringMap.liftingLocalSystemEquiv`). A Moore loop `ω` acts on it through its point chain,
by moving each point of the fibre to the end of its lift along `ω`
(`IsCoveringMap.op_lof_point_smul_liftingLocalSystemEquiv`), which is the monodromy along the class
of `ω`. So the representation of the fundamental group carried by this DG local system in degree
zero (`TauCeti.DGRightModuleCat.IsConcentratedInDegreeZero.representation`), through which it is
the DG local system of a classical local system, is the permutation representation of the
monodromy action on the fibre: a class `g ∈ π₁(B, b)` sends the basis vector at `f ∈ F` to the
basis vector at the image of `f` under Mathlib's monodromy permutation
`IsCoveringMap.monodromyPerm` (`IsCoveringMap.representation_liftingLocalSystemEquiv_single`).

For the double cover `x ↦ 2 • x` of the circle `ℝ ⧸ ℤ` (`TauCeti.addCircleDoubleCover`) the fibre
over `0` has the two points `0` and `1 / 2` (`TauCeti.natCard_fiber_addCircleDoubleCover`), which
the generator of the fundamental group exchanges: the DG local system is `R²` in degree zero, with
the generator acting by the swap
(`TauCeti.representation_liftingLocalSystemEquiv_addCircleDoubleCover`). It is the permutation
module of the fibre, not the sign representation.

## Main definitions

* `IsCoveringMap.liftingLocalSystemEquiv`: the DG local system of a covering map is, as a module,
  the free module on the points of the fibre.
* `TauCeti.addCircleDoubleCover`: the double cover of the circle.

## Main results

* `IsCoveringMap.isConcentratedInDegreeZero_liftingLocalSystem`: the DG local system of a covering
  map is concentrated in degree zero.
* `IsCoveringMap.op_lof_point_smul_liftingLocalSystemEquiv`: a Moore loop acts on the basis of
  points by lifting.
* `IsCoveringMap.representation_liftingLocalSystemEquiv_single`: the representation of the
  fundamental group on it is the permutation representation of the monodromy.
* `TauCeti.representation_liftingLocalSystemEquiv_addCircleDoubleCover`: for the double cover of
  the circle, the generator swaps the two basis vectors.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (the monodromy action
  on the fibre of a covering).
-/

public section

noncomputable section

open MulOpposite TauCeti

universe u

namespace IsCoveringMap

section Module

open NormalizedCubicalChain

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
  (hp : IsCoveringMap p) (Φ : MooreLiftingFunction p) (b : B) (R : Type*) [CommRing R]

/-- **The DG local system of a covering map is concentrated in degree zero**: its fibre is
discrete, so its chains vanish in positive dimensions. -/
theorem isConcentratedInDegreeZero_liftingLocalSystem :
    (liftingLocalSystem (R := R) (hp.isTransitive Φ) b).IsConcentratedInDegreeZero :=
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  letI := (hp.isTransitive Φ).mulAction b
  letI := (hp.isTransitive Φ).continuousSMul b
  isConcentratedInDegreeZero_cubicalChainModuleDG _ _ R

/-- **The DG local system of a covering map is the free module on the fibre**: the basis vector at a
point `f` of the fibre is its point chain. -/
def liftingLocalSystemEquiv :
    ({e // p e = b} →₀ R) ≃ₗ[R] liftingLocalSystem (R := R) (hp.isTransitive Φ) b :=
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  cubicalChainModuleZeroEquiv _ _ R

variable {R}

/-- The basis vector at a point of the fibre is the point chain of that point. -/
@[simp]
theorem liftingLocalSystemEquiv_single (f : {e // p e = b}) (r : R) :
    hp.liftingLocalSystemEquiv Φ b R (Finsupp.single f r) =
      r • cubicalChainModulePoint {e // p e = b} (MooreLoopSpace B b) R f :=
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  cubicalChainModuleZeroEquiv_single f r

/-- **A Moore loop acts on the fibre of a covering map by lifting**: the point chain of a Moore loop
`ω` at `b` acts on the DG local system, read in the basis of points of the fibre, by sending each
point `f` to the end of the lift of `ω` from `f`. -/
theorem op_lof_point_smul_liftingLocalSystemEquiv (ω : MooreLoopSpace B b)
    (x : {e // p e = b} →₀ R) :
    letI := (hp.isTransitive Φ).mulAction b
    letI := (hp.isTransitive Φ).continuousSMul b
    op (cubicalChainLof (MooreLoopSpace B b) R 0 (ofCube _ R (SingularCube.point ω))) •
        hp.liftingLocalSystemEquiv Φ b R x =
      hp.liftingLocalSystemEquiv Φ b R (Finsupp.mapDomain (Φ.fiberAct b · ω) x) :=
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  letI := (hp.isTransitive Φ).mulAction b
  letI := (hp.isTransitive Φ).continuousSMul b
  op_lof_point_smul_cubicalChainModuleZeroEquiv ω x

end Module

section Representation

open NormalizedCubicalChain

variable {E : Type u} {B : TopCat.{u}} [TopologicalSpace E] {p : C(E, B)} (hp : IsCoveringMap p)
  (Φ : MooreLiftingFunction p) (b : B) {R : Type u} [CommRing R]

/-- **The DG local system of a covering map is the permutation module of the monodromy**: the
representation of `π₁(B, b)` through which the DG local system, concentrated in degree zero, is
classical sends the basis vector at a point `f` of the fibre to the basis vector at the image of `f`
under the monodromy permutation of the class. -/
theorem representation_liftingLocalSystemEquiv_single (g : FundamentalGroup B b)
    (f : {e // p e = b}) (r : R) :
    (hp.isConcentratedInDegreeZero_liftingLocalSystem Φ b R).representation g
        (hp.liftingLocalSystemEquiv Φ b R (Finsupp.single f r)) =
      hp.liftingLocalSystemEquiv Φ b R (Finsupp.single
        ⟨hp.monodromyPerm b g ⟨f, f.property⟩, (hp.monodromyPerm b g ⟨f, f.property⟩).property⟩
        r) := by
  obtain ⟨γ, hγ⟩ := MooreLoopSpace.fundamentalGroupHom_surjective b g⁻¹
  obtain rfl : g = (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ := by rw [hγ, inv_inv]
  rw [DGRightModuleCat.IsConcentratedInDegreeZero.representation_fundamentalGroupHom_inv_apply]
  refine (hp.op_lof_point_smul_liftingLocalSystemEquiv Φ b γ _).trans ?_
  rw [Finsupp.mapDomain_single]
  congr 2
  exact Subtype.ext (hp.coe_fiberAct_eq_monodromyPerm Φ b f γ)

end Representation

end IsCoveringMap

namespace TauCeti

/-! ### The double cover of the circle -/

/-- The **double cover of the circle** `x ↦ 2 • x` of `ℝ ⧸ ℤ`, with its target read as a
topological space in `TopCat`, where the DG local systems of a covering live. -/
def addCircleDoubleCover : C(AddCircle (1 : ℝ), TopCat.of (AddCircle (1 : ℝ))) :=
  ⟨fun x ↦ 2 • x, continuous_id.nsmul 2⟩

@[simp]
theorem addCircleDoubleCover_apply (x : AddCircle (1 : ℝ)) : addCircleDoubleCover x = 2 • x :=
  (rfl)

/-- The doubling map of the circle is a covering map. -/
theorem isCoveringMap_addCircleDoubleCover : IsCoveringMap addCircleDoubleCover :=
  (AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 2).isCoveringMap

/-- **The fibre of the double cover over `0` has the two points `0` and `1 / 2`.** -/
theorem addCircleDoubleCover_eq_zero_iff (x : AddCircle (1 : ℝ)) :
    addCircleDoubleCover x = ((0 : ℝ) : AddCircle (1 : ℝ)) ↔
      x = ((0 : ℝ) : AddCircle (1 : ℝ)) ∨ x = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [addCircleDoubleCover_apply, AddCircle.coe_zero]
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa using AddCircle.eq_zero_or_eq_coe_period_div_two (1 : ℝ) two_ne_zero
      (by rwa [ofNat_zsmul])
  · rintro (rfl | rfl)
    · simp
    · rw [← AddCircle.coe_nsmul]
      norm_num [AddCircle.coe_period]

/-- **The fibre of the double cover over `0` has two points**: it is the `2`-torsion of the
circle (`AddCircle.natCard_torsionBy`). -/
theorem natCard_fiber_addCircleDoubleCover :
    Nat.card {x // addCircleDoubleCover x = ((0 : ℝ) : AddCircle (1 : ℝ))} = 2 := by
  rw [← AddCircle.natCard_torsionBy (1 : ℝ) (n := 2)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)
  rw [addCircleDoubleCover_apply, AddCircle.coe_zero, AddSubgroup.torsionBy.nsmul_iff]

/-- `0` lies in the fibre of the double cover over `0`. -/
theorem addCircleDoubleCover_zero :
    addCircleDoubleCover ((0 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) :=
  (addCircleDoubleCover_eq_zero_iff _).2 (Or.inl rfl)

/-- `1 / 2` lies in the fibre of the double cover over `0`. -/
theorem addCircleDoubleCover_half :
    addCircleDoubleCover ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) :=
  (addCircleDoubleCover_eq_zero_iff _).2 (Or.inr rfl)

/-- **The generator of the fundamental group moves `0` to `1 / 2`**: the loop `t ↦ t` of the circle
lifts along the double cover from `0` to the path `t ↦ t / 2`. -/
theorem coe_monodromyPerm_addCircleDoubleCover_zero :
    (isCoveringMap_addCircleDoubleCover.monodromyPerm _
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1)))
        ⟨_, addCircleDoubleCover_zero⟩ : AddCircle (1 : ℝ)) =
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [IsCoveringMap.coe_monodromyPerm]
  refine isCoveringMap_addCircleDoubleCover.monodromy_eq_apply_one
    (Γ := ⟨fun t ↦ ((t / 2 : ℝ) : AddCircle (1 : ℝ)), by fun_prop⟩) ?_ ?_
  · funext t
    have h : (2 • ((t : ℝ) / 2) : ℝ) = t := by rw [nsmul_eq_mul]; push_cast; ring
    rw [Function.comp_apply, addCircleDoubleCover_apply, ContinuousMap.coe_mk,
      ← AddCircle.coe_nsmul, h, AddCircle.zsmulLoop_apply]
    simp
  · simp

/-- **The generator of the fundamental group moves `1 / 2` back to `0`**: the loop `t ↦ t` of the
circle lifts along the double cover from `1 / 2` to the path `t ↦ (1 + t) / 2`. -/
theorem coe_monodromyPerm_addCircleDoubleCover_half :
    (isCoveringMap_addCircleDoubleCover.monodromyPerm _
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1)))
        ⟨_, addCircleDoubleCover_half⟩ : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [IsCoveringMap.coe_monodromyPerm]
  refine (isCoveringMap_addCircleDoubleCover.monodromy_eq_apply_one
    (Γ := ⟨fun t ↦ (((1 + t) / 2 : ℝ) : AddCircle (1 : ℝ)), by fun_prop⟩) ?_ ?_).trans ?_
  · funext t
    have h : (2 • ((1 + (t : ℝ)) / 2) : ℝ) = t + 1 := by rw [nsmul_eq_mul]; push_cast; ring
    rw [Function.comp_apply, addCircleDoubleCover_apply, ContinuousMap.coe_mk,
      ← AddCircle.coe_nsmul, h, AddCircle.coe_add_period, AddCircle.zsmulLoop_apply]
    simp
  · simp
  · norm_num [AddCircle.coe_period]

/-- **The DG local system of the double cover of the circle is the permutation module of the
fibre**: the generator of the fundamental group exchanges the basis vectors at the two points `0`
and `1 / 2` of the fibre over `0`. So the DG local system is `R²` in degree zero with the generator
acting by the swap, not by a sign. -/
theorem representation_liftingLocalSystemEquiv_addCircleDoubleCover {R : Type} [CommRing R]
    (Φ : MooreLiftingFunction addCircleDoubleCover) (r : R) :
    let hM := isCoveringMap_addCircleDoubleCover.isConcentratedInDegreeZero_liftingLocalSystem Φ
      ((0 : ℝ) : AddCircle (1 : ℝ)) R
    let e := isCoveringMap_addCircleDoubleCover.liftingLocalSystemEquiv Φ
      ((0 : ℝ) : AddCircle (1 : ℝ)) R
    let g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1))
    hM.representation g (e (Finsupp.single ⟨_, addCircleDoubleCover_zero⟩ r)) =
        e (Finsupp.single ⟨_, addCircleDoubleCover_half⟩ r) ∧
      hM.representation g (e (Finsupp.single ⟨_, addCircleDoubleCover_half⟩ r)) =
        e (Finsupp.single ⟨_, addCircleDoubleCover_zero⟩ r) := by
  refine ⟨?_, ?_⟩ <;>
  · rw [IsCoveringMap.representation_liftingLocalSystemEquiv_single]
    congr 2
    exact Subtype.ext (by first
      | exact coe_monodromyPerm_addCircleDoubleCover_zero
      | exact coe_monodromyPerm_addCircleDoubleCover_half)

end TauCeti
