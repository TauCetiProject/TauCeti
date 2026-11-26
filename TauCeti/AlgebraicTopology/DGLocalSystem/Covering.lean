/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.EssImage
public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Augmentation
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.TotallyDisconnected
public import TauCeti.Topology.Circle.DoubleCover
public import TauCeti.Topology.Covering.AddCircle
public import TauCeti.Topology.PathSpace.Moore.Covering

/-!
# The DG local system of a covering map

Let `p : E → B` be a covering map and `b ∈ B`. Its unique Moore lifting function is transitive
(`IsCoveringMap.isTransitive`), so the Moore loops at `b` act strictly on the fibre
`F = p⁻¹(b)` and its normalized cubical chains form the DG local system `C_*(F)_Φ`
(`TauCeti.liftingLocalSystem`). This file identifies that DG local system.

The fibre of a covering map is discrete, so its chains vanish in positive dimension and
`C_*(F)_Φ` is concentrated in degree zero
(`IsCoveringMap.isConcentratedInDegreeZero_liftingLocalSystem`): it is the free module `R[F]` on
the sheets, and a Moore loop acts on a sheet by lifting the loop from it, that is by monodromy
(`IsCoveringMap.coe_fiberAct_eq_monodromy`). So `C_*(F)_Φ` is the DG local system of the
classical **permutation local system** of the covering, whose fibre over `x` is the free module on
`p⁻¹(x)` with transport the linear extension of monodromy
(`IsCoveringMap.liftingLocalSystemPermutationIso`, on the classical side
`IsCoveringMap.permutationLocalSystem` and `TauCeti.classicalDGLocalSystem`). In other words, the DG
local system of a covering map is the permutation module of the monodromy action of `π₁(B, b)` on
the fibre, placed in degree zero.

For the double cover `z ↦ z²` of the circle, the lift of the loop `t ↦ exp(2πit)` from `1` is the
half turn `t ↦ exp(πit)`, which ends at `-1`; so the generator of `π₁(S¹)` exchanges the two
sheets `±1` (`Circle.coe_monodromy_sq_expLoop`, in `TauCeti.Topology.Circle.DoubleCover`), and it
acts on the point chains of `C_*(F)_Φ` by swapping `[1]` and `[-1]`
(`Circle.representation_liftingLocalSystem_sq`). The DG local system of this cover is the rank-two
permutation module `R[ℤ/2]` with the generator acting by the swap, not the trivial module and not
the rank-one sign representation.

In the basis of points of the fibre (`IsCoveringMap.liftingLocalSystemEquiv`), the point chain of
a Moore loop `ω` moves each point of the fibre to the end of its lift along `ω`
(`IsCoveringMap.op_cubicalChainPoint_smul_liftingLocalSystemEquiv`), and a class
`g ∈ π₁(B, b)` acts through Mathlib's monodromy permutation `IsCoveringMap.monodromyPerm`
(`IsCoveringMap.representation_liftingLocalSystemEquiv_single`). For the double cover
`x ↦ 2 • x` of the circle `ℝ ⧸ ℤ` (`TauCeti.addCircleDoubleCover`), whose fibre over `0` is
`{0, 1 / 2}`, the generator swaps the two basis vectors
(`TauCeti.representation_liftingLocalSystemEquiv_addCircleDoubleCover`).

## Main definitions

* `IsCoveringMap.liftingLocalSystemPermutationIso`: the DG local system of a covering map is the DG
  local system of its permutation local system.
* `IsCoveringMap.liftingLocalSystemEquiv`: the DG local system of a covering map is, as a module,
  the free module on the points of the fibre.

## Main results

* `IsCoveringMap.isConcentratedInDegreeZero_liftingLocalSystem`: the DG local system of a covering
  map is concentrated in degree zero.
* `IsCoveringMap.liftingLocalSystemPermutationIso_hom_apply_lof_ofCube_point`: the identification
  sends the `0`-chain of a sheet to that sheet.
* `IsCoveringMap.liftingLocalSystemPermutationIso_inv_apply_single`: conversely, its inverse sends a
  sheet to the `0`-chain of that sheet.
* `Circle.representation_liftingLocalSystem_sq`: for the double cover of the circle, the generator
  of the fundamental group exchanges the two point chains of the DG local system.
* `IsCoveringMap.op_cubicalChainPoint_smul_liftingLocalSystemEquiv`: a Moore loop acts on the
  basis of points by lifting.
* `IsCoveringMap.representation_liftingLocalSystemEquiv_single`: the representation of the
  fundamental group on it is the permutation representation of the monodromy.
* `TauCeti.representation_liftingLocalSystemEquiv_addCircleDoubleCover`: for the double cover of
  `ℝ ⧸ ℤ`, the generator swaps the two basis vectors.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (the monodromy action
  on the fibre of a covering) and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory MulOpposite TauCeti NormalizedCubicalChain

universe u

namespace IsCoveringMap

section Degree

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
  (hp : IsCoveringMap p) (R : Type*) [CommRing R]

/-- **The DG local system of a covering map is concentrated in degree zero**: its fibre is
discrete, so its chains of positive dimension vanish. -/
theorem isConcentratedInDegreeZero_liftingLocalSystem (Φ : MooreLiftingFunction p) (b : B) :
    (liftingLocalSystem (R := R) (hp.isTransitive Φ) b).IsConcentratedInDegreeZero :=
  let _ := (hp.isTransitive Φ).mulAction b
  let _ := (hp.isTransitive Φ).continuousSMul b
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  isConcentratedInDegreeZero_cubicalChainModuleDG _ _ R

variable (Φ : MooreLiftingFunction p) (b : B)

/-- **The DG local system of a covering map is the free module on the fibre**: the basis vector at a
point `f` of the fibre is its point chain. -/
def liftingLocalSystemEquiv :
    ({e // p e = b} →₀ R) ≃ₗ[R] liftingLocalSystem (R := R) (hp.isTransitive Φ) b :=
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  (cubicalChainModuleFinsuppEquiv _ _ R).symm

variable {R}

/-- The basis vector at a point of the fibre is the point chain of that point. -/
@[simp]
theorem liftingLocalSystemEquiv_single (f : {e // p e = b}) (r : R) :
    hp.liftingLocalSystemEquiv R Φ b (Finsupp.single f r) =
      r • cubicalChainModulePoint {e // p e = b} (MooreLoopSpace B b) R f := by
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  rw [liftingLocalSystemEquiv, cubicalChainModuleFinsuppEquiv_symm_single,
    cubicalChainModulePoint_def]

/-- **A Moore loop acts on the fibre of a covering map by lifting**: the point chain of a Moore loop
`ω` at `b` acts on the DG local system, read in the basis of points of the fibre, by sending each
point `f` to the end of the lift of `ω` from `f`. -/
theorem op_cubicalChainPoint_smul_liftingLocalSystemEquiv (ω : MooreLoopSpace B b)
    (x : {e // p e = b} →₀ R) :
    letI := (hp.isTransitive Φ).mulAction b
    letI := (hp.isTransitive Φ).continuousSMul b
    op (cubicalChainPoint (MooreLoopSpace B b) R ω) • hp.liftingLocalSystemEquiv R Φ b x =
      hp.liftingLocalSystemEquiv R Φ b (Finsupp.mapDomain (Φ.fiberAct b · ω) x) := by
  have : DiscreteTopology {e // p e = b} := (hp b).discreteTopology_fiber
  let := (hp.isTransitive Φ).mulAction b
  let := (hp.isTransitive Φ).continuousSMul b
  apply (cubicalChainModuleFinsuppEquiv _ (MooreLoopSpace B b) R).injective
  simp only [liftingLocalSystemEquiv, cubicalChainPoint_def, cubicalChainModuleFinsuppEquiv_op_smul,
    LinearEquiv.apply_symm_apply, MooreLiftingFunction.IsTransitive.op_smul_eq_fiberAct]

end Degree

section Basis

variable {E : Type u} {B : TopCat.{u}} [TopologicalSpace E] {p : C(E, B)} (hp : IsCoveringMap p)
  (Φ : MooreLiftingFunction p) (b : B) {R : Type u} [CommRing R]

/-- **The DG local system of a covering map is the permutation module of the monodromy**: the
representation of `π₁(B, b)` through which the DG local system, concentrated in degree zero, is
classical sends the basis vector at a point `f` of the fibre to the basis vector at the image of `f`
under the monodromy permutation of the class. -/
theorem representation_liftingLocalSystemEquiv_single (g : FundamentalGroup B b)
    (f : {e // p e = b}) (r : R) :
    (hp.isConcentratedInDegreeZero_liftingLocalSystem R Φ b).representation g
        (hp.liftingLocalSystemEquiv R Φ b (Finsupp.single f r)) =
      hp.liftingLocalSystemEquiv R Φ b (Finsupp.single
        ⟨hp.monodromyPerm b g ⟨f, f.property⟩, (hp.monodromyPerm b g ⟨f, f.property⟩).property⟩
        r) := by
  obtain ⟨γ, hγ⟩ := MooreLoopSpace.fundamentalGroupHom_surjective b g⁻¹
  obtain rfl : g = (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ := by rw [hγ, inv_inv]
  rw [DGRightModuleCat.IsConcentratedInDegreeZero.representation_fundamentalGroupHom_inv_apply]
  refine (hp.op_cubicalChainPoint_smul_liftingLocalSystemEquiv Φ b γ _).trans ?_
  rw [Finsupp.mapDomain_single]
  congr 2
  exact Subtype.ext (hp.coe_fiberAct_eq_monodromyPerm Φ b f γ)

end Basis

section Permutation

variable {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) (R : Type u) [CommRing R]
  (Φ : MooreLiftingFunction p.hom) (b : B)

/-- **A class of loops acts on the `0`-chain of a sheet by monodromy**: in the representation of
`π₁(B, b)` on the DG local system of a covering map, a class `g` sends the `0`-chain of a sheet `f`
over `b` to the `0`-chain of its image under the monodromy of `g`. -/
@[simp]
theorem representation_liftingLocalSystem_lof_ofCube_point (g : FundamentalGroup B b)
    (f : {e // p.hom e = b}) :
    (hp.isConcentratedInDegreeZero_liftingLocalSystem R Φ b).representation g
        (cubicalChainModuleLof _ (MooreLoopSpace B b) R 0 (ofCube _ R (SingularCube.point f))) =
      cubicalChainModuleLof _ (MooreLoopSpace B b) R 0 (ofCube _ R (SingularCube.point
        ⟨_, (hp.monodromy g.asHom ⟨f, f.property⟩).property⟩)) := by
  obtain ⟨γ, hγ⟩ := MooreLoopSpace.fundamentalGroupHom_surjective b g⁻¹
  rw [← inv_inv g, ← hγ,
    DGRightModuleCat.IsConcentratedInDegreeZero.representation_fundamentalGroupHom_inv_apply,
    cubicalChainPoint_def]
  let _ := (hp.isTransitive Φ).mulAction b
  let _ := (hp.isTransitive Φ).continuousSMul b
  refine (op_lof_smul_cubicalChainModuleLof (Y := {e // p.hom e = b}) _ _).trans ?_
  rw [act_ofCube_point]
  congr 3
  refine Subtype.ext ((hp.coe_fiberAct_eq_monodromyPerm Φ b f γ).trans ?_)
  rw [coe_monodromyPerm]

/-- The chains on the fibre over `b` are the free module on the sheets over `b`. -/
private def chainEquiv :
    (liftingLocalSystem (R := R) (hp.isTransitive Φ) b : Type u) ≃ₗ[R]
      (hp.permutationLocalSystem R).obj (FundamentalGroupoid.mk b) :=
  have : DiscreteTopology {e // p.hom e = b} := (hp b).discreteTopology_fiber
  cubicalChainModuleFinsuppEquiv {e // p.hom e = b} (MooreLoopSpace B b) R ≪≫ₗ
    Finsupp.domLCongr (M := R) (R := R) (Equiv.subtypeEquivRight fun _ ↦ Set.mem_singleton_iff.symm)

private theorem chainEquiv_lof_ofCube_point (f : {e // p.hom e = b}) :
    chainEquiv hp R Φ b (cubicalChainModuleLof _ (MooreLoopSpace B b) R 0
        (ofCube _ R (SingularCube.point f))) =
      Finsupp.single ⟨f, f.property⟩ 1 := by
  have : DiscreteTopology {e // p.hom e = b} := (hp b).discreteTopology_fiber
  -- `chainEquiv` is the composite of its two factors by definition, and the sheet `f` read in the
  -- preimage of `b` is `⟨f, f.property⟩`.
  exact (congrArg (Finsupp.domLCongr (M := R) (R := R)
      (Equiv.subtypeEquivRight fun _ ↦ Set.mem_singleton_iff.symm))
    (cubicalChainModuleFinsuppEquiv_lof_ofCube_point (G := MooreLoopSpace B b) (R := R) f)).trans
    (Finsupp.domLCongr_single _ _ _)

/-- The representation of `π₁(B, b)` on the DG local system of a covering map is the permutation
representation of the monodromy action on the sheets. -/
private def representationEquiv :
    (hp.isConcentratedInDegreeZero_liftingLocalSystem R Φ b).representation.Equiv
      (LocalCoefficientSystem.monodromyRepresentation (hp.permutationLocalSystem R) b) :=
  .mk (chainEquiv hp R Φ b) fun g ↦ LinearMap.ext fun m ↦ by
    have : DiscreteTopology {e // p.hom e = b} := (hp b).discreteTopology_fiber
    -- Check the intertwining on the basis of `0`-chains of points.
    rw [← (cubicalChainModuleFinsuppEquiv _ (MooreLoopSpace B b) R).symm_apply_apply m]
    induction cubicalChainModuleFinsuppEquiv _ (MooreLoopSpace B b) R m using
      Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add a c ha hc => simp only [map_add, ha, hc]
    | single f r =>
      rw [cubicalChainModuleFinsuppEquiv_symm_single, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, map_smul, map_smul, map_smul, map_smul,
        representation_liftingLocalSystem_lof_ofCube_point hp R Φ b, chainEquiv_lof_ofCube_point,
        chainEquiv_lof_ofCube_point]
      exact congrArg (r • ·) ((LocalCoefficientSystem.monodromyRepresentation_apply _ b g _).trans
        (hp.permutationLocalSystem_map_single R g.asHom _ 1)).symm

/-- **The DG local system of a covering map is its permutation local system**: the chains on the
fibre of `p` over `b`, with the Moore loops acting through the lifting function, are the free
module on the sheets over `b`, concentrated in degree zero, with a loop acting by the monodromy of
its class. -/
def liftingLocalSystemPermutationIso [PathConnectedSpace B] :
    liftingLocalSystem (R := R) (hp.isTransitive Φ) b ≅
      classicalDGLocalSystem b (hp.permutationLocalSystem R) :=
  (hp.isConcentratedInDegreeZero_liftingLocalSystem R Φ b).classicalDGLocalSystemIso.symm ≪≫
    (classicalDGLocalSystemFunctor R b).mapIso
      (LocalCoefficientSystem.ofRepresentationIso b (representationEquiv hp R Φ b) ≪≫
        LocalCoefficientSystem.ofRepresentationMonodromyIso b (hp.permutationLocalSystem R))

/-- **The identification sends the `0`-chain of a sheet to that sheet.** -/
@[simp]
theorem liftingLocalSystemPermutationIso_hom_apply_lof_ofCube_point [PathConnectedSpace B]
    (f : {e // p.hom e = b}) :
    (hp.liftingLocalSystemPermutationIso R Φ b).hom
        (cubicalChainModuleLof _ (MooreLoopSpace B b) R 0 (ofCube _ R (SingularCube.point f))) =
      Finsupp.single ⟨f, f.property⟩ 1 := by
  have hmon (v) : ((LocalCoefficientSystem.ofRepresentationMonodromyIso b
      (hp.permutationLocalSystem R)).hom.app (FundamentalGroupoid.mk b)).hom v = v := by
    rw [← Iso.app_hom, LocalCoefficientSystem.ofRepresentationMonodromyIso_app_mk, Iso.refl_hom]
    -- `ModuleCat.id_apply` does not apply syntactically: the identity is typed at the fibre of
    -- `ofRepresentation`, equal to that of the permutation local system only by unfolding.
    rfl
  refine (DGRightModuleCat.comp_apply _ _ _).trans ?_
  rw [Iso.symm_hom,
    DGRightModuleCat.IsConcentratedInDegreeZero.classicalDGLocalSystemIso_inv_apply]
  refine (classicalDGLocalSystemMap_apply _ _).trans ?_
  rw [Iso.trans_hom, NatTrans.comp_app]
  exact (hmon _).trans ((LocalCoefficientSystem.ofRepresentationIso_hom_app_apply b _ _ _).trans
    (chainEquiv_lof_ofCube_point hp R Φ b f))

/-- **The inverse identification sends a sheet to the `0`-chain of that sheet.** -/
@[simp]
theorem liftingLocalSystemPermutationIso_inv_apply_single [PathConnectedSpace B]
    (f : {e // p.hom e = b}) (r : R) :
    (hp.liftingLocalSystemPermutationIso R Φ b).inv (Finsupp.single ⟨f, f.property⟩ r) =
      r • cubicalChainModuleLof _ (MooreLoopSpace B b) R 0 (ofCube _ R (SingularCube.point f)) := by
  have h : (hp.liftingLocalSystemPermutationIso R Φ b).hom
      (r • cubicalChainModuleLof _ (MooreLoopSpace B b) R 0 (ofCube _ R (SingularCube.point f))) =
        Finsupp.single ⟨f, f.property⟩ r := by
    -- The identification is `R`-linear: its underlying `R`-linear map is its image under
    -- `DGRightModuleCat.forgetToModuleCat`.
    exact ((DGRightModuleCat.forgetToModuleCat.map
        (hp.liftingLocalSystemPermutationIso R Φ b).hom).hom.map_smul r _).trans
      ((congrArg (r • ·)
        (hp.liftingLocalSystemPermutationIso_hom_apply_lof_ofCube_point R Φ b f)).trans
          (Finsupp.smul_single_one _ r))
  rw [← h, ← DGRightModuleCat.comp_apply, Iso.hom_inv_id, DGRightModuleCat.id_apply]

end Permutation

end IsCoveringMap

namespace Circle

open Real

/-- **The DG local system of the double cover of the circle is the permutation module of the
swap**: the generator of `π₁(S¹)`, the class of `t ↦ exp(2πit)`, sends the `0`-chain of the sheet
`z` of the fibre of `z ↦ z²` over `1` to the `0`-chain of the sheet `-z`. So it exchanges the two
point chains `[1]` and `[-1]`. -/
theorem representation_liftingLocalSystem_sq (z : Circle) (hz : z ^ 2 = 1) {R : Type}
    [CommRing R]
    (Φ : MooreLiftingFunction
      (TopCat.ofHom (⟨(· ^ 2), continuous_pow 2⟩ : C(Circle, Circle))).hom) :
    ((isQuotientCoveringMap_npow 2).isCoveringMap.isConcentratedInDegreeZero_liftingLocalSystem R Φ
        (1 : TopCat.of Circle)).representation
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk expLoop))
        (cubicalChainModuleLof _ _ R 0 (ofCube _ R (SingularCube.point ⟨z, hz⟩))) =
      cubicalChainModuleLof _ _ R 0
        (ofCube _ R (SingularCube.point ⟨-z, (by rw [neg_sq]; exact hz : (-z) ^ 2 = 1)⟩)) := by
  refine (IsCoveringMap.representation_liftingLocalSystem_lof_ofCube_point
    (isQuotientCoveringMap_npow 2).isCoveringMap R Φ (1 : TopCat.of Circle) _ ⟨z, hz⟩).trans ?_
  congr 3
  exact Subtype.ext (coe_monodromy_sq_expLoop z hz)

end Circle

namespace TauCeti

/-! ### The double cover of `ℝ ⧸ ℤ` -/

/-- **The DG local system of the double cover of `ℝ ⧸ ℤ` is the permutation module of the
fibre**: the generator of the fundamental group exchanges the basis vectors at the two points `0`
and `1 / 2` of the fibre over `0`. So the DG local system is `R²` in degree zero with the generator
acting by the swap, not by a sign. The target of the double cover is read in `TopCat`, where the
DG local systems of a covering live. -/
theorem representation_liftingLocalSystemEquiv_addCircleDoubleCover {R : Type} [CommRing R]
    (Φ : MooreLiftingFunction (B := TopCat.of (AddCircle (1 : ℝ))) addCircleDoubleCover) (r : R) :
    let hM := isCoveringMap_addCircleDoubleCover.isConcentratedInDegreeZero_liftingLocalSystem R Φ
      (B := TopCat.of (AddCircle (1 : ℝ))) ((0 : ℝ) : AddCircle (1 : ℝ))
    let e := isCoveringMap_addCircleDoubleCover.liftingLocalSystemEquiv R Φ
      (B := TopCat.of (AddCircle (1 : ℝ))) ((0 : ℝ) : AddCircle (1 : ℝ))
    let g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1))
    hM.representation g (e (Finsupp.single ⟨_, addCircleDoubleCover_zero⟩ r)) =
        e (Finsupp.single ⟨_, addCircleDoubleCover_half⟩ r) ∧
      hM.representation g (e (Finsupp.single ⟨_, addCircleDoubleCover_half⟩ r)) =
        e (Finsupp.single ⟨_, addCircleDoubleCover_zero⟩ r) := by
  constructor
  · rw [IsCoveringMap.representation_liftingLocalSystemEquiv_single]
    congr 2
    exact Subtype.ext coe_monodromyPerm_addCircleDoubleCover_zero
  · rw [IsCoveringMap.representation_liftingLocalSystemEquiv_single]
    congr 2
    exact Subtype.ext coe_monodromyPerm_addCircleDoubleCover_half

end TauCeti
