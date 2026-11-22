/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.EssImage
public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.TotallyDisconnected
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Inner
public import TauCeti.Topology.Circle.Degree
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
(`IsCoveringMap.liftingLocalSystemIso`, on the classical side `IsCoveringMap.permutationLocalSystem`
and `TauCeti.classicalDGLocalSystem`). In other words, the DG local system of a covering map is
the permutation module of the monodromy action of `π₁(B, b)` on the fibre, placed in degree zero.

For the double cover `z ↦ z²` of the circle, the lift of the loop `t ↦ exp(2πit)` from `1` is the
half turn `t ↦ exp(πit)`, which ends at `-1`; so the generator of `π₁(S¹)` exchanges the two
sheets `±1` (`Circle.coe_monodromy_sq_expLoop`), and it acts on the point chains of `C_*(F)_Φ` by
swapping `[1]` and `[-1]` (`Circle.representation_liftingLocalSystem_sq`). The DG local system of
this cover is the rank-two permutation module `R[ℤ/2]` with the generator acting by the swap, not
the trivial module and not the rank-one sign representation.

## Main definitions

* `IsCoveringMap.liftingLocalSystemIso`: the DG local system of a covering map is the DG local
  system of its permutation local system.

## Main results

* `IsCoveringMap.isConcentratedInDegreeZero_liftingLocalSystem`: the DG local system of a covering
  map is concentrated in degree zero.
* `IsCoveringMap.liftingLocalSystemIso_hom_apply_lof_ofCube_point`: the identification sends the
  `0`-chain of a sheet to that sheet.
* `Circle.coe_monodromy_sq_expLoop`, `Circle.representation_liftingLocalSystem_sq`: for the double
  cover of the circle, the generator of the fundamental group exchanges the two sheets, in the
  monodromy and in the DG local system.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.
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

end Degree

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
    DGRightModuleCat.IsConcentratedInDegreeZero.representation_fundamentalGroupHom_inv_apply]
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
  .mk (chainEquiv hp R Φ b) fun g ↦ by
    have : DiscreteTopology {e // p.hom e = b} := (hp b).discreteTopology_fiber
    refine cubicalChainModule_linearMap_ext (Y := {e // p.hom e = b}) (G := MooreLoopSpace B b)
      fun n c ↦ ?_
    cases n with
    | succ n => rw [Subsingleton.elim c 0, map_zero, map_zero, map_zero]
    | zero =>
      induction c using NormalizedCubicalChain.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | add c c' hc hc' => rw [map_add, map_add, map_add, hc, hc']
      | smul r c hc => rw [map_smul, map_smul, map_smul, hc]
      | ofCube c =>
        rw [SingularCube.eq_point c, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, representation_liftingLocalSystem_lof_ofCube_point hp R Φ b g,
          chainEquiv_lof_ofCube_point, chainEquiv_lof_ofCube_point]
        -- The monodromy representation acts by the transport of the local system by definition
        -- (`LocalCoefficientSystem.monodromyRepresentation_apply`), and both sides name the same
        -- sheet, as a subtype of `E` and of the preimage of `b`.
        exact (hp.permutationLocalSystem_map_single R g.asHom _ 1).symm

/-- **The DG local system of a covering map is its permutation local system**: the chains on the
fibre of `p` over `b`, with the Moore loops acting through the lifting function, are the free
module on the sheets over `b`, concentrated in degree zero, with a loop acting by the monodromy of
its class. -/
def liftingLocalSystemIso [PathConnectedSpace B] :
    liftingLocalSystem (R := R) (hp.isTransitive Φ) b ≅
      classicalDGLocalSystem b (hp.permutationLocalSystem R) :=
  (hp.isConcentratedInDegreeZero_liftingLocalSystem R Φ b).classicalDGLocalSystemIso.symm ≪≫
    (classicalDGLocalSystemFunctor R b).mapIso
      (LocalCoefficientSystem.ofRepresentationIso b (representationEquiv hp R Φ b) ≪≫
        LocalCoefficientSystem.ofRepresentationMonodromyIso b (hp.permutationLocalSystem R))

/-- **The identification sends the `0`-chain of a sheet to that sheet.** -/
@[simp]
theorem liftingLocalSystemIso_hom_apply_lof_ofCube_point [PathConnectedSpace B]
    (f : {e // p.hom e = b}) :
    (hp.liftingLocalSystemIso R Φ b).hom
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

end Permutation

end IsCoveringMap

namespace Circle

open Real

/-- **For the double cover of the circle, the generator of `π₁(S¹)` exchanges the sheets**: lifting
the loop `t ↦ exp(2πit)` through `z ↦ z²` from the sheet `z` traces the half turn
`t ↦ z exp(πit)`, which ends at `-z`. -/
theorem coe_monodromy_sq_expLoop (z : Circle) (hz : z ^ 2 = 1) :
    ((isQuotientCoveringMap_npow 2).isCoveringMap.monodromy (.mk expLoop) ⟨z, hz⟩ : Circle) =
      -z := by
  have hΓ : (fun w : Circle ↦ w ^ 2) ∘
      (⟨fun t : unitInterval ↦ z * exp (π * t), by fun_prop⟩ : C(unitInterval, Circle)) =
        expLoop := by
    funext t
    rw [Function.comp_apply, ContinuousMap.coe_mk, mul_pow, hz, _root_.one_mul, expLoop_apply,
      ← exp_nsmul]
    congr 1
    rw [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [(isQuotientCoveringMap_npow 2).isCoveringMap.monodromy_eq_apply_one hΓ (by simp)]
  simp [exp_pi]

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
