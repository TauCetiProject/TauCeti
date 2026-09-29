/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReductionModVariables
public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
public import TauCeti.KnotTheory.Grid.Stabilization.Map

/-!
# Stabilization invariance reduced to the fully blocked comparison

Let `G` be a grid diagram of size `n`, let `s` be a column, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the `X`-marking
of column `s`. Write `S = R[V₀, …, V_n]` for the coefficient ring of `GC⁻(G')`. By
`TauCeti.KnotTheory.Grid.Stabilization.Map`, the comparison map `GC⁻(G') ⟶ GC⁻(G)` is a
quasi-isomorphism as soon as the component `H_I^N : N ⟶ I` of the `X₂`-homotopy, from the
off-center complex `N` to the center complex `I`, is one. This file reduces that remaining
hypothesis to a statement in which every variable is set to zero.

Both `N` and `I` are free `S`-modules on finitely many grid states of `G'`, and their differentials
and `H_I^N` count empty rectangles weighted by the monomials `V^{O(r)}`. Giving each variable the
weight `-2`, the matrix coefficient between two states `x` and `y` is weighted homogeneous of
degree `M_O(x) - 1 - M_O(y)`, for `M_O` the `O`-Maslov grading of `G'`
(`GridDiagram.isWeightedHomogeneous_sum_OMonomial`). The graded Nakayama argument of
`TauCeti.Algebra.Homology.ReductionModVariables` therefore applies: `H_I^N` is a
quasi-isomorphism if its reduction modulo the variables `V₀, …, V_n`,
`LinearMap.constantCoeffReduction`, induces a bijection between the homologies of the reductions
of the two differentials (`quasiIso_stabilizeXOffCenterToCenterHom_of_bijective`).

The reductions are the fully blocked objects of Ozsváth--Stipsicz--Szabó. The reduction of the
center differential counts the fully blocked rectangles of `G`, so the reduced center complex is
the fully blocked complex of `G`
(`constantCoeffReduction_stabilizeXCenterDifferential_single_apply`). The reduction of the
off-center differential counts the fully blocked rectangles of `G'` between off-center states
(`constantCoeffReduction_stabilizeXOffCenterDifferential_single_apply`). The reduction of `H_I^N`
counts the empty rectangles from an off-center state to a center state whose only marking is the
`X`-marking `X₂` (`constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply`). That this
fully blocked comparison induces a bijection on homology is the combinatorial content of
stabilization invariance, and is not proved here.

## Main results

* `TauCeti.GridDiagram.isWeightedHomogeneous_stabilizeXCenterDifferential_single_apply`,
  `TauCeti.GridDiagram.isWeightedHomogeneous_stabilizeXOffCenterDifferential_single_apply` and
  `TauCeti.GridDiagram.isWeightedHomogeneous_stabilizeXOffCenterToCenter_single_apply`: the two
  differentials and `H_I^N` lower the `O`-Maslov grading of `G'` by one.
* `TauCeti.GridDiagram.constantCoeffReduction_stabilizeXCenterDifferential_single_apply`,
  `TauCeti.GridDiagram.constantCoeffReduction_stabilizeXOffCenterDifferential_single_apply` and
  `TauCeti.GridDiagram.constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply`: the
  reductions modulo the variables count fully blocked rectangles.
* `TauCeti.GridDiagram.quasiIso_stabilizeXOffCenterToCenterHom_of_bijective`: `H_I^N` is a
  quasi-isomorphism if its reduction modulo the variables induces a bijection on homology.
* `TauCeti.GridDiagram.quasiIso_stabilizeXMap_of_bijective`: under the same hypothesis the
  comparison map `GC⁻(G') ⟶ GC⁻(G)` is a quasi-isomorphism.

## References

The fully blocked comparison map is the one of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Section 5.2; the passage between the fully blocked and the unblocked theory is the
graded algebra of its Appendix A.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-! ### The `O`-Maslov grading of the two blocks -/

section Grading

variable (R : Type*) [CommSemiring R]

/-- The center differential lowers the `O`-Maslov grading of the stabilization by one: with every
variable of weight `-2`, its matrix coefficient from `x` to `y` is weighted homogeneous of degree
`M_O(x') - 1 - M_O(y')`, for `x'` and `y'` the states of the stabilization containing the center of
the new block. -/
theorem isWeightedHomogeneous_stabilizeXCenterDifferential_single_apply (x y : GridState n) :
    IsWeightedHomogeneous (fun _ : Fin (n + 1) ↦ (-2 : ℤ))
      (G.stabilizeXCenterDifferential s R (Finsupp.single x 1) y)
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ (x.insertPoint s.succ (G.X s).succ) -
        1 - (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ
          (y.insertPoint s.succ (G.X s).succ)) := by
  rw [stabilizeXCenterDifferential_single_apply, ← unblockedCoefficient_stabilizeX_insertPoint]
  exact isWeightedHomogeneous_unblockedCoefficient _ R _ _

/-- The off-center differential lowers the `O`-Maslov grading of the stabilization by one. -/
theorem isWeightedHomogeneous_stabilizeXOffCenterDifferential_single_apply
    (y z : G.StabilizeXOffCenterState s) :
    IsWeightedHomogeneous (fun _ : Fin (n + 1) ↦ (-2 : ℤ))
      (G.stabilizeXOffCenterDifferential s R (Finsupp.single y 1) z)
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y -
        1 - (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ z) := by
  rw [stabilizeXOffCenterDifferential_single_apply]
  exact isWeightedHomogeneous_unblockedCoefficient _ R _ _

/-- The component `H_I^N` of the `X₂`-homotopy lowers the `O`-Maslov grading of the stabilization
by one: like the differential, it counts empty rectangles weighted by their `O`-markings. -/
theorem isWeightedHomogeneous_stabilizeXOffCenterToCenter_single_apply
    (y : G.StabilizeXOffCenterState s) (x : GridState n) :
    IsWeightedHomogeneous (fun _ : Fin (n + 1) ↦ (-2 : ℤ))
      (G.stabilizeXOffCenterToCenter s R (Finsupp.single y 1) x)
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y -
        1 - (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ
          (x.insertPoint s.succ (G.X s).succ)) := by
  rw [stabilizeXOffCenterToCenter_single_apply, XHomotopyCoefficient_def]
  exact isWeightedHomogeneous_sum_OMonomial _ R _ fun _ hr ↦
    (GridRectangleBetween.mem_emptyRectangles _).mp
      (XHomotopyRectangles_subset_emptyRectangles _ _ _ _ hr)

end Grading

/-! ### The reductions modulo the variables -/

section Reduction

variable (R : Type*) [CommRing R]

/-- The reduction of the center differential modulo the variables counts the fully blocked
rectangles of `G`: over `ZMod 2` it is the fully blocked differential of `G`. -/
theorem constantCoeffReduction_stabilizeXCenterDifferential_single_apply (x y : GridState n)
    (c : R) :
    (G.stabilizeXCenterDifferential s R).constantCoeffReduction (Finsupp.single x c) y =
      c * (G.fullyBlockedRectangles x y).card := by
  rw [LinearMap.constantCoeffReduction_single_apply, stabilizeXCenterDifferential_single_apply,
    constantCoeff_rename, constantCoeff_unblockedCoefficient_eq_card_fullyBlockedRectangles]

/-- The reduction of the off-center differential modulo the variables counts the fully blocked
rectangles of the stabilization between off-center states. -/
theorem constantCoeffReduction_stabilizeXOffCenterDifferential_single_apply
    (y z : G.StabilizeXOffCenterState s) (c : R) :
    (G.stabilizeXOffCenterDifferential s R).constantCoeffReduction (Finsupp.single y c) z =
      c * ((G.stabilizeX s.castSucc (G.X s).castSucc s).fullyBlockedRectangles y.1 z.1).card := by
  rw [LinearMap.constantCoeffReduction_single_apply, stabilizeXOffCenterDifferential_single_apply,
    constantCoeff_unblockedCoefficient_eq_card_fullyBlockedRectangles]

/-- The reduction of `H_I^N` modulo the variables counts the empty rectangles of the stabilization
from an off-center state to a center state that carry no `O`-marking and whose only `X`-marking is
the southeast `X`-marking `X₂` of the new block. -/
theorem constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply
    (y : G.StabilizeXOffCenterState s) (x : GridState n) (c : R) :
    (G.stabilizeXOffCenterToCenter s R).constantCoeffReduction (Finsupp.single y c) x =
      c * (((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles s.succ y.1
        (x.insertPoint s.succ (G.X s).succ)).filter fun r =>
          (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅).card := by
  rw [LinearMap.constantCoeffReduction_single_apply, stabilizeXOffCenterToCenter_single_apply,
    constantCoeff_XHomotopyCoefficient]

variable [CharP R 2]

/-- The reduction of the center differential squares to zero. -/
theorem constantCoeffReduction_stabilizeXCenterDifferential_comp_self :
    (G.stabilizeXCenterDifferential s R).constantCoeffReduction ∘ₗ
        (G.stabilizeXCenterDifferential s R).constantCoeffReduction = 0 := by
  rw [← LinearMap.constantCoeffReduction_comp, stabilizeXCenterDifferential_comp_self_eq_zero,
    LinearMap.constantCoeffReduction_zero]

/-- The reduction of the off-center differential squares to zero. -/
theorem constantCoeffReduction_stabilizeXOffCenterDifferential_comp_self :
    (G.stabilizeXOffCenterDifferential s R).constantCoeffReduction ∘ₗ
        (G.stabilizeXOffCenterDifferential s R).constantCoeffReduction = 0 := by
  rw [← LinearMap.constantCoeffReduction_comp, stabilizeXOffCenterDifferential_comp_self_eq_zero,
    LinearMap.constantCoeffReduction_zero]

/-- The reduction of `H_I^N` is a chain map between the reductions of the two differentials. -/
theorem constantCoeffReduction_stabilizeXOffCenterToCenter_comp :
    (G.stabilizeXOffCenterToCenter s R).constantCoeffReduction ∘ₗ
        (G.stabilizeXOffCenterDifferential s R).constantCoeffReduction =
      (G.stabilizeXCenterDifferential s R).constantCoeffReduction ∘ₗ
        (G.stabilizeXOffCenterToCenter s R).constantCoeffReduction := by
  rw [← LinearMap.constantCoeffReduction_comp, ← LinearMap.constantCoeffReduction_comp,
    stabilizeXOffCenterToCenter_comp_offCenterDifferential]

local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- The off-center complex with its unique object and differential spelled out, so that its
homology is the homology of the off-center differential in the sense of `LinearMap.homology`. -/
private noncomputable abbrev stabilizeXOffCenterComplex' :
    HomologicalComplex (ModuleCat S) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of S (G.StabilizeXOffCenterState s →₀ S)
  d _ _ := ModuleCat.ofHom (G.stabilizeXOffCenterDifferential s R)
  d_comp_d' _ _ _ _ _ := ((G.stabilizeXOffCenterDifferential s R).shortComplex
    (G.stabilizeXOffCenterDifferential_comp_self_eq_zero s R)).zero

/-- The center complex with its unique object and differential spelled out. -/
private noncomputable abbrev stabilizeXCenterComplex' :
    HomologicalComplex (ModuleCat S) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of S (GridState n →₀ S)
  d _ _ := ModuleCat.ofHom (G.stabilizeXCenterDifferential s R)
  d_comp_d' _ _ _ _ _ := ((G.stabilizeXCenterDifferential s R).shortComplex
    (G.stabilizeXCenterDifferential_comp_self_eq_zero s R)).zero

/-- The off-center complex is isomorphic to its spelled-out form. -/
private noncomputable def stabilizeXOffCenterComplexIso :
    G.stabilizeXOffCenterComplex s R ≅ G.stabilizeXOffCenterComplex' s R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ eqToIso (G.stabilizeXOffCenterComplex_X s R i)) (by
      rintro ⟨⟩ ⟨⟩ -
      simp)

/-- The center complex is isomorphic to its spelled-out form. -/
private noncomputable def stabilizeXCenterComplexIso :
    G.stabilizeXCenterComplex s R ≅ G.stabilizeXCenterComplex' s R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ eqToIso (G.stabilizeXCenterComplex_X s R i)) (by
      rintro ⟨⟩ ⟨⟩ -
      simp)

/-- `H_I^N` as a chain map between the spelled-out complexes. -/
private noncomputable def stabilizeXOffCenterToCenterHom' :
    G.stabilizeXOffCenterComplex' s R ⟶ G.stabilizeXCenterComplex' s R where
  f _ := ModuleCat.ofHom (G.stabilizeXOffCenterToCenter s R)
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
      G.stabilizeXOffCenterToCenter_comp_offCenterDifferential s R]

/-- The spelled-out form of `H_I^N` is isomorphic to `H_I^N` as an arrow. -/
private noncomputable def stabilizeXOffCenterToCenterHomArrowIso :
    Arrow.mk (G.stabilizeXOffCenterToCenterHom s R) ≅
      Arrow.mk (G.stabilizeXOffCenterToCenterHom' s R) :=
  Arrow.isoMk (G.stabilizeXOffCenterComplexIso s R) (G.stabilizeXCenterComplexIso s R) (by
    ext ⟨⟩ : 1
    simp [stabilizeXOffCenterComplexIso, stabilizeXCenterComplexIso,
      stabilizeXOffCenterToCenterHom'])

/-- **`H_I^N` is a quasi-isomorphism if its fully blocked reduction is.** If the reduction of
`H_I^N` modulo the variables induces a bijection from the homology of the reduced off-center
complex to the homology of the reduced center complex, the fully blocked grid homology of `G`, then
`H_I^N` is a quasi-isomorphism of complexes over `R[V₀, …, V_n]`. -/
theorem quasiIso_stabilizeXOffCenterToCenterHom_of_bijective
    (h : Function.Bijective (LinearMap.homologyMap
      (G.stabilizeXOffCenterToCenter s R).constantCoeffReduction
      (G.constantCoeffReduction_stabilizeXOffCenterDifferential_comp_self s R)
      (G.constantCoeffReduction_stabilizeXCenterDifferential_comp_self s R)
      (G.constantCoeffReduction_stabilizeXOffCenterToCenter_comp s R))) :
    QuasiIso (G.stabilizeXOffCenterToCenterHom s R) := by
  rw [quasiIso_iff_of_arrow_mk_iso _ _
      (G.stabilizeXOffCenterToCenterHomArrowIso s R),
    HomologicalComplex.quasiIso_iff_bijective_homologyMap]
  exact LinearMap.homologyMap_bijective_of_mapRange_constantCoeff
    (G.stabilizeXOffCenterToCenter s R) (w := fun _ ↦ (-2 : ℤ))
    (g := fun y ↦ (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y.1)
    (g' := fun x ↦ (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ
      (x.insertPoint s.succ (G.X s).succ)) (r := -1) (δ := -1)
    (fun _ ↦ by decide) (Set.finite_range _).bddAbove (Set.finite_range _).bddAbove
    (fun y z ↦ by
      simpa only [← sub_eq_add_neg] using
        G.isWeightedHomogeneous_stabilizeXOffCenterDifferential_single_apply s R y z)
    (fun x y ↦ by
      simpa only [← sub_eq_add_neg] using
        G.isWeightedHomogeneous_stabilizeXCenterDifferential_single_apply s R x y)
    (fun y x ↦ by
      simpa only [← sub_eq_add_neg] using
        G.isWeightedHomogeneous_stabilizeXOffCenterToCenter_single_apply s R y x)
    (LinearMap.constantCoeffReduction_mapRange_constantCoeff _)
    (LinearMap.constantCoeffReduction_mapRange_constantCoeff _)
    (LinearMap.constantCoeffReduction_mapRange_constantCoeff _)
    (G.stabilizeXOffCenterDifferential_comp_self_eq_zero s R)
    (G.stabilizeXCenterDifferential_comp_self_eq_zero s R)
    (G.stabilizeXOffCenterToCenter_comp_offCenterDifferential s R) h

/-- **The stabilization map is a quasi-isomorphism if the fully blocked comparison is.** Under the
hypothesis of `quasiIso_stabilizeXOffCenterToCenterHom_of_bijective`, the comparison map
`GC⁻(G') ⟶ GC⁻(G)` of complexes over `R[V₀, …, V_{n-1}]` is a quasi-isomorphism. -/
theorem quasiIso_stabilizeXMap_of_bijective
    (h : Function.Bijective (LinearMap.homologyMap
      (G.stabilizeXOffCenterToCenter s R).constantCoeffReduction
      (G.constantCoeffReduction_stabilizeXOffCenterDifferential_comp_self s R)
      (G.constantCoeffReduction_stabilizeXCenterDifferential_comp_self s R)
      (G.constantCoeffReduction_stabilizeXOffCenterToCenter_comp s R))) :
    QuasiIso (G.stabilizeXMap s R) :=
  have := G.quasiIso_stabilizeXOffCenterToCenterHom_of_bijective s R h
  G.quasiIso_stabilizeXMap s R

end Reduction

end GridDiagram

end TauCeti
