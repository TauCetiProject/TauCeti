/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.Homotopy.GenLoop.Map
import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Generalized loops in a covering space

Let `p : E → X` be a covering map and `e : E`. In dimension at least two, that is, for a
nontrivial index type `N`, postcomposition with `p` is a homeomorphism
`Ω^ N E e ≃ₜ Ω^ N X (p e)` of the spaces of generalized loops, with their compact-open topologies
(`IsCoveringMap.genLoopHomeomorph`). On homotopy classes this is the isomorphism
`IsCoveringMap.homotopyGroupMulEquiv` of higher homotopy groups; here it holds at the level of
spaces, so, for instance, the double loop space of a space is contractible as soon as that of a
covering space is.

The inverse lifts a generalized loop `γ` in `X`. Shrinking the cube radially onto its corner `0`
turns `γ` into the homotopy `(t, y) ↦ γ (t • y)`, which starts at the constant map `p e`. Lifting
this homotopy for all loops at once, with the loop `γ` itself as an extra parameter, gives a lift
that depends continuously on `γ`. The lift is constant at `e` on the cube boundary, because there
it takes values in the discrete fibre over `p e` and the boundary is connected; this is where the
second coordinate supplied by `Nontrivial N` is used. In dimension one the statement fails: a loop
in the base lifts to a path whose endpoint need not return to `e`.

## Main declarations

* `IsCoveringMap.genLoopHomeomorph`: the homeomorphism `Ω^ N E e ≃ₜ Ω^ N X (p e)` for
  `[Nontrivial N]`, given by postcomposition with `p`.
* `IsCoveringMap.genLoopHomeomorph_apply`, `IsCoveringMap.apply_genLoopHomeomorph_symm_apply`:
  the homeomorphism postcomposes with `p`, and its inverse lifts along `p`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.30 (homotopy
  lifting for covering spaces) and Proposition 4.1.
-/

public section

open scoped unitInterval Topology Topology.Homotopy

variable {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X}

namespace IsCoveringMap

variable (hp : IsCoveringMap p) (e : E)

/-- The generalized loops in `X` at `p e`, precomposed with the straight-line contraction of the
cube onto its corner `0`: the homotopy `(t, (γ, y)) ↦ γ (t • y)`, with the loop `γ` as a
parameter. -/
private def genLoopFamily : C(I × (Ω^ N X (p e) × I^N), X) :=
  ⟨fun q => q.2.1 (TauCeti.cubeContraction N (q.1, q.2.2)),
    (continuous_fst.comp continuous_snd).eval (by fun_prop)⟩

omit [TopologicalSpace E] in
private theorem genLoopFamily_apply (t : I) (q : Ω^ N X (p e) × I^N) :
    genLoopFamily e (t, q) = q.1 (TauCeti.cubeContraction N (t, q.2)) :=
  rfl

omit [TopologicalSpace E] in
/-- The family `genLoopFamily` starts at the constant map `p e`. -/
private theorem genLoopFamily_zero [Nonempty N] (q : Ω^ N X (p e) × I^N) :
    genLoopFamily e (0, q) = p e := by
  rw [genLoopFamily_apply, ContinuousMap.Homotopy.apply_zero]
  exact GenLoop.boundary q.1 0 TauCeti.zero_mem_cubeBoundary

/-- The lift of `genLoopFamily` along the covering map, starting at the constant map `e`. -/
private noncomputable def genLoopFamilyLift [Nonempty N] : C(I × (Ω^ N X (p e) × I^N), E) :=
  hp.liftHomotopy (genLoopFamily e) (.const _ e) (genLoopFamily_zero e)

private theorem apply_genLoopFamilyLift [Nonempty N] (q : I × (Ω^ N X (p e) × I^N)) :
    p (genLoopFamilyLift hp e q) = genLoopFamily e q :=
  congrFun (hp.liftHomotopy_lifts _ _ _) q

/-- The lifts of all generalized loops at `p e`, as one continuous map into `C(I^N, E)`: the end
`t = 1` of the lifted homotopy. -/
private noncomputable def genLoopLiftCurry [Nonempty N] : C(Ω^ N X (p e), C(I^N, E)) :=
  ContinuousMap.curry ((genLoopFamilyLift hp e).comp ⟨fun q => (1, q), by fun_prop⟩)

private theorem genLoopLiftCurry_apply [Nonempty N] (γ : Ω^ N X (p e)) (y : I^N) :
    genLoopLiftCurry hp e γ y = genLoopFamilyLift hp e (1, γ, y) :=
  rfl

private theorem apply_genLoopLiftCurry [Nonempty N] (γ : Ω^ N X (p e)) (y : I^N) :
    p (genLoopLiftCurry hp e γ y) = γ y := by
  rw [genLoopLiftCurry_apply, apply_genLoopFamilyLift hp e, genLoopFamily_apply,
    ContinuousMap.Homotopy.apply_one, ContinuousMap.id_apply]

/-- The lift of a generalized loop is `e` at the corner `0` of the cube: there the lifted
homotopy lifts a constant path starting at `e`. -/
private theorem genLoopLiftCurry_zero [Nonempty N] (γ : Ω^ N X (p e)) :
    genLoopLiftCurry hp e γ 0 = e := by
  have hconst := hp.const_of_comp (g := fun t : I => genLoopFamilyLift hp e (t, γ, 0))
    (by fun_prop) (fun t t' => by
      simp only [apply_genLoopFamilyLift hp e, genLoopFamily_apply,
        TauCeti.cubeContraction_apply_zero]) 1 0
  exact hconst.trans (hp.liftHomotopy_zero _ _ (genLoopFamily_zero e) _)

/-- The lift is constant at `e` on the cube boundary: there it takes values in the discrete fibre
over `p e`, the boundary is connected since `N` has two coordinates, and it contains the corner
`0`, where the lift is `e`. -/
private theorem genLoopLiftCurry_of_mem_boundary [Nontrivial N] (γ : Ω^ N X (p e)) {y : I^N}
    (hy : y ∈ Cube.boundary N) : genLoopLiftCurry hp e γ y = e := by
  have : PreconnectedSpace (Cube.boundary N) := isPreconnected_iff_preconnectedSpace.1
    TauCeti.isPathConnected_cubeBoundary.isConnected.isPreconnected
  have hconst := hp.const_of_comp (g := fun z : Cube.boundary N => genLoopLiftCurry hp e γ z)
    (by fun_prop) (fun z z' => by
      simp only [apply_genLoopLiftCurry hp e, GenLoop.boundary γ _ z.2,
        GenLoop.boundary γ _ z'.2])
    ⟨y, hy⟩ ⟨0, TauCeti.zero_mem_cubeBoundary⟩
  exact hconst.trans (genLoopLiftCurry_zero hp e γ)

/-- The lift of a generalized loop at `p e` to a generalized loop at `e`. -/
private noncomputable def genLoopLift [Nontrivial N] (γ : Ω^ N X (p e)) : Ω^ N E e :=
  ⟨genLoopLiftCurry hp e γ, fun _ hy => genLoopLiftCurry_of_mem_boundary hp e γ hy⟩

private theorem continuous_genLoopLift [Nontrivial N] : Continuous (genLoopLift hp e (N := N)) :=
  (genLoopLiftCurry hp e).continuous.subtype_mk _

private theorem genLoopLift_apply [Nontrivial N] (γ : Ω^ N X (p e)) (y : I^N) :
    genLoopLift hp e γ y = genLoopLiftCurry hp e γ y :=
  rfl

private theorem apply_genLoopLift [Nontrivial N] (γ : Ω^ N X (p e)) (y : I^N) :
    p (genLoopLift hp e γ y) = γ y := by
  rw [genLoopLift_apply, apply_genLoopLiftCurry hp e]

/-- **Postcomposition with a covering map is a homeomorphism of spaces of generalized loops** in
dimension at least two: for a covering map `p : E → X` and a nontrivial index type `N`,
`γ ↦ p ∘ γ` is a homeomorphism `Ω^ N E e ≃ₜ Ω^ N X (p e)` for the compact-open topologies. Its
inverse lifts a generalized loop in `X` to the unique lift starting at `e`. -/
noncomputable def genLoopHomeomorph [Nontrivial N] : Ω^ N E e ≃ₜ Ω^ N X (p e) where
  toFun := GenLoop.map ⟨p, hp.continuous⟩ rfl
  invFun := genLoopLift hp e
  left_inv F := by
    refine GenLoop.ext _ _ fun y => congrFun (hp.eq_of_comp_eq (map_continuous _)
      (map_continuous (F : C(I^N, E))) (funext fun z => ?_) 0 ?_) y
    · simp only [Function.comp_apply, GenLoop.coe_coe, apply_genLoopLift, GenLoop.map_apply,
        ContinuousMap.coe_mk]
    · simp only [GenLoop.coe_coe]
      rw [GenLoop.boundary _ 0 TauCeti.zero_mem_cubeBoundary,
        GenLoop.boundary F 0 TauCeti.zero_mem_cubeBoundary]
  right_inv γ := GenLoop.ext _ _ fun y => by
    rw [GenLoop.map_apply, ContinuousMap.coe_mk, apply_genLoopLift hp e]
  continuous_toFun := GenLoop.continuous_map _ _
  continuous_invFun := continuous_genLoopLift hp e

/-- The homeomorphism `IsCoveringMap.genLoopHomeomorph` postcomposes with the covering map. -/
@[simp]
theorem genLoopHomeomorph_apply [Nontrivial N] (F : Ω^ N E e) (y : I^N) :
    hp.genLoopHomeomorph e F y = p (F y) :=
  GenLoop.map_apply _ _ F y

/-- The inverse of `IsCoveringMap.genLoopHomeomorph` lifts a generalized loop along the covering
map. -/
theorem apply_genLoopHomeomorph_symm_apply [Nontrivial N] (γ : Ω^ N X (p e)) (y : I^N) :
    p ((hp.genLoopHomeomorph e).symm γ y) = γ y :=
  apply_genLoopLift hp e γ y

end IsCoveringMap
