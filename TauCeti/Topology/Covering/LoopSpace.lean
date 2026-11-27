/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.Homotopy.LoopSpaceFibration
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Topology.PathComponent
public import TauCeti.Topology.PathSpace.Moore.Covering

/-!
# Contractible loops of a covering space

Let `p : E → B` be a covering map and `e : E`. The loop map `γ ↦ p ∘ γ` sends the space `Ω₀E` of
contractible loops at `e`, the path component of the constant loop in `Ω E e`, homeomorphically
onto the space `Ω₀B` of contractible loops at `p e`
(`IsCoveringMap.pathComponentLoopSpaceHomeomorph`). It is injective by unique path lifting. Its
inverse lifts a contractible loop `δ` from `e`: the lifts, taken all at once by homotopy lifting
over the path-connected space `Ω₀B`, depend continuously on `δ`, and their end points lie in the
discrete fibre over `p e`, so they all end where the lift of the constant loop does, at `e`.

When `Ω E e` is path connected, for instance when `E` is simply connected, every loop at `e` is
contractible, so `Ω E e = Ω₀E` and the loop map identifies `Ω E e` with `Ω₀B`
(`IsCoveringMap.loopSpaceHomeomorph`). For the universal cover `Sⁿ → ℝPⁿ`, `n ≥ 2`, this says
that the contractible loops of `ℝPⁿ` are the loop space of `Sⁿ`; the mod-two vanishing theorem
applied to `Ω₀ℝPⁿ` in the proof of Theorem C of Barraud–Damian–Humilière–Oancea sees the homology
of `ΩSⁿ`. The loop map is not onto all of `Ω B (p e)` in general: a loop whose lift from `e` does
not close up has no preimage.

The same holds for the Moore loops: the Moore loop map is a homeomorphism from the path component
of the unit of `MooreLoopSpace E e` onto that of `MooreLoopSpace B (p e)`
(`IsCoveringMap.pathComponentMooreLoopSpaceHomeomorph`), its inverse lifting a Moore loop through
the lifting function `IsCoveringMap.mooreLiftingFunction`, and when `MooreLoopSpace E e` is path
connected it identifies all of it with that component (`IsCoveringMap.mooreLoopSpaceHomeomorph`).

## Main results

* `IsCoveringMap.pathComponentLoopSpaceHomeomorph`: the loop map of a covering map is a
  homeomorphism `Ω₀E ≃ₜ Ω₀B` of contractible loops.
* `IsCoveringMap.loopSpaceHomeomorph`: if `Ω E e` is path connected, the loop map is a
  homeomorphism `Ω E e ≃ₜ Ω₀B`.
* `IsCoveringMap.pathComponentMooreLoopSpaceHomeomorph`,
  `IsCoveringMap.mooreLoopSpaceHomeomorph`: the same for the Moore loops.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.30 and
  Proposition 4.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Theorem 5.15.
-/

public noncomputable section

open unitInterval Topology
open scoped NNReal Topology.Homotopy

namespace IsCoveringMap

open TauCeti

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-! ### Fixed-interval loops -/

section LoopSpace

variable {p : E → B} (hp : IsCoveringMap p) (e : E)

include hp

/-- The contractible loops at `p e` as a homotopy of paths, parametrized by the loop. -/
private def evalHomotopy : C(I × pathComponent (Path.refl (p e)), B) :=
  ⟨fun q ↦ (q.2 : Ω B (p e)) q.1, by fun_prop⟩

/-- The lifts from `e` of all contractible loops at `p e`. -/
private def liftFamily : C(I × pathComponent (Path.refl (p e)), E) :=
  hp.liftHomotopy (evalHomotopy e) (.const _ e) fun δ ↦ by simp [evalHomotopy]

private theorem apply_liftFamily (q : I × pathComponent (Path.refl (p e))) :
    p (liftFamily hp e q) = (q.2 : Ω B (p e)) q.1 :=
  congrFun (hp.liftHomotopy_lifts _ _ _) q

private theorem liftFamily_zero (δ : pathComponent (Path.refl (p e))) :
    liftFamily hp e (0, δ) = e :=
  hp.liftHomotopy_zero _ _ _ δ

/-- The lift of a contractible loop closes up: the end points of the lifts lie in the fibre over
`p e` and vary continuously over the path-connected space of contractible loops, so they agree
with the end point `e` of the lift of the constant loop. -/
private theorem liftFamily_one (δ : pathComponent (Path.refl (p e))) :
    liftFamily hp e (1, δ) = e := by
  rw [hp.const_of_comp (g := fun δ ↦ liftFamily hp e (1, δ)) (by fun_prop)
    (fun δ δ' ↦ by simp [apply_liftFamily]) δ ⟨Path.refl (p e), mem_pathComponent_self _⟩]
  -- The lift of the constant loop lies over a point, so it is constant.
  rw [hp.const_of_comp (g := fun t : I ↦ liftFamily hp e (t, ⟨Path.refl (p e),
    mem_pathComponent_self _⟩)) (by fun_prop) (fun t t' ↦ by simp [apply_liftFamily]) 1 0,
    liftFamily_zero]

/-- The lift from `e` of a contractible loop at `p e`, as a loop at `e`. -/
private def liftLoop (δ : pathComponent (Path.refl (p e))) : Ω E e where
  toFun t := liftFamily hp e (t, δ)
  continuous_toFun := by fun_prop
  source' := liftFamily_zero hp e δ
  target' := liftFamily_one hp e δ

private theorem continuous_liftLoop : Continuous (liftLoop hp e) :=
  Path.continuous_uncurry_iff.1 <| (liftFamily hp e).continuous.comp continuous_swap

private theorem map_liftLoop (δ : pathComponent (Path.refl (p e))) :
    (liftLoop hp e δ).map hp.continuous = δ :=
  Path.ext <| funext fun t ↦ apply_liftFamily hp e (t, δ)

/-- A loop at `e` is the lift of its image: both lie over the same loop and start at `e`. -/
private theorem liftLoop_map (γ : Ω E e)
    (hγ : γ.map hp.continuous ∈ pathComponent (Path.refl (p e))) :
    liftLoop hp e ⟨γ.map hp.continuous, hγ⟩ = γ :=
  Path.ext <| hp.eq_of_comp_eq (map_continuous (liftLoop hp e _)) γ.continuous
    (funext fun t ↦ by
      simpa using congrArg (fun δ : Ω B (p e) ↦ δ t) (map_liftLoop hp e ⟨_, hγ⟩)) 0 (by simp)

/-- The lift of a contractible loop is contractible: it is joined to the lift of the constant
loop, which is the constant loop. -/
private theorem liftLoop_mem_pathComponent (δ : pathComponent (Path.refl (p e))) :
    liftLoop hp e δ ∈ pathComponent (Path.refl e) := by
  have h := (PathConnectedSpace.joined ⟨Path.refl (p e), mem_pathComponent_self _⟩ δ).map
    (continuous_liftLoop hp e)
  have hrefl := liftLoop_map hp e (Path.refl e) (by
    rw [Path.map_refl]
    exact mem_pathComponent_self _)
  simp only [Path.map_refl] at hrefl
  rwa [hrefl] at h

/-- **The contractible loops of a covering space**: for a covering map `p : E → B`, the loop map
`γ ↦ p ∘ γ` is a homeomorphism from the path component of the constant loop in `Ω E e` onto the
path component of the constant loop in `Ω B (p e)`. Its inverse lifts a loop from `e`. -/
def pathComponentLoopSpaceHomeomorph :
    pathComponent (Path.refl e) ≃ₜ pathComponent (Path.refl (p e)) where
  toFun γ := ⟨(γ : Ω E e).map hp.continuous,
    Path.map_refl hp.continuous e ▸
      (TauCeti.continuous_loopMap hp.continuous e).mapsTo_pathComponent (Path.refl e)
        γ.property⟩
  invFun δ := ⟨liftLoop hp e δ, liftLoop_mem_pathComponent hp e δ⟩
  left_inv γ := Subtype.ext <| liftLoop_map hp e γ _
  right_inv δ := Subtype.ext <| map_liftLoop hp e δ
  continuous_toFun :=
    ((TauCeti.continuous_loopMap hp.continuous e).comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_liftLoop hp e).subtype_mk _

@[simp]
theorem coe_pathComponentLoopSpaceHomeomorph_apply (γ : pathComponent (Path.refl e)) :
    (hp.pathComponentLoopSpaceHomeomorph e γ : Ω B (p e)) = (γ : Ω E e).map hp.continuous :=
  (rfl)

/-- The inverse of `pathComponentLoopSpaceHomeomorph` lifts a loop: the lift lies over it. -/
@[simp]
theorem map_coe_pathComponentLoopSpaceHomeomorph_symm_apply
    (δ : pathComponent (Path.refl (p e))) :
    ((hp.pathComponentLoopSpaceHomeomorph e).symm δ : Ω E e).map hp.continuous = δ :=
  map_liftLoop hp e δ

/-- **The loop space of a covering space with path-connected loop space**: if `Ω E e` is path
connected, as when `E` is simply connected, the loop map of a covering map `p : E → B` is a
homeomorphism from `Ω E e` onto the space of contractible loops at `p e`. -/
def loopSpaceHomeomorph [PathConnectedSpace (Ω E e)] :
    Ω E e ≃ₜ pathComponent (Path.refl (p e)) :=
  (Homeomorph.pathComponentOfPathConnectedSpace (Path.refl e)).trans <|
    hp.pathComponentLoopSpaceHomeomorph e

@[simp]
theorem coe_loopSpaceHomeomorph_apply [PathConnectedSpace (Ω E e)] (γ : Ω E e) :
    (hp.loopSpaceHomeomorph e γ : Ω B (p e)) = γ.map hp.continuous := by
  simp [loopSpaceHomeomorph]

/-- The inverse of `loopSpaceHomeomorph` lifts a loop: the lift lies over it. -/
@[simp]
theorem map_loopSpaceHomeomorph_symm_apply [PathConnectedSpace (Ω E e)]
    (δ : pathComponent (Path.refl (p e))) :
    ((hp.loopSpaceHomeomorph e).symm δ).map hp.continuous = δ := by
  simp [loopSpaceHomeomorph]

end LoopSpace

/-! ### Moore loops -/

section MooreLoopSpace

variable {p : C(E, B)} (hp : IsCoveringMap p) (e : E)

include hp

/-- The lifts from `e` of the contractible Moore loops at `p e`, as Moore paths. -/
private def mooreLiftPath (δ : pathComponent (1 : MooreLoopSpace B (p e))) : MoorePath E :=
  hp.mooreLiftingFunction.lift e (δ : MooreLoopSpace B (p e)).toMoorePath (by simp)

private theorem continuous_mooreLiftPath : Continuous (mooreLiftPath hp e) :=
  hp.mooreLiftingFunction.continuous_lift continuous_const
    (MooreLoopSpace.continuous_toMoorePath.comp continuous_subtypeVal) fun _ ↦ by simp

/-- The lift of a contractible Moore loop closes up, by the argument of `liftFamily_one`. -/
private theorem target_mooreLiftPath (δ : pathComponent (1 : MooreLoopSpace B (p e))) :
    (mooreLiftPath hp e δ).target = e := by
  rw [hp.const_of_comp (g := fun δ ↦ (mooreLiftPath hp e δ).target)
    (MoorePath.continuous_target.comp (continuous_mooreLiftPath hp e))
    (fun δ δ' ↦ by simp [mooreLiftPath]) δ ⟨1, mem_pathComponent_self _⟩]
  simp [mooreLiftPath]

/-- The lift from `e` of a contractible Moore loop at `p e`, as a Moore loop at `e`. -/
private def mooreLiftLoop (δ : pathComponent (1 : MooreLoopSpace B (p e))) :
    MooreLoopSpace E e :=
  ⟨mooreLiftPath hp e δ, by simp [mooreLiftPath], target_mooreLiftPath hp e δ⟩

private theorem continuous_mooreLiftLoop : Continuous (mooreLiftLoop hp e) :=
  MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 (continuous_mooreLiftPath hp e)

private theorem map_mooreLiftLoop (δ : pathComponent (1 : MooreLoopSpace B (p e))) :
    MooreLoopSpace.map p rfl (mooreLiftLoop hp e δ) = δ :=
  MooreLoopSpace.ext <| by simp [mooreLiftLoop, mooreLiftPath]

private theorem mooreLiftLoop_map (γ : MooreLoopSpace E e)
    (hγ : MooreLoopSpace.map p rfl γ ∈ pathComponent (1 : MooreLoopSpace B (p e))) :
    mooreLiftLoop hp e ⟨MooreLoopSpace.map p rfl γ, hγ⟩ = γ :=
  MooreLoopSpace.ext <| hp.moorePath_eq_of_map_eq (by simp [mooreLiftLoop, mooreLiftPath])
    (by simp [mooreLiftLoop, mooreLiftPath])

private theorem mooreLiftLoop_mem_pathComponent (δ : pathComponent (1 : MooreLoopSpace B (p e))) :
    mooreLiftLoop hp e δ ∈ pathComponent (1 : MooreLoopSpace E e) := by
  have h := (PathConnectedSpace.joined ⟨1, mem_pathComponent_self _⟩ δ).map
    (continuous_mooreLiftLoop hp e)
  have hone := mooreLiftLoop_map hp e 1 (by
    rw [map_one]
    exact mem_pathComponent_self _)
  simp only [map_one] at hone
  rwa [hone] at h

/-- **The contractible Moore loops of a covering space**: for a covering map `p : E → B`, the
Moore loop map is a homeomorphism from the path component of the unit in `MooreLoopSpace E e` onto
the path component of the unit in `MooreLoopSpace B (p e)`. Its inverse lifts a Moore loop from
`e`. -/
def pathComponentMooreLoopSpaceHomeomorph :
    pathComponent (1 : MooreLoopSpace E e) ≃ₜ pathComponent (1 : MooreLoopSpace B (p e)) where
  toFun γ := ⟨MooreLoopSpace.map p rfl γ,
    map_one (MooreLoopSpace.map p (rfl : p e = p e)) ▸
      (map_continuous (MooreLoopSpace.map p (rfl : p e = p e))).mapsTo_pathComponent 1 γ.property⟩
  invFun δ := ⟨mooreLiftLoop hp e δ, mooreLiftLoop_mem_pathComponent hp e δ⟩
  left_inv γ := Subtype.ext <| mooreLiftLoop_map hp e γ _
  right_inv δ := Subtype.ext <| map_mooreLiftLoop hp e δ
  continuous_toFun :=
    ((map_continuous (MooreLoopSpace.map p (rfl : p e = p e))).comp
      continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_mooreLiftLoop hp e).subtype_mk _

@[simp]
theorem coe_pathComponentMooreLoopSpaceHomeomorph_apply
    (γ : pathComponent (1 : MooreLoopSpace E e)) :
    (hp.pathComponentMooreLoopSpaceHomeomorph e γ : MooreLoopSpace B (p e)) =
      MooreLoopSpace.map p rfl γ :=
  (rfl)

/-- The inverse of `pathComponentMooreLoopSpaceHomeomorph` lifts a Moore loop: the lift lies over
it. -/
@[simp]
theorem map_coe_pathComponentMooreLoopSpaceHomeomorph_symm_apply
    (δ : pathComponent (1 : MooreLoopSpace B (p e))) :
    MooreLoopSpace.map p rfl ((hp.pathComponentMooreLoopSpaceHomeomorph e).symm δ :
      MooreLoopSpace E e) = δ :=
  map_mooreLiftLoop hp e δ

/-- **The Moore loop space of a covering space with path-connected Moore loop space**: if
`MooreLoopSpace E e` is path connected, as when `E` is simply connected, the Moore loop map of a
covering map `p : E → B` is a homeomorphism from `MooreLoopSpace E e` onto the space of contractible
Moore loops at `p e`. -/
def mooreLoopSpaceHomeomorph [PathConnectedSpace (MooreLoopSpace E e)] :
    MooreLoopSpace E e ≃ₜ pathComponent (1 : MooreLoopSpace B (p e)) :=
  (Homeomorph.pathComponentOfPathConnectedSpace (1 : MooreLoopSpace E e)).trans <|
    hp.pathComponentMooreLoopSpaceHomeomorph e

@[simp]
theorem coe_mooreLoopSpaceHomeomorph_apply [PathConnectedSpace (MooreLoopSpace E e)]
    (γ : MooreLoopSpace E e) :
    (hp.mooreLoopSpaceHomeomorph e γ : MooreLoopSpace B (p e)) =
      MooreLoopSpace.map p rfl γ := by
  simp [mooreLoopSpaceHomeomorph]

/-- The inverse of `mooreLoopSpaceHomeomorph` lifts a Moore loop: the lift lies over it. -/
@[simp]
theorem map_mooreLoopSpaceHomeomorph_symm_apply [PathConnectedSpace (MooreLoopSpace E e)]
    (δ : pathComponent (1 : MooreLoopSpace B (p e))) :
    MooreLoopSpace.map p rfl ((hp.mooreLoopSpaceHomeomorph e).symm δ) = δ := by
  simp [mooreLoopSpaceHomeomorph]

end MooreLoopSpace

end IsCoveringMap
