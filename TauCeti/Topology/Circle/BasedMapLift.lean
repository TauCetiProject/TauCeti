/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.MappingSpace.Based
public import TauCeti.Topology.MappingSpace.Group
import TauCeti.Topology.Circle.Arc
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Based maps into the circle from a simply connected compact space

Let `Y` be a compact, simply connected and locally path-connected space with a basepoint `y₀`.
Every based map `f : (Y, y₀) → (S¹, 1)` lifts uniquely through the covering `Circle.exp : ℝ → S¹`
to an angle function `θ : Y → ℝ` with `θ y₀ = 0` (Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`). The lift depends continuously on `f` for the
compact-open topologies: near a based map `f₀`, the lift of `f` is the lift of `f₀` plus the
principal argument of `f / f₀`, which is continuous because `Y` is compact and `f / f₀` stays
uniformly close to `1`. So postcomposition with `Circle.exp` is a homeomorphism
`Map_*(Y, ℝ) ≃ₜ Map_*(Y, S¹)`. Since `Map_*(Y, ℝ)` is a linear subspace of `C(Y, ℝ)`, it is
contractible, and therefore so is `Map_*(Y, S¹)`. Combined with the decomposition
`C(Y, S¹) ≃ₜ S¹ × Map_*(Y, S¹)` of maps into a topological group
(`TauCeti.mappingSpaceGroupHomeomorph`), evaluation at `y₀` is a homotopy equivalence
`C(Y, S¹) ≃ₕ S¹`.

For `Y = S²` this is the statement that `Map_*(S², S¹)`, a model of `Ω²S¹`, is contractible and
that `Map(S², S¹) ≃ S¹ × Map_*(S², S¹)` is homotopy equivalent to `S¹`.

## Main declarations

* `Circle.basedMapLift`: the angle function of a based circle-valued map, characterized by
  `Circle.exp_basedMapLift_apply` and `Circle.eq_basedMapLift`.
* `Circle.continuous_basedMapLift`: the angle function depends continuously on the map.
* `Circle.basedMapExpHomeomorph`: `Map_*(Y, ℝ) ≃ₜ Map_*(Y, S¹)`, postcomposition with
  `Circle.exp`.
* `Circle.contractibleSpace_basedMap`: `Map_*(Y, S¹)` is contractible.
* `Circle.continuousMapHomotopyEquiv`: evaluation at `y₀` is a homotopy equivalence
  `C(Y, S¹) ≃ₕ S¹`, with homotopy inverse the constant maps.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.33.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

noncomputable section

open Topology TauCeti

namespace Circle

variable {Y : Type*} [TopologicalSpace Y] [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
  {y₀ : Y}

section Lift

private theorem existsUnique_basedMapLift (f : BasedMap Y Circle y₀ 1) :
    ∃! θ : C(Y, ℝ), θ y₀ = 0 ∧ exp ∘ θ = f.val :=
  isCoveringMap_exp.existsUnique_continuousMap_lifts f.val y₀ 0 (by rw [exp_zero, f.property])

/-- The **angle function** of a based map `f : (Y, y₀) → (S¹, 1)` on a simply connected, locally
path-connected space: the unique continuous `θ : Y → ℝ` with `θ y₀ = 0` and
`Circle.exp (θ y) = f y` for every `y`. -/
def basedMapLift (f : BasedMap Y Circle y₀ 1) : BasedMap Y ℝ y₀ 0 :=
  ⟨(existsUnique_basedMapLift f).exists.choose, (existsUnique_basedMapLift f).exists.choose_spec.1⟩

/-- The angle function of `f` lifts `f` through `Circle.exp`. -/
@[simp]
theorem exp_basedMapLift_apply (f : BasedMap Y Circle y₀ 1) (y : Y) :
    exp ((basedMapLift f).val y) = f.val y :=
  congr_fun (existsUnique_basedMapLift f).exists.choose_spec.2 y

/-- A based angle function of `f` is the angle function of `f`. -/
theorem eq_basedMapLift {f : BasedMap Y Circle y₀ 1} {θ : BasedMap Y ℝ y₀ 0}
    (h : ∀ y, exp (θ.val y) = f.val y) : θ = basedMapLift f :=
  Subtype.ext <| (existsUnique_basedMapLift f).unique ⟨θ.property, funext h⟩
    ⟨(basedMapLift f).property, funext (exp_basedMapLift_apply f)⟩

/-- The angle function of the based map `y ↦ Circle.exp (θ y)` is `θ`. -/
@[simp]
theorem basedMapLift_map_exp (θ : BasedMap Y ℝ y₀ 0) :
    basedMapLift (BasedMap.map exp exp_zero θ) = θ :=
  (eq_basedMapLift fun _ ↦ (BasedMap.map_apply _ _ _ _).symm).symm

/-- Postcomposing the angle function of `f` with `Circle.exp` gives back `f`. -/
@[simp]
theorem map_exp_basedMapLift (f : BasedMap Y Circle y₀ 1) :
    BasedMap.map exp exp_zero (basedMapLift f) = f :=
  Subtype.ext <| ContinuousMap.ext fun y ↦ by
    rw [BasedMap.map_apply, exp_basedMapLift_apply]

end Lift

section Continuity

/-- Near `f₀`, the angle function of `f` is that of `f₀` plus the principal argument of
`f / f₀`, as long as `f / f₀` avoids `-1`. -/
private theorem basedMapLift_apply_eq_add_arg {f₀ f : BasedMap Y Circle y₀ 1}
    (hf : ∀ y, f.val y * (f₀.val y)⁻¹ ≠ -1) (y : Y) :
    (basedMapLift f).val y =
      (basedMapLift f₀).val y + Complex.arg (f.val y * (f₀.val y)⁻¹ : Circle) := by
  have hcont : Continuous fun y ↦ Complex.arg (f.val y * (f₀.val y)⁻¹ : Circle) :=
    continuous_iff_continuousAt.2 fun y ↦ (continuousAt_arg (hf y)).comp
      (f := fun y ↦ f.val y * (f₀.val y)⁻¹) (by fun_prop : Continuous _).continuousAt
  let θ : BasedMap Y ℝ y₀ 0 := ⟨(basedMapLift f₀).val + ⟨_, hcont⟩, by
    simp [(basedMapLift f₀).property, f.property, f₀.property]⟩
  have hθ : θ = basedMapLift f := eq_basedMapLift fun y ↦ by
    simp only [θ, ContinuousMap.add_apply, ContinuousMap.coe_mk, exp_add,
      exp_basedMapLift_apply, exp_arg]
    rw [mul_comm (f.val y), mul_inv_cancel_left]
  -- the value of `θ` at `y` is the right-hand side by construction
  rw [← hθ]
  rfl

end Continuity

section Compact

variable [CompactSpace Y]

/-- The **angle function depends continuously on the map**: for a compact, simply connected and
locally path-connected space `Y`, the lift `Map_*(Y, S¹) → Map_*(Y, ℝ)` through `Circle.exp` is
continuous for the compact-open topologies. -/
theorem continuous_basedMapLift :
    Continuous (basedMapLift : BasedMap Y Circle y₀ 1 → BasedMap Y ℝ y₀ 0) := by
  have h1 : (1 : Circle) ≠ -1 := fun h ↦ by
    have := congrArg ((↑) : Circle → ℂ) h
    norm_num at this
  refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
  refine continuous_iff_continuousAt.2 fun ⟨f₀, y₁⟩ ↦ ?_
  -- the maps `f` with `f / f₀` avoiding `-1` form a neighbourhood of `f₀`, as `Y` is compact
  have hnhds : ∀ᶠ f : BasedMap Y Circle y₀ 1 in 𝓝 f₀,
      ∀ y, f.val y * (f₀.val y)⁻¹ ≠ -1 := by
    have hc : Continuous fun f : BasedMap Y Circle y₀ 1 ↦ f.val * f₀.val⁻¹ :=
      continuous_subtypeVal.mul continuous_const
    filter_upwards [hc.continuousAt.eventually (ContinuousMap.eventually_mapsTo isCompact_univ
      isOpen_ne fun y _ ↦ by
        simpa only [mul_inv_cancel, ContinuousMap.one_apply, Set.mem_ofPred_eq] using h1)]
      with f hf y
    exact hf (Set.mem_univ y)
  -- on that neighbourhood the angle function is given by `basedMapLift_apply_eq_add_arg`
  refine ContinuousAt.congr ?_ ((hnhds.prod_inl_nhds y₁).mono fun p hp ↦
    (basedMapLift_apply_eq_add_arg hp p.2).symm)
  have hev : Continuous fun p : BasedMap Y Circle y₀ 1 × Y ↦ p.1.val p.2 * (f₀.val p.2)⁻¹ :=
    (continuous_eval.comp (continuous_subtypeVal.prodMap continuous_id)).mul
      (f₀.val.continuous.comp continuous_snd).inv
  refine ((basedMapLift f₀).val.continuous.comp continuous_snd).continuousAt.add
    (ContinuousAt.comp (g := fun w : Circle ↦ Complex.arg w) ?_ hev.continuousAt)
  simpa only [mul_inv_cancel] using continuousAt_arg h1

/-- **Based maps into the circle are based angle functions.** For a compact, simply connected and
locally path-connected space `Y`, postcomposition with `Circle.exp` is a homeomorphism
`Map_*(Y, ℝ) ≃ₜ Map_*(Y, S¹)`, with inverse the angle function `Circle.basedMapLift`. -/
def basedMapExpHomeomorph (y₀ : Y) : BasedMap Y ℝ y₀ 0 ≃ₜ BasedMap Y Circle y₀ 1 where
  toFun := BasedMap.map exp exp_zero
  invFun := basedMapLift
  left_inv := basedMapLift_map_exp
  right_inv := map_exp_basedMapLift
  continuous_toFun := BasedMap.continuous_map _ _
  continuous_invFun := continuous_basedMapLift

/-- `Circle.basedMapExpHomeomorph` postcomposes with `Circle.exp`. -/
@[simp]
theorem basedMapExpHomeomorph_apply_val_apply (θ : BasedMap Y ℝ y₀ 0) (y : Y) :
    (basedMapExpHomeomorph y₀ θ).val y = exp (θ.val y) :=
  BasedMap.map_apply _ _ _ _

/-- The inverse of `Circle.basedMapExpHomeomorph` is the angle function. -/
@[simp]
theorem basedMapExpHomeomorph_symm_apply (f : BasedMap Y Circle y₀ 1) :
    (basedMapExpHomeomorph y₀).symm f = basedMapLift f :=
  (rfl)

/-- **`Map_*(Y, S¹)` is contractible** for a compact, simply connected and locally path-connected
space `Y`. For `Y = S²` this is the contractibility of `Map_*(S², S¹)`, a model of `Ω²S¹`. -/
instance contractibleSpace_basedMap (y₀ : Y) : ContractibleSpace (BasedMap Y Circle y₀ 1) := by
  -- `Map_*(Y, ℝ)` is a linear subspace of `C(Y, ℝ)`, hence contractible
  have hconv : Convex ℝ {θ : C(Y, ℝ) | θ y₀ = 0} := by
    intro θ hθ η hη a b _ _ _
    simp_all
  have : ContractibleSpace (BasedMap Y ℝ y₀ 0) :=
    hconv.contractibleSpace ⟨0, ContinuousMap.zero_apply y₀⟩
  exact (basedMapExpHomeomorph y₀).symm.contractibleSpace

/-- **Maps into the circle are homotopy equivalent to the circle.** For a compact, simply
connected and locally path-connected space `Y`, evaluation at a point `y₀` is a homotopy
equivalence `C(Y, S¹) ≃ₕ S¹`, with homotopy inverse the constant maps. -/
def continuousMapHomotopyEquiv (y₀ : Y) : ContinuousMap.HomotopyEquiv C(Y, Circle) Circle where
  toFun := ⟨fun f ↦ f y₀, continuous_eval_const y₀⟩
  invFun := ⟨ContinuousMap.const Y, ContinuousMap.continuous_const'⟩
  left_inv := by
    -- evaluation is `C(Y, S¹) ≃ₜ S¹ × Map_*(Y, S¹) ≃ₕ S¹`, collapsing the contractible factor,
    -- and the constant maps are a right inverse of it, hence a homotopy inverse
    let e := (mappingSpaceGroupHomeomorph (G := Circle) y₀).symm.toHomotopyEquiv.trans
      (ContinuousMap.HomotopyEquiv.prodContractible Circle (BasedMap Y Circle y₀ 1))
    have he : e.toFun = ⟨fun f ↦ f y₀, continuous_eval_const y₀⟩ := by
      ext f
      simp [e, -Homeomorph.symm_toHomotopyEquiv]
    refine ContinuousMap.Homotopic.comp_homotopic_id_of_comp_homotopic_id ?_ (he ▸ e.left_inv)
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id Circle) using 1
    ext z
    simp
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id Circle) using 1
    ext z
    simp

/-- `Circle.continuousMapHomotopyEquiv` is evaluation at the basepoint. -/
@[simp]
theorem continuousMapHomotopyEquiv_apply (y₀ : Y) (f : C(Y, Circle)) :
    continuousMapHomotopyEquiv y₀ f = f y₀ :=
  (rfl)

/-- The homotopy inverse of `Circle.continuousMapHomotopyEquiv` sends a point to the constant
map. -/
@[simp]
theorem continuousMapHomotopyEquiv_symm_apply (y₀ : Y) (z : Circle) :
    (continuousMapHomotopyEquiv y₀).symm z = ContinuousMap.const Y z :=
  (rfl)

end Compact

end Circle
